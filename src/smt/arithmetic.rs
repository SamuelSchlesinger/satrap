use std::collections::{BTreeMap, HashMap, HashSet};

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use crate::UnknownReason;

use super::term::{Sort, TermError, TermId, TermStore};
use super::theory::{SignedTerm, Theory, TheoryCheck, TheoryLemma, TheoryPropagation};

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(crate) struct ArithmeticExpressionId(pub(crate) u32);

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(crate) struct ArithmeticVariableId(pub(crate) u32);

/// A canonical affine expression over exact rational coefficients.
///
/// Integer-sorted terms use the same representation but are admitted only
/// when every coefficient and constant is integral. Keeping one exact
/// representation makes Int-to-Real coercion lossless.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) struct LinearExpression {
    pub(crate) constant: BigRational,
    pub(crate) coefficients: BTreeMap<ArithmeticVariableId, BigRational>,
}

impl LinearExpression {
    pub(crate) fn zero() -> Self {
        Self {
            constant: BigRational::zero(),
            coefficients: BTreeMap::new(),
        }
    }

    pub(crate) fn constant(value: BigRational) -> Self {
        Self {
            constant: value,
            coefficients: BTreeMap::new(),
        }
    }

    pub(crate) fn variable(variable: ArithmeticVariableId) -> Self {
        Self {
            constant: BigRational::zero(),
            coefficients: BTreeMap::from([(variable, BigRational::one())]),
        }
    }

    pub(crate) fn is_constant(&self) -> bool {
        self.coefficients.is_empty()
    }

    pub(crate) fn add_scaled(&mut self, other: &Self, scale: &BigRational) {
        self.constant += &other.constant * scale;
        for (&variable, coefficient) in &other.coefficients {
            let updated = self
                .coefficients
                .get(&variable)
                .cloned()
                .unwrap_or_else(BigRational::zero)
                + coefficient * scale;
            if updated.is_zero() {
                self.coefficients.remove(&variable);
            } else {
                self.coefficients.insert(variable, updated);
            }
        }
    }

    pub(crate) fn sum(expressions: impl IntoIterator<Item = Self>) -> Self {
        let mut result = Self::zero();
        for expression in expressions {
            result.add_scaled(&expression, &BigRational::one());
        }
        result
    }

    pub(crate) fn scaled(mut self, scale: &BigRational) -> Self {
        if scale.is_zero() {
            return Self::zero();
        }
        self.constant *= scale;
        for coefficient in self.coefficients.values_mut() {
            *coefficient *= scale;
        }
        self
    }

    pub(crate) fn evaluate(
        &self,
        value: impl Fn(ArithmeticVariableId) -> BigRational,
    ) -> BigRational {
        self.coefficients
            .iter()
            .fold(self.constant.clone(), |sum, (&variable, coefficient)| {
                sum + coefficient * value(variable)
            })
    }
}

pub(crate) fn rational_from_decimal(text: &str) -> Option<BigRational> {
    let (whole, fractional) = text.split_once('.')?;
    if whole.is_empty()
        || fractional.is_empty()
        || !whole.bytes().all(|byte| byte.is_ascii_digit())
        || !fractional.bytes().all(|byte| byte.is_ascii_digit())
    {
        return None;
    }
    let denominator = BigInt::from(10_u8).pow(u32::try_from(fractional.len()).ok()?);
    let whole = BigInt::parse_bytes(whole.as_bytes(), 10)?;
    let fractional = BigInt::parse_bytes(fractional.as_bytes(), 10)?;
    Some(BigRational::new(
        whole * &denominator + fractional,
        denominator,
    ))
}

#[derive(Clone, Debug, Default)]
pub(crate) struct ArithmeticModel {
    values: HashMap<ArithmeticVariableId, BigRational>,
}

impl ArithmeticModel {
    pub(crate) fn variable_value(&self, variable: ArithmeticVariableId) -> BigRational {
        self.values
            .get(&variable)
            .cloned()
            .unwrap_or_else(BigRational::zero)
    }

    pub(crate) fn expression_value(&self, expression: &LinearExpression) -> BigRational {
        expression.evaluate(|variable| self.variable_value(variable))
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct LinearConstraint {
    /// `expression <= 0`, or `expression < 0` when `strict` is set.
    expression: LinearExpression,
    strict: bool,
    sort: Sort,
}

#[derive(Clone, Debug)]
struct EliminationStage {
    variable: ArithmeticVariableId,
    bounds: Vec<LinearConstraint>,
}

enum ArithmeticSolve {
    Sat(ArithmeticModel),
    Unsat,
    Incomplete,
}

fn solve_constraints(
    constraints: Vec<LinearConstraint>,
    variable_sorts: &[Sort],
) -> ArithmeticSolve {
    let involved = constraints
        .iter()
        .flat_map(|constraint| constraint.expression.coefficients.keys().copied())
        .collect::<HashSet<_>>();
    let has_integer = involved
        .iter()
        .any(|variable| variable_sorts[variable.0 as usize] == Sort::Int);
    let has_real = involved
        .iter()
        .any(|variable| variable_sorts[variable.0 as usize] == Sort::Real);
    if has_integer
        && (has_real
            || constraints
                .iter()
                .any(|constraint| constraint.sort == Sort::Real))
    {
        return ArithmeticSolve::Incomplete;
    }
    if has_integer {
        return match solve_integer_difference(constraints.clone(), variable_sorts) {
            ArithmeticSolve::Incomplete => solve_integer_linear(constraints, variable_sorts),
            result => result,
        };
    }
    solve_real_linear(constraints, variable_sorts)
}

fn solve_real_linear(
    constraints: Vec<LinearConstraint>,
    variable_sorts: &[Sort],
) -> ArithmeticSolve {
    let Some(mut constraints) = simplify_constraints(constraints) else {
        return ArithmeticSolve::Unsat;
    };
    let variables = constraints
        .iter()
        .flat_map(|constraint| constraint.expression.coefficients.keys().copied())
        .collect::<HashSet<_>>();
    let mut variables = variables.into_iter().collect::<Vec<_>>();
    variables.sort_unstable();
    let mut stages = Vec::with_capacity(variables.len());

    for variable in variables {
        let mut independent = Vec::new();
        let mut upper = Vec::new();
        let mut lower = Vec::new();
        let mut bounds = Vec::new();
        for constraint in constraints {
            let coefficient = constraint
                .expression
                .coefficients
                .get(&variable)
                .cloned()
                .unwrap_or_else(BigRational::zero);
            if coefficient.is_zero() {
                independent.push(constraint);
            } else if coefficient.is_positive() {
                bounds.push(constraint.clone());
                upper.push((constraint, coefficient));
            } else {
                bounds.push(constraint.clone());
                lower.push((constraint, coefficient));
            }
        }
        for (upper_constraint, upper_coefficient) in &upper {
            for (lower_constraint, lower_coefficient) in &lower {
                let mut expression = upper_constraint
                    .expression
                    .clone()
                    .scaled(&(-lower_coefficient));
                expression.add_scaled(&lower_constraint.expression, upper_coefficient);
                expression.coefficients.remove(&variable);
                independent.push(LinearConstraint {
                    expression,
                    strict: upper_constraint.strict || lower_constraint.strict,
                    sort: Sort::Real,
                });
            }
        }
        stages.push(EliminationStage { variable, bounds });
        let Some(simplified) = simplify_constraints(independent) else {
            return ArithmeticSolve::Unsat;
        };
        constraints = simplified;
    }

    let mut values = HashMap::new();
    for stage in stages.into_iter().rev() {
        let mut lower: Option<(BigRational, bool)> = None;
        let mut upper: Option<(BigRational, bool)> = None;
        for constraint in stage.bounds {
            let coefficient = constraint.expression.coefficients[&stage.variable].clone();
            let mut remainder = constraint.expression.constant;
            for (&variable, coefficient) in &constraint.expression.coefficients {
                if variable != stage.variable {
                    remainder += coefficient
                        * values
                            .get(&variable)
                            .cloned()
                            .unwrap_or_else(BigRational::zero);
                }
            }
            let bound = -remainder / &coefficient;
            if coefficient.is_positive() {
                strengthen_upper(&mut upper, bound, constraint.strict);
            } else {
                strengthen_lower(&mut lower, bound, constraint.strict);
            }
        }
        let value = choose_between(lower.as_ref(), upper.as_ref());
        values.insert(stage.variable, value);
    }
    for (index, &sort) in variable_sorts.iter().enumerate() {
        if sort == Sort::Real {
            values
                .entry(ArithmeticVariableId(index as u32))
                .or_insert_with(BigRational::zero);
        }
    }
    ArithmeticSolve::Sat(ArithmeticModel { values })
}

fn simplify_constraints(constraints: Vec<LinearConstraint>) -> Option<Vec<LinearConstraint>> {
    let mut seen = HashSet::new();
    let mut result = Vec::new();
    for constraint in constraints {
        if constraint.expression.coefficients.is_empty() {
            let satisfied = if constraint.strict {
                constraint.expression.constant.is_negative()
            } else {
                !constraint.expression.constant.is_positive()
            };
            if !satisfied {
                return None;
            }
        } else if seen.insert(constraint.clone()) {
            result.push(constraint);
        }
    }
    Some(result)
}

fn strengthen_lower(current: &mut Option<(BigRational, bool)>, value: BigRational, strict: bool) {
    match current {
        Some((best, _)) if value < *best => {}
        Some((best, best_strict)) if value == *best => *best_strict |= strict,
        _ => *current = Some((value, strict)),
    }
}

fn strengthen_upper(current: &mut Option<(BigRational, bool)>, value: BigRational, strict: bool) {
    match current {
        Some((best, _)) if value > *best => {}
        Some((best, best_strict)) if value == *best => *best_strict |= strict,
        _ => *current = Some((value, strict)),
    }
}

fn choose_between(
    lower: Option<&(BigRational, bool)>,
    upper: Option<&(BigRational, bool)>,
) -> BigRational {
    match (lower, upper) {
        (Some((lower, lower_strict)), Some((upper, upper_strict))) => {
            debug_assert!(
                lower < upper || (lower == upper && !lower_strict && !upper_strict),
                "Fourier-Motzkin reconstruction received incompatible bounds"
            );
            if lower == upper {
                lower.clone()
            } else {
                (lower + upper) / BigInt::from(2)
            }
        }
        (Some((lower, strict)), None) => {
            if *strict {
                lower + BigInt::one()
            } else {
                lower.clone()
            }
        }
        (None, Some((upper, strict))) => {
            if *strict {
                upper - BigInt::one()
            } else {
                upper.clone()
            }
        }
        (None, None) => BigRational::zero(),
    }
}

#[derive(Clone, Debug)]
struct DifferenceEdge {
    from: usize,
    to: usize,
    weight: BigInt,
}

fn solve_integer_difference(
    constraints: Vec<LinearConstraint>,
    variable_sorts: &[Sort],
) -> ArithmeticSolve {
    let zero = variable_sorts.len();
    let mut edges = Vec::new();
    for constraint in constraints {
        if constraint.sort != Sort::Int {
            return ArithmeticSolve::Incomplete;
        }
        if constraint.expression.coefficients.is_empty() {
            let satisfied = if constraint.strict {
                constraint.expression.constant.is_negative()
            } else {
                !constraint.expression.constant.is_positive()
            };
            if !satisfied {
                return ArithmeticSolve::Unsat;
            }
            continue;
        }
        let Some(edge) = difference_edge(&constraint, zero) else {
            return ArithmeticSolve::Incomplete;
        };
        edges.push(edge);
    }

    let vertex_count = variable_sorts.len() + 1;
    let mut distance = vec![BigInt::zero(); vertex_count];
    for iteration in 0..vertex_count {
        let mut changed = false;
        for edge in &edges {
            let candidate = &distance[edge.from] + &edge.weight;
            if candidate < distance[edge.to] {
                distance[edge.to] = candidate;
                changed = true;
            }
        }
        if !changed {
            break;
        }
        if iteration + 1 == vertex_count {
            return ArithmeticSolve::Unsat;
        }
    }

    let zero_value = distance[zero].clone();
    let values = variable_sorts
        .iter()
        .enumerate()
        .filter(|(_, sort)| **sort == Sort::Int)
        .map(|(index, _)| {
            (
                ArithmeticVariableId(index as u32),
                BigRational::from_integer(&distance[index] - &zero_value),
            )
        })
        .collect();
    ArithmeticSolve::Sat(ArithmeticModel { values })
}

fn difference_edge(constraint: &LinearConstraint, zero: usize) -> Option<DifferenceEdge> {
    let coefficients = constraint
        .expression
        .coefficients
        .iter()
        .map(|(&variable, coefficient)| (variable, coefficient.clone()))
        .collect::<Vec<_>>();
    let (positive, negative, scale) = match coefficients.as_slice() {
        [(variable, coefficient)] if coefficient.is_positive() => {
            (variable.0 as usize, zero, coefficient.clone())
        }
        [(variable, coefficient)] if coefficient.is_negative() => {
            (zero, variable.0 as usize, -coefficient)
        }
        [(first, first_coefficient), (second, second_coefficient)]
            if first_coefficient.is_positive() && first_coefficient == &(-second_coefficient) =>
        {
            (
                first.0 as usize,
                second.0 as usize,
                first_coefficient.clone(),
            )
        }
        [(first, first_coefficient), (second, second_coefficient)]
            if second_coefficient.is_positive() && second_coefficient == &(-first_coefficient) =>
        {
            (
                second.0 as usize,
                first.0 as usize,
                second_coefficient.clone(),
            )
        }
        _ => return None,
    };
    let bound = -constraint.expression.constant.clone() / scale;
    let weight = if constraint.strict {
        bound.ceil().to_integer() - BigInt::one()
    } else {
        bound.floor().to_integer()
    };
    Some(DifferenceEdge {
        from: negative,
        to: positive,
        weight,
    })
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct IntegerExpression {
    constant: BigInt,
    coefficients: BTreeMap<ArithmeticVariableId, BigInt>,
}

impl IntegerExpression {
    fn from_linear(expression: &LinearExpression) -> Option<Self> {
        if !expression.constant.is_integer()
            || expression
                .coefficients
                .values()
                .any(|coefficient| !coefficient.is_integer())
        {
            return None;
        }
        Some(Self {
            constant: expression.constant.to_integer(),
            coefficients: expression
                .coefficients
                .iter()
                .map(|(&variable, coefficient)| (variable, coefficient.to_integer()))
                .collect(),
        })
    }

    fn variable(variable: ArithmeticVariableId) -> Self {
        Self {
            constant: BigInt::zero(),
            coefficients: BTreeMap::from([(variable, BigInt::one())]),
        }
    }

    fn coefficient(&self, variable: ArithmeticVariableId) -> BigInt {
        self.coefficients
            .get(&variable)
            .cloned()
            .unwrap_or_else(BigInt::zero)
    }

    fn without(&self, variable: ArithmeticVariableId) -> Self {
        let mut result = self.clone();
        result.coefficients.remove(&variable);
        result
    }

    fn scaled(mut self, scale: &BigInt) -> Self {
        if scale.is_zero() {
            return Self {
                constant: BigInt::zero(),
                coefficients: BTreeMap::new(),
            };
        }
        self.constant *= scale;
        for coefficient in self.coefficients.values_mut() {
            *coefficient *= scale;
        }
        self
    }

    fn negated(self) -> Self {
        self.scaled(&BigInt::from(-1))
    }

    fn add_scaled(&mut self, other: &Self, scale: &BigInt) {
        self.constant += &other.constant * scale;
        for (&variable, coefficient) in &other.coefficients {
            let updated = self
                .coefficients
                .get(&variable)
                .cloned()
                .unwrap_or_else(BigInt::zero)
                + coefficient * scale;
            if updated.is_zero() {
                self.coefficients.remove(&variable);
            } else {
                self.coefficients.insert(variable, updated);
            }
        }
    }

    fn substitute(&self, variable: ArithmeticVariableId, value: &Self) -> Self {
        let coefficient = self.coefficient(variable);
        let mut result = self.without(variable);
        result.add_scaled(value, &coefficient);
        result
    }

    fn evaluate(&self, values: &HashMap<ArithmeticVariableId, BigInt>) -> BigInt {
        self.coefficients
            .iter()
            .fold(self.constant.clone(), |sum, (&variable, coefficient)| {
                sum + coefficient * values.get(&variable).cloned().unwrap_or_else(BigInt::zero)
            })
    }

    fn as_linear(&self) -> LinearExpression {
        LinearExpression {
            constant: BigRational::from_integer(self.constant.clone()),
            coefficients: self
                .coefficients
                .iter()
                .map(|(&variable, coefficient)| {
                    (variable, BigRational::from_integer(coefficient.clone()))
                })
                .collect(),
        }
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct IntegerInequality {
    /// An integer-valued affine expression constrained to be strictly negative.
    expression: IntegerExpression,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct DivisibilityConstraint {
    modulus: BigInt,
    expression: IntegerExpression,
}

#[derive(Clone, Debug, Default)]
struct IntegerProblem {
    inequalities: Vec<IntegerInequality>,
    divisibilities: Vec<DivisibilityConstraint>,
}

impl IntegerProblem {
    fn substitute(&self, variable: ArithmeticVariableId, value: &IntegerExpression) -> Self {
        Self {
            inequalities: self
                .inequalities
                .iter()
                .map(|constraint| IntegerInequality {
                    expression: constraint.expression.substitute(variable, value),
                })
                .collect(),
            divisibilities: self
                .divisibilities
                .iter()
                .map(|constraint| DivisibilityConstraint {
                    modulus: constraint.modulus.clone(),
                    expression: constraint.expression.substitute(variable, value),
                })
                .collect(),
        }
    }

    fn mentions(&self, variable: ArithmeticVariableId) -> bool {
        self.inequalities
            .iter()
            .any(|constraint| constraint.expression.coefficients.contains_key(&variable))
            || self
                .divisibilities
                .iter()
                .any(|constraint| constraint.expression.coefficients.contains_key(&variable))
    }
}

struct CooperElimination {
    normalized: IntegerProblem,
    scale: BigInt,
    period: BigInt,
    lower_bases: Vec<IntegerExpression>,
    upper_bases: Vec<IntegerExpression>,
}

fn solve_integer_linear(
    constraints: Vec<LinearConstraint>,
    variable_sorts: &[Sort],
) -> ArithmeticSolve {
    let mut problem = IntegerProblem::default();
    for constraint in &constraints {
        if constraint.sort != Sort::Int {
            return ArithmeticSolve::Incomplete;
        }
        let Some(mut expression) = IntegerExpression::from_linear(&constraint.expression) else {
            return ArithmeticSolve::Incomplete;
        };
        if !constraint.strict {
            // Integer e <= 0 is exactly e - 1 < 0.
            expression.constant -= BigInt::one();
        }
        problem.inequalities.push(IntegerInequality { expression });
    }

    let mut variables = problem
        .inequalities
        .iter()
        .flat_map(|constraint| constraint.expression.coefficients.keys().copied())
        .collect::<HashSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    variables.sort_unstable();

    let Some(mut integer_values) = solve_integer_problem(problem, &variables) else {
        return ArithmeticSolve::Unsat;
    };
    for (index, &sort) in variable_sorts.iter().enumerate() {
        if sort == Sort::Int {
            integer_values
                .entry(ArithmeticVariableId(index as u32))
                .or_insert_with(BigInt::zero);
        }
    }
    let values = integer_values
        .into_iter()
        .map(|(variable, value)| (variable, BigRational::from_integer(value)))
        .collect::<HashMap<_, _>>();
    let model = ArithmeticModel { values };
    if constraints.iter().all(|constraint| {
        let value = model.expression_value(&constraint.expression);
        if constraint.strict {
            value.is_negative()
        } else {
            !value.is_positive()
        }
    }) {
        ArithmeticSolve::Sat(model)
    } else {
        // A candidate that fails replay indicates an internal reconstruction
        // defect. Never expose it as a satisfiable model.
        ArithmeticSolve::Incomplete
    }
}

fn solve_integer_problem(
    problem: IntegerProblem,
    variables: &[ArithmeticVariableId],
) -> Option<HashMap<ArithmeticVariableId, BigInt>> {
    let problem = simplify_integer_problem(problem)?;
    if variables.is_empty() {
        debug_assert!(
            problem.inequalities.is_empty() && problem.divisibilities.is_empty(),
            "all constant constraints should be removed during simplification"
        );
        return Some(HashMap::new());
    }
    if variables.len() >= 5
        && problem.divisibilities.is_empty()
        && variables.iter().all(|&variable| {
            !problem.mentions(variable) || integer_constant_bounds(&problem, variable).is_some()
        })
    {
        return solve_bounded_integer_relaxation(problem, variables);
    }
    if let Some((variable, lower, upper)) = choose_bounded_integer_variable(&problem, variables) {
        if lower > upper {
            return None;
        }
        let remaining = variables
            .iter()
            .copied()
            .filter(|candidate| *candidate != variable)
            .collect::<Vec<_>>();
        let mut value = lower;
        while value <= upper {
            let candidate = IntegerExpression {
                constant: value.clone(),
                coefficients: BTreeMap::new(),
            };
            let reduced = problem.substitute(variable, &candidate);
            if let Some(mut values) = solve_integer_problem(reduced, &remaining) {
                values.insert(variable, value);
                return Some(values);
            }
            value += BigInt::one();
        }
        return None;
    }
    let variable = choose_elimination_variable(&problem, variables)
        .expect("the nonempty variable slice has an elimination candidate");
    let remaining = variables
        .iter()
        .copied()
        .filter(|candidate| *candidate != variable)
        .collect::<Vec<_>>();
    if !problem.mentions(variable) {
        let mut values = solve_integer_problem(problem, &remaining)?;
        values.insert(variable, BigInt::zero());
        return Some(values);
    }

    let elimination = normalize_cooper_variable(&problem, variable);
    if !elimination.lower_bases.is_empty() {
        for base in &elimination.lower_bases {
            let mut offset = BigInt::one();
            while offset <= elimination.period {
                let mut candidate = base.clone();
                candidate.constant += &offset;
                if let Some(values) =
                    solve_cooper_candidate(&elimination, variable, &candidate, &remaining)
                {
                    return Some(values);
                }
                offset += BigInt::one();
            }
        }
    } else if !elimination.upper_bases.is_empty() {
        for base in &elimination.upper_bases {
            let mut offset = BigInt::one();
            while offset <= elimination.period {
                let mut candidate = base.clone();
                candidate.constant -= &offset;
                if let Some(values) =
                    solve_cooper_candidate(&elimination, variable, &candidate, &remaining)
                {
                    return Some(values);
                }
                offset += BigInt::one();
            }
        }
    } else {
        let mut candidate_value = BigInt::zero();
        while candidate_value < elimination.period {
            let candidate = IntegerExpression {
                constant: candidate_value.clone(),
                coefficients: BTreeMap::new(),
            };
            if let Some(values) =
                solve_cooper_candidate(&elimination, variable, &candidate, &remaining)
            {
                return Some(values);
            }
            candidate_value += BigInt::one();
        }
    }
    None
}

fn solve_bounded_integer_relaxation(
    problem: IntegerProblem,
    variables: &[ArithmeticVariableId],
) -> Option<HashMap<ArithmeticVariableId, BigInt>> {
    let variable_count = variables
        .iter()
        .map(|variable| variable.0 as usize + 1)
        .max()
        .unwrap_or(0);
    let relaxation = problem
        .inequalities
        .iter()
        .map(|constraint| {
            let mut expression = constraint.expression.as_linear();
            // Integer e < 0 is equivalent to e + 1 <= 0. The latter is a
            // tighter real relaxation than retaining the open integer bound.
            expression.constant += BigInt::one();
            LinearConstraint {
                expression,
                strict: false,
                sort: Sort::Real,
            }
        })
        .collect();
    let model = match solve_real_linear(relaxation, &vec![Sort::Real; variable_count]) {
        ArithmeticSolve::Sat(model) => model,
        ArithmeticSolve::Unsat => return None,
        ArithmeticSolve::Incomplete => {
            unreachable!("exact real linear elimination is complete")
        }
    };
    let fractional = variables.iter().copied().find_map(|variable| {
        let value = model.variable_value(variable);
        (!value.is_integer()).then_some((variable, value))
    });
    let Some((variable, value)) = fractional else {
        let values = variables
            .iter()
            .copied()
            .map(|variable| (variable, model.variable_value(variable).to_integer()))
            .collect::<HashMap<_, _>>();
        debug_assert!(
            problem
                .inequalities
                .iter()
                .all(|constraint| constraint.expression.evaluate(&values).is_negative()),
            "an integral relaxation model must satisfy the integer problem"
        );
        return Some(values);
    };

    let floor = value.floor().to_integer();
    let ceil = value.ceil().to_integer();
    let mut lower_branch = problem.clone();
    lower_branch.inequalities.push(IntegerInequality {
        // variable <= floor
        expression: IntegerExpression {
            constant: -floor - BigInt::one(),
            coefficients: BTreeMap::from([(variable, BigInt::one())]),
        },
    });
    if let Some(values) = solve_integer_problem(lower_branch, variables) {
        return Some(values);
    }
    let mut upper_branch = problem;
    upper_branch.inequalities.push(IntegerInequality {
        // variable >= ceil
        expression: IntegerExpression {
            constant: ceil - BigInt::one(),
            coefficients: BTreeMap::from([(variable, BigInt::from(-1))]),
        },
    });
    solve_integer_problem(upper_branch, variables)
}

fn choose_bounded_integer_variable(
    problem: &IntegerProblem,
    variables: &[ArithmeticVariableId],
) -> Option<(ArithmeticVariableId, BigInt, BigInt)> {
    variables
        .iter()
        .filter_map(|&variable| {
            let (lower, upper) = integer_constant_bounds(problem, variable)?;
            let width = &upper - &lower;
            Some((width, variable, lower, upper))
        })
        .min_by(|left, right| left.0.cmp(&right.0).then_with(|| left.1.cmp(&right.1)))
        .map(|(_, variable, lower, upper)| (variable, lower, upper))
}

fn integer_constant_bounds(
    problem: &IntegerProblem,
    variable: ArithmeticVariableId,
) -> Option<(BigInt, BigInt)> {
    let mut lower = None;
    let mut upper = None;
    for constraint in &problem.inequalities {
        if constraint.expression.coefficients.len() != 1 {
            continue;
        }
        let coefficient = constraint.expression.coefficient(variable);
        if coefficient.is_zero() {
            continue;
        }
        let boundary =
            BigRational::new(-constraint.expression.constant.clone(), coefficient.clone());
        if coefficient.is_positive() {
            let candidate = boundary.ceil().to_integer() - BigInt::one();
            if upper.as_ref().is_none_or(|current| candidate < *current) {
                upper = Some(candidate);
            }
        } else {
            let candidate = boundary.floor().to_integer() + BigInt::one();
            if lower.as_ref().is_none_or(|current| candidate > *current) {
                lower = Some(candidate);
            }
        }
    }
    Some((lower?, upper?))
}

fn solve_cooper_candidate(
    elimination: &CooperElimination,
    variable: ArithmeticVariableId,
    candidate: &IntegerExpression,
    remaining: &[ArithmeticVariableId],
) -> Option<HashMap<ArithmeticVariableId, BigInt>> {
    let reduced = elimination.normalized.substitute(variable, candidate);
    let mut values = solve_integer_problem(reduced, remaining)?;
    let scaled_value = candidate.evaluate(&values);
    if (&scaled_value % &elimination.scale) != BigInt::zero() {
        return None;
    }
    values.insert(variable, scaled_value / &elimination.scale);
    Some(values)
}

fn choose_elimination_variable(
    problem: &IntegerProblem,
    variables: &[ArithmeticVariableId],
) -> Option<ArithmeticVariableId> {
    variables.iter().copied().min_by(|left, right| {
        cooper_elimination_cost(problem, *left)
            .cmp(&cooper_elimination_cost(problem, *right))
            .then_with(|| left.cmp(right))
    })
}

fn cooper_elimination_cost(problem: &IntegerProblem, variable: ArithmeticVariableId) -> BigInt {
    let mut scale = BigInt::one();
    let mut lower_count = 0_u64;
    let mut upper_count = 0_u64;
    let mut mentioned = false;
    for constraint in &problem.inequalities {
        let coefficient = constraint.expression.coefficient(variable);
        if coefficient.is_zero() {
            continue;
        }
        mentioned = true;
        scale = integer_lcm(&scale, &coefficient.abs());
        if coefficient.is_negative() {
            lower_count += 1;
        } else {
            upper_count += 1;
        }
    }
    for constraint in &problem.divisibilities {
        let coefficient = constraint.expression.coefficient(variable);
        if coefficient.is_zero() {
            continue;
        }
        mentioned = true;
        scale = integer_lcm(&scale, &coefficient.abs());
    }
    if !mentioned {
        return BigInt::zero();
    }

    let mut period = scale.clone();
    for constraint in &problem.divisibilities {
        let coefficient = constraint.expression.coefficient(variable);
        if coefficient.is_zero() {
            continue;
        }
        let transformed_modulus = (&scale / coefficient.abs()) * constraint.modulus.abs();
        period = integer_lcm(&period, &transformed_modulus);
    }
    let candidate_count = if lower_count != 0 {
        lower_count
    } else if upper_count != 0 {
        upper_count
    } else {
        1
    };
    period * BigInt::from(candidate_count)
}

fn normalize_cooper_variable(
    problem: &IntegerProblem,
    variable: ArithmeticVariableId,
) -> CooperElimination {
    let coefficients = problem
        .inequalities
        .iter()
        .map(|constraint| constraint.expression.coefficient(variable))
        .chain(
            problem
                .divisibilities
                .iter()
                .map(|constraint| constraint.expression.coefficient(variable)),
        )
        .filter(|coefficient| !coefficient.is_zero())
        .collect::<Vec<_>>();
    debug_assert!(
        !coefficients.is_empty(),
        "normalization requires a mentioned variable"
    );
    let scale = coefficients
        .iter()
        .fold(BigInt::one(), |result, coefficient| {
            integer_lcm(&result, &coefficient.abs())
        });

    let mut normalized = IntegerProblem::default();
    let mut lower_bases = Vec::new();
    let mut upper_bases = Vec::new();
    for constraint in &problem.inequalities {
        let coefficient = constraint.expression.coefficient(variable);
        if coefficient.is_zero() {
            normalized.inequalities.push(constraint.clone());
            continue;
        }
        let factor = &scale / coefficient.abs();
        let mut expression = constraint.expression.without(variable).scaled(&factor);
        expression.coefficients.insert(
            variable,
            if coefficient.is_positive() {
                BigInt::one()
            } else {
                BigInt::from(-1)
            },
        );
        if coefficient.is_positive() {
            upper_bases.push(expression.without(variable).negated());
        } else {
            lower_bases.push(expression.without(variable));
        }
        normalized
            .inequalities
            .push(IntegerInequality { expression });
    }

    for constraint in &problem.divisibilities {
        let coefficient = constraint.expression.coefficient(variable);
        if coefficient.is_zero() {
            normalized.divisibilities.push(constraint.clone());
            continue;
        }
        let factor = &scale / coefficient.abs();
        let mut expression = constraint.expression.without(variable).scaled(&factor);
        expression.coefficients.insert(
            variable,
            if coefficient.is_positive() {
                BigInt::one()
            } else {
                BigInt::from(-1)
            },
        );
        normalized.divisibilities.push(DivisibilityConstraint {
            modulus: &constraint.modulus * factor,
            expression,
        });
    }
    normalized.divisibilities.push(DivisibilityConstraint {
        modulus: scale.clone(),
        expression: IntegerExpression::variable(variable),
    });
    let period = normalized
        .divisibilities
        .iter()
        .fold(BigInt::one(), |result, constraint| {
            integer_lcm(&result, &constraint.modulus)
        });

    CooperElimination {
        normalized,
        scale,
        period,
        lower_bases,
        upper_bases,
    }
}

fn simplify_integer_problem(problem: IntegerProblem) -> Option<IntegerProblem> {
    let mut inequalities = Vec::new();
    let mut seen_inequalities = HashSet::new();
    for mut constraint in problem.inequalities {
        let coefficient_gcd = constraint
            .expression
            .coefficients
            .values()
            .fold(BigInt::zero(), |result, coefficient| {
                integer_gcd(&result, coefficient)
            });
        if coefficient_gcd > BigInt::one() {
            constraint.expression.constant =
                BigRational::new(constraint.expression.constant, coefficient_gcd.clone())
                    .floor()
                    .to_integer();
            for coefficient in constraint.expression.coefficients.values_mut() {
                *coefficient /= &coefficient_gcd;
            }
        }
        if constraint.expression.coefficients.is_empty() {
            if !constraint.expression.constant.is_negative() {
                return None;
            }
        } else if seen_inequalities.insert(constraint.clone()) {
            inequalities.push(constraint);
        }
    }

    let mut divisibilities = Vec::new();
    let mut seen_divisibilities = HashSet::new();
    for mut constraint in problem.divisibilities {
        constraint.modulus = constraint.modulus.abs();
        debug_assert!(
            !constraint.modulus.is_zero(),
            "divisibility modulus must be positive"
        );
        if constraint.modulus.is_zero() {
            return None;
        }
        let common_gcd = constraint
            .expression
            .coefficients
            .values()
            .fold(constraint.modulus.clone(), |result, coefficient| {
                integer_gcd(&result, coefficient)
            });
        if (&constraint.expression.constant % &common_gcd) != BigInt::zero() {
            return None;
        }
        if common_gcd > BigInt::one() {
            constraint.modulus /= &common_gcd;
            constraint.expression.constant /= &common_gcd;
            for coefficient in constraint.expression.coefficients.values_mut() {
                *coefficient /= &common_gcd;
            }
        }
        if constraint.modulus == BigInt::one() {
            continue;
        }
        if constraint.expression.coefficients.is_empty() {
            if (&constraint.expression.constant % &constraint.modulus) != BigInt::zero() {
                return None;
            }
        } else if seen_divisibilities.insert(constraint.clone()) {
            divisibilities.push(constraint);
        }
    }
    Some(IntegerProblem {
        inequalities,
        divisibilities,
    })
}

fn integer_gcd(left: &BigInt, right: &BigInt) -> BigInt {
    let mut left = left.abs();
    let mut right = right.abs();
    while !right.is_zero() {
        let remainder = &left % &right;
        left = right;
        right = remainder;
    }
    left
}

fn integer_lcm(left: &BigInt, right: &BigInt) -> BigInt {
    if left.is_zero() || right.is_zero() {
        BigInt::zero()
    } else {
        ((left / integer_gcd(left, right)) * right).abs()
    }
}

#[derive(Debug, Default)]
pub(crate) struct ArithmeticTheory {
    required: Vec<TermId>,
    predicates: Vec<super::term::ArithmeticPredicate>,
    ites: Vec<super::term::ArithmeticIte>,
    assignments: HashMap<TermId, bool>,
    levels: Vec<usize>,
    trail: Vec<(TermId, Option<bool>)>,
}

impl Theory for ArithmeticTheory {
    type Model = ArithmeticModel;

    fn prepare(
        &mut self,
        terms: &mut TermStore,
        relevant: &HashSet<TermId>,
    ) -> Result<(), TermError> {
        self.required.clear();
        self.predicates.clear();
        self.ites.clear();
        let mut relevant_boolean = relevant.clone();
        let mut variables = HashSet::new();
        let mut selected_predicates = HashSet::new();
        let mut selected_ites = HashSet::new();
        loop {
            let mut changed = false;
            for predicate in terms.arithmetic_predicates() {
                if !relevant_boolean.contains(&predicate.term)
                    || !selected_predicates.insert(predicate.term)
                {
                    continue;
                }
                self.predicates.push(*predicate);
                self.required.push(predicate.term);
                variables.extend(
                    terms
                        .arithmetic_expression(predicate.expression)
                        .expect("arithmetic predicates refer to stored expressions")
                        .coefficients
                        .keys()
                        .copied(),
                );
                changed = true;
            }
            for (index, item) in terms.arithmetic_ites().iter().enumerate() {
                if selected_ites.contains(&index) {
                    continue;
                }
                let result = terms
                    .arithmetic_expression_for_term(item.result)
                    .expect("arithmetic ite result is affine");
                if !result
                    .coefficients
                    .keys()
                    .any(|variable| variables.contains(variable))
                {
                    continue;
                }
                selected_ites.insert(index);
                self.ites.push(*item);
                self.required.push(item.condition);
                relevant_boolean.extend(terms.reachable_boolean_terms(&[item.condition])?);
                for branch in [item.then_term, item.else_term] {
                    variables.extend(
                        terms
                            .arithmetic_expression_for_term(branch)?
                            .coefficients
                            .keys()
                            .copied(),
                    );
                }
                changed = true;
            }
            if !changed {
                break;
            }
        }
        self.required.sort_unstable();
        self.required.dedup();
        Ok(())
    }

    fn required_terms(&self, _terms: &TermStore) -> Vec<TermId> {
        self.required.clone()
    }

    fn begin_check(&mut self) {
        self.assignments.clear();
        self.levels.clear();
        self.trail.clear();
    }

    fn push_level(&mut self) {
        self.levels.push(self.trail.len());
    }

    fn notify_assignment(&mut self, assignment: SignedTerm) {
        let previous = self
            .assignments
            .insert(assignment.term, assignment.positive);
        self.trail.push((assignment.term, previous));
    }

    fn propagate(&mut self, _terms: &TermStore) -> Option<TheoryPropagation> {
        None
    }

    fn final_check(&mut self, terms: &TermStore) -> TheoryCheck<Self::Model> {
        let mut constraints = Vec::new();
        let mut explanation = Vec::new();
        let minus_one = BigRational::from_integer(BigInt::from(-1));
        for predicate in &self.predicates {
            let positive = self
                .assignments
                .get(&predicate.term)
                .copied()
                .unwrap_or(false);
            let mut expression = terms
                .arithmetic_expression(predicate.expression)
                .expect("arithmetic predicates refer to stored expressions")
                .clone();
            if !positive {
                expression = expression.scaled(&minus_one);
            }
            constraints.push(LinearConstraint {
                expression,
                strict: predicate.strict == positive,
                sort: terms
                    .arithmetic_expression_sort(predicate.expression)
                    .expect("arithmetic predicates have stored sorts"),
            });
            explanation.push(SignedTerm {
                term: predicate.term,
                positive,
            });
        }
        for item in &self.ites {
            let condition = self
                .assignments
                .get(&item.condition)
                .copied()
                .unwrap_or(false);
            let selected = if condition {
                item.then_term
            } else {
                item.else_term
            };
            let sort = terms
                .sort(item.result)
                .expect("arithmetic ite result belongs to the term store");
            let mut forward = terms
                .arithmetic_expression_for_term(item.result)
                .expect("arithmetic ite result is affine")
                .clone();
            forward.add_scaled(
                terms
                    .arithmetic_expression_for_term(selected)
                    .expect("arithmetic ite branch is affine"),
                &minus_one,
            );
            constraints.push(LinearConstraint {
                expression: forward.clone(),
                strict: false,
                sort,
            });
            constraints.push(LinearConstraint {
                expression: forward.scaled(&minus_one),
                strict: false,
                sort,
            });
            explanation.push(SignedTerm {
                term: item.condition,
                positive: condition,
            });
        }

        match solve_constraints(constraints, terms.arithmetic_variable_sorts()) {
            ArithmeticSolve::Sat(model) => TheoryCheck::Consistent(model),
            ArithmeticSolve::Incomplete => TheoryCheck::Unknown(UnknownReason::IncompleteTheory),
            ArithmeticSolve::Unsat => {
                explanation.sort_unstable_by_key(|literal| (literal.term, literal.positive));
                explanation.dedup();
                TheoryCheck::Conflict(TheoryLemma {
                    literals: explanation.into_iter().map(SignedTerm::negate).collect(),
                })
            }
        }
    }

    fn backtrack(&mut self, level: usize) {
        let target = if level == 0 {
            0
        } else {
            self.levels
                .get(level - 1)
                .copied()
                .unwrap_or(self.trail.len())
        };
        while self.trail.len() > target {
            let (term, previous) = self.trail.pop().expect("length checked");
            if let Some(value) = previous {
                self.assignments.insert(term, value);
            } else {
                self.assignments.remove(&term);
            }
        }
        self.levels.truncate(level);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn integer_expression(constant: i64, coefficients: &[(u32, i64)]) -> LinearExpression {
        LinearExpression {
            constant: BigRational::from_integer(BigInt::from(constant)),
            coefficients: coefficients
                .iter()
                .filter(|(_, coefficient)| *coefficient != 0)
                .map(|(variable, coefficient)| {
                    (
                        ArithmeticVariableId(*variable),
                        BigRational::from_integer(BigInt::from(*coefficient)),
                    )
                })
                .collect(),
        }
    }

    fn integer_constraint(constant: i64, coefficients: &[(u32, i64)]) -> LinearConstraint {
        LinearConstraint {
            expression: integer_expression(constant, coefficients),
            strict: false,
            sort: Sort::Int,
        }
    }

    fn integer_equality(constant: i64, coefficients: &[(u32, i64)]) -> Vec<LinearConstraint> {
        vec![
            integer_constraint(constant, coefficients),
            integer_constraint(
                -constant,
                &coefficients
                    .iter()
                    .map(|(variable, coefficient)| (*variable, -*coefficient))
                    .collect::<Vec<_>>(),
            ),
        ]
    }

    fn model_satisfies(model: &ArithmeticModel, constraints: &[LinearConstraint]) -> bool {
        constraints.iter().all(|constraint| {
            let value = model.expression_value(&constraint.expression);
            if constraint.strict {
                value.is_negative()
            } else {
                !value.is_positive()
            }
        })
    }

    #[test]
    fn cooper_elimination_finds_general_integer_model() {
        let mut constraints = integer_equality(-7, &[(0, 2), (1, 3)]);
        constraints.push(integer_constraint(0, &[(0, -1)]));
        constraints.push(integer_constraint(0, &[(1, -1)]));
        let ArithmeticSolve::Sat(model) =
            solve_constraints(constraints.clone(), &[Sort::Int, Sort::Int])
        else {
            panic!("nonnegative solution to 2*x + 3*y = 7 must be found");
        };
        assert!(model_satisfies(&model, &constraints));
        assert!(model.variable_value(ArithmeticVariableId(0)).is_integer());
        assert!(model.variable_value(ArithmeticVariableId(1)).is_integer());
    }

    #[test]
    fn cooper_elimination_refutes_parity_contradictions() {
        for constraints in [
            integer_equality(-1, &[(0, 2)]),
            integer_equality(-1, &[(0, 2), (1, -2)]),
        ] {
            assert!(matches!(
                solve_constraints(constraints, &[Sort::Int, Sort::Int]),
                ArithmeticSolve::Unsat
            ));
        }
    }

    #[test]
    fn bounded_integer_equalities_match_exhaustive_search() {
        let bounds = [
            integer_constraint(-2, &[(0, 1)]),
            integer_constraint(-2, &[(0, -1)]),
            integer_constraint(-2, &[(1, 1)]),
            integer_constraint(-2, &[(1, -1)]),
        ];
        for left in -3_i64..=3 {
            for right in -3_i64..=3 {
                if left == 0 && right == 0 {
                    continue;
                }
                for target in -5_i64..=5 {
                    let mut constraints = integer_equality(-target, &[(0, left), (1, right)]);
                    constraints.extend(bounds.clone());
                    let expected =
                        (-2_i64..=2).any(|x| (-2_i64..=2).any(|y| left * x + right * y == target));
                    match solve_constraints(constraints.clone(), &[Sort::Int, Sort::Int]) {
                        ArithmeticSolve::Sat(model) => {
                            assert!(
                                expected,
                                "unexpected model for {left}*x + {right}*y = {target}"
                            );
                            assert!(model_satisfies(&model, &constraints));
                        }
                        ArithmeticSolve::Unsat => assert!(
                            !expected,
                            "missed model for {left}*x + {right}*y = {target}"
                        ),
                        ArithmeticSolve::Incomplete => {
                            panic!(
                                "bounded linear integer equality unexpectedly returned incomplete"
                            );
                        }
                    }
                }
            }
        }
    }
}
