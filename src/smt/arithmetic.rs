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
        return solve_integer_difference(constraints, variable_sorts);
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
        self.predicates.extend(
            terms
                .arithmetic_predicates()
                .iter()
                .filter(|atom| relevant.contains(&atom.term))
                .copied(),
        );
        self.required
            .extend(self.predicates.iter().map(|atom| atom.term));

        let mut variables = self
            .predicates
            .iter()
            .flat_map(|predicate| {
                terms
                    .arithmetic_expression(predicate.expression)
                    .expect("arithmetic predicates refer to stored expressions")
                    .coefficients
                    .keys()
                    .copied()
            })
            .collect::<HashSet<_>>();
        let mut selected = HashSet::new();
        loop {
            let mut changed = false;
            for (index, item) in terms.arithmetic_ites().iter().enumerate() {
                if selected.contains(&index) {
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
                selected.insert(index);
                self.ites.push(*item);
                self.required.push(item.condition);
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
