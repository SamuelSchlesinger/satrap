use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::error::Error;
use std::fmt;
use std::io::{self, Write};
use std::sync::{Arc, Mutex};

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use crate::{Lit, SolveResult, Solver};

use super::arithmetic::{ArithmeticExpressionId, ArithmeticVariableId, LinearExpression};
use super::term::{FunctionId, Sort, SymbolId, TermId, TermKind, TermStore, UninterpretedSortId};

#[derive(Clone, Debug)]
pub(crate) struct BooleanRefutation {
    logic: ProofLogic,
    variable_count: usize,
    clauses: Vec<crate::solver::ProofInputClause>,
    premises: Vec<String>,
    drat: Vec<u8>,
}

impl BooleanRefutation {
    pub(crate) fn render(&self) -> String {
        let premises = self
            .premises
            .iter()
            .map(|premise| quote_string(premise))
            .collect::<Vec<_>>()
            .join(" ");
        let clauses = self
            .clauses
            .iter()
            .map(|clause| {
                let kind = match clause.kind {
                    crate::solver::ProofClauseKind::Formula => "formula",
                    crate::solver::ProofClauseKind::Encoding => "encoding",
                    crate::solver::ProofClauseKind::Theory => "theory",
                    crate::solver::ProofClauseKind::Administrative => "administrative",
                };
                let literals = clause
                    .literals
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(" ");
                if literals.is_empty() {
                    format!("({kind})")
                } else {
                    format!("({kind} {literals})")
                }
            })
            .collect::<Vec<_>>()
            .join(" ");
        let drat = String::from_utf8_lossy(&self.drat);
        format!(
            "(satrap-edrat :version 1 :logic {} :variables {} \
             :premises ({premises}) :clauses ({clauses}) :drat {})",
            self.logic.name(),
            self.variable_count,
            quote_string(&drat)
        )
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ProofLogic {
    Bool,
    Bv,
    Uf,
    UfBv,
    Abv,
    Aufbv,
    Idl,
    Lia,
    Rdl,
    Lra,
}

impl ProofLogic {
    pub(crate) fn from_name(name: &str) -> Option<Self> {
        match name {
            "QF_BOOL" => Some(Self::Bool),
            "QF_BV" => Some(Self::Bv),
            "QF_UF" => Some(Self::Uf),
            "QF_UFBV" => Some(Self::UfBv),
            "QF_ABV" => Some(Self::Abv),
            "QF_AUFBV" => Some(Self::Aufbv),
            "QF_IDL" => Some(Self::Idl),
            "QF_LIA" => Some(Self::Lia),
            "QF_RDL" => Some(Self::Rdl),
            "QF_LRA" => Some(Self::Lra),
            _ => None,
        }
    }

    fn name(self) -> &'static str {
        match self {
            Self::Bool => "QF_BOOL",
            Self::Bv => "QF_BV",
            Self::Uf => "QF_UF",
            Self::UfBv => "QF_UFBV",
            Self::Abv => "QF_ABV",
            Self::Aufbv => "QF_AUFBV",
            Self::Idl => "QF_IDL",
            Self::Lia => "QF_LIA",
            Self::Rdl => "QF_RDL",
            Self::Lra => "QF_LRA",
        }
    }

    fn admits_theory_clauses(self) -> bool {
        matches!(
            self,
            Self::Uf
                | Self::UfBv
                | Self::Abv
                | Self::Aufbv
                | Self::Idl
                | Self::Lia
                | Self::Rdl
                | Self::Lra
        )
    }

    fn arithmetic_kind(self) -> Option<ArithmeticProofKind> {
        match self {
            Self::Idl => Some(ArithmeticProofKind::IntegerDifference),
            Self::Lia => Some(ArithmeticProofKind::LinearInteger),
            Self::Rdl => Some(ArithmeticProofKind::RealDifference),
            Self::Lra => Some(ArithmeticProofKind::LinearReal),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ArithmeticProofKind {
    IntegerDifference,
    LinearInteger,
    RealDifference,
    LinearReal,
}

impl ArithmeticProofKind {
    fn sort(self) -> ProofSort {
        match self {
            Self::IntegerDifference | Self::LinearInteger => ProofSort::Int,
            Self::RealDifference | Self::LinearReal => ProofSort::Real,
        }
    }
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum ProofAtom {
    Bool(String),
    BitVecBit {
        name: String,
        index: u32,
    },
    ApplicationBit {
        application: ProofApplication,
        index: u32,
    },
    ClassBit {
        sort: ProofSort,
        term: AbstractExpr,
        index: u32,
    },
    ArrayWitnessBit {
        sort: ProofSort,
        left: AbstractExpr,
        right: AbstractExpr,
        index: u32,
    },
    ArithmeticPredicate {
        sort: ProofSort,
        expression: ProofLinearExpression,
        strict: bool,
    },
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum ProofSort {
    Bool,
    BitVec(u32),
    Uninterpreted(String),
    Array(Box<ProofSort>, Box<ProofSort>),
    Int,
    Real,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum ProofArithmeticVariable {
    Declared {
        sort: ProofSort,
        name: String,
    },
    Ite {
        sort: ProofSort,
        condition: BoolExpr,
        then_expression: Box<ProofLinearExpression>,
        else_expression: Box<ProofLinearExpression>,
    },
    Application {
        sort: ProofSort,
        application: Box<ProofApplication>,
    },
    ArrayWitness {
        sort: ProofSort,
        array_sort: ProofSort,
        left: AbstractExpr,
        right: AbstractExpr,
    },
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct ProofLinearExpression {
    constant: BigRational,
    coefficients: BTreeMap<ProofArithmeticVariable, BigRational>,
}

impl ProofLinearExpression {
    fn variable(variable: ProofArithmeticVariable) -> Self {
        Self {
            constant: BigRational::zero(),
            coefficients: BTreeMap::from([(variable, BigRational::one())]),
        }
    }

    fn scaled(mut self, scale: &BigRational) -> Self {
        self.constant *= scale;
        for coefficient in self.coefficients.values_mut() {
            *coefficient *= scale;
        }
        self.coefficients
            .retain(|_, coefficient| !coefficient.is_zero());
        self
    }

    fn add_scaled(&mut self, other: &Self, scale: &BigRational) {
        self.constant += &other.constant * scale;
        for (variable, coefficient) in &other.coefficients {
            let updated = self
                .coefficients
                .get(variable)
                .cloned()
                .unwrap_or_else(BigRational::zero)
                + coefficient * scale;
            if updated.is_zero() {
                self.coefficients.remove(variable);
            } else {
                self.coefficients.insert(variable.clone(), updated);
            }
        }
    }
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct ProofLinearConstraint {
    sort: ProofSort,
    expression: ProofLinearExpression,
    strict: bool,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum ProofFunction {
    Declared(String),
    ArraySelect(ProofSort),
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct ProofApplication {
    function: ProofFunction,
    domain: Vec<ProofSort>,
    range: ProofSort,
    arguments: Vec<ProofValue>,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum ProofValue {
    Bool(BoolExpr),
    BitVec(Vec<BoolExpr>),
    Abstract(AbstractExpr),
    Arithmetic {
        sort: ProofSort,
        expression: ProofLinearExpression,
    },
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct AbstractExpr(Arc<AbstractNode>);

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum AbstractNode {
    Constant {
        sort: ProofSort,
        name: String,
    },
    Application(ProofApplication),
    Ite {
        sort: ProofSort,
        condition: BoolExpr,
        then_term: AbstractExpr,
        else_term: AbstractExpr,
    },
    ArrayConst {
        sort: ProofSort,
        value: ProofValue,
    },
    ArrayStore {
        sort: ProofSort,
        array: AbstractExpr,
        index: ProofValue,
        value: ProofValue,
    },
    ArrayWitness {
        sort: ProofSort,
        array_sort: ProofSort,
        left: AbstractExpr,
        right: AbstractExpr,
    },
}

impl AbstractExpr {
    fn node(&self) -> &AbstractNode {
        &self.0
    }
}

#[derive(Clone, Debug, Default)]
pub(crate) struct ProofNames {
    atoms: HashMap<SymbolId, ProofAtom>,
    constants: HashMap<TermId, String>,
    functions: HashMap<FunctionId, String>,
    sorts: HashMap<UninterpretedSortId, String>,
    arithmetic_variables: HashMap<ArithmeticVariableId, (ProofSort, String)>,
}

impl ProofNames {
    pub(crate) fn insert_bool(&mut self, symbol: SymbolId, name: String) {
        self.atoms.insert(symbol, ProofAtom::Bool(name));
    }

    pub(crate) fn insert_bit(&mut self, symbol: SymbolId, name: String, index: u32) {
        self.atoms
            .insert(symbol, ProofAtom::BitVecBit { name, index });
    }

    pub(crate) fn insert_constant(&mut self, term: TermId, name: String) {
        self.constants.insert(term, name);
    }

    pub(crate) fn insert_function(&mut self, function: FunctionId, name: String) {
        self.functions.insert(function, name);
    }

    pub(crate) fn insert_sort(&mut self, sort: UninterpretedSortId, name: String) {
        self.sorts.insert(sort, name);
    }

    pub(crate) fn insert_arithmetic(
        &mut self,
        variable: ArithmeticVariableId,
        sort: Sort,
        name: String,
    ) -> Result<(), ProofError> {
        let sort = match sort {
            Sort::Int => ProofSort::Int,
            Sort::Real => ProofSort::Real,
            _ => {
                return Err(ProofError::new(
                    "arithmetic proof name has a non-arithmetic sort",
                ));
            }
        };
        self.arithmetic_variables.insert(variable, (sort, name));
        Ok(())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ProofError(String);

impl ProofError {
    fn new(message: impl Into<String>) -> Self {
        Self(message.into())
    }
}

impl fmt::Display for ProofError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.0)
    }
}

impl Error for ProofError {}

/// Re-encodes one active proof-bearing query in a fresh, non-incremental SAT
/// solver.
///
/// Turning every active assertion into a permanent unit avoids the unsound
/// "global empty clause under temporary assumptions" problem. SMT-LIB permits
/// `get-proof` only after a check with an empty explicit assumption set. A
/// proof-specific canonical lowering makes the CNF independent of term-ID
/// allocation history. Ground UF and arrays are reduced to finite class bits
/// plus independently validated theory axioms. Arithmetic replay learns only
/// clauses whose blocked Boolean assignments have an independently detected
/// exact theory conflict. A separate checker can therefore reconstruct and
/// validate the entire propositional input from the original SMT-LIB query
/// before validating the DRAT suffix.
pub(crate) fn prove_boolean_unsat(
    logic: ProofLogic,
    terms: &TermStore,
    roots: &[TermId],
    premises: &[String],
    names: &ProofNames,
) -> Result<BooleanRefutation, ProofError> {
    if roots.len() != premises.len() {
        return Err(ProofError::new(
            "SMT proof roots and rendered premises are inconsistent",
        ));
    }

    let mut canonicalizer = Canonicalizer::new(terms)?;
    let raw_roots = roots
        .iter()
        .map(|&root| canonicalizer.convert(terms, root, names))
        .collect::<Result<Vec<_>, _>>()?;
    let (roots, theory_axioms) = if logic.admits_theory_clauses() {
        canonicalizer.prepare_theory()?;
        let roots = raw_roots
            .iter()
            .map(|root| canonicalizer.lower(root))
            .collect::<Result<Vec<_>, _>>()?;
        (roots, canonicalizer.theory_axioms()?)
    } else {
        // Boolean and bit-vector conversion already produces the final
        // canonical DAG. Rewalking and structurally hashing that potentially
        // large circuit is only needed when ground-UF equalities remain.
        (raw_roots, Vec::new())
    };

    let arithmetic_problem = if let Some(kind) = logic.arithmetic_kind() {
        let mut formulas = Vec::with_capacity(roots.len() + theory_axioms.len());
        formulas.extend(roots.iter().cloned());
        formulas.extend(theory_axioms.iter().cloned());
        Some(ArithmeticProblem::from_roots(kind, &formulas)?)
    } else {
        None
    };
    let theory_lemmas = arithmetic_problem
        .as_ref()
        .map(|problem| discover_arithmetic_lemmas(&roots, &theory_axioms, problem))
        .transpose()?
        .unwrap_or_default();
    let empty_required = BTreeSet::new();
    let required = arithmetic_problem
        .as_ref()
        .map_or(&empty_required, |problem| &problem.required);

    let output = SharedBuffer::default();
    let mut solver = Solver::new();
    solver.enable_smt_proof_recording();
    let mut encoder = ProofEncoder::default();
    install_proof_input(
        &mut solver,
        &mut encoder,
        &roots,
        &theory_axioms,
        required,
        &theory_lemmas,
    )?;
    let clauses = solver
        .proof_input()
        .expect("proof recording was enabled")
        .to_vec();
    if let Some(clause) = clauses.iter().find(|clause| {
        !matches!(
            clause.kind,
            crate::solver::ProofClauseKind::Formula | crate::solver::ProofClauseKind::Encoding
        ) && !(logic.admits_theory_clauses()
            && clause.kind == crate::solver::ProofClauseKind::Theory)
    }) {
        return Err(ProofError::new(format!(
            "{} proof replay produced an unsupported {:?} clause",
            logic.name(),
            clause.kind,
        )));
    }
    solver.enable_drat_proof(output.clone());

    match solver.solve() {
        SolveResult::Unsat => {}
        SolveResult::Sat(_) => {
            return Err(ProofError::new(
                "fresh SMT proof replay unexpectedly found a model",
            ));
        }
        SolveResult::Unknown(reason) => {
            return Err(ProofError::new(format!(
                "fresh SMT proof replay stopped with {reason:?}"
            )));
        }
    }
    if let Some(error) = solver.proof_error() {
        return Err(ProofError::new(format!(
            "could not finish SMT DRAT proof: {error}"
        )));
    }

    Ok(BooleanRefutation {
        logic,
        variable_count: solver.variable_count(),
        clauses,
        premises: premises.to_vec(),
        drat: output.snapshot()?,
    })
}

fn install_proof_input(
    solver: &mut Solver,
    encoder: &mut ProofEncoder,
    roots: &[BoolExpr],
    theory_axioms: &[BoolExpr],
    required: &BTreeSet<BoolExpr>,
    theory_lemmas: &[Vec<ProofSignedBool>],
) -> Result<(), ProofError> {
    for root in roots {
        let literal = encoder.encode(solver, root)?;
        solver
            .try_add_clause(&[literal])
            .map_err(|error| ProofError::new(error.to_string()))?;
    }
    for axiom in theory_axioms {
        let literal = encoder.encode(solver, axiom)?;
        solver
            .add_theory_clause(&[literal])
            .map_err(|error| ProofError::new(error.to_string()))?;
    }
    for expression in required {
        encoder.encode(solver, expression)?;
    }
    for lemma in theory_lemmas {
        let clause = lemma
            .iter()
            .map(|signed| {
                let literal = encoder.encode(solver, &signed.expression)?;
                Ok(if signed.positive { literal } else { !literal })
            })
            .collect::<Result<Vec<_>, ProofError>>()?;
        solver
            .add_theory_clause(&clause)
            .map_err(|error| ProofError::new(error.to_string()))?;
    }
    Ok(())
}

fn discover_arithmetic_lemmas(
    roots: &[BoolExpr],
    theory_axioms: &[BoolExpr],
    problem: &ArithmeticProblem,
) -> Result<Vec<Vec<ProofSignedBool>>, ProofError> {
    let mut solver = Solver::new();
    let mut encoder = ProofEncoder::default();
    install_proof_input(
        &mut solver,
        &mut encoder,
        roots,
        theory_axioms,
        &problem.required,
        &[],
    )?;
    let mut lemmas = Vec::new();
    loop {
        match solver.solve() {
            SolveResult::Sat(model) => {
                let assignment = problem
                    .required
                    .iter()
                    .map(|expression| {
                        let literal = encoder.encode(&mut solver, expression)?;
                        Ok((expression.clone(), model.literal_value(literal)))
                    })
                    .collect::<Result<BTreeMap<_, _>, ProofError>>()?;
                let constraints = problem.constraints(&assignment)?;
                if !arithmetic_constraints_unsat(&constraints, problem.kind)? {
                    return Err(ProofError::new(
                        "fresh arithmetic proof replay found a theory-consistent model",
                    ));
                }
                let lemma = problem.blocking_lemma(&assignment)?;
                let clause = lemma
                    .iter()
                    .map(|signed| {
                        let literal = encoder.encode(&mut solver, &signed.expression)?;
                        Ok(if signed.positive { literal } else { !literal })
                    })
                    .collect::<Result<Vec<_>, ProofError>>()?;
                solver
                    .add_theory_clause(&clause)
                    .map_err(|error| ProofError::new(error.to_string()))?;
                lemmas.push(lemma);
            }
            SolveResult::Unsat => return Ok(lemmas),
            SolveResult::Unknown(reason) => {
                return Err(ProofError::new(format!(
                    "arithmetic proof discovery stopped with {reason:?}"
                )));
            }
        }
    }
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct BoolExpr(Arc<BoolNode>);

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum BoolNode {
    False,
    True,
    Atom(ProofAtom),
    Not(BoolExpr),
    And(Vec<BoolExpr>),
    Or(Vec<BoolExpr>),
    Xor(BoolExpr, BoolExpr),
    Iff(BoolExpr, BoolExpr),
    Ite(BoolExpr, BoolExpr, BoolExpr),
    TheoryEquality(AbstractExpr, AbstractExpr),
}

impl BoolExpr {
    fn node(&self) -> &BoolNode {
        &self.0
    }
}

#[derive(Clone, Debug)]
struct ProofSignedBool {
    expression: BoolExpr,
    positive: bool,
}

#[derive(Debug)]
struct ArithmeticProblem {
    kind: ArithmeticProofKind,
    sort: ProofSort,
    predicates: BTreeMap<BoolExpr, ProofLinearConstraint>,
    ites: BTreeSet<ProofArithmeticVariable>,
    required: BTreeSet<BoolExpr>,
}

impl ArithmeticProblem {
    fn from_roots(kind: ArithmeticProofKind, roots: &[BoolExpr]) -> Result<Self, ProofError> {
        let mut problem = Self {
            kind,
            sort: kind.sort(),
            predicates: BTreeMap::new(),
            ites: BTreeSet::new(),
            required: BTreeSet::new(),
        };
        let mut visited_boolean = HashSet::new();
        let mut visited_variables = HashSet::new();
        for root in roots {
            problem.collect_bool(root, &mut visited_boolean, &mut visited_variables)?;
        }
        problem.required.extend(problem.predicates.keys().cloned());
        Ok(problem)
    }

    fn collect_bool(
        &mut self,
        expression: &BoolExpr,
        visited_boolean: &mut HashSet<BoolExpr>,
        visited_variables: &mut HashSet<ProofArithmeticVariable>,
    ) -> Result<(), ProofError> {
        if !visited_boolean.insert(expression.clone()) {
            return Ok(());
        }
        match expression.node() {
            BoolNode::False | BoolNode::True => {}
            BoolNode::Atom(ProofAtom::ArithmeticPredicate {
                sort,
                expression: linear,
                strict,
            }) => {
                if sort != &self.sort {
                    return Err(ProofError::new(
                        "arithmetic proof contains a predicate of the wrong sort",
                    ));
                }
                self.predicates.insert(
                    expression.clone(),
                    ProofLinearConstraint {
                        sort: sort.clone(),
                        expression: linear.clone(),
                        strict: *strict,
                    },
                );
                self.collect_linear(linear, visited_boolean, visited_variables)?;
            }
            BoolNode::Atom(_) => {}
            BoolNode::Not(inner) => {
                self.collect_bool(inner, visited_boolean, visited_variables)?;
            }
            BoolNode::And(items) | BoolNode::Or(items) => {
                for item in items {
                    self.collect_bool(item, visited_boolean, visited_variables)?;
                }
            }
            BoolNode::Xor(left, right) | BoolNode::Iff(left, right) => {
                self.collect_bool(left, visited_boolean, visited_variables)?;
                self.collect_bool(right, visited_boolean, visited_variables)?;
            }
            BoolNode::Ite(condition, then_term, else_term) => {
                self.collect_bool(condition, visited_boolean, visited_variables)?;
                self.collect_bool(then_term, visited_boolean, visited_variables)?;
                self.collect_bool(else_term, visited_boolean, visited_variables)?;
            }
            BoolNode::TheoryEquality(_, _) => {
                return Err(ProofError::new(
                    "arithmetic proof contains an unlowered theory equality",
                ));
            }
        }
        Ok(())
    }

    fn collect_linear(
        &mut self,
        expression: &ProofLinearExpression,
        visited_boolean: &mut HashSet<BoolExpr>,
        visited_variables: &mut HashSet<ProofArithmeticVariable>,
    ) -> Result<(), ProofError> {
        for variable in expression.coefficients.keys() {
            if !visited_variables.insert(variable.clone()) {
                continue;
            }
            match variable {
                ProofArithmeticVariable::Declared { sort, .. }
                | ProofArithmeticVariable::Application { sort, .. }
                | ProofArithmeticVariable::ArrayWitness { sort, .. } => {
                    if sort != &self.sort {
                        return Err(ProofError::new(
                            "arithmetic proof contains a variable of the wrong sort",
                        ));
                    }
                }
                variable @ ProofArithmeticVariable::Ite {
                    sort,
                    condition,
                    then_expression,
                    else_expression,
                } => {
                    if sort != &self.sort {
                        return Err(ProofError::new(
                            "arithmetic proof contains an ite of the wrong sort",
                        ));
                    }
                    self.ites.insert(variable.clone());
                    self.required.insert(condition.clone());
                    self.collect_bool(condition, visited_boolean, visited_variables)?;
                    self.collect_linear(then_expression, visited_boolean, visited_variables)?;
                    self.collect_linear(else_expression, visited_boolean, visited_variables)?;
                }
            }
        }
        Ok(())
    }

    fn constraints(
        &self,
        assignment: &BTreeMap<BoolExpr, bool>,
    ) -> Result<Vec<ProofLinearConstraint>, ProofError> {
        let minus_one = BigRational::from_integer(BigInt::from(-1));
        let mut constraints = Vec::new();
        for (term, predicate) in &self.predicates {
            let positive = assignment
                .get(term)
                .copied()
                .ok_or_else(|| ProofError::new("arithmetic predicate has no Boolean assignment"))?;
            let expression = if positive {
                predicate.expression.clone()
            } else {
                predicate.expression.clone().scaled(&minus_one)
            };
            constraints.push(ProofLinearConstraint {
                sort: self.sort.clone(),
                expression,
                strict: predicate.strict == positive,
            });
        }
        for variable in &self.ites {
            let ProofArithmeticVariable::Ite {
                condition,
                then_expression,
                else_expression,
                ..
            } = variable
            else {
                unreachable!("the ite set contains only ite variables");
            };
            let selected = if assignment.get(condition).copied().ok_or_else(|| {
                ProofError::new("arithmetic ite condition has no Boolean assignment")
            })? {
                then_expression.as_ref()
            } else {
                else_expression.as_ref()
            };
            let mut forward = ProofLinearExpression::variable(variable.clone());
            forward.add_scaled(selected, &minus_one);
            constraints.push(ProofLinearConstraint {
                sort: self.sort.clone(),
                expression: forward.clone(),
                strict: false,
            });
            constraints.push(ProofLinearConstraint {
                sort: self.sort.clone(),
                expression: forward.scaled(&minus_one),
                strict: false,
            });
        }
        Ok(constraints)
    }

    fn blocking_lemma(
        &self,
        assignment: &BTreeMap<BoolExpr, bool>,
    ) -> Result<Vec<ProofSignedBool>, ProofError> {
        self.required
            .iter()
            .map(|expression| {
                Ok(ProofSignedBool {
                    expression: expression.clone(),
                    positive: !assignment.get(expression).copied().ok_or_else(|| {
                        ProofError::new("arithmetic required term has no Boolean assignment")
                    })?,
                })
            })
            .collect()
    }
}

fn arithmetic_constraints_unsat(
    constraints: &[ProofLinearConstraint],
    kind: ArithmeticProofKind,
) -> Result<bool, ProofError> {
    match kind {
        ArithmeticProofKind::IntegerDifference | ArithmeticProofKind::RealDifference => {
            difference_constraints_unsat(constraints, &kind.sort())
        }
        ArithmeticProofKind::LinearInteger => integer_linear_constraints_unsat(constraints),
        ArithmeticProofKind::LinearReal => real_linear_constraints_unsat(constraints),
    }
}

const MAX_INTEGER_PROOF_VARIABLES: usize = 512;
const MAX_INTEGER_PROOF_WORK: usize = 1_000_000;

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct ProofIntegerExpression {
    constant: BigInt,
    coefficients: BTreeMap<ProofArithmeticVariable, BigInt>,
}

impl ProofIntegerExpression {
    fn from_linear(expression: &ProofLinearExpression) -> Option<Self> {
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
                .map(|(variable, coefficient)| (variable.clone(), coefficient.to_integer()))
                .collect(),
        })
    }

    fn variable(variable: ProofArithmeticVariable) -> Self {
        Self {
            constant: BigInt::zero(),
            coefficients: BTreeMap::from([(variable, BigInt::one())]),
        }
    }

    fn coefficient(&self, variable: &ProofArithmeticVariable) -> BigInt {
        self.coefficients
            .get(variable)
            .cloned()
            .unwrap_or_else(BigInt::zero)
    }

    fn without(&self, variable: &ProofArithmeticVariable) -> Self {
        let mut result = self.clone();
        result.coefficients.remove(variable);
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
        for (variable, coefficient) in &other.coefficients {
            let updated = self
                .coefficients
                .get(variable)
                .cloned()
                .unwrap_or_else(BigInt::zero)
                + coefficient * scale;
            if updated.is_zero() {
                self.coefficients.remove(variable);
            } else {
                self.coefficients.insert(variable.clone(), updated);
            }
        }
    }

    fn substitute(&self, variable: &ProofArithmeticVariable, value: &Self) -> Self {
        let coefficient = self.coefficient(variable);
        let mut result = self.without(variable);
        result.add_scaled(value, &coefficient);
        result
    }
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct ProofIntegerInequality {
    expression: ProofIntegerExpression,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct ProofDivisibilityConstraint {
    modulus: BigInt,
    expression: ProofIntegerExpression,
}

#[derive(Clone, Debug, Default)]
struct ProofIntegerProblem {
    inequalities: Vec<ProofIntegerInequality>,
    divisibilities: Vec<ProofDivisibilityConstraint>,
}

impl ProofIntegerProblem {
    fn substitute(
        &self,
        variable: &ProofArithmeticVariable,
        value: &ProofIntegerExpression,
    ) -> Self {
        Self {
            inequalities: self
                .inequalities
                .iter()
                .map(|constraint| ProofIntegerInequality {
                    expression: constraint.expression.substitute(variable, value),
                })
                .collect(),
            divisibilities: self
                .divisibilities
                .iter()
                .map(|constraint| ProofDivisibilityConstraint {
                    modulus: constraint.modulus.clone(),
                    expression: constraint.expression.substitute(variable, value),
                })
                .collect(),
        }
    }

    fn mentions(&self, variable: &ProofArithmeticVariable) -> bool {
        self.inequalities
            .iter()
            .any(|constraint| constraint.expression.coefficients.contains_key(variable))
            || self
                .divisibilities
                .iter()
                .any(|constraint| constraint.expression.coefficients.contains_key(variable))
    }
}

struct ProofCooperElimination {
    normalized: ProofIntegerProblem,
    period: BigInt,
    lower_bases: Vec<ProofIntegerExpression>,
    upper_bases: Vec<ProofIntegerExpression>,
}

struct IntegerProofBudget {
    remaining: usize,
}

impl IntegerProofBudget {
    fn new() -> Self {
        Self {
            remaining: MAX_INTEGER_PROOF_WORK,
        }
    }

    fn spend(&mut self, amount: usize) -> Result<(), ProofError> {
        self.remaining = self.remaining.checked_sub(amount).ok_or_else(|| {
            ProofError::new(format!(
                "linear-integer proof exceeded its deterministic work limit of \
                 {MAX_INTEGER_PROOF_WORK} steps"
            ))
        })?;
        Ok(())
    }
}

fn integer_linear_constraints_unsat(
    constraints: &[ProofLinearConstraint],
) -> Result<bool, ProofError> {
    let mut problem = ProofIntegerProblem::default();
    for constraint in constraints {
        if constraint.sort != ProofSort::Int {
            return Err(ProofError::new(
                "linear-integer proof contains a constraint of the wrong sort",
            ));
        }
        let Some(mut expression) = ProofIntegerExpression::from_linear(&constraint.expression)
        else {
            return Err(ProofError::new(
                "linear-integer proof contains a non-integral affine expression",
            ));
        };
        if !constraint.strict {
            expression.constant -= BigInt::one();
        }
        problem
            .inequalities
            .push(ProofIntegerInequality { expression });
    }
    let variables = problem
        .inequalities
        .iter()
        .flat_map(|constraint| constraint.expression.coefficients.keys().cloned())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    if variables.len() > MAX_INTEGER_PROOF_VARIABLES {
        return Err(ProofError::new(format!(
            "linear-integer proof has {} variables; the deterministic proof limit is \
             {MAX_INTEGER_PROOF_VARIABLES}",
            variables.len()
        )));
    }
    let mut budget = IntegerProofBudget::new();
    Ok(!integer_problem_satisfiable(
        problem,
        &variables,
        &mut budget,
    )?)
}

fn integer_problem_satisfiable(
    problem: ProofIntegerProblem,
    variables: &[ProofArithmeticVariable],
    budget: &mut IntegerProofBudget,
) -> Result<bool, ProofError> {
    budget.spend(1)?;
    let Some(problem) = simplify_proof_integer_problem(problem, budget)? else {
        return Ok(false);
    };
    let Some(variable) = choose_proof_elimination_variable(&problem, variables) else {
        return Ok(true);
    };
    let remaining = variables
        .iter()
        .filter(|candidate| *candidate != variable)
        .cloned()
        .collect::<Vec<_>>();
    if !problem.mentions(variable) {
        return integer_problem_satisfiable(problem, &remaining, budget);
    }

    let elimination = normalize_proof_cooper_variable(&problem, variable, budget)?;
    if !elimination.lower_bases.is_empty() {
        for base in &elimination.lower_bases {
            let mut offset = BigInt::one();
            while offset <= elimination.period {
                budget.spend(1)?;
                let mut candidate = base.clone();
                candidate.constant += &offset;
                let reduced = elimination.normalized.substitute(variable, &candidate);
                if integer_problem_satisfiable(reduced, &remaining, budget)? {
                    return Ok(true);
                }
                offset += BigInt::one();
            }
        }
    } else if !elimination.upper_bases.is_empty() {
        for base in &elimination.upper_bases {
            let mut offset = BigInt::one();
            while offset <= elimination.period {
                budget.spend(1)?;
                let mut candidate = base.clone();
                candidate.constant -= &offset;
                let reduced = elimination.normalized.substitute(variable, &candidate);
                if integer_problem_satisfiable(reduced, &remaining, budget)? {
                    return Ok(true);
                }
                offset += BigInt::one();
            }
        }
    } else {
        let mut value = BigInt::zero();
        while value < elimination.period {
            budget.spend(1)?;
            let candidate = ProofIntegerExpression {
                constant: value.clone(),
                coefficients: BTreeMap::new(),
            };
            let reduced = elimination.normalized.substitute(variable, &candidate);
            if integer_problem_satisfiable(reduced, &remaining, budget)? {
                return Ok(true);
            }
            value += BigInt::one();
        }
    }
    Ok(false)
}

fn choose_proof_elimination_variable<'a>(
    problem: &ProofIntegerProblem,
    variables: &'a [ProofArithmeticVariable],
) -> Option<&'a ProofArithmeticVariable> {
    variables.iter().min_by(|left, right| {
        proof_cooper_elimination_cost(problem, left)
            .cmp(&proof_cooper_elimination_cost(problem, right))
            .then_with(|| left.cmp(right))
    })
}

fn proof_cooper_elimination_cost(
    problem: &ProofIntegerProblem,
    variable: &ProofArithmeticVariable,
) -> BigInt {
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
        scale = proof_integer_lcm(&scale, &coefficient.abs());
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
        scale = proof_integer_lcm(&scale, &coefficient.abs());
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
        period = proof_integer_lcm(&period, &transformed_modulus);
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

fn normalize_proof_cooper_variable(
    problem: &ProofIntegerProblem,
    variable: &ProofArithmeticVariable,
    budget: &mut IntegerProofBudget,
) -> Result<ProofCooperElimination, ProofError> {
    budget.spend(problem.inequalities.len() + problem.divisibilities.len())?;
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
    if coefficients.is_empty() {
        return Err(ProofError::new(
            "linear-integer proof tried to eliminate an absent variable",
        ));
    }
    let scale = coefficients
        .iter()
        .fold(BigInt::one(), |result, coefficient| {
            proof_integer_lcm(&result, &coefficient.abs())
        });

    let mut normalized = ProofIntegerProblem::default();
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
            variable.clone(),
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
            .push(ProofIntegerInequality { expression });
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
            variable.clone(),
            if coefficient.is_positive() {
                BigInt::one()
            } else {
                BigInt::from(-1)
            },
        );
        normalized.divisibilities.push(ProofDivisibilityConstraint {
            modulus: &constraint.modulus * factor,
            expression,
        });
    }
    normalized.divisibilities.push(ProofDivisibilityConstraint {
        modulus: scale.clone(),
        expression: ProofIntegerExpression::variable(variable.clone()),
    });
    let period = normalized
        .divisibilities
        .iter()
        .fold(BigInt::one(), |result, constraint| {
            proof_integer_lcm(&result, &constraint.modulus)
        });
    Ok(ProofCooperElimination {
        normalized,
        period,
        lower_bases,
        upper_bases,
    })
}

fn simplify_proof_integer_problem(
    problem: ProofIntegerProblem,
    budget: &mut IntegerProofBudget,
) -> Result<Option<ProofIntegerProblem>, ProofError> {
    budget.spend(problem.inequalities.len() + problem.divisibilities.len())?;
    let mut inequalities = BTreeSet::new();
    for mut constraint in problem.inequalities {
        let coefficient_gcd = constraint
            .expression
            .coefficients
            .values()
            .fold(BigInt::zero(), |result, coefficient| {
                proof_integer_gcd(&result, coefficient)
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
                return Ok(None);
            }
        } else {
            inequalities.insert(constraint);
        }
    }

    let mut divisibilities = BTreeSet::new();
    for mut constraint in problem.divisibilities {
        constraint.modulus = constraint.modulus.abs();
        if constraint.modulus.is_zero() {
            return Err(ProofError::new(
                "linear-integer proof produced a zero divisibility modulus",
            ));
        }
        let common_gcd = constraint
            .expression
            .coefficients
            .values()
            .fold(constraint.modulus.clone(), |result, coefficient| {
                proof_integer_gcd(&result, coefficient)
            });
        if (&constraint.expression.constant % &common_gcd) != BigInt::zero() {
            return Ok(None);
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
                return Ok(None);
            }
        } else {
            divisibilities.insert(constraint);
        }
    }
    Ok(Some(ProofIntegerProblem {
        inequalities: inequalities.into_iter().collect(),
        divisibilities: divisibilities.into_iter().collect(),
    }))
}

fn proof_integer_gcd(left: &BigInt, right: &BigInt) -> BigInt {
    let mut left = left.abs();
    let mut right = right.abs();
    while !right.is_zero() {
        let remainder = &left % &right;
        left = right;
        right = remainder;
    }
    left
}

fn proof_integer_lcm(left: &BigInt, right: &BigInt) -> BigInt {
    if left.is_zero() || right.is_zero() {
        BigInt::zero()
    } else {
        ((left / proof_integer_gcd(left, right)) * right).abs()
    }
}

fn real_linear_constraints_unsat(
    constraints: &[ProofLinearConstraint],
) -> Result<bool, ProofError> {
    let Some(mut constraints) = simplify_real_constraints(constraints.iter().cloned())? else {
        return Ok(true);
    };
    let variables = constraints
        .iter()
        .flat_map(|constraint| constraint.expression.coefficients.keys().cloned())
        .collect::<BTreeSet<_>>();

    for variable in variables {
        let mut independent = Vec::new();
        let mut upper = Vec::new();
        let mut lower = Vec::new();
        for constraint in constraints {
            if constraint.sort != ProofSort::Real {
                return Err(ProofError::new(
                    "linear-real proof contains a constraint of the wrong sort",
                ));
            }
            let coefficient = constraint
                .expression
                .coefficients
                .get(&variable)
                .cloned()
                .unwrap_or_else(BigRational::zero);
            if coefficient.is_zero() {
                independent.push(constraint);
            } else if coefficient.is_positive() {
                upper.push((constraint, coefficient));
            } else {
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
                independent.push(ProofLinearConstraint {
                    sort: ProofSort::Real,
                    expression,
                    strict: upper_constraint.strict || lower_constraint.strict,
                });
            }
        }
        let Some(next) = simplify_real_constraints(independent)? else {
            return Ok(true);
        };
        constraints = next;
    }
    Ok(false)
}

fn simplify_real_constraints(
    constraints: impl IntoIterator<Item = ProofLinearConstraint>,
) -> Result<Option<Vec<ProofLinearConstraint>>, ProofError> {
    let mut seen = BTreeSet::new();
    for constraint in constraints {
        if constraint.sort != ProofSort::Real {
            return Err(ProofError::new(
                "linear-real proof contains a constraint of the wrong sort",
            ));
        }
        if constraint.expression.coefficients.is_empty() {
            let satisfied = if constraint.strict {
                constraint.expression.constant.is_negative()
            } else {
                !constraint.expression.constant.is_positive()
            };
            if !satisfied {
                return Ok(None);
            }
        } else {
            seen.insert(constraint);
        }
    }
    Ok(Some(seen.into_iter().collect()))
}

#[derive(Clone, Debug)]
struct DifferenceEdge {
    from: usize,
    to: usize,
    weight: BigRational,
    epsilon: i64,
}

fn difference_constraints_unsat(
    constraints: &[ProofLinearConstraint],
    expected_sort: &ProofSort,
) -> Result<bool, ProofError> {
    let mut variables = BTreeSet::new();
    for constraint in constraints {
        if &constraint.sort != expected_sort {
            return Err(ProofError::new(
                "difference-logic constraint has an inconsistent sort",
            ));
        }
        variables.extend(constraint.expression.coefficients.keys().cloned());
    }
    let variable_indices = variables
        .into_iter()
        .enumerate()
        .map(|(index, variable)| (variable, index))
        .collect::<BTreeMap<_, _>>();
    let zero = variable_indices.len();
    let mut edges = Vec::new();
    for constraint in constraints {
        if constraint.expression.coefficients.is_empty() {
            let satisfied = if constraint.strict {
                constraint.expression.constant.is_negative()
            } else {
                !constraint.expression.constant.is_positive()
            };
            if !satisfied {
                return Ok(true);
            }
            continue;
        }
        edges.push(proof_difference_edge(
            constraint,
            expected_sort,
            &variable_indices,
            zero,
        )?);
    }

    let vertex_count = variable_indices.len() + 1;
    let mut distances = vec![(BigRational::zero(), 0_i64); vertex_count];
    for iteration in 0..vertex_count {
        let mut changed = false;
        for edge in &edges {
            let candidate = (
                &distances[edge.from].0 + &edge.weight,
                distances[edge.from].1.saturating_add(edge.epsilon),
            );
            if candidate.0 < distances[edge.to].0
                || (candidate.0 == distances[edge.to].0 && candidate.1 < distances[edge.to].1)
            {
                distances[edge.to] = candidate;
                changed = true;
            }
        }
        if !changed {
            return Ok(false);
        }
        if iteration + 1 == vertex_count {
            return Ok(true);
        }
    }
    Ok(false)
}

fn proof_difference_edge(
    constraint: &ProofLinearConstraint,
    expected_sort: &ProofSort,
    variable_indices: &BTreeMap<ProofArithmeticVariable, usize>,
    zero: usize,
) -> Result<DifferenceEdge, ProofError> {
    let coefficients = constraint
        .expression
        .coefficients
        .iter()
        .collect::<Vec<_>>();
    let (positive, negative, scale) = match coefficients.as_slice() {
        [(variable, coefficient)] if coefficient.is_positive() => {
            (variable_indices[*variable], zero, (*coefficient).clone())
        }
        [(variable, coefficient)] if coefficient.is_negative() => {
            (zero, variable_indices[*variable], -(*coefficient).clone())
        }
        [(first, first_coefficient), (second, second_coefficient)]
            if first_coefficient.is_positive()
                && *first_coefficient == &(-(*second_coefficient)) =>
        {
            (
                variable_indices[*first],
                variable_indices[*second],
                (*first_coefficient).clone(),
            )
        }
        [(first, first_coefficient), (second, second_coefficient)]
            if second_coefficient.is_positive()
                && *second_coefficient == &(-(*first_coefficient)) =>
        {
            (
                variable_indices[*second],
                variable_indices[*first],
                (*second_coefficient).clone(),
            )
        }
        _ => {
            return Err(ProofError::new(
                "proof predicate is outside the declared difference-logic fragment",
            ));
        }
    };
    let bound = -constraint.expression.constant.clone() / scale;
    let (weight, epsilon) = match expected_sort {
        ProofSort::Int => {
            let integer = if constraint.strict {
                bound.ceil().to_integer() - BigInt::one()
            } else {
                bound.floor().to_integer()
            };
            (BigRational::from_integer(integer), 0)
        }
        ProofSort::Real => (bound, if constraint.strict { -1 } else { 0 }),
        _ => {
            return Err(ProofError::new(
                "difference-logic proof selected a non-arithmetic sort",
            ));
        }
    };
    Ok(DifferenceEdge {
        from: negative,
        to: positive,
        weight,
        epsilon,
    })
}

#[derive(Debug)]
struct Canonicalizer {
    converted: HashMap<TermId, BoolExpr>,
    abstract_converted: HashMap<TermId, AbstractExpr>,
    application_converted: HashMap<usize, ProofApplication>,
    application_results: HashMap<TermId, usize>,
    application_bits: HashMap<TermId, (usize, u32)>,
    arithmetic_applications: HashMap<ArithmeticVariableId, usize>,
    arithmetic_converted: HashMap<ArithmeticVariableId, ProofArithmeticVariable>,
    arithmetic_ites: HashMap<ArithmeticVariableId, super::term::ArithmeticIte>,
    abstract_terms: BTreeMap<ProofSort, BTreeSet<AbstractExpr>>,
    applications: BTreeSet<ProofApplication>,
    processed_array_selects: BTreeSet<ProofApplication>,
    lowered: HashMap<BoolExpr, BoolExpr>,
    lowered_abstract: HashMap<AbstractExpr, Vec<BoolExpr>>,
    interned: HashMap<BoolNode, BoolExpr>,
}

impl Canonicalizer {
    fn new(terms: &TermStore) -> Result<Self, ProofError> {
        let mut application_bits = HashMap::new();
        let mut application_results = HashMap::new();
        let mut arithmetic_applications = HashMap::new();
        for (application_index, application) in terms.applications().iter().enumerate() {
            application_results.insert(application.result, application_index);
            match terms
                .sort(application.result)
                .map_err(|error| ProofError::new(error.to_string()))?
            {
                Sort::Bool => {
                    application_bits.insert(application.result, (application_index, 0));
                }
                Sort::BitVec(_) => {
                    for (bit_index, &bit) in terms
                        .bitvec_bits(application.result)
                        .map_err(|error| ProofError::new(error.to_string()))?
                        .iter()
                        .enumerate()
                    {
                        let bit_index = u32::try_from(bit_index)
                            .map_err(|_| ProofError::new("proof application result is too wide"))?;
                        application_bits.insert(bit, (application_index, bit_index));
                    }
                }
                Sort::Int | Sort::Real => {
                    let variable = terms
                        .arithmetic_variable_for_term(application.result)
                        .map_err(|error| ProofError::new(error.to_string()))?
                        .ok_or_else(|| {
                            ProofError::new(
                                "arithmetic application result is not a canonical variable",
                            )
                        })?;
                    arithmetic_applications.insert(variable, application_index);
                }
                Sort::Uninterpreted(_) | Sort::Array(_) => {}
            }
        }
        let mut arithmetic_ites = HashMap::new();
        for item in terms.arithmetic_ites() {
            let variable = terms
                .arithmetic_variable_for_term(item.result)
                .map_err(|error| ProofError::new(error.to_string()))?
                .ok_or_else(|| {
                    ProofError::new("arithmetic ite result is not a canonical variable")
                })?;
            arithmetic_ites.insert(variable, *item);
        }
        Ok(Self {
            converted: HashMap::new(),
            abstract_converted: HashMap::new(),
            application_converted: HashMap::new(),
            application_results,
            application_bits,
            arithmetic_applications,
            arithmetic_converted: HashMap::new(),
            arithmetic_ites,
            abstract_terms: BTreeMap::new(),
            applications: BTreeSet::new(),
            processed_array_selects: BTreeSet::new(),
            lowered: HashMap::new(),
            lowered_abstract: HashMap::new(),
            interned: HashMap::new(),
        })
    }

    fn convert(
        &mut self,
        terms: &TermStore,
        term: TermId,
        names: &ProofNames,
    ) -> Result<BoolExpr, ProofError> {
        if let Some(expression) = self.converted.get(&term) {
            return Ok(expression.clone());
        }
        let expression = match terms.node(term).kind.clone() {
            TermKind::Bool(false) => self.intern(BoolNode::False),
            TermKind::Bool(true) => self.intern(BoolNode::True),
            TermKind::Atom(symbol) => {
                let atom = if let Some(name) = names.atoms.get(&symbol) {
                    name.clone()
                } else if let Some((application_index, bit_index)) =
                    self.application_bits.get(&term).copied()
                {
                    ProofAtom::ApplicationBit {
                        application: self.convert_application(terms, application_index, names)?,
                        index: bit_index,
                    }
                } else {
                    return Err(ProofError::new(format!(
                        "proof atom {} has no active declaration or application",
                        symbol.0
                    )));
                };
                self.intern(BoolNode::Atom(atom))
            }
            TermKind::Not(inner) => {
                let inner = self.convert(terms, inner, names)?;
                self.not(inner)
            }
            TermKind::And(items) => {
                let items = items
                    .iter()
                    .map(|&item| self.convert(terms, item, names))
                    .collect::<Result<Vec<_>, _>>()?;
                self.junction(items, true)
            }
            TermKind::Or(items) => {
                let items = items
                    .iter()
                    .map(|&item| self.convert(terms, item, names))
                    .collect::<Result<Vec<_>, _>>()?;
                self.junction(items, false)
            }
            TermKind::Xor(left, right) => {
                let left = self.convert(terms, left, names)?;
                let right = self.convert(terms, right, names)?;
                self.xor(left, right)
            }
            TermKind::Iff(left, right) => {
                let left = self.convert(terms, left, names)?;
                let right = self.convert(terms, right, names)?;
                self.iff(left, right)
            }
            TermKind::Ite(condition, then_term, else_term) => {
                let condition = self.convert(terms, condition, names)?;
                let then_term = self.convert(terms, then_term, names)?;
                let else_term = self.convert(terms, else_term, names)?;
                self.ite(condition, then_term, else_term)
            }
            TermKind::TheoryEquality(_, left, right) => {
                let left = self.convert_abstract(terms, left, names)?;
                let right = self.convert_abstract(terms, right, names)?;
                let (left, right) = ordered_abstract_pair(left, right);
                self.intern(BoolNode::TheoryEquality(left, right))
            }
            TermKind::ArithmeticPredicate(_, expression, strict) => {
                let source_sort = terms
                    .arithmetic_expression_sort(expression)
                    .map_err(|error| ProofError::new(error.to_string()))?;
                let sort = self.proof_sort(terms, source_sort, names)?;
                let expression =
                    self.convert_arithmetic_expression(terms, expression, source_sort, names)?;
                self.intern(BoolNode::Atom(ProofAtom::ArithmeticPredicate {
                    sort,
                    expression,
                    strict,
                }))
            }
            TermKind::UfConstant(_)
            | TermKind::UfApplication(_, _)
            | TermKind::UfIte(_, _, _)
            | TermKind::Arithmetic(_)
            | TermKind::ArrayConst(_)
            | TermKind::ArrayStore(_, _, _)
            | TermKind::BitVec(_) => {
                return Err(ProofError::new(
                    "SMT proof replay encountered an unsupported non-Boolean node",
                ));
            }
        };
        self.converted.insert(term, expression.clone());
        Ok(expression)
    }

    fn convert_arithmetic_expression(
        &mut self,
        terms: &TermStore,
        expression: ArithmeticExpressionId,
        sort: Sort,
        names: &ProofNames,
    ) -> Result<ProofLinearExpression, ProofError> {
        let expression = terms
            .arithmetic_expression(expression)
            .map_err(|error| ProofError::new(error.to_string()))?;
        self.convert_linear_expression(terms, expression, sort, names)
    }

    fn convert_linear_expression(
        &mut self,
        terms: &TermStore,
        expression: &LinearExpression,
        sort: Sort,
        names: &ProofNames,
    ) -> Result<ProofLinearExpression, ProofError> {
        let expected_sort = self.proof_sort(terms, sort, names)?;
        if !matches!(expected_sort, ProofSort::Int | ProofSort::Real) {
            return Err(ProofError::new(
                "proof arithmetic expression has a non-arithmetic sort",
            ));
        }
        let mut coefficients = BTreeMap::new();
        for (&variable, coefficient) in &expression.coefficients {
            let variable = self.convert_arithmetic_variable(terms, variable, names)?;
            let updated = coefficients
                .get(&variable)
                .cloned()
                .unwrap_or_else(BigRational::zero)
                + coefficient;
            if updated.is_zero() {
                coefficients.remove(&variable);
            } else {
                coefficients.insert(variable, updated);
            }
        }
        Ok(ProofLinearExpression {
            constant: expression.constant.clone(),
            coefficients,
        })
    }

    fn convert_arithmetic_variable(
        &mut self,
        terms: &TermStore,
        variable: ArithmeticVariableId,
        names: &ProofNames,
    ) -> Result<ProofArithmeticVariable, ProofError> {
        if let Some(converted) = self.arithmetic_converted.get(&variable) {
            return Ok(converted.clone());
        }
        let converted = if let Some((sort, name)) = names.arithmetic_variables.get(&variable) {
            ProofArithmeticVariable::Declared {
                sort: sort.clone(),
                name: name.clone(),
            }
        } else if let Some(application_index) = self.arithmetic_applications.get(&variable).copied()
        {
            let application = self.convert_application(terms, application_index, names)?;
            let sort = application.range.clone();
            if !matches!(sort, ProofSort::Int | ProofSort::Real) {
                return Err(ProofError::new(
                    "arithmetic proof application has a non-arithmetic result sort",
                ));
            }
            ProofArithmeticVariable::Application {
                sort,
                application: Box::new(application),
            }
        } else if let Some(item) = self.arithmetic_ites.get(&variable).copied() {
            let source_sort = terms
                .sort(item.result)
                .map_err(|error| ProofError::new(error.to_string()))?;
            let sort = self.proof_sort(terms, source_sort, names)?;
            let then_expression = self.convert_linear_expression(
                terms,
                terms
                    .arithmetic_expression_for_term(item.then_term)
                    .map_err(|error| ProofError::new(error.to_string()))?,
                source_sort,
                names,
            )?;
            let else_expression = self.convert_linear_expression(
                terms,
                terms
                    .arithmetic_expression_for_term(item.else_term)
                    .map_err(|error| ProofError::new(error.to_string()))?,
                source_sort,
                names,
            )?;
            ProofArithmeticVariable::Ite {
                sort,
                condition: self.convert(terms, item.condition, names)?,
                then_expression: Box::new(then_expression),
                else_expression: Box::new(else_expression),
            }
        } else {
            return Err(ProofError::new(format!(
                "arithmetic proof variable {} has no active declaration or canonical definition",
                variable.0
            )));
        };
        self.arithmetic_converted
            .insert(variable, converted.clone());
        Ok(converted)
    }

    fn convert_value(
        &mut self,
        terms: &TermStore,
        term: TermId,
        expected: Sort,
        names: &ProofNames,
    ) -> Result<ProofValue, ProofError> {
        let actual = terms
            .sort(term)
            .map_err(|error| ProofError::new(error.to_string()))?;
        if actual != expected {
            return Err(ProofError::new(
                "proof application argument has an inconsistent sort",
            ));
        }
        match expected {
            Sort::Bool => Ok(ProofValue::Bool(self.convert(terms, term, names)?)),
            Sort::BitVec(_) => Ok(ProofValue::BitVec(
                terms
                    .bitvec_bits(term)
                    .map_err(|error| ProofError::new(error.to_string()))?
                    .iter()
                    .map(|&bit| self.convert(terms, bit, names))
                    .collect::<Result<Vec<_>, _>>()?,
            )),
            Sort::Uninterpreted(_) | Sort::Array(_) => Ok(ProofValue::Abstract(
                self.convert_abstract(terms, term, names)?,
            )),
            Sort::Int | Sort::Real => Ok(ProofValue::Arithmetic {
                sort: self.proof_sort(terms, expected, names)?,
                expression: self.convert_linear_expression(
                    terms,
                    terms
                        .arithmetic_expression_for_term(term)
                        .map_err(|error| ProofError::new(error.to_string()))?,
                    expected,
                    names,
                )?,
            }),
        }
    }

    fn convert_application(
        &mut self,
        terms: &TermStore,
        application_index: usize,
        names: &ProofNames,
    ) -> Result<ProofApplication, ProofError> {
        if let Some(application) = self.application_converted.get(&application_index) {
            return Ok(application.clone());
        }
        let application = terms
            .applications()
            .get(application_index)
            .ok_or_else(|| ProofError::new("proof application index is invalid"))?;
        let signature = terms
            .function_signature(application.function)
            .map_err(|error| ProofError::new(error.to_string()))?;
        let function = if let Some(array_sort) = terms.select_array_sort(application.function) {
            ProofFunction::ArraySelect(self.proof_sort(terms, Sort::Array(array_sort), names)?)
        } else {
            ProofFunction::Declared(
                names
                    .functions
                    .get(&application.function)
                    .ok_or_else(|| {
                        ProofError::new(format!(
                            "proof application {:?} has no active function declaration",
                            application.function
                        ))
                    })?
                    .clone(),
            )
        };
        let arguments = application
            .arguments
            .iter()
            .zip(signature.domain.iter())
            .map(|(&argument, &sort)| self.convert_value(terms, argument, sort, names))
            .collect::<Result<Vec<_>, _>>()?;
        let converted = ProofApplication {
            function,
            domain: signature
                .domain
                .iter()
                .map(|&sort| self.proof_sort(terms, sort, names))
                .collect::<Result<Vec<_>, _>>()?,
            range: self.proof_sort(terms, signature.range, names)?,
            arguments,
        };
        self.application_converted
            .insert(application_index, converted.clone());
        self.applications.insert(converted.clone());
        if matches!(
            &converted.range,
            ProofSort::Uninterpreted(_) | ProofSort::Array(_, _)
        ) {
            let sort = converted.range.clone();
            self.register_abstract(
                &sort,
                AbstractExpr(Arc::new(AbstractNode::Application(converted.clone()))),
            );
        }
        Ok(converted)
    }

    fn convert_abstract(
        &mut self,
        terms: &TermStore,
        term: TermId,
        names: &ProofNames,
    ) -> Result<AbstractExpr, ProofError> {
        if let Some(expression) = self.abstract_converted.get(&term) {
            return Ok(expression.clone());
        }
        let source_sort = terms
            .sort(term)
            .map_err(|error| ProofError::new(error.to_string()))?;
        let sort = self.proof_sort(terms, source_sort, names)?;
        if matches!(sort, ProofSort::Bool | ProofSort::BitVec(_)) {
            return Err(ProofError::new(
                "abstract proof term has a lowered Boolean sort",
            ));
        }
        let expression = match terms.node(term).kind.clone() {
            TermKind::UfConstant(_) => {
                let name = names.constants.get(&term).ok_or_else(|| {
                    ProofError::new("abstract proof constant has no active declaration")
                })?;
                AbstractExpr(Arc::new(AbstractNode::Constant {
                    sort: sort.clone(),
                    name: name.clone(),
                }))
            }
            TermKind::UfApplication(_, _) => {
                let application_index =
                    self.application_results
                        .get(&term)
                        .copied()
                        .ok_or_else(|| {
                            ProofError::new("abstract proof application has no application record")
                        })?;
                AbstractExpr(Arc::new(AbstractNode::Application(
                    self.convert_application(terms, application_index, names)?,
                )))
            }
            TermKind::UfIte(condition, then_term, else_term) => {
                let condition = self.convert(terms, condition, names)?;
                let then_term = self.convert_abstract(terms, then_term, names)?;
                let else_term = self.convert_abstract(terms, else_term, names)?;
                AbstractExpr(Arc::new(AbstractNode::Ite {
                    sort: sort.clone(),
                    condition,
                    then_term,
                    else_term,
                }))
            }
            TermKind::ArrayConst(value) => {
                let Sort::Array(array_sort) = source_sort else {
                    return Err(ProofError::new("constant-array term has a non-array sort"));
                };
                let signature = terms
                    .array_signature(array_sort)
                    .map_err(|error| ProofError::new(error.to_string()))?;
                let value = self.convert_value(terms, value, signature.element, names)?;
                AbstractExpr(Arc::new(AbstractNode::ArrayConst {
                    sort: sort.clone(),
                    value,
                }))
            }
            TermKind::ArrayStore(array, index, value) => {
                let Sort::Array(array_sort) = source_sort else {
                    return Err(ProofError::new("array-store term has a non-array sort"));
                };
                let signature = terms
                    .array_signature(array_sort)
                    .map_err(|error| ProofError::new(error.to_string()))?;
                let array = self.convert_abstract(terms, array, names)?;
                let index = self.convert_value(terms, index, signature.index, names)?;
                let value = self.convert_value(terms, value, signature.element, names)?;
                AbstractExpr(Arc::new(AbstractNode::ArrayStore {
                    sort: sort.clone(),
                    array,
                    index,
                    value,
                }))
            }
            _ => {
                return Err(ProofError::new(
                    "proof replay encountered a non-abstract term",
                ));
            }
        };
        self.register_abstract(&sort, expression.clone());
        self.abstract_converted.insert(term, expression.clone());
        Ok(expression)
    }

    fn proof_sort(
        &self,
        terms: &TermStore,
        sort: Sort,
        names: &ProofNames,
    ) -> Result<ProofSort, ProofError> {
        match sort {
            Sort::Bool => Ok(ProofSort::Bool),
            Sort::BitVec(width) => Ok(ProofSort::BitVec(width)),
            Sort::Uninterpreted(sort) => names
                .sorts
                .get(&sort)
                .cloned()
                .map(ProofSort::Uninterpreted)
                .ok_or_else(|| {
                    ProofError::new(format!(
                        "uninterpreted proof sort {} has no active declaration",
                        sort.index()
                    ))
                }),
            Sort::Array(sort) => {
                let signature = terms
                    .array_signature(sort)
                    .map_err(|error| ProofError::new(error.to_string()))?;
                if matches!(signature.index, Sort::Array(_))
                    || matches!(signature.element, Sort::Array(_))
                {
                    return Err(ProofError::new(
                        "nested arrays are outside the proof boundary",
                    ));
                }
                Ok(ProofSort::Array(
                    Box::new(self.proof_sort(terms, signature.index, names)?),
                    Box::new(self.proof_sort(terms, signature.element, names)?),
                ))
            }
            Sort::Int => Ok(ProofSort::Int),
            Sort::Real => Ok(ProofSort::Real),
        }
    }

    fn register_abstract(&mut self, sort: &ProofSort, expression: AbstractExpr) {
        // A ground theory model needs at most one class per non-ite abstract
        // term. An ite denotes one of its branches, so counting it as another
        // possible class would only widen the encoding without adding models.
        if matches!(
            expression.node(),
            AbstractNode::Constant { .. }
                | AbstractNode::Application(_)
                | AbstractNode::ArrayConst { .. }
                | AbstractNode::ArrayStore { .. }
                | AbstractNode::ArrayWitness { .. }
        ) {
            self.abstract_terms
                .entry(sort.clone())
                .or_default()
                .insert(expression);
        }
    }

    fn lower(&mut self, expression: &BoolExpr) -> Result<BoolExpr, ProofError> {
        if let Some(lowered) = self.lowered.get(expression) {
            return Ok(lowered.clone());
        }
        let lowered = match expression.node() {
            BoolNode::False | BoolNode::True => expression.clone(),
            BoolNode::Atom(ProofAtom::ArithmeticPredicate {
                sort,
                expression,
                strict,
            }) => {
                let expression = self.lower_linear_expression(expression)?;
                self.arithmetic_predicate(sort.clone(), expression, *strict)?
            }
            BoolNode::Atom(_) => expression.clone(),
            BoolNode::Not(inner) => {
                let inner = self.lower(inner)?;
                self.not(inner)
            }
            BoolNode::And(items) => {
                let items = items
                    .iter()
                    .map(|item| self.lower(item))
                    .collect::<Result<Vec<_>, _>>()?;
                self.junction(items, true)
            }
            BoolNode::Or(items) => {
                let items = items
                    .iter()
                    .map(|item| self.lower(item))
                    .collect::<Result<Vec<_>, _>>()?;
                self.junction(items, false)
            }
            BoolNode::Xor(left, right) => {
                let left = self.lower(left)?;
                let right = self.lower(right)?;
                self.xor(left, right)
            }
            BoolNode::Iff(left, right) => {
                let left = self.lower(left)?;
                let right = self.lower(right)?;
                self.iff(left, right)
            }
            BoolNode::Ite(condition, then_term, else_term) => {
                let condition = self.lower(condition)?;
                let then_term = self.lower(then_term)?;
                let else_term = self.lower(else_term)?;
                self.ite(condition, then_term, else_term)
            }
            BoolNode::TheoryEquality(left, right) => self.abstract_equal(left, right)?,
        };
        self.lowered.insert(expression.clone(), lowered.clone());
        Ok(lowered)
    }

    fn lower_linear_expression(
        &mut self,
        expression: &ProofLinearExpression,
    ) -> Result<ProofLinearExpression, ProofError> {
        let mut coefficients = BTreeMap::new();
        for (variable, coefficient) in &expression.coefficients {
            let variable = self.lower_arithmetic_variable(variable)?;
            let updated = coefficients
                .get(&variable)
                .cloned()
                .unwrap_or_else(BigRational::zero)
                + coefficient;
            if updated.is_zero() {
                coefficients.remove(&variable);
            } else {
                coefficients.insert(variable, updated);
            }
        }
        Ok(ProofLinearExpression {
            constant: expression.constant.clone(),
            coefficients,
        })
    }

    fn lower_arithmetic_variable(
        &mut self,
        variable: &ProofArithmeticVariable,
    ) -> Result<ProofArithmeticVariable, ProofError> {
        match variable {
            ProofArithmeticVariable::Declared { .. }
            | ProofArithmeticVariable::Application { .. }
            | ProofArithmeticVariable::ArrayWitness { .. } => Ok(variable.clone()),
            ProofArithmeticVariable::Ite {
                sort,
                condition,
                then_expression,
                else_expression,
            } => Ok(ProofArithmeticVariable::Ite {
                sort: sort.clone(),
                condition: self.lower(condition)?,
                then_expression: Box::new(self.lower_linear_expression(then_expression)?),
                else_expression: Box::new(self.lower_linear_expression(else_expression)?),
            }),
        }
    }

    fn arithmetic_predicate(
        &mut self,
        sort: ProofSort,
        expression: ProofLinearExpression,
        strict: bool,
    ) -> Result<BoolExpr, ProofError> {
        if !matches!(sort, ProofSort::Int | ProofSort::Real) {
            return Err(ProofError::new(
                "proof arithmetic predicate has a non-arithmetic sort",
            ));
        }
        if expression.coefficients.is_empty() {
            let satisfied = if strict {
                expression.constant.is_negative()
            } else {
                expression.constant.is_negative() || expression.constant.is_zero()
            };
            return Ok(self.bool_constant(satisfied));
        }
        Ok(self.intern(BoolNode::Atom(ProofAtom::ArithmeticPredicate {
            sort,
            expression,
            strict,
        })))
    }

    fn arithmetic_equal(
        &mut self,
        sort: ProofSort,
        left: &ProofLinearExpression,
        right: &ProofLinearExpression,
    ) -> Result<BoolExpr, ProofError> {
        let minus_one = BigRational::from_integer(BigInt::from(-1));
        let mut forward = left.clone();
        forward.add_scaled(right, &minus_one);
        let reverse = forward.clone().scaled(&minus_one);
        let forward = self.arithmetic_predicate(sort.clone(), forward, false)?;
        let reverse = self.arithmetic_predicate(sort, reverse, false)?;
        Ok(self.junction(vec![forward, reverse], true))
    }

    fn abstract_bits(&mut self, expression: &AbstractExpr) -> Result<Vec<BoolExpr>, ProofError> {
        if let Some(bits) = self.lowered_abstract.get(expression) {
            return Ok(bits.clone());
        }
        let (sort, bits) = match expression.node() {
            AbstractNode::Constant { sort, .. }
            | AbstractNode::Application(ProofApplication { range: sort, .. })
            | AbstractNode::ArrayConst { sort, .. }
            | AbstractNode::ArrayStore { sort, .. }
            | AbstractNode::ArrayWitness { sort, .. } => {
                if !matches!(sort, ProofSort::Uninterpreted(_) | ProofSort::Array(_, _)) {
                    return Err(ProofError::new(
                        "abstract proof term has a non-abstract result sort",
                    ));
                }
                let width = self.class_width(sort)?;
                let bits = (0..width)
                    .map(|index| {
                        let index = u32::try_from(index)
                            .map_err(|_| ProofError::new("proof class encoding is too wide"))?;
                        Ok(self.intern(BoolNode::Atom(ProofAtom::ClassBit {
                            sort: sort.clone(),
                            term: expression.clone(),
                            index,
                        })))
                    })
                    .collect::<Result<Vec<_>, ProofError>>()?;
                (sort.clone(), bits)
            }
            AbstractNode::Ite {
                sort,
                condition,
                then_term,
                else_term,
            } => {
                let condition = self.lower(condition)?;
                let then_bits = self.abstract_bits(then_term)?;
                let else_bits = self.abstract_bits(else_term)?;
                if then_bits.len() != else_bits.len() {
                    return Err(ProofError::new(
                        "abstract ite branches have inconsistent class encodings",
                    ));
                }
                let bits = then_bits
                    .into_iter()
                    .zip(else_bits)
                    .map(|(then_bit, else_bit)| self.ite(condition.clone(), then_bit, else_bit))
                    .collect();
                (sort.clone(), bits)
            }
        };
        if abstract_sort(expression) != &sort {
            return Err(ProofError::new(
                "abstract term and class encoding sorts disagree",
            ));
        }
        self.lowered_abstract
            .insert(expression.clone(), bits.clone());
        Ok(bits)
    }

    fn class_width(&self, sort: &ProofSort) -> Result<usize, ProofError> {
        let count = self
            .abstract_terms
            .get(sort)
            .map(BTreeSet::len)
            .unwrap_or(0);
        if count == 0 {
            return Err(ProofError::new(
                "abstract proof sort has no canonical ground terms",
            ));
        }
        // ceil(log2(count)) bits can name every equivalence class in the
        // finite projection of any model onto these ground terms.
        let width = usize::BITS - (count.saturating_sub(1)).leading_zeros();
        Ok(usize::try_from(width.max(1)).expect("usize bit width always fits in usize"))
    }

    fn abstract_equal(
        &mut self,
        left: &AbstractExpr,
        right: &AbstractExpr,
    ) -> Result<BoolExpr, ProofError> {
        if abstract_sort(left) != abstract_sort(right) {
            return Err(ProofError::new(
                "abstract equality operands have different sorts",
            ));
        }
        let left_bits = self.abstract_bits(left)?;
        let right_bits = self.abstract_bits(right)?;
        let equalities = left_bits
            .into_iter()
            .zip(right_bits)
            .map(|(left, right)| self.iff(left, right))
            .collect();
        Ok(self.junction(equalities, true))
    }

    fn value_equal(
        &mut self,
        left: &ProofValue,
        right: &ProofValue,
    ) -> Result<BoolExpr, ProofError> {
        match (left, right) {
            (ProofValue::Bool(left), ProofValue::Bool(right)) => {
                let left = self.lower(left)?;
                let right = self.lower(right)?;
                Ok(self.iff(left, right))
            }
            (ProofValue::BitVec(left), ProofValue::BitVec(right)) => {
                if left.len() != right.len() {
                    return Err(ProofError::new(
                        "bit-vector proof values have different widths",
                    ));
                }
                let mut equalities = Vec::with_capacity(left.len());
                for (left, right) in left.iter().zip(right) {
                    let left = self.lower(left)?;
                    let right = self.lower(right)?;
                    equalities.push(self.iff(left, right));
                }
                Ok(self.junction(equalities, true))
            }
            (ProofValue::Abstract(left), ProofValue::Abstract(right)) => {
                self.abstract_equal(left, right)
            }
            (
                ProofValue::Arithmetic {
                    sort: left_sort,
                    expression: left,
                },
                ProofValue::Arithmetic {
                    sort: right_sort,
                    expression: right,
                },
            ) => {
                if left_sort != right_sort {
                    return Err(ProofError::new(
                        "arithmetic proof values have different sorts",
                    ));
                }
                let left = self.lower_linear_expression(left)?;
                let right = self.lower_linear_expression(right)?;
                self.arithmetic_equal(left_sort.clone(), &left, &right)
            }
            _ => Err(ProofError::new(
                "proof values with different sorts were compared",
            )),
        }
    }

    fn application_result(
        &mut self,
        application: &ProofApplication,
    ) -> Result<ProofValue, ProofError> {
        match &application.range {
            ProofSort::Bool => Ok(ProofValue::Bool(self.intern(BoolNode::Atom(
                ProofAtom::ApplicationBit {
                    application: application.clone(),
                    index: 0,
                },
            )))),
            ProofSort::BitVec(width) => Ok(ProofValue::BitVec(
                (0..*width)
                    .map(|index| {
                        self.intern(BoolNode::Atom(ProofAtom::ApplicationBit {
                            application: application.clone(),
                            index,
                        }))
                    })
                    .collect(),
            )),
            sort @ (ProofSort::Uninterpreted(_) | ProofSort::Array(_, _)) => {
                let expression =
                    AbstractExpr(Arc::new(AbstractNode::Application(application.clone())));
                self.register_abstract(sort, expression.clone());
                Ok(ProofValue::Abstract(expression))
            }
            sort @ (ProofSort::Int | ProofSort::Real) => Ok(ProofValue::Arithmetic {
                sort: sort.clone(),
                expression: ProofLinearExpression::variable(ProofArithmeticVariable::Application {
                    sort: sort.clone(),
                    application: Box::new(application.clone()),
                }),
            }),
        }
    }

    fn prepare_theory(&mut self) -> Result<(), ProofError> {
        for (sort, left, right) in self.array_pairs() {
            let witness = self.array_witness(&sort, &left, &right)?;
            self.array_select_application(&left, &witness)?;
            self.array_select_application(&right, &witness)?;
        }

        loop {
            let pending = self
                .applications
                .iter()
                .filter(|application| {
                    matches!(&application.function, ProofFunction::ArraySelect(_))
                        && !self.processed_array_selects.contains(*application)
                })
                .cloned()
                .collect::<Vec<_>>();
            if pending.is_empty() {
                return Ok(());
            }
            for application in pending {
                self.processed_array_selects.insert(application.clone());
                self.expand_array_select(&application)?;
            }
        }
    }

    fn theory_axioms(&mut self) -> Result<Vec<BoolExpr>, ProofError> {
        let application_count = self.applications.len();
        let abstract_term_count = self
            .abstract_terms
            .values()
            .map(BTreeSet::len)
            .sum::<usize>();
        let mut axioms = BTreeSet::new();
        axioms.extend(self.array_semantics_axioms()?);
        axioms.extend(self.array_extensionality_axioms()?);
        axioms.extend(self.congruence_axioms()?);
        if self.applications.len() != application_count
            || self
                .abstract_terms
                .values()
                .map(BTreeSet::len)
                .sum::<usize>()
                != abstract_term_count
        {
            return Err(ProofError::new(
                "array proof theory closure changed after Boolean lowering",
            ));
        }
        Ok(axioms.into_iter().collect())
    }

    fn array_pairs(&self) -> Vec<(ProofSort, AbstractExpr, AbstractExpr)> {
        let mut pairs = Vec::new();
        for (sort, terms) in &self.abstract_terms {
            if !matches!(sort, ProofSort::Array(_, _)) {
                continue;
            }
            let terms = terms.iter().cloned().collect::<Vec<_>>();
            for (left_index, left) in terms.iter().enumerate() {
                for right in &terms[left_index + 1..] {
                    pairs.push((sort.clone(), left.clone(), right.clone()));
                }
            }
        }
        pairs
    }

    fn array_witness(
        &mut self,
        array_sort: &ProofSort,
        left: &AbstractExpr,
        right: &AbstractExpr,
    ) -> Result<ProofValue, ProofError> {
        let ProofSort::Array(index_sort, _) = array_sort else {
            return Err(ProofError::new(
                "array extensionality requested for a non-array sort",
            ));
        };
        match index_sort.as_ref() {
            ProofSort::Bool => Ok(ProofValue::Bool(self.intern(BoolNode::Atom(
                ProofAtom::ArrayWitnessBit {
                    sort: array_sort.clone(),
                    left: left.clone(),
                    right: right.clone(),
                    index: 0,
                },
            )))),
            ProofSort::BitVec(width) => Ok(ProofValue::BitVec(
                (0..*width)
                    .map(|index| {
                        self.intern(BoolNode::Atom(ProofAtom::ArrayWitnessBit {
                            sort: array_sort.clone(),
                            left: left.clone(),
                            right: right.clone(),
                            index,
                        }))
                    })
                    .collect(),
            )),
            sort @ ProofSort::Uninterpreted(_) => {
                let witness = AbstractExpr(Arc::new(AbstractNode::ArrayWitness {
                    sort: sort.clone(),
                    array_sort: array_sort.clone(),
                    left: left.clone(),
                    right: right.clone(),
                }));
                self.register_abstract(sort, witness.clone());
                Ok(ProofValue::Abstract(witness))
            }
            ProofSort::Array(_, _) => Err(ProofError::new(
                "nested array indices are outside the proof boundary",
            )),
            sort @ (ProofSort::Int | ProofSort::Real) => Ok(ProofValue::Arithmetic {
                sort: sort.clone(),
                expression: ProofLinearExpression::variable(
                    ProofArithmeticVariable::ArrayWitness {
                        sort: sort.clone(),
                        array_sort: array_sort.clone(),
                        left: left.clone(),
                        right: right.clone(),
                    },
                ),
            }),
        }
    }

    fn value_sort(&self, value: &ProofValue) -> Result<ProofSort, ProofError> {
        match value {
            ProofValue::Bool(_) => Ok(ProofSort::Bool),
            ProofValue::BitVec(bits) => Ok(ProofSort::BitVec(
                u32::try_from(bits.len())
                    .map_err(|_| ProofError::new("proof bit-vector value is too wide"))?,
            )),
            ProofValue::Abstract(expression) => Ok(abstract_sort(expression).clone()),
            ProofValue::Arithmetic { sort, .. } => Ok(sort.clone()),
        }
    }

    fn array_select_application(
        &mut self,
        array: &AbstractExpr,
        index: &ProofValue,
    ) -> Result<ProofApplication, ProofError> {
        let array_sort = abstract_sort(array).clone();
        let ProofSort::Array(index_sort, element_sort) = &array_sort else {
            return Err(ProofError::new("array select has a non-array source"));
        };
        if self.value_sort(index)? != **index_sort {
            return Err(ProofError::new(
                "array select index has an inconsistent proof sort",
            ));
        }
        if matches!(element_sort.as_ref(), ProofSort::Array(_, _)) {
            return Err(ProofError::new(
                "nested array elements are outside the proof boundary",
            ));
        }
        let application = ProofApplication {
            function: ProofFunction::ArraySelect(array_sort.clone()),
            domain: vec![array_sort.clone(), (**index_sort).clone()],
            range: (**element_sort).clone(),
            arguments: vec![ProofValue::Abstract(array.clone()), index.clone()],
        };
        self.applications.insert(application.clone());
        if matches!(
            &application.range,
            ProofSort::Uninterpreted(_) | ProofSort::Array(_, _)
        ) {
            let result = AbstractExpr(Arc::new(AbstractNode::Application(application.clone())));
            let sort = application.range.clone();
            self.register_abstract(&sort, result);
        }
        Ok(application)
    }

    fn expand_array_select(&mut self, application: &ProofApplication) -> Result<(), ProofError> {
        let ProofFunction::ArraySelect(_) = &application.function else {
            return Ok(());
        };
        let [ProofValue::Abstract(array), index] = application.arguments.as_slice() else {
            return Err(ProofError::new(
                "canonical array select has malformed arguments",
            ));
        };
        match array.node() {
            AbstractNode::ArrayStore { array, .. } => {
                self.array_select_application(array, index)?;
            }
            AbstractNode::Ite {
                then_term,
                else_term,
                ..
            } => {
                self.array_select_application(then_term, index)?;
                self.array_select_application(else_term, index)?;
            }
            AbstractNode::Constant { .. }
            | AbstractNode::Application(_)
            | AbstractNode::ArrayConst { .. }
            | AbstractNode::ArrayWitness { .. } => {}
        }
        Ok(())
    }

    fn value_ite(
        &mut self,
        condition: BoolExpr,
        then_value: &ProofValue,
        else_value: &ProofValue,
    ) -> Result<ProofValue, ProofError> {
        if self.value_sort(then_value)? != self.value_sort(else_value)? {
            return Err(ProofError::new("proof ite values have inconsistent sorts"));
        }
        let condition = self.lower(&condition)?;
        match (then_value, else_value) {
            (ProofValue::Bool(then_term), ProofValue::Bool(else_term)) => {
                let then_term = self.lower(then_term)?;
                let else_term = self.lower(else_term)?;
                Ok(ProofValue::Bool(self.ite(condition, then_term, else_term)))
            }
            (ProofValue::BitVec(then_bits), ProofValue::BitVec(else_bits)) => {
                let bits = then_bits
                    .iter()
                    .zip(else_bits)
                    .map(|(then_bit, else_bit)| {
                        let then_bit = self.lower(then_bit)?;
                        let else_bit = self.lower(else_bit)?;
                        Ok(self.ite(condition.clone(), then_bit, else_bit))
                    })
                    .collect::<Result<Vec<_>, ProofError>>()?;
                Ok(ProofValue::BitVec(bits))
            }
            (ProofValue::Abstract(then_term), ProofValue::Abstract(else_term)) => {
                let sort = abstract_sort(then_term).clone();
                Ok(ProofValue::Abstract(AbstractExpr(Arc::new(
                    AbstractNode::Ite {
                        sort,
                        condition,
                        then_term: then_term.clone(),
                        else_term: else_term.clone(),
                    },
                ))))
            }
            (
                ProofValue::Arithmetic {
                    sort,
                    expression: then_expression,
                },
                ProofValue::Arithmetic {
                    expression: else_expression,
                    ..
                },
            ) => {
                let then_expression = self.lower_linear_expression(then_expression)?;
                let else_expression = self.lower_linear_expression(else_expression)?;
                if then_expression == else_expression {
                    return Ok(ProofValue::Arithmetic {
                        sort: sort.clone(),
                        expression: then_expression,
                    });
                }
                Ok(ProofValue::Arithmetic {
                    sort: sort.clone(),
                    expression: ProofLinearExpression::variable(ProofArithmeticVariable::Ite {
                        sort: sort.clone(),
                        condition,
                        then_expression: Box::new(then_expression),
                        else_expression: Box::new(else_expression),
                    }),
                })
            }
            _ => Err(ProofError::new(
                "proof ite values have inconsistent representations",
            )),
        }
    }

    fn array_semantics_axioms(&mut self) -> Result<Vec<BoolExpr>, ProofError> {
        let applications = self
            .applications
            .iter()
            .filter(|application| matches!(&application.function, ProofFunction::ArraySelect(_)))
            .cloned()
            .collect::<Vec<_>>();
        let mut axioms = BTreeSet::new();
        for application in applications {
            let [ProofValue::Abstract(array), index] = application.arguments.as_slice() else {
                return Err(ProofError::new(
                    "canonical array select has malformed arguments",
                ));
            };
            let semantic_value = match array.node() {
                AbstractNode::ArrayConst { value, .. } => Some(value.clone()),
                AbstractNode::ArrayStore {
                    array: base,
                    index: stored_index,
                    value: stored_value,
                    ..
                } => {
                    let fallback_application = self.array_select_application(base, index)?;
                    let fallback = self.application_result(&fallback_application)?;
                    let same_index = self.value_equal(stored_index, index)?;
                    Some(self.value_ite(same_index, stored_value, &fallback)?)
                }
                AbstractNode::Ite {
                    condition,
                    then_term,
                    else_term,
                    ..
                } => {
                    let then_application = self.array_select_application(then_term, index)?;
                    let then_value = self.application_result(&then_application)?;
                    let else_application = self.array_select_application(else_term, index)?;
                    let else_value = self.application_result(&else_application)?;
                    Some(self.value_ite(condition.clone(), &then_value, &else_value)?)
                }
                AbstractNode::Constant { .. }
                | AbstractNode::Application(_)
                | AbstractNode::ArrayWitness { .. } => None,
            };
            if let Some(semantic_value) = semantic_value {
                let result = self.application_result(&application)?;
                axioms.insert(self.value_equal(&result, &semantic_value)?);
            }
        }
        Ok(axioms.into_iter().collect())
    }

    fn array_extensionality_axioms(&mut self) -> Result<Vec<BoolExpr>, ProofError> {
        let mut axioms = BTreeSet::new();
        for (sort, left, right) in self.array_pairs() {
            let witness = self.array_witness(&sort, &left, &right)?;
            let left_application = self.array_select_application(&left, &witness)?;
            let left_value = self.application_result(&left_application)?;
            let right_application = self.array_select_application(&right, &witness)?;
            let right_value = self.application_result(&right_application)?;
            let arrays_equal = self.abstract_equal(&left, &right)?;
            let values_equal = self.value_equal(&left_value, &right_value)?;
            let values_differ = self.not(values_equal);
            axioms.insert(self.junction(vec![arrays_equal, values_differ], false));
        }
        Ok(axioms.into_iter().collect())
    }

    fn congruence_axioms(&mut self) -> Result<Vec<BoolExpr>, ProofError> {
        let applications = self.applications.iter().cloned().collect::<Vec<_>>();
        let mut axioms = BTreeSet::new();
        // This is ground Ackermannization: equal argument tuples must have
        // equal results. Class bits already supply reflexive, symmetric, and
        // transitive equality, so no separate cubic equality axioms are
        // needed.
        for (left_index, left) in applications.iter().enumerate() {
            for right in &applications[left_index + 1..] {
                if left.function != right.function {
                    continue;
                }
                if left.domain != right.domain || left.range != right.range {
                    return Err(ProofError::new(
                        "proof function name has inconsistent signatures",
                    ));
                }
                let argument_equalities = left
                    .arguments
                    .iter()
                    .zip(&right.arguments)
                    .map(|(left, right)| self.value_equal(left, right))
                    .collect::<Result<Vec<_>, _>>()?;
                let arguments_equal = self.junction(argument_equalities, true);
                let left_result = self.application_result(left)?;
                let right_result = self.application_result(right)?;
                let results_equal = self.value_equal(&left_result, &right_result)?;
                let not_arguments_equal = self.not(arguments_equal);
                axioms.insert(self.junction(vec![not_arguments_equal, results_equal], false));
            }
        }
        Ok(axioms.into_iter().collect())
    }

    fn intern(&mut self, node: BoolNode) -> BoolExpr {
        if let Some(expression) = self.interned.get(&node) {
            return expression.clone();
        }
        let expression = BoolExpr(Arc::new(node.clone()));
        self.interned.insert(node, expression.clone());
        expression
    }

    fn bool_constant(&mut self, value: bool) -> BoolExpr {
        self.intern(if value {
            BoolNode::True
        } else {
            BoolNode::False
        })
    }

    fn not(&mut self, expression: BoolExpr) -> BoolExpr {
        match expression.node() {
            BoolNode::False => self.bool_constant(true),
            BoolNode::True => self.bool_constant(false),
            BoolNode::Not(inner) => inner.clone(),
            _ => self.intern(BoolNode::Not(expression)),
        }
    }

    fn junction(&mut self, expressions: Vec<BoolExpr>, conjunction: bool) -> BoolExpr {
        let mut flattened = Vec::new();
        for expression in expressions {
            match expression.node() {
                BoolNode::False if conjunction => return self.bool_constant(false),
                BoolNode::True if !conjunction => return self.bool_constant(true),
                BoolNode::True | BoolNode::False => {}
                BoolNode::And(nested) if conjunction => flattened.extend(nested.iter().cloned()),
                BoolNode::Or(nested) if !conjunction => flattened.extend(nested.iter().cloned()),
                _ => flattened.push(expression),
            }
        }
        flattened.sort_unstable();
        flattened.dedup();
        let members = flattened.iter().cloned().collect::<HashSet<_>>();
        if flattened
            .iter()
            .any(|member| matches!(member.node(), BoolNode::Not(inner) if members.contains(inner)))
        {
            return self.bool_constant(!conjunction);
        }
        match flattened.len() {
            0 => self.bool_constant(conjunction),
            1 => flattened.pop().expect("length checked"),
            _ if conjunction => self.intern(BoolNode::And(flattened)),
            _ => self.intern(BoolNode::Or(flattened)),
        }
    }

    fn xor(&mut self, left: BoolExpr, right: BoolExpr) -> BoolExpr {
        if left == right {
            return self.bool_constant(false);
        }
        if complements(&left, &right) {
            return self.bool_constant(true);
        }
        match (left.node(), right.node()) {
            (BoolNode::False, _) => right,
            (_, BoolNode::False) => left,
            (BoolNode::True, _) => self.not(right),
            (_, BoolNode::True) => self.not(left),
            _ => {
                let (left, right) = ordered_pair(left, right);
                self.intern(BoolNode::Xor(left, right))
            }
        }
    }

    fn iff(&mut self, left: BoolExpr, right: BoolExpr) -> BoolExpr {
        if left == right {
            return self.bool_constant(true);
        }
        if complements(&left, &right) {
            return self.bool_constant(false);
        }
        match (left.node(), right.node()) {
            (BoolNode::True, _) => right,
            (_, BoolNode::True) => left,
            (BoolNode::False, _) => self.not(right),
            (_, BoolNode::False) => self.not(left),
            _ => {
                let (left, right) = ordered_pair(left, right);
                self.intern(BoolNode::Iff(left, right))
            }
        }
    }

    fn ite(&mut self, condition: BoolExpr, then_term: BoolExpr, else_term: BoolExpr) -> BoolExpr {
        if then_term == else_term {
            return then_term;
        }
        match condition.node() {
            BoolNode::True => return then_term,
            BoolNode::False => return else_term,
            _ => {}
        }
        match (then_term.node(), else_term.node()) {
            (BoolNode::True, BoolNode::False) => condition,
            (BoolNode::False, BoolNode::True) => self.not(condition),
            _ => self.intern(BoolNode::Ite(condition, then_term, else_term)),
        }
    }
}

fn complements(left: &BoolExpr, right: &BoolExpr) -> bool {
    matches!(left.node(), BoolNode::Not(inner) if inner == right)
        || matches!(right.node(), BoolNode::Not(inner) if inner == left)
}

fn ordered_pair(left: BoolExpr, right: BoolExpr) -> (BoolExpr, BoolExpr) {
    if left <= right {
        (left, right)
    } else {
        (right, left)
    }
}

fn abstract_sort(expression: &AbstractExpr) -> &ProofSort {
    match expression.node() {
        AbstractNode::Constant { sort, .. }
        | AbstractNode::Ite { sort, .. }
        | AbstractNode::ArrayConst { sort, .. }
        | AbstractNode::ArrayStore { sort, .. }
        | AbstractNode::ArrayWitness { sort, .. } => sort,
        AbstractNode::Application(application) => {
            if matches!(
                &application.range,
                ProofSort::Uninterpreted(_) | ProofSort::Array(_, _)
            ) {
                &application.range
            } else {
                unreachable!("abstract applications have an abstract range")
            }
        }
    }
}

fn ordered_abstract_pair(left: AbstractExpr, right: AbstractExpr) -> (AbstractExpr, AbstractExpr) {
    if left <= right {
        (left, right)
    } else {
        (right, left)
    }
}

#[derive(Debug, Default)]
struct ProofEncoder {
    literals: HashMap<BoolExpr, Lit>,
    truth_literal: Option<Lit>,
}

impl ProofEncoder {
    fn encode(&mut self, solver: &mut Solver, expression: &BoolExpr) -> Result<Lit, ProofError> {
        if let Some(&literal) = self.literals.get(expression) {
            return Ok(literal);
        }
        let literal = match expression.node() {
            BoolNode::False => !self.truth_literal(solver)?,
            BoolNode::True => self.truth_literal(solver)?,
            BoolNode::Atom(_) => Lit::positive(
                solver
                    .new_variable()
                    .map_err(|error| ProofError::new(error.to_string()))?,
            ),
            BoolNode::Not(inner) => !self.encode(solver, inner)?,
            BoolNode::And(items) => {
                let inputs = items
                    .iter()
                    .map(|item| self.encode(solver, item))
                    .collect::<Result<Vec<_>, _>>()?;
                let output = self.new_literal(solver)?;
                for &input in &inputs {
                    self.add_encoding_clause(solver, &[!output, input])?;
                }
                let mut backward = Vec::with_capacity(inputs.len() + 1);
                backward.push(output);
                backward.extend(inputs.iter().map(|&input| !input));
                self.add_encoding_clause(solver, &backward)?;
                output
            }
            BoolNode::Or(items) => {
                let inputs = items
                    .iter()
                    .map(|item| self.encode(solver, item))
                    .collect::<Result<Vec<_>, _>>()?;
                let output = self.new_literal(solver)?;
                for &input in &inputs {
                    self.add_encoding_clause(solver, &[!input, output])?;
                }
                let mut backward = Vec::with_capacity(inputs.len() + 1);
                backward.push(!output);
                backward.extend_from_slice(&inputs);
                self.add_encoding_clause(solver, &backward)?;
                output
            }
            BoolNode::Xor(left, right) => {
                let left = self.encode(solver, left)?;
                let right = self.encode(solver, right)?;
                let output = self.new_literal(solver)?;
                for clause in [
                    [left, right, !output],
                    [!left, !right, !output],
                    [left, !right, output],
                    [!left, right, output],
                ] {
                    self.add_encoding_clause(solver, &clause)?;
                }
                output
            }
            BoolNode::Iff(left, right) => {
                let left = self.encode(solver, left)?;
                let right = self.encode(solver, right)?;
                let output = self.new_literal(solver)?;
                for clause in [
                    [left, right, output],
                    [!left, !right, output],
                    [left, !right, !output],
                    [!left, right, !output],
                ] {
                    self.add_encoding_clause(solver, &clause)?;
                }
                output
            }
            BoolNode::Ite(condition, then_term, else_term) => {
                let condition = self.encode(solver, condition)?;
                let then_term = self.encode(solver, then_term)?;
                let else_term = self.encode(solver, else_term)?;
                let output = self.new_literal(solver)?;
                for clause in [
                    [!condition, !then_term, output],
                    [!condition, then_term, !output],
                    [condition, !else_term, output],
                    [condition, else_term, !output],
                ] {
                    self.add_encoding_clause(solver, &clause)?;
                }
                output
            }
            BoolNode::TheoryEquality(_, _) => {
                return Err(ProofError::new(
                    "unlowered theory equality reached the proof encoder",
                ));
            }
        };
        self.literals.insert(expression.clone(), literal);
        Ok(literal)
    }

    fn truth_literal(&mut self, solver: &mut Solver) -> Result<Lit, ProofError> {
        if let Some(literal) = self.truth_literal {
            return Ok(literal);
        }
        let literal = self.new_literal(solver)?;
        self.add_encoding_clause(solver, &[literal])?;
        self.truth_literal = Some(literal);
        Ok(literal)
    }

    fn new_literal(&self, solver: &mut Solver) -> Result<Lit, ProofError> {
        solver
            .new_variable()
            .map(Lit::positive)
            .map_err(|error| ProofError::new(error.to_string()))
    }

    fn add_encoding_clause(&self, solver: &mut Solver, clause: &[Lit]) -> Result<(), ProofError> {
        solver
            .add_encoding_clause(clause)
            .map(|_| ())
            .map_err(|error| ProofError::new(error.to_string()))
    }
}

#[derive(Clone, Debug, Default)]
struct SharedBuffer(Arc<Mutex<Vec<u8>>>);

impl SharedBuffer {
    fn snapshot(&self) -> Result<Vec<u8>, ProofError> {
        self.0
            .lock()
            .map(|buffer| buffer.clone())
            .map_err(|_| ProofError::new("Boolean proof buffer lock was poisoned"))
    }
}

impl Write for SharedBuffer {
    fn write(&mut self, buffer: &[u8]) -> io::Result<usize> {
        self.0
            .lock()
            .map_err(|_| io::Error::other("Boolean proof buffer lock was poisoned"))?
            .extend_from_slice(buffer);
        Ok(buffer.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

fn quote_string(text: &str) -> String {
    format!("\"{}\"", text.replace('"', "\"\""))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fresh_replay_turns_query_roots_into_a_global_drat_refutation() {
        let mut terms = TermStore::new();
        let (a_symbol, a) = terms.fresh_bool_atom();
        let (b_symbol, b) = terms.fresh_bool_atom();
        let either = terms.or(&[a, b]).unwrap();
        let not_a = terms.not(a).unwrap();
        let not_b = terms.not(b).unwrap();
        let mut names = ProofNames::default();
        names.insert_bool(a_symbol, "a".to_owned());
        names.insert_bool(b_symbol, "b".to_owned());

        let proof = prove_boolean_unsat(
            ProofLogic::Bool,
            &terms,
            &[either, not_a, not_b],
            &[
                "(or a b)".to_owned(),
                "(not a)".to_owned(),
                "(not b)".to_owned(),
            ],
            &names,
        )
        .unwrap();

        assert!(proof.drat.ends_with(b"0\n"));
        assert_eq!(
            proof
                .clauses
                .iter()
                .filter(|clause| { clause.kind == crate::solver::ProofClauseKind::Formula })
                .count(),
            3
        );
        let rendered = proof.render();
        assert!(rendered.starts_with("(satrap-edrat :version 1 :logic QF_BOOL"));
        assert!(rendered.contains(":premises (\"(or a b)\""));
        assert!(rendered.contains(":drat \""));
    }

    #[test]
    fn canonical_proof_cnf_does_not_depend_on_internal_term_creation_order() {
        fn build(extra_first: bool) -> BooleanRefutation {
            let mut terms = TermStore::new();
            if extra_first {
                let (_, unused) = terms.fresh_bool_atom();
                let _ = terms.not(unused).unwrap();
            }
            let (a_symbol, a) = terms.fresh_bool_atom();
            let (b_symbol, b) = terms.fresh_bool_atom();
            let either = terms.or(&[b, a]).unwrap();
            let not_a = terms.not(a).unwrap();
            let not_b = terms.not(b).unwrap();
            let mut names = ProofNames::default();
            names.insert_bool(a_symbol, "a".to_owned());
            names.insert_bool(b_symbol, "b".to_owned());
            prove_boolean_unsat(
                ProofLogic::Bool,
                &terms,
                &[either, not_a, not_b],
                &[
                    "(or a b)".to_owned(),
                    "(not a)".to_owned(),
                    "(not b)".to_owned(),
                ],
                &names,
            )
            .unwrap()
        }

        let first = build(false);
        let second = build(true);
        assert_eq!(first.variable_count, second.variable_count);
        assert_eq!(first.clauses, second.clauses);
        assert_eq!(first.drat, second.drat);
    }

    #[test]
    fn canonical_lowering_combines_integer_arithmetic_with_congruence() {
        let mut terms = TermStore::new();
        let x = terms.fresh_term(Sort::Int).unwrap();
        let zero = terms.arithmetic_integer(BigInt::zero()).unwrap();
        let one = terms.arithmetic_integer(BigInt::one()).unwrap();
        let function = terms.declare_function(&[Sort::Int], Sort::Int).unwrap();
        let f_x = terms.apply(function, &[x]).unwrap();
        let f_zero = terms.apply(function, &[zero]).unwrap();
        let x_is_zero = terms.equal(&[x, zero]).unwrap();
        let f_x_is_zero = terms.equal(&[f_x, zero]).unwrap();
        let f_zero_is_one = terms.equal(&[f_zero, one]).unwrap();

        let mut names = ProofNames::default();
        let x_variable = terms
            .arithmetic_variable_for_term(x)
            .unwrap()
            .expect("fresh arithmetic term is a variable");
        names
            .insert_arithmetic(x_variable, Sort::Int, "x".to_owned())
            .unwrap();
        names.insert_function(function, "f".to_owned());

        let proof = prove_boolean_unsat(
            ProofLogic::Lia,
            &terms,
            &[x_is_zero, f_x_is_zero, f_zero_is_one],
            &[
                "(= x 0)".to_owned(),
                "(= (f x) 0)".to_owned(),
                "(= (f 0) 1)".to_owned(),
            ],
            &names,
        )
        .unwrap();

        assert!(proof.drat.ends_with(b"0\n"));
        assert!(
            proof
                .clauses
                .iter()
                .any(|clause| { clause.kind == crate::solver::ProofClauseKind::Theory })
        );
    }

    #[test]
    fn canonical_lowering_supports_integer_array_witnesses() {
        let mut terms = TermStore::new();
        let array_sort = terms.array_sort(Sort::Int, Sort::Int).unwrap();
        let array = terms.fresh_term(Sort::Array(array_sort)).unwrap();
        let index = terms.fresh_term(Sort::Int).unwrap();
        let selected = terms.select(array, index).unwrap();
        let restored = terms.store(array, index, selected).unwrap();
        let equal = terms.equal(&[restored, array]).unwrap();
        let distinct = terms.not(equal).unwrap();

        let mut names = ProofNames::default();
        names.insert_constant(array, "a".to_owned());
        let index_variable = terms
            .arithmetic_variable_for_term(index)
            .unwrap()
            .expect("fresh arithmetic term is a variable");
        names
            .insert_arithmetic(index_variable, Sort::Int, "i".to_owned())
            .unwrap();

        let proof = prove_boolean_unsat(
            ProofLogic::Lia,
            &terms,
            &[distinct],
            &["(distinct (store a i (select a i)) a)".to_owned()],
            &names,
        )
        .unwrap();

        assert!(proof.drat.ends_with(b"0\n"));
        assert!(
            proof
                .clauses
                .iter()
                .any(|clause| { clause.kind == crate::solver::ProofClauseKind::Theory })
        );
    }

    #[test]
    fn cooper_proof_decision_matches_bounded_exhaustive_search() {
        let x = ProofArithmeticVariable::Declared {
            sort: ProofSort::Int,
            name: "x".to_owned(),
        };
        let y = ProofArithmeticVariable::Declared {
            sort: ProofSort::Int,
            name: "y".to_owned(),
        };
        let constraint = |constant: i64, coefficients: Vec<(ProofArithmeticVariable, i64)>| {
            ProofLinearConstraint {
                sort: ProofSort::Int,
                expression: ProofLinearExpression {
                    constant: BigRational::from_integer(BigInt::from(constant)),
                    coefficients: coefficients
                        .into_iter()
                        .filter(|(_, coefficient)| *coefficient != 0)
                        .map(|(variable, coefficient)| {
                            (
                                variable,
                                BigRational::from_integer(BigInt::from(coefficient)),
                            )
                        })
                        .collect(),
                },
                strict: false,
            }
        };
        let bounds = [
            constraint(-2, vec![(x.clone(), 1)]),
            constraint(-2, vec![(x.clone(), -1)]),
            constraint(-2, vec![(y.clone(), 1)]),
            constraint(-2, vec![(y.clone(), -1)]),
        ];
        for left in -3_i64..=3 {
            for right in -3_i64..=3 {
                if left == 0 && right == 0 {
                    continue;
                }
                for target in -6_i64..=6 {
                    let mut constraints = bounds.to_vec();
                    constraints.push(constraint(
                        -target,
                        vec![(x.clone(), left), (y.clone(), right)],
                    ));
                    constraints.push(constraint(
                        target,
                        vec![(x.clone(), -left), (y.clone(), -right)],
                    ));
                    let expected = !(-2_i64..=2).any(|x_value| {
                        (-2_i64..=2).any(|y_value| left * x_value + right * y_value == target)
                    });
                    assert_eq!(
                        integer_linear_constraints_unsat(&constraints).unwrap(),
                        expected,
                        "{left}*x + {right}*y = {target}"
                    );
                }
            }
        }
    }
}
