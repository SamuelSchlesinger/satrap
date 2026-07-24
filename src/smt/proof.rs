use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::error::Error;
use std::fmt;
use std::io::{self, Write};
use std::sync::{Arc, Mutex};

use crate::{Lit, SolveResult, Solver};

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
        }
    }

    fn admits_theory_clauses(self) -> bool {
        matches!(self, Self::Uf | Self::UfBv | Self::Abv | Self::Aufbv)
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
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum ProofSort {
    Bool,
    BitVec(u32),
    Uninterpreted(String),
    Array(Box<ProofSort>, Box<ProofSort>),
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
/// allocation history. Ground UF is reduced to finite class bits plus
/// congruence axioms. A separate checker can therefore reconstruct the entire
/// propositional input from the original SMT-LIB query before validating the
/// DRAT suffix.
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

    let output = SharedBuffer::default();
    let mut solver = Solver::new();
    solver.enable_smt_proof_recording();
    let mut encoder = ProofEncoder::default();
    for root in &roots {
        let literal = encoder.encode(&mut solver, root)?;
        solver
            .try_add_clause(&[literal])
            .map_err(|error| ProofError::new(error.to_string()))?;
    }
    for axiom in &theory_axioms {
        let literal = encoder.encode(&mut solver, axiom)?;
        solver
            .add_theory_clause(&[literal])
            .map_err(|error| ProofError::new(error.to_string()))?;
    }
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

#[derive(Debug)]
struct Canonicalizer {
    converted: HashMap<TermId, BoolExpr>,
    abstract_converted: HashMap<TermId, AbstractExpr>,
    application_converted: HashMap<usize, ProofApplication>,
    application_results: HashMap<TermId, usize>,
    application_bits: HashMap<TermId, (usize, u32)>,
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
                Sort::Int | Sort::Real | Sort::Uninterpreted(_) | Sort::Array(_) => {}
            }
        }
        Ok(Self {
            converted: HashMap::new(),
            abstract_converted: HashMap::new(),
            application_converted: HashMap::new(),
            application_results,
            application_bits,
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
            TermKind::ArithmeticPredicate(_, _, _)
            | TermKind::UfConstant(_)
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
            Sort::Int | Sort::Real => Err(ProofError::new(
                "proof replay encountered an unsupported application sort",
            )),
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
            Sort::Int | Sort::Real => Err(ProofError::new(
                "proof replay encountered an unsupported sort",
            )),
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
            BoolNode::False | BoolNode::True | BoolNode::Atom(_) => expression.clone(),
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
        let mut axioms = BTreeSet::new();
        axioms.extend(self.array_semantics_axioms()?);
        axioms.extend(self.array_extensionality_axioms()?);
        axioms.extend(self.congruence_axioms()?);
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
}
