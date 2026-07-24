use std::collections::{HashMap, HashSet};
use std::error::Error;
use std::fmt;
use std::sync::atomic::{AtomicU64, Ordering};

use crate::{IncrementalError, Interrupter, Lit, Model, SolveLimits, Solver, UnknownReason};

use super::encode::BoolEncoder;
use super::engine::{SmtEngineError, SmtSolveResult, solve as solve_smt};
use super::term::{
    ArraySortId, FunctionId, Sort, TermError, TermId, TermStore, UninterpretedSortId,
};
use super::theory::{TheoryManager, TheoryModel};

static NEXT_CONTEXT_ID: AtomicU64 = AtomicU64::new(1);

/// A Boolean term owned by one [`Context`].
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct BoolTerm {
    context: u64,
    id: TermId,
}

/// A fixed-width bit-vector term owned by one [`Context`].
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct BitVecTerm {
    context: u64,
    id: TermId,
    width: u32,
}

impl BitVecTerm {
    #[must_use]
    pub const fn width(self) -> u32 {
        self.width
    }
}

/// An uninterpreted sort owned by one [`Context`].
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct UninterpretedSort {
    context: u64,
    id: UninterpretedSortId,
}

/// A term whose value belongs to an [`UninterpretedSort`].
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct UninterpretedTerm {
    context: u64,
    id: TermId,
    sort: UninterpretedSort,
}

impl UninterpretedTerm {
    #[must_use]
    pub const fn sort(self) -> UninterpretedSort {
        self.sort
    }
}

/// A structural extensional-array sort owned by one [`Context`].
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct ArraySort {
    context: u64,
    id: ArraySortId,
}

/// An extensional-array term owned by one [`Context`].
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct ArrayTerm {
    context: u64,
    id: TermId,
    sort: ArraySort,
}

impl ArrayTerm {
    #[must_use]
    pub const fn sort(self) -> ArraySort {
        self.sort
    }
}

/// A term sort accepted by the typed context.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum SmtSort {
    Bool,
    BitVec(u32),
    Uninterpreted(UninterpretedSort),
    Array(ArraySort),
}

/// An uninterpreted function declaration owned by one [`Context`].
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Function {
    context: u64,
    id: FunctionId,
}

/// A dynamically sorted term, used for named bindings and generic equality.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum AnyTerm {
    Bool(BoolTerm),
    BitVec(BitVecTerm),
    Uninterpreted(UninterpretedTerm),
    Array(ArrayTerm),
}

impl From<BoolTerm> for AnyTerm {
    fn from(term: BoolTerm) -> Self {
        Self::Bool(term)
    }
}

impl From<BitVecTerm> for AnyTerm {
    fn from(term: BitVecTerm) -> Self {
        Self::BitVec(term)
    }
}

impl From<UninterpretedTerm> for AnyTerm {
    fn from(term: UninterpretedTerm) -> Self {
        Self::Uninterpreted(term)
    }
}

impl From<ArrayTerm> for AnyTerm {
    fn from(term: ArrayTerm) -> Self {
        Self::Array(term)
    }
}

/// A total value in the model selected by the most recent check.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Value {
    Bool(bool),
    BitVec(BitVecValue),
    Uninterpreted(UninterpretedValue),
    Array(ArrayValue),
}

/// A deterministic representative of one model equivalence class.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct UninterpretedValue {
    sort: UninterpretedSort,
    index: u32,
}

/// The equivalence class chosen for an array in the latest model.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct ArrayValue {
    sort: ArraySort,
    index: u32,
}

impl ArrayValue {
    #[must_use]
    pub const fn sort(self) -> ArraySort {
        self.sort
    }

    #[must_use]
    pub const fn index(self) -> u32 {
        self.index
    }
}

impl UninterpretedValue {
    #[must_use]
    pub const fn sort(self) -> UninterpretedSort {
        self.sort
    }

    #[must_use]
    pub const fn index(self) -> u32 {
        self.index
    }
}

/// A fixed-width bit-vector value, stored least-significant bit first.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BitVecValue {
    bits: Vec<bool>,
}

impl BitVecValue {
    #[must_use]
    pub fn width(&self) -> u32 {
        u32::try_from(self.bits.len()).expect("bit-vector values have u32 widths")
    }

    #[must_use]
    pub fn bit(&self, index: u32) -> Option<bool> {
        self.bits.get(index as usize).copied()
    }

    #[must_use]
    pub fn to_binary_literal(&self) -> String {
        let digits = self
            .bits
            .iter()
            .rev()
            .map(|&bit| if bit { '1' } else { '0' })
            .collect::<String>();
        format!("#b{digits}")
    }

    #[must_use]
    pub fn as_u64(&self) -> Option<u64> {
        (self.bits.len() <= u64::BITS as usize).then(|| {
            self.bits
                .iter()
                .enumerate()
                .fold(0, |value, (index, &bit)| value | (u64::from(bit) << index))
        })
    }
}

/// Result of a typed satisfiability query.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CheckResult {
    Sat,
    Unsat,
    Unknown(UnknownReason),
}

/// A checked error from the typed SMT context.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ContextError {
    ForeignTerm,
    DuplicateName(String),
    DuplicateLabel(String),
    ScopeUnderflow,
    NoModel,
    NoUnsatResult,
    Term(TermError),
    Incremental(IncrementalError),
}

impl fmt::Display for ContextError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ForeignTerm => formatter.write_str("term belongs to a different SMT context"),
            Self::DuplicateName(name) => write!(formatter, "name `{name}` is already defined"),
            Self::DuplicateLabel(name) => {
                write!(formatter, "assertion label `{name}` is already active")
            }
            Self::ScopeUnderflow => formatter.write_str("cannot pop beyond the base scope"),
            Self::NoModel => {
                formatter.write_str("model inspection requires a preceding sat or unknown result")
            }
            Self::NoUnsatResult => {
                formatter.write_str("unsat information requires a preceding unsat result")
            }
            Self::Term(error) => error.fmt(formatter),
            Self::Incremental(error) => error.fmt(formatter),
        }
    }
}

impl Error for ContextError {}

impl From<TermError> for ContextError {
    fn from(error: TermError) -> Self {
        Self::Term(error)
    }
}

impl From<IncrementalError> for ContextError {
    fn from(error: IncrementalError) -> Self {
        Self::Incremental(error)
    }
}

impl From<SmtEngineError> for ContextError {
    fn from(error: SmtEngineError) -> Self {
        match error {
            SmtEngineError::Term(error) => Self::Term(error),
            SmtEngineError::Incremental(error) => Self::Incremental(error),
        }
    }
}

#[derive(Clone, Debug)]
struct NamedAssertion {
    name: String,
    term: BoolTerm,
    selector: Lit,
}

#[derive(Debug, Default)]
struct Frame {
    named_assertions: Vec<NamedAssertion>,
    assertions: Vec<TermId>,
}

#[derive(Clone, Debug)]
enum LastCheck {
    None,
    Sat {
        boolean: Model,
        theory: TheoryModel,
    },
    Unsat {
        core: Vec<String>,
        assumptions: Vec<BoolTerm>,
    },
    Unknown {
        reason: UnknownReason,
        boolean: Model,
        theory: TheoryModel,
    },
}

/// A persistent typed SMT context for Core and QF_BV.
///
/// Declarations and definitions are global, as in an SMT-LIB session with
/// `:global-declarations true`; `push` and `pop` scope assertions. A full
/// [`Context::reset`] invalidates all previously returned term handles.
#[derive(Debug)]
pub struct Context {
    id: u64,
    terms: TermStore,
    solver: Solver,
    encoder: BoolEncoder,
    theories: TheoryManager,
    bindings: HashMap<String, AnyTerm>,
    sort_bindings: HashMap<String, UninterpretedSort>,
    function_bindings: HashMap<String, Function>,
    declarations: Vec<(String, AnyTerm)>,
    active_labels: HashSet<String>,
    frames: Vec<Frame>,
    last_check: LastCheck,
}

impl Default for Context {
    fn default() -> Self {
        Self::new()
    }
}

impl Context {
    #[must_use]
    pub fn new() -> Self {
        Self {
            id: NEXT_CONTEXT_ID.fetch_add(1, Ordering::Relaxed),
            terms: TermStore::new(),
            solver: Solver::new(),
            encoder: BoolEncoder::default(),
            theories: TheoryManager::default(),
            bindings: HashMap::new(),
            sort_bindings: HashMap::new(),
            function_bindings: HashMap::new(),
            declarations: Vec::new(),
            active_labels: HashSet::new(),
            frames: vec![Frame::default()],
            last_check: LastCheck::None,
        }
    }

    #[must_use]
    pub fn interrupter(&self) -> Interrupter {
        self.solver.interrupter()
    }

    pub fn declare_bool(&mut self, name: impl Into<String>) -> Result<BoolTerm, ContextError> {
        let name = name.into();
        self.ensure_fresh_name(&name)?;
        let id = self.terms.fresh_term(Sort::Bool)?;
        let term = self.wrap_bool(id)?;
        self.bindings.insert(name.clone(), term.into());
        self.declarations.push((name, term.into()));
        self.invalidate_check();
        Ok(term)
    }

    pub fn declare_bitvec(
        &mut self,
        name: impl Into<String>,
        width: u32,
    ) -> Result<BitVecTerm, ContextError> {
        let name = name.into();
        self.ensure_fresh_name(&name)?;
        let id = self.terms.fresh_term(Sort::BitVec(width))?;
        let term = self.wrap_bitvec(id)?;
        self.bindings.insert(name.clone(), term.into());
        self.declarations.push((name, term.into()));
        self.invalidate_check();
        Ok(term)
    }

    pub fn declare_uninterpreted_sort(
        &mut self,
        name: impl Into<String>,
    ) -> Result<UninterpretedSort, ContextError> {
        let name = name.into();
        if self.sort_bindings.contains_key(&name) {
            return Err(ContextError::DuplicateName(name));
        }
        let sort = UninterpretedSort {
            context: self.id,
            id: self.terms.fresh_uninterpreted_sort()?,
        };
        self.sort_bindings.insert(name, sort);
        self.invalidate_check();
        Ok(sort)
    }

    pub fn declare_uninterpreted(
        &mut self,
        name: impl Into<String>,
        sort: UninterpretedSort,
    ) -> Result<UninterpretedTerm, ContextError> {
        let name = name.into();
        self.ensure_fresh_name(&name)?;
        let sort = self.internal_sort(SmtSort::Uninterpreted(sort))?;
        let id = self.terms.fresh_term(sort)?;
        let term = self.wrap_uninterpreted(id)?;
        self.bindings.insert(name.clone(), term.into());
        self.declarations.push((name, term.into()));
        self.invalidate_check();
        Ok(term)
    }

    pub fn array_sort(
        &mut self,
        index: SmtSort,
        element: SmtSort,
    ) -> Result<ArraySort, ContextError> {
        let index = self.internal_sort(index)?;
        let element = self.internal_sort(element)?;
        Ok(ArraySort {
            context: self.id,
            id: self.terms.array_sort(index, element)?,
        })
    }

    pub fn declare_array(
        &mut self,
        name: impl Into<String>,
        sort: ArraySort,
    ) -> Result<ArrayTerm, ContextError> {
        let name = name.into();
        self.ensure_fresh_name(&name)?;
        let sort = self.internal_sort(SmtSort::Array(sort))?;
        let id = self.terms.fresh_term(sort)?;
        let term = self.wrap_array(id)?;
        self.bindings.insert(name.clone(), term.into());
        self.declarations.push((name, term.into()));
        self.invalidate_check();
        Ok(term)
    }

    pub fn declare_function(
        &mut self,
        name: impl Into<String>,
        domain: &[SmtSort],
        range: SmtSort,
    ) -> Result<Function, ContextError> {
        let name = name.into();
        self.ensure_fresh_name(&name)?;
        let domain = domain
            .iter()
            .map(|&sort| self.internal_sort(sort))
            .collect::<Result<Vec<_>, _>>()?;
        let range = self.internal_sort(range)?;
        let function = Function {
            context: self.id,
            id: self.terms.declare_function(&domain, range)?,
        };
        self.function_bindings.insert(name, function);
        self.invalidate_check();
        Ok(function)
    }

    pub fn apply(
        &mut self,
        function: Function,
        arguments: &[AnyTerm],
    ) -> Result<AnyTerm, ContextError> {
        if function.context != self.id {
            return Err(ContextError::ForeignTerm);
        }
        self.terms.function_signature(function.id)?;
        let arguments = arguments
            .iter()
            .map(|&term| self.any_id(term))
            .collect::<Result<Vec<_>, _>>()?;
        let result = self.terms.apply(function.id, &arguments)?;
        self.invalidate_check();
        self.wrap_any(result)
    }

    pub fn define(
        &mut self,
        name: impl Into<String>,
        term: impl Into<AnyTerm>,
    ) -> Result<(), ContextError> {
        let name = name.into();
        self.ensure_fresh_name(&name)?;
        let term = term.into();
        self.any_id(term)?;
        self.bindings.insert(name, term);
        self.invalidate_check();
        Ok(())
    }

    #[must_use]
    pub fn lookup(&self, name: &str) -> Option<AnyTerm> {
        self.bindings.get(name).copied()
    }

    #[must_use]
    pub fn lookup_sort(&self, name: &str) -> Option<UninterpretedSort> {
        self.sort_bindings.get(name).copied()
    }

    #[must_use]
    pub fn lookup_function(&self, name: &str) -> Option<Function> {
        self.function_bindings.get(name).copied()
    }

    pub fn assert(&mut self, term: BoolTerm) -> Result<(), ContextError> {
        let id = self.bool_id(term)?;
        let literal = self.encoder.encode(&self.terms, &mut self.solver, id)?;
        self.solver.try_add_clause(&[literal])?;
        self.frames
            .last_mut()
            .expect("base frame exists")
            .assertions
            .push(id);
        self.invalidate_check();
        Ok(())
    }

    pub fn assert_named(
        &mut self,
        name: impl Into<String>,
        term: BoolTerm,
    ) -> Result<(), ContextError> {
        let name = name.into();
        let id = self.bool_id(term)?;
        if !self.active_labels.insert(name.clone()) {
            return Err(ContextError::DuplicateLabel(name));
        }
        let literal = match self.encoder.encode(&self.terms, &mut self.solver, id) {
            Ok(literal) => literal,
            Err(error) => {
                self.active_labels.remove(&name);
                return Err(error.into());
            }
        };
        let selector = match self.solver.new_variable() {
            Ok(variable) => Lit::positive(variable),
            Err(error) => {
                self.active_labels.remove(&name);
                return Err(error.into());
            }
        };
        if let Err(error) = self.solver.try_add_clause(&[!selector, literal]) {
            self.active_labels.remove(&name);
            return Err(error.into());
        }
        self.frames
            .last_mut()
            .expect("base frame exists")
            .named_assertions
            .push(NamedAssertion {
                name,
                term,
                selector,
            });
        self.frames
            .last_mut()
            .expect("base frame exists")
            .assertions
            .push(id);
        self.invalidate_check();
        Ok(())
    }

    pub fn push(&mut self, levels: usize) -> Result<(), ContextError> {
        for _ in 0..levels {
            self.solver.push()?;
            self.frames.push(Frame::default());
        }
        self.invalidate_check();
        Ok(())
    }

    pub fn pop(&mut self, levels: usize) -> Result<(), ContextError> {
        if levels >= self.frames.len() {
            return Err(ContextError::ScopeUnderflow);
        }
        self.solver.pop(levels)?;
        for _ in 0..levels {
            let frame = self.frames.pop().expect("scope count checked above");
            for assertion in frame.named_assertions {
                self.active_labels.remove(&assertion.name);
            }
        }
        self.invalidate_check();
        Ok(())
    }

    pub fn reset_assertions(&mut self) {
        self.solver = Solver::new();
        self.encoder = BoolEncoder::default();
        self.active_labels.clear();
        self.frames.clear();
        self.frames.push(Frame::default());
        self.invalidate_check();
    }

    pub fn reset(&mut self) {
        *self = Self::new();
    }

    pub fn check(&mut self) -> Result<CheckResult, ContextError> {
        self.check_assuming_with_limits(&[], SolveLimits::default())
    }

    pub fn check_with_limits(&mut self, limits: SolveLimits) -> Result<CheckResult, ContextError> {
        self.check_assuming_with_limits(&[], limits)
    }

    pub fn check_assuming(
        &mut self,
        assumptions: &[BoolTerm],
    ) -> Result<CheckResult, ContextError> {
        self.check_assuming_with_limits(assumptions, SolveLimits::default())
    }

    pub fn check_assuming_with_limits(
        &mut self,
        user_assumptions: &[BoolTerm],
        limits: SolveLimits,
    ) -> Result<CheckResult, ContextError> {
        let named = self
            .frames
            .iter()
            .flat_map(|frame| frame.named_assertions.iter())
            .cloned()
            .collect::<Vec<_>>();
        let mut literals = named
            .iter()
            .map(|assertion| assertion.selector)
            .collect::<Vec<_>>();
        let mut roots = self
            .frames
            .iter()
            .flat_map(|frame| frame.assertions.iter().copied())
            .collect::<Vec<_>>();
        let mut encoded_users = Vec::with_capacity(user_assumptions.len());
        for &term in user_assumptions {
            let id = self.bool_id(term)?;
            let literal = self.encoder.encode(&self.terms, &mut self.solver, id)?;
            literals.push(literal);
            roots.push(id);
            encoded_users.push((term, literal));
        }
        let result = solve_smt(
            &mut self.terms,
            &mut self.solver,
            &mut self.encoder,
            &mut self.theories,
            &roots,
            &literals,
            limits,
        )?;
        Ok(match result {
            SmtSolveResult::Sat { boolean, theory } => {
                self.last_check = LastCheck::Sat { boolean, theory };
                CheckResult::Sat
            }
            SmtSolveResult::Unsat => {
                let failed = self.solver.failed_assumptions();
                let core = named
                    .iter()
                    .filter(|assertion| failed.contains(&assertion.selector))
                    .map(|assertion| assertion.name.clone())
                    .collect();
                let assumptions = encoded_users
                    .iter()
                    .filter(|(_, literal)| failed.contains(literal))
                    .map(|(term, _)| *term)
                    .collect();
                self.last_check = LastCheck::Unsat { core, assumptions };
                CheckResult::Unsat
            }
            SmtSolveResult::Unknown(reason) => {
                self.last_check = LastCheck::Unknown {
                    reason,
                    boolean: Model::arbitrary(self.solver.variable_count()),
                    theory: TheoryModel::default(),
                };
                CheckResult::Unknown(reason)
            }
        })
    }

    pub fn value(&self, term: impl Into<AnyTerm>) -> Result<Value, ContextError> {
        let model = self.model_ref()?;
        match term.into() {
            AnyTerm::Bool(term) => Ok(Value::Bool(self.evaluate_bool(model, term)?)),
            AnyTerm::BitVec(term) => {
                self.bitvec_id(term)?;
                let bits = self
                    .terms
                    .evaluate_bitvec(term.id, |symbol| self.symbol_value(model, symbol))?;
                Ok(Value::BitVec(BitVecValue { bits }))
            }
            AnyTerm::Uninterpreted(term) => {
                let id = self.uninterpreted_id(term)?;
                let theory = self.theory_model_ref()?;
                Ok(Value::Uninterpreted(UninterpretedValue {
                    sort: term.sort,
                    index: theory.value(id).unwrap_or(0),
                }))
            }
            AnyTerm::Array(term) => {
                let id = self.array_id(term)?;
                let theory = self.theory_model_ref()?;
                Ok(Value::Array(ArrayValue {
                    sort: term.sort,
                    index: theory.value(id).unwrap_or(0),
                }))
            }
        }
    }

    pub fn model(&self) -> Result<Vec<(String, Value)>, ContextError> {
        self.declarations
            .iter()
            .map(|(name, term)| Ok((name.clone(), self.value(*term)?)))
            .collect()
    }

    pub fn assignment(&self) -> Result<Vec<(String, bool)>, ContextError> {
        let model = self.model_ref()?;
        self.frames
            .iter()
            .flat_map(|frame| frame.named_assertions.iter())
            .map(|assertion| {
                Ok((
                    assertion.name.clone(),
                    self.evaluate_bool(model, assertion.term)?,
                ))
            })
            .collect()
    }

    pub fn unsat_core(&self) -> Result<&[String], ContextError> {
        match &self.last_check {
            LastCheck::Unsat { core, .. } => Ok(core),
            _ => Err(ContextError::NoUnsatResult),
        }
    }

    pub fn unsat_assumptions(&self) -> Result<&[BoolTerm], ContextError> {
        match &self.last_check {
            LastCheck::Unsat { assumptions, .. } => Ok(assumptions),
            _ => Err(ContextError::NoUnsatResult),
        }
    }

    #[must_use]
    pub fn last_unknown_reason(&self) -> Option<UnknownReason> {
        match self.last_check {
            LastCheck::Unknown { reason, .. } => Some(reason),
            _ => None,
        }
    }

    #[must_use]
    pub fn bool_value(&self, value: bool) -> BoolTerm {
        BoolTerm {
            context: self.id,
            id: self.terms.bool_constant(value),
        }
    }

    pub fn bool_not(&mut self, term: BoolTerm) -> Result<BoolTerm, ContextError> {
        let id = self.bool_id(term)?;
        let result = self.terms.not(id)?;
        self.wrap_bool(result)
    }

    pub fn bool_and(&mut self, terms: &[BoolTerm]) -> Result<BoolTerm, ContextError> {
        let ids = self.bool_ids(terms)?;
        let result = self.terms.and(&ids)?;
        self.wrap_bool(result)
    }

    pub fn bool_or(&mut self, terms: &[BoolTerm]) -> Result<BoolTerm, ContextError> {
        let ids = self.bool_ids(terms)?;
        let result = self.terms.or(&ids)?;
        self.wrap_bool(result)
    }

    pub fn bool_xor(&mut self, terms: &[BoolTerm]) -> Result<BoolTerm, ContextError> {
        if terms.len() < 2 {
            return Err(TermError::new("Boolean xor expects at least two arguments").into());
        }
        let ids = self.bool_ids(terms)?;
        let mut result = ids[0];
        for &term in &ids[1..] {
            result = self.terms.xor(result, term)?;
        }
        self.wrap_bool(result)
    }

    pub fn implies(&mut self, terms: &[BoolTerm]) -> Result<BoolTerm, ContextError> {
        let ids = self.bool_ids(terms)?;
        let result = self.terms.implies(&ids)?;
        self.wrap_bool(result)
    }

    pub fn equal(&mut self, terms: &[AnyTerm]) -> Result<BoolTerm, ContextError> {
        let ids = terms
            .iter()
            .map(|&term| self.any_id(term))
            .collect::<Result<Vec<_>, _>>()?;
        let result = self.terms.equal(&ids)?;
        self.wrap_bool(result)
    }

    pub fn distinct(&mut self, terms: &[AnyTerm]) -> Result<BoolTerm, ContextError> {
        let ids = terms
            .iter()
            .map(|&term| self.any_id(term))
            .collect::<Result<Vec<_>, _>>()?;
        let result = self.terms.distinct(&ids)?;
        self.wrap_bool(result)
    }

    pub fn bool_ite(
        &mut self,
        condition: BoolTerm,
        then_term: BoolTerm,
        else_term: BoolTerm,
    ) -> Result<BoolTerm, ContextError> {
        let condition = self.bool_id(condition)?;
        let then_term = self.bool_id(then_term)?;
        let else_term = self.bool_id(else_term)?;
        let result = self.terms.ite(condition, then_term, else_term)?;
        self.wrap_bool(result)
    }

    pub fn uninterpreted_ite(
        &mut self,
        condition: BoolTerm,
        then_term: UninterpretedTerm,
        else_term: UninterpretedTerm,
    ) -> Result<UninterpretedTerm, ContextError> {
        let condition = self.bool_id(condition)?;
        let then_term = self.uninterpreted_id(then_term)?;
        let else_term = self.uninterpreted_id(else_term)?;
        let result = self.terms.ite(condition, then_term, else_term)?;
        self.wrap_uninterpreted(result)
    }

    pub fn const_array(
        &mut self,
        sort: ArraySort,
        value: AnyTerm,
    ) -> Result<ArrayTerm, ContextError> {
        let Sort::Array(sort_id) = self.internal_sort(SmtSort::Array(sort))? else {
            unreachable!("array handle always maps to an array sort");
        };
        let value = self.any_id(value)?;
        let result = self.terms.const_array(sort_id, value)?;
        self.wrap_array(result)
    }

    pub fn select(&mut self, array: ArrayTerm, index: AnyTerm) -> Result<AnyTerm, ContextError> {
        let array = self.array_id(array)?;
        let index = self.any_id(index)?;
        let result = self.terms.select(array, index)?;
        self.wrap_any(result)
    }

    pub fn store(
        &mut self,
        array: ArrayTerm,
        index: AnyTerm,
        value: AnyTerm,
    ) -> Result<ArrayTerm, ContextError> {
        let array = self.array_id(array)?;
        let index = self.any_id(index)?;
        let value = self.any_id(value)?;
        let result = self.terms.store(array, index, value)?;
        self.wrap_array(result)
    }

    pub fn array_ite(
        &mut self,
        condition: BoolTerm,
        then_term: ArrayTerm,
        else_term: ArrayTerm,
    ) -> Result<ArrayTerm, ContextError> {
        let condition = self.bool_id(condition)?;
        let then_term = self.array_id(then_term)?;
        let else_term = self.array_id(else_term)?;
        let result = self.terms.ite(condition, then_term, else_term)?;
        self.wrap_array(result)
    }

    pub fn bitvec_binary(&mut self, literal: &str) -> Result<BitVecTerm, ContextError> {
        let result = self.terms.bitvec_from_binary(literal)?;
        self.wrap_bitvec(result)
    }

    pub fn bitvec_hexadecimal(&mut self, literal: &str) -> Result<BitVecTerm, ContextError> {
        let result = self.terms.bitvec_from_hexadecimal(literal)?;
        self.wrap_bitvec(result)
    }

    pub fn bitvec_decimal(
        &mut self,
        decimal: &str,
        width: u32,
    ) -> Result<BitVecTerm, ContextError> {
        let result = self.terms.bitvec_from_decimal(decimal, width)?;
        self.wrap_bitvec(result)
    }

    pub fn bitvec_u64(&mut self, value: u64, width: u32) -> Result<BitVecTerm, ContextError> {
        self.bitvec_decimal(&value.to_string(), width)
    }

    pub fn bv_not(&mut self, term: BitVecTerm) -> Result<BitVecTerm, ContextError> {
        let id = self.bitvec_id(term)?;
        let result = self.terms.bvnot(id)?;
        self.wrap_bitvec(result)
    }

    pub fn bv_neg(&mut self, term: BitVecTerm) -> Result<BitVecTerm, ContextError> {
        let id = self.bitvec_id(term)?;
        let result = self.terms.bvneg(id)?;
        self.wrap_bitvec(result)
    }

    pub fn bv_and(&mut self, terms: &[BitVecTerm]) -> Result<BitVecTerm, ContextError> {
        self.bv_nary(terms, |store, ids| store.bvand(ids))
    }

    pub fn bv_or(&mut self, terms: &[BitVecTerm]) -> Result<BitVecTerm, ContextError> {
        self.bv_nary(terms, |store, ids| store.bvor(ids))
    }

    pub fn bv_xor(&mut self, terms: &[BitVecTerm]) -> Result<BitVecTerm, ContextError> {
        self.bv_nary(terms, |store, ids| store.bvxor(ids))
    }

    pub fn bv_add(&mut self, terms: &[BitVecTerm]) -> Result<BitVecTerm, ContextError> {
        self.bv_nary(terms, |store, ids| store.bvadd(ids))
    }

    pub fn bv_mul(&mut self, terms: &[BitVecTerm]) -> Result<BitVecTerm, ContextError> {
        self.bv_nary(terms, |store, ids| store.bvmul(ids))
    }

    pub fn bv_nand(
        &mut self,
        left: BitVecTerm,
        right: BitVecTerm,
    ) -> Result<BitVecTerm, ContextError> {
        self.bv_binary(left, right, |store, a, b| store.bvnand(a, b))
    }

    pub fn bv_nor(
        &mut self,
        left: BitVecTerm,
        right: BitVecTerm,
    ) -> Result<BitVecTerm, ContextError> {
        self.bv_binary(left, right, |store, a, b| store.bvnor(a, b))
    }

    pub fn bv_xnor(
        &mut self,
        left: BitVecTerm,
        right: BitVecTerm,
    ) -> Result<BitVecTerm, ContextError> {
        self.bv_binary(left, right, |store, a, b| store.bvxnor(a, b))
    }

    pub fn bv_comp(
        &mut self,
        left: BitVecTerm,
        right: BitVecTerm,
    ) -> Result<BitVecTerm, ContextError> {
        self.bv_binary(left, right, |store, a, b| store.bvcomp(a, b))
    }

    pub fn bv_sub(
        &mut self,
        left: BitVecTerm,
        right: BitVecTerm,
    ) -> Result<BitVecTerm, ContextError> {
        self.bv_binary(left, right, |store, a, b| store.bvsub(a, b))
    }

    pub fn bv_udiv(
        &mut self,
        left: BitVecTerm,
        right: BitVecTerm,
    ) -> Result<BitVecTerm, ContextError> {
        self.bv_binary(left, right, |store, a, b| store.bvudiv(a, b))
    }

    pub fn bv_urem(
        &mut self,
        left: BitVecTerm,
        right: BitVecTerm,
    ) -> Result<BitVecTerm, ContextError> {
        self.bv_binary(left, right, |store, a, b| store.bvurem(a, b))
    }

    pub fn bv_sdiv(
        &mut self,
        left: BitVecTerm,
        right: BitVecTerm,
    ) -> Result<BitVecTerm, ContextError> {
        self.bv_binary(left, right, |store, a, b| store.bvsdiv(a, b))
    }

    pub fn bv_srem(
        &mut self,
        left: BitVecTerm,
        right: BitVecTerm,
    ) -> Result<BitVecTerm, ContextError> {
        self.bv_binary(left, right, |store, a, b| store.bvsrem(a, b))
    }

    pub fn bv_smod(
        &mut self,
        left: BitVecTerm,
        right: BitVecTerm,
    ) -> Result<BitVecTerm, ContextError> {
        self.bv_binary(left, right, |store, a, b| store.bvsmod(a, b))
    }

    pub fn bv_shl(
        &mut self,
        value: BitVecTerm,
        amount: BitVecTerm,
    ) -> Result<BitVecTerm, ContextError> {
        self.bv_binary(value, amount, |store, a, b| store.bvshl(a, b))
    }

    pub fn bv_lshr(
        &mut self,
        value: BitVecTerm,
        amount: BitVecTerm,
    ) -> Result<BitVecTerm, ContextError> {
        self.bv_binary(value, amount, |store, a, b| store.bvlshr(a, b))
    }

    pub fn bv_ashr(
        &mut self,
        value: BitVecTerm,
        amount: BitVecTerm,
    ) -> Result<BitVecTerm, ContextError> {
        self.bv_binary(value, amount, |store, a, b| store.bvashr(a, b))
    }

    pub fn concat(
        &mut self,
        left: BitVecTerm,
        right: BitVecTerm,
    ) -> Result<BitVecTerm, ContextError> {
        self.bv_binary(left, right, |store, a, b| store.concat(a, b))
    }

    pub fn extract(
        &mut self,
        term: BitVecTerm,
        high: u32,
        low: u32,
    ) -> Result<BitVecTerm, ContextError> {
        let id = self.bitvec_id(term)?;
        let result = self.terms.extract(id, high, low)?;
        self.wrap_bitvec(result)
    }

    pub fn repeat(&mut self, term: BitVecTerm, count: u32) -> Result<BitVecTerm, ContextError> {
        let id = self.bitvec_id(term)?;
        let result = self.terms.repeat(id, count)?;
        self.wrap_bitvec(result)
    }

    pub fn zero_extend(
        &mut self,
        term: BitVecTerm,
        amount: u32,
    ) -> Result<BitVecTerm, ContextError> {
        let id = self.bitvec_id(term)?;
        let result = self.terms.zero_extend(id, amount)?;
        self.wrap_bitvec(result)
    }

    pub fn sign_extend(
        &mut self,
        term: BitVecTerm,
        amount: u32,
    ) -> Result<BitVecTerm, ContextError> {
        let id = self.bitvec_id(term)?;
        let result = self.terms.sign_extend(id, amount)?;
        self.wrap_bitvec(result)
    }

    pub fn rotate_left(
        &mut self,
        term: BitVecTerm,
        amount: u32,
    ) -> Result<BitVecTerm, ContextError> {
        let id = self.bitvec_id(term)?;
        let result = self.terms.rotate_left(id, amount)?;
        self.wrap_bitvec(result)
    }

    pub fn rotate_right(
        &mut self,
        term: BitVecTerm,
        amount: u32,
    ) -> Result<BitVecTerm, ContextError> {
        let id = self.bitvec_id(term)?;
        let result = self.terms.rotate_right(id, amount)?;
        self.wrap_bitvec(result)
    }

    pub fn bitvec_ite(
        &mut self,
        condition: BoolTerm,
        then_term: BitVecTerm,
        else_term: BitVecTerm,
    ) -> Result<BitVecTerm, ContextError> {
        let condition = self.bool_id(condition)?;
        let then_term = self.bitvec_id(then_term)?;
        let else_term = self.bitvec_id(else_term)?;
        let result = self.terms.ite(condition, then_term, else_term)?;
        self.wrap_bitvec(result)
    }

    pub fn bv_ult(
        &mut self,
        left: BitVecTerm,
        right: BitVecTerm,
    ) -> Result<BoolTerm, ContextError> {
        self.bv_predicate(left, right, |store, a, b| store.bvult(a, b))
    }

    pub fn bv_ule(
        &mut self,
        left: BitVecTerm,
        right: BitVecTerm,
    ) -> Result<BoolTerm, ContextError> {
        self.bv_predicate(left, right, |store, a, b| store.bvule(a, b))
    }

    pub fn bv_ugt(
        &mut self,
        left: BitVecTerm,
        right: BitVecTerm,
    ) -> Result<BoolTerm, ContextError> {
        self.bv_predicate(left, right, |store, a, b| store.bvugt(a, b))
    }

    pub fn bv_uge(
        &mut self,
        left: BitVecTerm,
        right: BitVecTerm,
    ) -> Result<BoolTerm, ContextError> {
        self.bv_predicate(left, right, |store, a, b| store.bvuge(a, b))
    }

    pub fn bv_slt(
        &mut self,
        left: BitVecTerm,
        right: BitVecTerm,
    ) -> Result<BoolTerm, ContextError> {
        self.bv_predicate(left, right, |store, a, b| store.bvslt(a, b))
    }

    pub fn bv_sle(
        &mut self,
        left: BitVecTerm,
        right: BitVecTerm,
    ) -> Result<BoolTerm, ContextError> {
        self.bv_predicate(left, right, |store, a, b| store.bvsle(a, b))
    }

    pub fn bv_sgt(
        &mut self,
        left: BitVecTerm,
        right: BitVecTerm,
    ) -> Result<BoolTerm, ContextError> {
        self.bv_predicate(left, right, |store, a, b| store.bvsgt(a, b))
    }

    pub fn bv_sge(
        &mut self,
        left: BitVecTerm,
        right: BitVecTerm,
    ) -> Result<BoolTerm, ContextError> {
        self.bv_predicate(left, right, |store, a, b| store.bvsge(a, b))
    }

    pub fn bv_neg_overflow(&mut self, term: BitVecTerm) -> Result<BoolTerm, ContextError> {
        let id = self.bitvec_id(term)?;
        let result = self.terms.bvnego(id)?;
        self.wrap_bool(result)
    }

    pub fn bv_uadd_overflow(
        &mut self,
        left: BitVecTerm,
        right: BitVecTerm,
    ) -> Result<BoolTerm, ContextError> {
        self.bv_predicate(left, right, |store, a, b| store.bvuaddo(a, b))
    }

    pub fn bv_sadd_overflow(
        &mut self,
        left: BitVecTerm,
        right: BitVecTerm,
    ) -> Result<BoolTerm, ContextError> {
        self.bv_predicate(left, right, |store, a, b| store.bvsaddo(a, b))
    }

    pub fn bv_umul_overflow(
        &mut self,
        left: BitVecTerm,
        right: BitVecTerm,
    ) -> Result<BoolTerm, ContextError> {
        self.bv_predicate(left, right, |store, a, b| store.bvumulo(a, b))
    }

    pub fn bv_smul_overflow(
        &mut self,
        left: BitVecTerm,
        right: BitVecTerm,
    ) -> Result<BoolTerm, ContextError> {
        self.bv_predicate(left, right, |store, a, b| store.bvsmulo(a, b))
    }

    pub fn bv_usub_overflow(
        &mut self,
        left: BitVecTerm,
        right: BitVecTerm,
    ) -> Result<BoolTerm, ContextError> {
        self.bv_predicate(left, right, |store, a, b| store.bvusubo(a, b))
    }

    pub fn bv_ssub_overflow(
        &mut self,
        left: BitVecTerm,
        right: BitVecTerm,
    ) -> Result<BoolTerm, ContextError> {
        self.bv_predicate(left, right, |store, a, b| store.bvssubo(a, b))
    }

    pub fn bv_sdiv_overflow(
        &mut self,
        left: BitVecTerm,
        right: BitVecTerm,
    ) -> Result<BoolTerm, ContextError> {
        self.bv_predicate(left, right, |store, a, b| store.bvsdivo(a, b))
    }

    fn bool_ids(&self, terms: &[BoolTerm]) -> Result<Vec<TermId>, ContextError> {
        terms.iter().map(|&term| self.bool_id(term)).collect()
    }

    fn bool_id(&self, term: BoolTerm) -> Result<TermId, ContextError> {
        if term.context != self.id {
            return Err(ContextError::ForeignTerm);
        }
        self.terms.require_bool(term.id)?;
        Ok(term.id)
    }

    fn bitvec_id(&self, term: BitVecTerm) -> Result<TermId, ContextError> {
        if term.context != self.id {
            return Err(ContextError::ForeignTerm);
        }
        if self.terms.bitvec_width(term.id)? != term.width {
            return Err(ContextError::ForeignTerm);
        }
        Ok(term.id)
    }

    fn any_id(&self, term: AnyTerm) -> Result<TermId, ContextError> {
        match term {
            AnyTerm::Bool(term) => self.bool_id(term),
            AnyTerm::BitVec(term) => self.bitvec_id(term),
            AnyTerm::Uninterpreted(term) => self.uninterpreted_id(term),
            AnyTerm::Array(term) => self.array_id(term),
        }
    }

    fn uninterpreted_id(&self, term: UninterpretedTerm) -> Result<TermId, ContextError> {
        if term.context != self.id || term.sort.context != self.id {
            return Err(ContextError::ForeignTerm);
        }
        if self.terms.sort(term.id)? != Sort::Uninterpreted(term.sort.id) {
            return Err(ContextError::ForeignTerm);
        }
        Ok(term.id)
    }

    fn array_id(&self, term: ArrayTerm) -> Result<TermId, ContextError> {
        if term.context != self.id || term.sort.context != self.id {
            return Err(ContextError::ForeignTerm);
        }
        if self.terms.sort(term.id)? != Sort::Array(term.sort.id) {
            return Err(ContextError::ForeignTerm);
        }
        Ok(term.id)
    }

    fn wrap_bool(&self, id: TermId) -> Result<BoolTerm, ContextError> {
        self.terms.require_bool(id)?;
        Ok(BoolTerm {
            context: self.id,
            id,
        })
    }

    fn wrap_bitvec(&self, id: TermId) -> Result<BitVecTerm, ContextError> {
        let width = self.terms.bitvec_width(id)?;
        Ok(BitVecTerm {
            context: self.id,
            id,
            width,
        })
    }

    fn wrap_uninterpreted(&self, id: TermId) -> Result<UninterpretedTerm, ContextError> {
        let Sort::Uninterpreted(sort) = self.terms.sort(id)? else {
            return Err(TermError::new("expected an uninterpreted term").into());
        };
        Ok(UninterpretedTerm {
            context: self.id,
            id,
            sort: UninterpretedSort {
                context: self.id,
                id: sort,
            },
        })
    }

    fn wrap_array(&self, id: TermId) -> Result<ArrayTerm, ContextError> {
        let Sort::Array(sort) = self.terms.sort(id)? else {
            return Err(TermError::new("expected an array term").into());
        };
        Ok(ArrayTerm {
            context: self.id,
            id,
            sort: ArraySort {
                context: self.id,
                id: sort,
            },
        })
    }

    fn wrap_any(&self, id: TermId) -> Result<AnyTerm, ContextError> {
        match self.terms.sort(id)? {
            Sort::Bool => self.wrap_bool(id).map(AnyTerm::Bool),
            Sort::BitVec(_) => self.wrap_bitvec(id).map(AnyTerm::BitVec),
            Sort::Int | Sort::Real => {
                Err(TermError::new("typed arithmetic terms are not exposed yet").into())
            }
            Sort::Uninterpreted(_) => self.wrap_uninterpreted(id).map(AnyTerm::Uninterpreted),
            Sort::Array(_) => self.wrap_array(id).map(AnyTerm::Array),
        }
    }

    fn internal_sort(&self, sort: SmtSort) -> Result<Sort, ContextError> {
        match sort {
            SmtSort::Bool => Ok(Sort::Bool),
            SmtSort::BitVec(width) => Ok(Sort::BitVec(width)),
            SmtSort::Uninterpreted(sort) if sort.context == self.id => {
                Ok(Sort::Uninterpreted(sort.id))
            }
            SmtSort::Uninterpreted(_) => Err(ContextError::ForeignTerm),
            SmtSort::Array(sort) if sort.context == self.id => Ok(Sort::Array(sort.id)),
            SmtSort::Array(_) => Err(ContextError::ForeignTerm),
        }
    }

    fn bv_nary(
        &mut self,
        terms: &[BitVecTerm],
        operation: impl FnOnce(&mut TermStore, &[TermId]) -> Result<TermId, TermError>,
    ) -> Result<BitVecTerm, ContextError> {
        let ids = terms
            .iter()
            .map(|&term| self.bitvec_id(term))
            .collect::<Result<Vec<_>, _>>()?;
        let result = operation(&mut self.terms, &ids)?;
        self.wrap_bitvec(result)
    }

    fn bv_binary(
        &mut self,
        left: BitVecTerm,
        right: BitVecTerm,
        operation: impl FnOnce(&mut TermStore, TermId, TermId) -> Result<TermId, TermError>,
    ) -> Result<BitVecTerm, ContextError> {
        let left = self.bitvec_id(left)?;
        let right = self.bitvec_id(right)?;
        let result = operation(&mut self.terms, left, right)?;
        self.wrap_bitvec(result)
    }

    fn bv_predicate(
        &mut self,
        left: BitVecTerm,
        right: BitVecTerm,
        operation: impl FnOnce(&mut TermStore, TermId, TermId) -> Result<TermId, TermError>,
    ) -> Result<BoolTerm, ContextError> {
        let left = self.bitvec_id(left)?;
        let right = self.bitvec_id(right)?;
        let result = operation(&mut self.terms, left, right)?;
        self.wrap_bool(result)
    }

    fn ensure_fresh_name(&self, name: &str) -> Result<(), ContextError> {
        if self.bindings.contains_key(name) || self.function_bindings.contains_key(name) {
            Err(ContextError::DuplicateName(name.to_owned()))
        } else {
            Ok(())
        }
    }

    fn model_ref(&self) -> Result<&Model, ContextError> {
        match &self.last_check {
            LastCheck::Sat { boolean, .. } | LastCheck::Unknown { boolean, .. } => Ok(boolean),
            _ => Err(ContextError::NoModel),
        }
    }

    fn theory_model_ref(&self) -> Result<&TheoryModel, ContextError> {
        match &self.last_check {
            LastCheck::Sat { theory, .. } | LastCheck::Unknown { theory, .. } => Ok(theory),
            _ => Err(ContextError::NoModel),
        }
    }

    fn evaluate_bool(&self, model: &Model, term: BoolTerm) -> Result<bool, ContextError> {
        let id = self.bool_id(term)?;
        Ok(self
            .terms
            .evaluate_bool(id, |symbol| self.symbol_value(model, symbol))?)
    }

    fn symbol_value(&self, model: &Model, symbol: super::term::SymbolId) -> bool {
        self.encoder
            .atom_literal(symbol)
            .is_some_and(|literal| model.literal_value(literal))
    }

    fn invalidate_check(&mut self) {
        self.last_check = LastCheck::None;
    }
}

#[cfg(test)]
mod tests {
    use crate::{SolveLimits, UnknownReason};

    use super::{AnyTerm, CheckResult, Context, ContextError, Value};

    #[test]
    fn typed_bitvector_context_is_incremental_and_reconstructs_models() {
        let mut context = Context::new();
        let x = context.declare_bitvec("x", 4).unwrap();
        let three = context.bitvec_u64(3, 4).unwrap();
        let five = context.bitvec_u64(5, 4).unwrap();
        let sum = context.bv_add(&[x, three]).unwrap();
        let equation = context.equal(&[sum.into(), five.into()]).unwrap();
        context.assert_named("sum", equation).unwrap();

        assert_eq!(context.check().unwrap(), CheckResult::Sat);
        let Value::BitVec(value) = context.value(x).unwrap() else {
            panic!("x must have a bit-vector value");
        };
        assert_eq!(value.as_u64(), Some(2));

        context.push(1).unwrap();
        let not_x = context.bool_not(equation).unwrap();
        context.assert(not_x).unwrap();
        assert_eq!(context.check().unwrap(), CheckResult::Unsat);
        assert_eq!(context.unsat_core().unwrap(), ["sum"]);
        context.pop(1).unwrap();
        assert_eq!(context.check().unwrap(), CheckResult::Sat);
    }

    #[test]
    fn arbitrary_assumptions_and_limits_leave_the_context_reusable() {
        let mut context = Context::new();
        let p = context.declare_bool("p").unwrap();
        let not_p = context.bool_not(p).unwrap();
        assert_eq!(
            context.check_assuming(&[p, not_p]).unwrap(),
            CheckResult::Unsat
        );
        assert_eq!(context.unsat_assumptions().unwrap(), [p, not_p]);
        assert_eq!(
            context
                .check_with_limits(SolveLimits {
                    conflicts: Some(0),
                    propagations: None,
                })
                .unwrap(),
            CheckResult::Unknown(UnknownReason::ConflictLimit)
        );
        assert_eq!(
            context.last_unknown_reason(),
            Some(UnknownReason::ConflictLimit)
        );
        assert_eq!(context.check().unwrap(), CheckResult::Sat);
    }

    #[test]
    fn terms_from_other_or_reset_contexts_are_rejected() {
        let mut first = Context::new();
        let foreign = first.declare_bool("p").unwrap();
        let mut second = Context::new();
        assert_eq!(second.assert(foreign), Err(ContextError::ForeignTerm));

        first.reset();
        assert_eq!(first.assert(foreign), Err(ContextError::ForeignTerm));
        assert!(first.lookup("p").is_none());
    }

    #[test]
    fn generic_equality_rejects_mixed_sorts() {
        let mut context = Context::new();
        let boolean = context.declare_bool("p").unwrap();
        let bitvector = context.declare_bitvec("x", 1).unwrap();
        assert!(
            context
                .equal(&[AnyTerm::Bool(boolean), AnyTerm::BitVec(bitvector)])
                .is_err()
        );
    }

    #[test]
    fn typed_uf_context_enforces_congruence_incrementally() {
        let mut context = Context::new();
        let sort = context.declare_uninterpreted_sort("U").unwrap();
        let a = context.declare_uninterpreted("a", sort).unwrap();
        let b = context.declare_uninterpreted("b", sort).unwrap();
        let function = context
            .declare_function(
                "f",
                &[super::SmtSort::Uninterpreted(sort)],
                super::SmtSort::Uninterpreted(sort),
            )
            .unwrap();
        let fa = context.apply(function, &[a.into()]).unwrap();
        let fb = context.apply(function, &[b.into()]).unwrap();
        let arguments_equal = context.equal(&[a.into(), b.into()]).unwrap();
        let results_equal = context.equal(&[fa, fb]).unwrap();
        let results_differ = context.bool_not(results_equal).unwrap();
        context.assert_named("arguments", arguments_equal).unwrap();

        assert_eq!(context.check().unwrap(), CheckResult::Sat);
        context.push(1).unwrap();
        context.assert(results_differ).unwrap();
        assert_eq!(context.check().unwrap(), CheckResult::Unsat);
        assert_eq!(context.unsat_core().unwrap(), ["arguments"]);
        context.pop(1).unwrap();
        assert_eq!(context.check().unwrap(), CheckResult::Sat);
    }

    #[test]
    fn uf_functions_returning_bitvectors_share_results_for_equal_arguments() {
        let mut context = Context::new();
        let sort = context.declare_uninterpreted_sort("U").unwrap();
        let a = context.declare_uninterpreted("a", sort).unwrap();
        let b = context.declare_uninterpreted("b", sort).unwrap();
        let function = context
            .declare_function(
                "color",
                &[super::SmtSort::Uninterpreted(sort)],
                super::SmtSort::BitVec(4),
            )
            .unwrap();
        let super::AnyTerm::BitVec(fa) = context.apply(function, &[a.into()]).unwrap() else {
            panic!("declared function has a bit-vector range");
        };
        let super::AnyTerm::BitVec(fb) = context.apply(function, &[b.into()]).unwrap() else {
            panic!("declared function has a bit-vector range");
        };
        let arguments_equal = context.equal(&[a.into(), b.into()]).unwrap();
        let results_equal = context.equal(&[fa.into(), fb.into()]).unwrap();
        let results_differ = context.bool_not(results_equal).unwrap();
        context.assert(arguments_equal).unwrap();
        context.assert(results_differ).unwrap();
        assert_eq!(context.check().unwrap(), CheckResult::Unsat);
    }

    #[test]
    fn uninterpreted_models_separate_asserted_disequalities() {
        let mut context = Context::new();
        let sort = context.declare_uninterpreted_sort("U").unwrap();
        let a = context.declare_uninterpreted("a", sort).unwrap();
        let b = context.declare_uninterpreted("b", sort).unwrap();
        let equality = context.equal(&[a.into(), b.into()]).unwrap();
        let disequality = context.bool_not(equality).unwrap();
        context.assert(disequality).unwrap();
        assert_eq!(context.check().unwrap(), CheckResult::Sat);
        let Value::Uninterpreted(a_value) = context.value(a).unwrap() else {
            panic!("a has an uninterpreted value");
        };
        let Value::Uninterpreted(b_value) = context.value(b).unwrap() else {
            panic!("b has an uninterpreted value");
        };
        assert_eq!(a_value.sort(), sort);
        assert_ne!(a_value, b_value);
    }

    #[test]
    fn array_store_select_rewrites_to_the_core_ite_semantics() {
        let mut context = Context::new();
        let sort = context
            .array_sort(super::SmtSort::BitVec(2), super::SmtSort::BitVec(4))
            .unwrap();
        let array = context.declare_array("a", sort).unwrap();
        let index = context.bitvec_u64(2, 2).unwrap();
        let value = context.bitvec_u64(9, 4).unwrap();
        let stored = context.store(array, index.into(), value.into()).unwrap();
        let super::AnyTerm::BitVec(selected) = context.select(stored, index.into()).unwrap() else {
            panic!("array has a bit-vector element sort");
        };
        let equality = context.equal(&[selected.into(), value.into()]).unwrap();
        let contradiction = context.bool_not(equality).unwrap();
        context.assert(contradiction).unwrap();
        assert_eq!(context.check().unwrap(), CheckResult::Unsat);
    }

    #[test]
    fn extensional_arrays_over_a_finite_index_sort_have_witnesses() {
        let mut context = Context::new();
        let sort = context
            .array_sort(super::SmtSort::BitVec(1), super::SmtSort::BitVec(2))
            .unwrap();
        let a = context.declare_array("a", sort).unwrap();
        let b = context.declare_array("b", sort).unwrap();
        for index in 0..2 {
            let index = context.bitvec_u64(index, 1).unwrap();
            let left = context.select(a, index.into()).unwrap();
            let right = context.select(b, index.into()).unwrap();
            let equality = context.equal(&[left, right]).unwrap();
            context.assert(equality).unwrap();
        }
        let arrays_equal = context.equal(&[a.into(), b.into()]).unwrap();
        let arrays_differ = context.bool_not(arrays_equal).unwrap();
        context.assert(arrays_differ).unwrap();
        assert_eq!(context.check().unwrap(), CheckResult::Unsat);
    }
}
