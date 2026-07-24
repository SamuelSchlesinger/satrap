use std::collections::{HashMap, HashSet};
use std::error::Error;
use std::fmt;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};

use super::arithmetic::{ArithmeticExpressionId, ArithmeticVariableId, LinearExpression};

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SortId(u32);

/// An opaque uninterpreted-sort identity owned by one [`TermStore`].
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct UninterpretedSortId(u32);

impl UninterpretedSortId {
    pub(crate) const fn index(self) -> u32 {
        self.0
    }
}

/// An opaque uninterpreted-function identity owned by one [`TermStore`].
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct FunctionId(u32);

/// An opaque extensional-array sort identity owned by one [`TermStore`].
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ArraySortId(u32);

/// A sort currently understood by the deliberately lowered SMT term layer.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Sort {
    Bool,
    BitVec(u32),
    Int,
    Real,
    Uninterpreted(UninterpretedSortId),
    Array(ArraySortId),
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TermId(u32);

impl TermId {
    pub(crate) fn index(self) -> usize {
        self.0 as usize
    }

    pub(crate) fn from_index(index: usize) -> Option<Self> {
        u32::try_from(index).ok().map(Self)
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(crate) struct SymbolId(pub(crate) u32);

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) struct TermNode {
    pub(crate) sort: SortId,
    pub(crate) kind: TermKind,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) enum TermKind {
    Bool(bool),
    /// A Boolean SAT-level atom. Bit-vector variables are represented by one
    /// such atom per bit and a hash-consed [`TermKind::BitVec`] view.
    Atom(SymbolId),
    Not(TermId),
    And(Box<[TermId]>),
    Or(Box<[TermId]>),
    Xor(TermId, TermId),
    Iff(TermId, TermId),
    Ite(TermId, TermId, TermId),
    /// A distinct term of an uninterpreted sort.
    UfConstant(u32),
    /// An application whose result has an uninterpreted sort. Applications
    /// returning Bool or BitVec use fresh lowered atoms and are recorded in
    /// [`TermStore::applications`] instead.
    UfApplication(FunctionId, Box<[TermId]>),
    /// A Core `ite` whose branches have an uninterpreted sort.
    UfIte(TermId, TermId, TermId),
    /// A canonical affine integer or real expression.
    Arithmetic(ArithmeticExpressionId),
    /// A Boolean abstraction atom for `expression <= 0` or `expression < 0`.
    ArithmeticPredicate(SymbolId, ArithmeticExpressionId, bool),
    /// A constant array whose every index maps to the given value.
    ArrayConst(TermId),
    /// A functional array update.
    ArrayStore(TermId, TermId, TermId),
    /// A Boolean abstraction atom for equality in an uninterpreted sort.
    TheoryEquality(SymbolId, TermId, TermId),
    /// Bits are stored least-significant first. Every member has sort Bool.
    BitVec(Box<[TermId]>),
}

#[derive(Clone, Debug)]
pub(crate) struct FunctionSignature {
    pub(crate) domain: Box<[Sort]>,
    pub(crate) range: Sort,
}

#[derive(Clone, Debug)]
pub(crate) struct Application {
    pub(crate) function: FunctionId,
    pub(crate) arguments: Box<[TermId]>,
    pub(crate) result: TermId,
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct TheoryEquality {
    pub(crate) term: TermId,
    pub(crate) left: TermId,
    pub(crate) right: TermId,
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct UfIte {
    pub(crate) result: TermId,
    pub(crate) condition: TermId,
    pub(crate) then_term: TermId,
    pub(crate) else_term: TermId,
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct ArithmeticPredicate {
    pub(crate) term: TermId,
    pub(crate) expression: ArithmeticExpressionId,
    pub(crate) strict: bool,
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct ArithmeticIte {
    pub(crate) result: TermId,
    pub(crate) condition: TermId,
    pub(crate) then_term: TermId,
    pub(crate) else_term: TermId,
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct ArraySignature {
    pub(crate) index: Sort,
    pub(crate) element: Sort,
    pub(crate) select_function: FunctionId,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct ApplicationKey {
    function: FunctionId,
    arguments: Box<[TermId]>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TermError(String);

impl TermError {
    pub(crate) fn new(message: impl Into<String>) -> Self {
        Self(message.into())
    }
}

impl fmt::Display for TermError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.0)
    }
}

impl Error for TermError {}

/// Typed, hash-consed SMT terms.
///
/// Bit-vector expressions are deliberately lowered to shared Boolean circuits.
/// This gives the SAT encoder one checked representation for Core and QF_BV
/// while preserving the original sort and word boundary for model production.
#[derive(Debug)]
pub struct TermStore {
    pub(crate) nodes: Vec<TermNode>,
    interned: HashMap<TermNode, TermId>,
    sorts: Vec<Sort>,
    sort_ids: HashMap<Sort, SortId>,
    bool_sort: SortId,
    true_term: TermId,
    false_term: TermId,
    next_symbol: u32,
    next_uninterpreted_sort: u32,
    next_uninterpreted_value: u32,
    functions: Vec<FunctionSignature>,
    applications: Vec<Application>,
    application_results: HashMap<ApplicationKey, TermId>,
    application_by_result: HashMap<TermId, usize>,
    application_by_bit: HashMap<TermId, (TermId, usize)>,
    theory_equalities: Vec<TheoryEquality>,
    theory_equality_terms: HashMap<(TermId, TermId), TermId>,
    uf_ites: Vec<UfIte>,
    arithmetic_expressions: Vec<(Sort, LinearExpression)>,
    arithmetic_expression_ids: HashMap<(Sort, LinearExpression), ArithmeticExpressionId>,
    arithmetic_variable_sorts: Vec<Sort>,
    arithmetic_predicates: Vec<ArithmeticPredicate>,
    arithmetic_predicate_terms: HashMap<(ArithmeticExpressionId, bool), TermId>,
    arithmetic_ites: Vec<ArithmeticIte>,
    arithmetic_ite_terms: HashMap<(TermId, TermId, TermId, Sort), TermId>,
    array_sorts: Vec<ArraySignature>,
    array_sort_ids: HashMap<(Sort, Sort), ArraySortId>,
    array_axioms: Vec<TermId>,
    array_semantic_selects: HashSet<TermId>,
    array_semantic_select_log: Vec<TermId>,
    /// Indices at which each concrete array term is observed. Array
    /// preparation propagates these demands only across relationships that
    /// can identify arrays, rather than materializing the global Cartesian
    /// product of every array and every index of the same sort.
    array_reads: HashMap<TermId, Vec<TermId>>,
    array_read_log: Vec<(TermId, TermId)>,
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct TermStoreCheckpoint {
    nodes: usize,
    sorts: usize,
    next_symbol: u32,
    next_uninterpreted_sort: u32,
    next_uninterpreted_value: u32,
    functions: usize,
    applications: usize,
    theory_equalities: usize,
    uf_ites: usize,
    arithmetic_expressions: usize,
    arithmetic_variable_sorts: usize,
    arithmetic_predicates: usize,
    arithmetic_ites: usize,
    array_sorts: usize,
    array_axioms: usize,
    array_semantic_select_log: usize,
    array_read_log: usize,
}

impl Default for TermStore {
    fn default() -> Self {
        Self::new()
    }
}

impl TermStore {
    #[must_use]
    pub fn new() -> Self {
        let bool_sort = SortId(0);
        let true_node = TermNode {
            sort: bool_sort,
            kind: TermKind::Bool(true),
        };
        let false_node = TermNode {
            sort: bool_sort,
            kind: TermKind::Bool(false),
        };
        let mut interned = HashMap::new();
        interned.insert(true_node.clone(), TermId(0));
        interned.insert(false_node.clone(), TermId(1));
        let mut sort_ids = HashMap::new();
        sort_ids.insert(Sort::Bool, bool_sort);
        Self {
            nodes: vec![true_node, false_node],
            interned,
            sorts: vec![Sort::Bool],
            sort_ids,
            bool_sort,
            true_term: TermId(0),
            false_term: TermId(1),
            next_symbol: 0,
            next_uninterpreted_sort: 0,
            next_uninterpreted_value: 0,
            functions: Vec::new(),
            applications: Vec::new(),
            application_results: HashMap::new(),
            application_by_result: HashMap::new(),
            application_by_bit: HashMap::new(),
            theory_equalities: Vec::new(),
            theory_equality_terms: HashMap::new(),
            uf_ites: Vec::new(),
            arithmetic_expressions: Vec::new(),
            arithmetic_expression_ids: HashMap::new(),
            arithmetic_variable_sorts: Vec::new(),
            arithmetic_predicates: Vec::new(),
            arithmetic_predicate_terms: HashMap::new(),
            arithmetic_ites: Vec::new(),
            arithmetic_ite_terms: HashMap::new(),
            array_sorts: Vec::new(),
            array_sort_ids: HashMap::new(),
            array_axioms: Vec::new(),
            array_semantic_selects: HashSet::new(),
            array_semantic_select_log: Vec::new(),
            array_reads: HashMap::new(),
            array_read_log: Vec::new(),
        }
    }

    pub(crate) fn checkpoint(&self) -> TermStoreCheckpoint {
        TermStoreCheckpoint {
            nodes: self.nodes.len(),
            sorts: self.sorts.len(),
            next_symbol: self.next_symbol,
            next_uninterpreted_sort: self.next_uninterpreted_sort,
            next_uninterpreted_value: self.next_uninterpreted_value,
            functions: self.functions.len(),
            applications: self.applications.len(),
            theory_equalities: self.theory_equalities.len(),
            uf_ites: self.uf_ites.len(),
            arithmetic_expressions: self.arithmetic_expressions.len(),
            arithmetic_variable_sorts: self.arithmetic_variable_sorts.len(),
            arithmetic_predicates: self.arithmetic_predicates.len(),
            arithmetic_ites: self.arithmetic_ites.len(),
            array_sorts: self.array_sorts.len(),
            array_axioms: self.array_axioms.len(),
            array_semantic_select_log: self.array_semantic_select_log.len(),
            array_read_log: self.array_read_log.len(),
        }
    }

    pub(crate) fn rollback(&mut self, checkpoint: TermStoreCheckpoint) {
        while self.array_read_log.len() > checkpoint.array_read_log {
            let (array, index) = self
                .array_read_log
                .pop()
                .expect("array-read log length checked above");
            let remove_entry = {
                let indices = self
                    .array_reads
                    .get_mut(&array)
                    .expect("logged array read has an index list");
                let removed = indices.pop();
                debug_assert_eq!(removed, Some(index));
                indices.is_empty()
            };
            if remove_entry {
                self.array_reads.remove(&array);
            }
        }
        while self.array_semantic_select_log.len() > checkpoint.array_semantic_select_log {
            let term = self
                .array_semantic_select_log
                .pop()
                .expect("semantic-select log length checked above");
            let removed = self.array_semantic_selects.remove(&term);
            debug_assert!(removed);
        }

        self.array_axioms.truncate(checkpoint.array_axioms);
        while self.array_sorts.len() > checkpoint.array_sorts {
            let signature = self
                .array_sorts
                .pop()
                .expect("array-sort length checked above");
            let removed = self
                .array_sort_ids
                .remove(&(signature.index, signature.element));
            debug_assert!(removed.is_some());
        }
        while self.arithmetic_ites.len() > checkpoint.arithmetic_ites {
            let item = self
                .arithmetic_ites
                .pop()
                .expect("arithmetic-ite length checked above");
            let sort = self
                .sort(item.result)
                .expect("arithmetic ite result remains live during rollback");
            let removed = self.arithmetic_ite_terms.remove(&(
                item.condition,
                item.then_term,
                item.else_term,
                sort,
            ));
            debug_assert!(removed.is_some());
        }
        while self.arithmetic_predicates.len() > checkpoint.arithmetic_predicates {
            let predicate = self
                .arithmetic_predicates
                .pop()
                .expect("arithmetic-predicate length checked above");
            let removed = self
                .arithmetic_predicate_terms
                .remove(&(predicate.expression, predicate.strict));
            debug_assert!(removed.is_some());
        }
        self.arithmetic_variable_sorts
            .truncate(checkpoint.arithmetic_variable_sorts);
        while self.arithmetic_expressions.len() > checkpoint.arithmetic_expressions {
            let (sort, expression) = self
                .arithmetic_expressions
                .pop()
                .expect("arithmetic-expression length checked above");
            let removed = self.arithmetic_expression_ids.remove(&(sort, expression));
            debug_assert!(removed.is_some());
        }
        self.uf_ites.truncate(checkpoint.uf_ites);
        while self.theory_equalities.len() > checkpoint.theory_equalities {
            let equality = self
                .theory_equalities
                .pop()
                .expect("theory-equality length checked above");
            let removed = self
                .theory_equality_terms
                .remove(&ordered_pair(equality.left, equality.right));
            debug_assert!(removed.is_some());
        }
        while self.applications.len() > checkpoint.applications {
            let application = self
                .applications
                .pop()
                .expect("application length checked above");
            if matches!(self.sort(application.result), Ok(Sort::BitVec(_))) {
                let bits = self
                    .bitvec_bits(application.result)
                    .expect("bit-vector application remains live during rollback")
                    .to_vec();
                for bit in bits {
                    let removed = self.application_by_bit.remove(&bit);
                    debug_assert!(removed.is_some());
                }
            }
            let key = ApplicationKey {
                function: application.function,
                arguments: application.arguments.clone(),
            };
            let removed_result = self.application_results.remove(&key);
            let removed_index = self.application_by_result.remove(&application.result);
            debug_assert_eq!(removed_result, Some(application.result));
            debug_assert!(removed_index.is_some());
        }
        self.functions.truncate(checkpoint.functions);

        while self.nodes.len() > checkpoint.nodes {
            let node = self.nodes.pop().expect("term-node length checked above");
            let removed = self.interned.remove(&node);
            debug_assert!(removed.is_some());
        }
        while self.sorts.len() > checkpoint.sorts {
            let sort = self.sorts.pop().expect("sort length checked above");
            let removed = self.sort_ids.remove(&sort);
            debug_assert!(removed.is_some());
        }
        self.next_symbol = checkpoint.next_symbol;
        self.next_uninterpreted_sort = checkpoint.next_uninterpreted_sort;
        self.next_uninterpreted_value = checkpoint.next_uninterpreted_value;
    }

    #[must_use]
    pub const fn bool_sort(&self) -> SortId {
        self.bool_sort
    }

    #[must_use]
    pub const fn bool_constant(&self, value: bool) -> TermId {
        if value {
            self.true_term
        } else {
            self.false_term
        }
    }

    pub fn sort(&self, term: TermId) -> Result<Sort, TermError> {
        let node = self
            .nodes
            .get(term.index())
            .ok_or_else(|| TermError::new("term does not belong to this term store"))?;
        Ok(self.sorts[node.sort.0 as usize])
    }

    pub(crate) fn sort_id(&self, term: TermId) -> Result<SortId, TermError> {
        self.nodes
            .get(term.index())
            .map(|node| node.sort)
            .ok_or_else(|| TermError::new("term does not belong to this term store"))
    }

    pub(crate) fn sort_id_for(&mut self, sort: Sort) -> Result<SortId, TermError> {
        if let Some(&id) = self.sort_ids.get(&sort) {
            return Ok(id);
        }
        if matches!(sort, Sort::BitVec(0)) {
            return Err(TermError::new("bit-vector width must be greater than zero"));
        }
        let id = SortId(
            u32::try_from(self.sorts.len())
                .map_err(|_| TermError::new("sort store exceeds the supported u32 index"))?,
        );
        self.sorts.push(sort);
        self.sort_ids.insert(sort, id);
        Ok(id)
    }

    pub(crate) fn fresh_uninterpreted_sort(&mut self) -> Result<UninterpretedSortId, TermError> {
        let id = UninterpretedSortId(self.next_uninterpreted_sort);
        self.next_uninterpreted_sort = self
            .next_uninterpreted_sort
            .checked_add(1)
            .ok_or_else(|| TermError::new("uninterpreted-sort store exceeds the u32 index"))?;
        self.sort_id_for(Sort::Uninterpreted(id))?;
        Ok(id)
    }

    pub(crate) fn arithmetic_integer(&mut self, value: BigInt) -> Result<TermId, TermError> {
        self.arithmetic_constant(Sort::Int, BigRational::from_integer(value))
    }

    pub(crate) fn arithmetic_real(&mut self, value: BigRational) -> Result<TermId, TermError> {
        self.arithmetic_constant(Sort::Real, value)
    }

    pub(crate) fn arithmetic_constant(
        &mut self,
        sort: Sort,
        value: BigRational,
    ) -> Result<TermId, TermError> {
        self.make_arithmetic_term(sort, LinearExpression::constant(value))
    }

    pub(crate) fn arithmetic_expression(
        &self,
        expression: ArithmeticExpressionId,
    ) -> Result<&LinearExpression, TermError> {
        self.arithmetic_expressions
            .get(expression.0 as usize)
            .map(|(_, expression)| expression)
            .ok_or_else(|| TermError::new("arithmetic expression does not belong to this store"))
    }

    pub(crate) fn arithmetic_expression_sort(
        &self,
        expression: ArithmeticExpressionId,
    ) -> Result<Sort, TermError> {
        self.arithmetic_expressions
            .get(expression.0 as usize)
            .map(|(sort, _)| *sort)
            .ok_or_else(|| TermError::new("arithmetic expression does not belong to this store"))
    }

    pub(crate) fn arithmetic_variable_sorts(&self) -> &[Sort] {
        &self.arithmetic_variable_sorts
    }

    pub(crate) fn arithmetic_predicates(&self) -> &[ArithmeticPredicate] {
        &self.arithmetic_predicates
    }

    pub(crate) fn arithmetic_ites(&self) -> &[ArithmeticIte] {
        &self.arithmetic_ites
    }

    pub(crate) fn arithmetic_add(&mut self, terms: &[TermId]) -> Result<TermId, TermError> {
        if terms.len() < 2 {
            return Err(TermError::new("`+` expects at least two arguments"));
        }
        let sort = self.common_arithmetic_sort(terms)?;
        let expressions = terms
            .iter()
            .map(|&term| self.arithmetic_expression_as(term, sort))
            .collect::<Result<Vec<_>, _>>()?;
        self.make_arithmetic_term(sort, LinearExpression::sum(expressions))
    }

    pub(crate) fn arithmetic_negate(&mut self, term: TermId) -> Result<TermId, TermError> {
        let sort = self.require_arithmetic(term)?;
        let expression = self
            .arithmetic_expression_for_term(term)?
            .clone()
            .scaled(&BigRational::from_integer(BigInt::from(-1)));
        self.make_arithmetic_term(sort, expression)
    }

    pub(crate) fn arithmetic_sub(&mut self, terms: &[TermId]) -> Result<TermId, TermError> {
        if terms.is_empty() {
            return Err(TermError::new("`-` expects at least one argument"));
        }
        if terms.len() == 1 {
            return self.arithmetic_negate(terms[0]);
        }
        let sort = self.common_arithmetic_sort(terms)?;
        let mut result = self.arithmetic_expression_as(terms[0], sort)?;
        let minus_one = BigRational::from_integer(BigInt::from(-1));
        for &term in &terms[1..] {
            result.add_scaled(&self.arithmetic_expression_as(term, sort)?, &minus_one);
        }
        self.make_arithmetic_term(sort, result)
    }

    pub(crate) fn arithmetic_mul(&mut self, terms: &[TermId]) -> Result<TermId, TermError> {
        if terms.len() < 2 {
            return Err(TermError::new("`*` expects at least two arguments"));
        }
        let sort = self.common_arithmetic_sort(terms)?;
        let mut scale = BigRational::one();
        let mut nonconstant = None;
        for &term in terms {
            let expression = self.arithmetic_expression_as(term, sort)?;
            if expression.is_constant() {
                scale *= expression.constant;
            } else if nonconstant.replace(expression).is_some() {
                return Err(TermError::new(
                    "nonlinear multiplication is outside the supported logics",
                ));
            }
        }
        let expression = match nonconstant {
            Some(expression) => expression.scaled(&scale),
            None => LinearExpression::constant(scale),
        };
        self.make_arithmetic_term(sort, expression)
    }

    pub(crate) fn arithmetic_divide(
        &mut self,
        numerator: TermId,
        denominator: TermId,
    ) -> Result<TermId, TermError> {
        self.require_arithmetic(numerator)?;
        self.require_arithmetic(denominator)?;
        let denominator = self.arithmetic_expression_for_term(denominator)?;
        if !denominator.is_constant() {
            return Err(TermError::new(
                "division by a nonconstant is outside linear arithmetic",
            ));
        }
        if denominator.constant.is_zero() {
            return Err(TermError::new(
                "division by zero is not a total linear-arithmetic operation",
            ));
        }
        let scale = denominator.constant.clone().recip();
        let expression = self
            .arithmetic_expression_as(numerator, Sort::Real)?
            .scaled(&scale);
        self.make_arithmetic_term(Sort::Real, expression)
    }

    pub(crate) fn arithmetic_to_real(&mut self, term: TermId) -> Result<TermId, TermError> {
        self.coerce_arithmetic_term(term, Sort::Real)
    }

    pub(crate) fn arithmetic_le(
        &mut self,
        left: TermId,
        right: TermId,
    ) -> Result<TermId, TermError> {
        self.arithmetic_comparison(left, right, false)
    }

    pub(crate) fn arithmetic_lt(
        &mut self,
        left: TermId,
        right: TermId,
    ) -> Result<TermId, TermError> {
        self.arithmetic_comparison(left, right, true)
    }

    pub(crate) fn arithmetic_ge(
        &mut self,
        left: TermId,
        right: TermId,
    ) -> Result<TermId, TermError> {
        self.arithmetic_comparison(right, left, false)
    }

    pub(crate) fn arithmetic_gt(
        &mut self,
        left: TermId,
        right: TermId,
    ) -> Result<TermId, TermError> {
        self.arithmetic_comparison(right, left, true)
    }

    fn arithmetic_comparison(
        &mut self,
        left: TermId,
        right: TermId,
        strict: bool,
    ) -> Result<TermId, TermError> {
        let sort = self.common_arithmetic_sort(&[left, right])?;
        let mut expression = self.arithmetic_expression_as(left, sort)?;
        expression.add_scaled(
            &self.arithmetic_expression_as(right, sort)?,
            &BigRational::from_integer(BigInt::from(-1)),
        );
        if expression.is_constant() {
            let zero = BigRational::zero();
            return Ok(self.bool_constant(if strict {
                expression.constant < zero
            } else {
                expression.constant <= zero
            }));
        }
        let expression = self.intern_arithmetic_expression(sort, expression)?;
        if let Some(&term) = self.arithmetic_predicate_terms.get(&(expression, strict)) {
            return Ok(term);
        }
        let symbol = self.fresh_symbol();
        let term = self.intern(
            self.bool_sort,
            TermKind::ArithmeticPredicate(symbol, expression, strict),
        );
        self.arithmetic_predicate_terms
            .insert((expression, strict), term);
        self.arithmetic_predicates.push(ArithmeticPredicate {
            term,
            expression,
            strict,
        });
        Ok(term)
    }

    fn arithmetic_equivalent(&mut self, left: TermId, right: TermId) -> Result<TermId, TermError> {
        let less_equal = self.arithmetic_le(left, right)?;
        let greater_equal = self.arithmetic_ge(left, right)?;
        self.and(&[less_equal, greater_equal])
    }

    fn arithmetic_ite(
        &mut self,
        condition: TermId,
        then_term: TermId,
        else_term: TermId,
    ) -> Result<TermId, TermError> {
        let sort = self.common_arithmetic_sort(&[then_term, else_term])?;
        let then_term = self.coerce_arithmetic_term(then_term, sort)?;
        let else_term = self.coerce_arithmetic_term(else_term, sort)?;
        let key = (condition, then_term, else_term, sort);
        if let Some(&result) = self.arithmetic_ite_terms.get(&key) {
            return Ok(result);
        }
        let result = self.fresh_arithmetic_variable(sort)?;
        self.arithmetic_ite_terms.insert(key, result);
        self.arithmetic_ites.push(ArithmeticIte {
            result,
            condition,
            then_term,
            else_term,
        });
        Ok(result)
    }

    fn fresh_arithmetic_variable(&mut self, sort: Sort) -> Result<TermId, TermError> {
        if !matches!(sort, Sort::Int | Sort::Real) {
            return Err(TermError::new("expected arithmetic sort"));
        }
        let index = u32::try_from(self.arithmetic_variable_sorts.len())
            .map_err(|_| TermError::new("arithmetic-variable store exceeds the u32 index"))?;
        let variable = ArithmeticVariableId(index);
        self.arithmetic_variable_sorts.push(sort);
        self.make_arithmetic_term(sort, LinearExpression::variable(variable))
    }

    fn make_arithmetic_term(
        &mut self,
        sort: Sort,
        expression: LinearExpression,
    ) -> Result<TermId, TermError> {
        if !matches!(sort, Sort::Int | Sort::Real) {
            return Err(TermError::new("expected arithmetic sort"));
        }
        if sort == Sort::Int
            && (!expression.constant.is_integer()
                || expression
                    .coefficients
                    .values()
                    .any(|coefficient| !coefficient.is_integer()))
        {
            return Err(TermError::new(
                "integer expression has a non-integral coefficient",
            ));
        }
        let expression = self.intern_arithmetic_expression(sort, expression)?;
        let sort = self.sort_id_for(sort)?;
        Ok(self.intern(sort, TermKind::Arithmetic(expression)))
    }

    fn intern_arithmetic_expression(
        &mut self,
        sort: Sort,
        expression: LinearExpression,
    ) -> Result<ArithmeticExpressionId, TermError> {
        if let Some(&id) = self
            .arithmetic_expression_ids
            .get(&(sort, expression.clone()))
        {
            return Ok(id);
        }
        let id = ArithmeticExpressionId(
            u32::try_from(self.arithmetic_expressions.len())
                .map_err(|_| TermError::new("arithmetic-expression store exceeds the u32 index"))?,
        );
        self.arithmetic_expressions.push((sort, expression.clone()));
        self.arithmetic_expression_ids
            .insert((sort, expression), id);
        Ok(id)
    }

    pub(crate) fn arithmetic_expression_for_term(
        &self,
        term: TermId,
    ) -> Result<&LinearExpression, TermError> {
        let TermKind::Arithmetic(expression) = self.node(term).kind else {
            return Err(TermError::new("expected an integer or real term"));
        };
        self.arithmetic_expression(expression)
    }

    pub(crate) fn arithmetic_variable_for_term(
        &self,
        term: TermId,
    ) -> Result<Option<ArithmeticVariableId>, TermError> {
        let expression = self.arithmetic_expression_for_term(term)?;
        if !expression.constant.is_zero() || expression.coefficients.len() != 1 {
            return Ok(None);
        }
        let (&variable, coefficient) = expression
            .coefficients
            .first_key_value()
            .expect("length checked");
        Ok((coefficient == &BigRational::one()).then_some(variable))
    }

    fn arithmetic_expression_as(
        &self,
        term: TermId,
        target: Sort,
    ) -> Result<LinearExpression, TermError> {
        let source = self.require_arithmetic(term)?;
        if source == Sort::Real && target == Sort::Int {
            return Err(TermError::new("cannot implicitly coerce Real to Int"));
        }
        if !matches!(target, Sort::Int | Sort::Real) {
            return Err(TermError::new("expected arithmetic target sort"));
        }
        Ok(self.arithmetic_expression_for_term(term)?.clone())
    }

    fn coerce_arithmetic_term(&mut self, term: TermId, target: Sort) -> Result<TermId, TermError> {
        if self.sort(term)? == target {
            return Ok(term);
        }
        let expression = self.arithmetic_expression_as(term, target)?;
        self.make_arithmetic_term(target, expression)
    }

    fn common_arithmetic_sort(&self, terms: &[TermId]) -> Result<Sort, TermError> {
        let mut result = Sort::Int;
        for &term in terms {
            match self.require_arithmetic(term)? {
                Sort::Int => {}
                Sort::Real => result = Sort::Real,
                _ => unreachable!("require_arithmetic filters the sort"),
            }
        }
        Ok(result)
    }

    fn require_arithmetic(&self, term: TermId) -> Result<Sort, TermError> {
        match self.sort(term)? {
            sort @ (Sort::Int | Sort::Real) => Ok(sort),
            _ => Err(TermError::new("expected an integer or real term")),
        }
    }

    pub(crate) fn declare_function(
        &mut self,
        domain: &[Sort],
        range: Sort,
    ) -> Result<FunctionId, TermError> {
        for &sort in domain {
            self.sort_id_for(sort)?;
        }
        self.sort_id_for(range)?;
        let id = FunctionId(
            u32::try_from(self.functions.len())
                .map_err(|_| TermError::new("function store exceeds the supported u32 index"))?,
        );
        self.functions.push(FunctionSignature {
            domain: domain.into(),
            range,
        });
        Ok(id)
    }

    pub(crate) fn array_sort(
        &mut self,
        index: Sort,
        element: Sort,
    ) -> Result<ArraySortId, TermError> {
        self.sort_id_for(index)?;
        self.sort_id_for(element)?;
        if let Some(&sort) = self.array_sort_ids.get(&(index, element)) {
            return Ok(sort);
        }
        let id = ArraySortId(
            u32::try_from(self.array_sorts.len())
                .map_err(|_| TermError::new("array-sort store exceeds the supported u32 index"))?,
        );
        let array = Sort::Array(id);
        self.sort_id_for(array)?;
        let select_function = self.declare_function(&[array, index], element)?;
        self.array_sorts.push(ArraySignature {
            index,
            element,
            select_function,
        });
        self.array_sort_ids.insert((index, element), id);
        Ok(id)
    }

    pub(crate) fn array_signature(&self, sort: ArraySortId) -> Result<ArraySignature, TermError> {
        self.array_sorts
            .get(sort.0 as usize)
            .copied()
            .ok_or_else(|| TermError::new("array sort does not belong to this term store"))
    }

    pub(crate) fn array_axioms(&self) -> &[TermId] {
        &self.array_axioms
    }

    pub(crate) fn select_array_sort(&self, function: FunctionId) -> Option<ArraySortId> {
        self.array_sorts
            .iter()
            .position(|signature| signature.select_function == function)
            .and_then(|index| u32::try_from(index).ok())
            .map(ArraySortId)
    }

    pub(crate) fn const_array(
        &mut self,
        sort: ArraySortId,
        value: TermId,
    ) -> Result<TermId, TermError> {
        let signature = self.array_signature(sort)?;
        if self.sort(value)? != signature.element {
            return Err(TermError::new(
                "constant-array value does not have the array element sort",
            ));
        }
        let sort_id = self.sort_id_for(Sort::Array(sort))?;
        Ok(self.intern(sort_id, TermKind::ArrayConst(value)))
    }

    pub(crate) fn store(
        &mut self,
        array: TermId,
        index: TermId,
        value: TermId,
    ) -> Result<TermId, TermError> {
        let Sort::Array(sort) = self.sort(array)? else {
            return Err(TermError::new("`store` expects an array"));
        };
        let signature = self.array_signature(sort)?;
        if self.sort(index)? != signature.index {
            return Err(TermError::new(
                "`store` index does not have the array index sort",
            ));
        }
        if self.sort(value)? != signature.element {
            return Err(TermError::new(
                "`store` value does not have the array element sort",
            ));
        }
        let sort_id = self.sort_id_for(Sort::Array(sort))?;
        Ok(self.intern(sort_id, TermKind::ArrayStore(array, index, value)))
    }

    pub(crate) fn select(&mut self, array: TermId, index: TermId) -> Result<TermId, TermError> {
        let Sort::Array(sort) = self.sort(array)? else {
            return Err(TermError::new("`select` expects an array"));
        };
        let signature = self.array_signature(sort)?;
        if self.sort(index)? != signature.index {
            return Err(TermError::new(
                "`select` index does not have the array index sort",
            ));
        }
        self.register_array_read(array, index);
        let result = self.apply(signature.select_function, &[array, index])?;
        if self.array_semantic_selects.insert(result) {
            self.array_semantic_select_log.push(result);
            let semantic_value = match self.node(array).kind.clone() {
                TermKind::ArrayConst(value) => Some(value),
                TermKind::ArrayStore(base, stored_index, stored_value) => {
                    let same_index = self.equivalent(stored_index, index)?;
                    let fallback = self.select(base, index)?;
                    Some(self.ite(same_index, stored_value, fallback)?)
                }
                _ => None,
            };
            if let Some(value) = semantic_value {
                let axiom = self.equivalent(result, value)?;
                self.array_axioms.push(axiom);
            }
        }
        Ok(result)
    }

    pub(crate) fn prepare_arrays(&mut self) -> Result<(), TermError> {
        loop {
            let before_applications = self.applications.len();
            let equalities = self
                .theory_equalities
                .iter()
                .filter(|equality| matches!(self.sort(equality.left), Ok(Sort::Array(_))))
                .map(|equality| (equality.left, equality.right))
                .collect::<Vec<_>>();
            for (left, right) in equalities {
                self.share_array_reads(&[left, right])?;
            }

            let ites = self
                .uf_ites
                .iter()
                .filter(|item| matches!(self.sort(item.result), Ok(Sort::Array(_))))
                .map(|item| [item.result, item.then_term, item.else_term])
                .collect::<Vec<_>>();
            for related in ites {
                self.share_array_reads(&related)?;
            }

            let mut application_groups: HashMap<FunctionId, Vec<TermId>> = HashMap::new();
            for application in &self.applications {
                if matches!(self.sort(application.result), Ok(Sort::Array(_))) {
                    application_groups
                        .entry(application.function)
                        .or_default()
                        .push(application.result);
                }
            }
            for related in application_groups.into_values() {
                self.share_array_reads(&related)?;
            }
            if self.applications.len() == before_applications {
                return Ok(());
            }
        }
    }

    fn register_array_read(&mut self, array: TermId, index: TermId) {
        let indices = self.array_reads.entry(array).or_default();
        if !indices.contains(&index) {
            indices.push(index);
            self.array_read_log.push((array, index));
        }
    }

    fn share_array_reads(&mut self, arrays: &[TermId]) -> Result<(), TermError> {
        let mut indices = arrays
            .iter()
            .filter_map(|array| self.array_reads.get(array))
            .flatten()
            .copied()
            .collect::<Vec<_>>();
        indices.sort_unstable();
        indices.dedup();
        for &array in arrays {
            for &index in &indices {
                self.select(array, index)?;
            }
        }
        Ok(())
    }

    pub(crate) fn function_signature(
        &self,
        function: FunctionId,
    ) -> Result<&FunctionSignature, TermError> {
        self.functions
            .get(function.0 as usize)
            .ok_or_else(|| TermError::new("function does not belong to this term store"))
    }

    pub(crate) fn apply(
        &mut self,
        function: FunctionId,
        arguments: &[TermId],
    ) -> Result<TermId, TermError> {
        let signature = self.function_signature(function)?.clone();
        if arguments.len() != signature.domain.len() {
            return Err(TermError::new(format!(
                "function expects {} argument(s), received {}",
                signature.domain.len(),
                arguments.len()
            )));
        }
        for (&argument, &expected) in arguments.iter().zip(signature.domain.iter()) {
            if self.sort(argument)? != expected {
                return Err(TermError::new(
                    "function argument does not have its declared sort",
                ));
            }
        }
        let key = ApplicationKey {
            function,
            arguments: arguments.into(),
        };
        if let Some(&result) = self.application_results.get(&key) {
            return Ok(result);
        }
        let result = match signature.range {
            Sort::Bool => self.fresh_bool_atom().1,
            Sort::BitVec(width) => self.fresh_bitvec(width)?,
            Sort::Int | Sort::Real => self.fresh_arithmetic_variable(signature.range)?,
            Sort::Uninterpreted(_) | Sort::Array(_) => {
                let sort = self.sort_id_for(signature.range)?;
                self.intern(sort, TermKind::UfApplication(function, arguments.into()))
            }
        };
        self.application_results.insert(key, result);
        self.application_by_result
            .insert(result, self.applications.len());
        if matches!(signature.range, Sort::BitVec(_)) {
            let bits = self.bitvec_bits(result)?.to_vec();
            for (index, bit) in bits.into_iter().enumerate() {
                let previous = self.application_by_bit.insert(bit, (result, index));
                debug_assert!(previous.is_none());
            }
        }
        self.applications.push(Application {
            function,
            arguments: arguments.into(),
            result,
        });
        Ok(result)
    }

    pub(crate) fn applications(&self) -> &[Application] {
        &self.applications
    }

    pub(crate) fn application_for_result(&self, term: TermId) -> Option<&Application> {
        self.application_by_result
            .get(&term)
            .and_then(|&index| self.applications.get(index))
    }

    pub(crate) fn application_for_bit(&self, term: TermId) -> Option<(TermId, usize)> {
        self.application_by_bit.get(&term).copied()
    }

    pub(crate) fn theory_equalities(&self) -> &[TheoryEquality] {
        &self.theory_equalities
    }

    pub(crate) fn uf_ites(&self) -> &[UfIte] {
        &self.uf_ites
    }

    pub(crate) fn node(&self, term: TermId) -> &TermNode {
        &self.nodes[term.index()]
    }

    pub(crate) fn fresh_term(&mut self, sort: Sort) -> Result<TermId, TermError> {
        match sort {
            Sort::Bool => Ok(self.fresh_bool_atom().1),
            Sort::BitVec(width) => self.fresh_bitvec(width),
            Sort::Int | Sort::Real => self.fresh_arithmetic_variable(sort),
            Sort::Uninterpreted(_) => {
                let sort_id = self.sort_id_for(sort)?;
                let value = self.next_uninterpreted_value;
                self.next_uninterpreted_value = self
                    .next_uninterpreted_value
                    .checked_add(1)
                    .ok_or_else(|| {
                        TermError::new("uninterpreted-value store exceeds the u32 index")
                    })?;
                Ok(self.intern(sort_id, TermKind::UfConstant(value)))
            }
            Sort::Array(_) => {
                let sort_id = self.sort_id_for(sort)?;
                let value = self.next_uninterpreted_value;
                self.next_uninterpreted_value = self
                    .next_uninterpreted_value
                    .checked_add(1)
                    .ok_or_else(|| TermError::new("abstract-value store exceeds the u32 index"))?;
                Ok(self.intern(sort_id, TermKind::UfConstant(value)))
            }
        }
    }

    #[cfg(test)]
    pub(crate) fn atom(&mut self, symbol: SymbolId) -> TermId {
        self.next_symbol = self.next_symbol.max(symbol.0.saturating_add(1));
        self.intern(self.bool_sort, TermKind::Atom(symbol))
    }

    pub(crate) fn fresh_bool_atom(&mut self) -> (SymbolId, TermId) {
        let symbol = self.fresh_symbol();
        (symbol, self.intern(self.bool_sort, TermKind::Atom(symbol)))
    }

    fn fresh_symbol(&mut self) -> SymbolId {
        let symbol = SymbolId(self.next_symbol);
        self.next_symbol = self
            .next_symbol
            .checked_add(1)
            .expect("Boolean atom store exceeds the supported u32 index");
        symbol
    }

    pub(crate) fn not(&mut self, term: TermId) -> Result<TermId, TermError> {
        self.require_bool(term)?;
        Ok(match self.node(term).kind {
            TermKind::Bool(value) => self.bool_constant(!value),
            TermKind::Not(inner) => inner,
            _ => self.intern(self.bool_sort, TermKind::Not(term)),
        })
    }

    pub(crate) fn and(&mut self, terms: &[TermId]) -> Result<TermId, TermError> {
        self.junction(terms, true, true)
    }

    pub(crate) fn or(&mut self, terms: &[TermId]) -> Result<TermId, TermError> {
        self.junction(terms, false, false)
    }

    fn junction(
        &mut self,
        terms: &[TermId],
        identity: bool,
        conjunction: bool,
    ) -> Result<TermId, TermError> {
        let mut flattened = Vec::new();
        for &term in terms {
            self.require_bool(term)?;
            match &self.node(term).kind {
                TermKind::Bool(value) if *value != identity => {
                    return Ok(self.bool_constant(*value));
                }
                TermKind::Bool(_) => {}
                TermKind::And(nested) if conjunction => flattened.extend_from_slice(nested),
                TermKind::Or(nested) if !conjunction => flattened.extend_from_slice(nested),
                _ => flattened.push(term),
            }
        }
        flattened.sort_unstable();
        flattened.dedup();
        let members = flattened.iter().copied().collect::<HashSet<_>>();
        for &member in &flattened {
            if let TermKind::Not(inner) = self.node(member).kind {
                if members.contains(&inner) {
                    return Ok(self.bool_constant(!identity));
                }
            }
        }
        Ok(match flattened.len() {
            0 => self.bool_constant(identity),
            1 => flattened[0],
            _ if conjunction => {
                self.intern(self.bool_sort, TermKind::And(flattened.into_boxed_slice()))
            }
            _ => self.intern(self.bool_sort, TermKind::Or(flattened.into_boxed_slice())),
        })
    }

    pub(crate) fn xor(&mut self, left: TermId, right: TermId) -> Result<TermId, TermError> {
        self.require_bool(left)?;
        self.require_bool(right)?;
        if left == right {
            return Ok(self.false_term);
        }
        if self.are_complements(left, right) {
            return Ok(self.true_term);
        }
        match (self.node(left).kind.clone(), self.node(right).kind.clone()) {
            (TermKind::Bool(false), _) => Ok(right),
            (_, TermKind::Bool(false)) => Ok(left),
            (TermKind::Bool(true), _) => self.not(right),
            (_, TermKind::Bool(true)) => self.not(left),
            _ => {
                let (first, second) = ordered_pair(left, right);
                Ok(self.intern(self.bool_sort, TermKind::Xor(first, second)))
            }
        }
    }

    pub(crate) fn iff(&mut self, left: TermId, right: TermId) -> Result<TermId, TermError> {
        self.require_bool(left)?;
        self.require_bool(right)?;
        if left == right {
            return Ok(self.true_term);
        }
        if self.are_complements(left, right) {
            return Ok(self.false_term);
        }
        match (self.node(left).kind.clone(), self.node(right).kind.clone()) {
            (TermKind::Bool(true), _) => Ok(right),
            (_, TermKind::Bool(true)) => Ok(left),
            (TermKind::Bool(false), _) => self.not(right),
            (_, TermKind::Bool(false)) => self.not(left),
            _ => {
                let (first, second) = ordered_pair(left, right);
                Ok(self.intern(self.bool_sort, TermKind::Iff(first, second)))
            }
        }
    }

    pub(crate) fn equal(&mut self, terms: &[TermId]) -> Result<TermId, TermError> {
        if terms.len() < 2 {
            return Err(TermError::new("`=` expects at least two arguments"));
        }
        let first_sort = self.sort(terms[0])?;
        let arithmetic = matches!(first_sort, Sort::Int | Sort::Real)
            && terms[1..]
                .iter()
                .all(|&term| matches!(self.sort(term), Ok(Sort::Int | Sort::Real)));
        for &term in &terms[1..] {
            if !arithmetic && self.sort(term)? != first_sort {
                return Err(TermError::new(
                    "all arguments to `=` must have the same sort",
                ));
            }
        }
        let first = terms[0];
        let equalities = terms[1..]
            .iter()
            .map(|&term| self.equivalent(first, term))
            .collect::<Result<Vec<_>, _>>()?;
        self.and(&equalities)
    }

    pub(crate) fn distinct(&mut self, terms: &[TermId]) -> Result<TermId, TermError> {
        if terms.len() < 2 {
            return Err(TermError::new("`distinct` expects at least two arguments"));
        }
        let first_sort = self.sort(terms[0])?;
        let arithmetic = matches!(first_sort, Sort::Int | Sort::Real)
            && terms[1..]
                .iter()
                .all(|&term| matches!(self.sort(term), Ok(Sort::Int | Sort::Real)));
        for &term in &terms[1..] {
            if !arithmetic && self.sort(term)? != first_sort {
                return Err(TermError::new(
                    "all arguments to `distinct` must have the same sort",
                ));
            }
        }
        let mut inequalities = Vec::new();
        for left in 0..terms.len() {
            for right in left + 1..terms.len() {
                let equality = self.equivalent(terms[left], terms[right])?;
                inequalities.push(self.not(equality)?);
            }
        }
        self.and(&inequalities)
    }

    pub(crate) fn equivalent(&mut self, left: TermId, right: TermId) -> Result<TermId, TermError> {
        let left_sort = self.sort(left)?;
        let right_sort = self.sort(right)?;
        if matches!(left_sort, Sort::Int | Sort::Real)
            && matches!(right_sort, Sort::Int | Sort::Real)
        {
            return self.arithmetic_equivalent(left, right);
        }
        if right_sort != left_sort {
            return Err(TermError::new("equality operands have different sorts"));
        }
        match left_sort {
            Sort::Bool => self.iff(left, right),
            Sort::BitVec(_) => {
                let left = self.bitvec_bits(left)?.to_vec();
                let right = self.bitvec_bits(right)?.to_vec();
                let bits = left
                    .into_iter()
                    .zip(right)
                    .map(|(a, b)| self.iff(a, b))
                    .collect::<Result<Vec<_>, _>>()?;
                self.and(&bits)
            }
            Sort::Int | Sort::Real => unreachable!("arithmetic equality handled above"),
            Sort::Uninterpreted(_) => self.theory_equality(left, right),
            Sort::Array(_) => self.theory_equality(left, right),
        }
    }

    fn theory_equality(&mut self, left: TermId, right: TermId) -> Result<TermId, TermError> {
        if left == right {
            return Ok(self.true_term);
        }
        let (left, right) = ordered_pair(left, right);
        if let Some(&term) = self.theory_equality_terms.get(&(left, right)) {
            return Ok(term);
        }
        let symbol = self.fresh_symbol();
        let term = self.intern(
            self.bool_sort,
            TermKind::TheoryEquality(symbol, left, right),
        );
        self.theory_equality_terms.insert((left, right), term);
        self.theory_equalities
            .push(TheoryEquality { term, left, right });
        if let Sort::Array(sort) = self.sort(left)? {
            let signature = self.array_signature(sort)?;
            let witness = self.fresh_term(signature.index)?;
            let left_value = self.select(left, witness)?;
            let right_value = self.select(right, witness)?;
            let values_equal = self.equivalent(left_value, right_value)?;
            let values_differ = self.not(values_equal)?;
            let extensionality = self.or(&[term, values_differ])?;
            self.array_axioms.push(extensionality);
        }
        Ok(term)
    }

    pub(crate) fn implies(&mut self, terms: &[TermId]) -> Result<TermId, TermError> {
        if terms.len() < 2 {
            return Err(TermError::new("`=>` expects at least two arguments"));
        }
        for &term in terms {
            self.require_bool(term)?;
        }
        let mut result = *terms.last().expect("length checked above");
        for &antecedent in terms[..terms.len() - 1].iter().rev() {
            let negated = self.not(antecedent)?;
            result = self.or(&[negated, result])?;
        }
        Ok(result)
    }

    pub(crate) fn ite(
        &mut self,
        condition: TermId,
        then_term: TermId,
        else_term: TermId,
    ) -> Result<TermId, TermError> {
        self.require_bool(condition)?;
        let sort = self.sort(then_term)?;
        let else_sort = self.sort(else_term)?;
        if matches!(sort, Sort::Int | Sort::Real) && matches!(else_sort, Sort::Int | Sort::Real) {
            let common = self.common_arithmetic_sort(&[then_term, else_term])?;
            return match self.node(condition).kind {
                TermKind::Bool(true) => self.coerce_arithmetic_term(then_term, common),
                TermKind::Bool(false) => self.coerce_arithmetic_term(else_term, common),
                _ => self.arithmetic_ite(condition, then_term, else_term),
            };
        }
        if else_sort != sort {
            return Err(TermError::new("`ite` branches must have the same sort"));
        }
        if then_term == else_term {
            return Ok(then_term);
        }
        match sort {
            Sort::Bool => match self.node(condition).kind {
                TermKind::Bool(true) => Ok(then_term),
                TermKind::Bool(false) => Ok(else_term),
                _ if then_term == self.true_term && else_term == self.false_term => Ok(condition),
                _ if then_term == self.false_term && else_term == self.true_term => {
                    self.not(condition)
                }
                _ => Ok(self.intern(
                    self.bool_sort,
                    TermKind::Ite(condition, then_term, else_term),
                )),
            },
            Sort::BitVec(_) => {
                let then_bits = self.bitvec_bits(then_term)?.to_vec();
                let else_bits = self.bitvec_bits(else_term)?.to_vec();
                let bits = then_bits
                    .into_iter()
                    .zip(else_bits)
                    .map(|(then_bit, else_bit)| self.ite(condition, then_bit, else_bit))
                    .collect::<Result<Vec<_>, _>>()?;
                self.make_bitvec(bits)
            }
            Sort::Int | Sort::Real => unreachable!("arithmetic ite handled above"),
            Sort::Uninterpreted(_) | Sort::Array(_) => {
                let sort_id = self.sort_id(then_term)?;
                let result = self.intern(sort_id, TermKind::UfIte(condition, then_term, else_term));
                if !self.uf_ites.iter().any(|item| item.result == result) {
                    self.uf_ites.push(UfIte {
                        result,
                        condition,
                        then_term,
                        else_term,
                    });
                }
                Ok(result)
            }
        }
    }

    pub(crate) fn evaluate_bool(
        &self,
        term: TermId,
        atom_value: impl Fn(SymbolId) -> bool,
    ) -> Result<bool, TermError> {
        self.require_bool(term)?;
        Ok(self.evaluate_bool_unchecked(term, &atom_value, &mut HashMap::new()))
    }

    pub(crate) fn evaluate_bitvec(
        &self,
        term: TermId,
        atom_value: impl Fn(SymbolId) -> bool,
    ) -> Result<Vec<bool>, TermError> {
        let bits = self.bitvec_bits(term)?;
        let mut memo = HashMap::new();
        Ok(bits
            .iter()
            .map(|&bit| self.evaluate_bool_unchecked(bit, &atom_value, &mut memo))
            .collect())
    }

    pub(crate) fn reachable_boolean_terms(
        &self,
        roots: &[TermId],
    ) -> Result<HashSet<TermId>, TermError> {
        let mut reachable = HashSet::new();
        let mut pending = roots.to_vec();
        while let Some(term) = pending.pop() {
            self.require_bool(term)?;
            if !reachable.insert(term) {
                continue;
            }
            match &self.node(term).kind {
                TermKind::Not(inner) => pending.push(*inner),
                TermKind::And(items) | TermKind::Or(items) => {
                    pending.extend(items.iter().copied());
                }
                TermKind::Xor(left, right) | TermKind::Iff(left, right) => {
                    pending.push(*left);
                    pending.push(*right);
                }
                TermKind::Ite(condition, then_term, else_term) => {
                    pending.push(*condition);
                    pending.push(*then_term);
                    pending.push(*else_term);
                }
                TermKind::Bool(_)
                | TermKind::Atom(_)
                | TermKind::TheoryEquality(_, _, _)
                | TermKind::ArithmeticPredicate(_, _, _) => {}
                TermKind::UfConstant(_)
                | TermKind::UfApplication(_, _)
                | TermKind::UfIte(_, _, _)
                | TermKind::Arithmetic(_)
                | TermKind::ArrayConst(_)
                | TermKind::ArrayStore(_, _, _)
                | TermKind::BitVec(_) => {
                    unreachable!("a Boolean circuit cannot contain a non-Boolean node")
                }
            }
        }
        Ok(reachable)
    }

    fn evaluate_bool_unchecked(
        &self,
        term: TermId,
        atom_value: &impl Fn(SymbolId) -> bool,
        memo: &mut HashMap<TermId, bool>,
    ) -> bool {
        if let Some(&value) = memo.get(&term) {
            return value;
        }
        let value = match &self.node(term).kind {
            TermKind::Bool(value) => *value,
            TermKind::Atom(symbol)
            | TermKind::TheoryEquality(symbol, _, _)
            | TermKind::ArithmeticPredicate(symbol, _, _) => atom_value(*symbol),
            TermKind::Not(inner) => !self.evaluate_bool_unchecked(*inner, atom_value, memo),
            TermKind::And(terms) => terms
                .iter()
                .all(|&item| self.evaluate_bool_unchecked(item, atom_value, memo)),
            TermKind::Or(terms) => terms
                .iter()
                .any(|&item| self.evaluate_bool_unchecked(item, atom_value, memo)),
            TermKind::Xor(left, right) => {
                self.evaluate_bool_unchecked(*left, atom_value, memo)
                    != self.evaluate_bool_unchecked(*right, atom_value, memo)
            }
            TermKind::Iff(left, right) => {
                self.evaluate_bool_unchecked(*left, atom_value, memo)
                    == self.evaluate_bool_unchecked(*right, atom_value, memo)
            }
            TermKind::Ite(condition, then_term, else_term) => {
                if self.evaluate_bool_unchecked(*condition, atom_value, memo) {
                    self.evaluate_bool_unchecked(*then_term, atom_value, memo)
                } else {
                    self.evaluate_bool_unchecked(*else_term, atom_value, memo)
                }
            }
            TermKind::UfConstant(_)
            | TermKind::UfApplication(_, _)
            | TermKind::UfIte(_, _, _)
            | TermKind::Arithmetic(_)
            | TermKind::ArrayConst(_)
            | TermKind::ArrayStore(_, _, _)
            | TermKind::BitVec(_) => {
                unreachable!("non-Boolean term cannot occur in Boolean circuit")
            }
        };
        memo.insert(term, value);
        value
    }

    pub(crate) fn bitvec_bits(&self, term: TermId) -> Result<&[TermId], TermError> {
        let node = self
            .nodes
            .get(term.index())
            .ok_or_else(|| TermError::new("term does not belong to this term store"))?;
        let TermKind::BitVec(bits) = &node.kind else {
            return Err(TermError::new("expected a bit-vector term"));
        };
        Ok(bits)
    }

    pub(crate) fn make_bitvec(&mut self, bits: Vec<TermId>) -> Result<TermId, TermError> {
        if bits.is_empty() {
            return Err(TermError::new("bit-vector width must be greater than zero"));
        }
        for &bit in &bits {
            self.require_bool(bit)?;
        }
        let width = u32::try_from(bits.len())
            .map_err(|_| TermError::new("bit-vector width exceeds the supported u32 size"))?;
        let sort = self.sort_id_for(Sort::BitVec(width))?;
        Ok(self.intern(sort, TermKind::BitVec(bits.into_boxed_slice())))
    }

    pub(crate) fn require_bool(&self, term: TermId) -> Result<(), TermError> {
        if self.sort_id(term)? == self.bool_sort {
            Ok(())
        } else {
            Err(TermError::new("expected a term of sort Bool"))
        }
    }

    fn are_complements(&self, left: TermId, right: TermId) -> bool {
        matches!(self.node(left).kind, TermKind::Not(inner) if inner == right)
            || matches!(self.node(right).kind, TermKind::Not(inner) if inner == left)
    }

    pub(crate) fn intern(&mut self, sort: SortId, kind: TermKind) -> TermId {
        let node = TermNode { sort, kind };
        if let Some(&term) = self.interned.get(&node) {
            return term;
        }
        let term = TermId(
            u32::try_from(self.nodes.len()).expect("term store exceeds the supported u32 index"),
        );
        self.nodes.push(node.clone());
        self.interned.insert(node, term);
        term
    }
}

fn ordered_pair(left: TermId, right: TermId) -> (TermId, TermId) {
    if left <= right {
        (left, right)
    } else {
        (right, left)
    }
}

#[cfg(test)]
mod tests {
    use super::{Sort, SymbolId, TermStore};

    #[test]
    fn hash_consing_and_boolean_canonicalization_are_stable() {
        let mut terms = TermStore::new();
        let a = terms.atom(SymbolId(0));
        let b = terms.atom(SymbolId(1));
        assert_eq!(terms.and(&[a, b]).unwrap(), terms.and(&[b, a]).unwrap());
        assert_eq!(terms.xor(a, b).unwrap(), terms.xor(b, a).unwrap());
        let not_a = terms.not(a).unwrap();
        assert_eq!(terms.and(&[a, not_a]).unwrap(), terms.bool_constant(false));
        assert_eq!(terms.or(&[]).unwrap(), terms.bool_constant(false));
    }

    #[test]
    fn evaluates_shared_terms() {
        let mut terms = TermStore::new();
        let a = terms.atom(SymbolId(0));
        let b = terms.atom(SymbolId(1));
        let xor = terms.xor(a, b).unwrap();
        let formula = terms.ite(a, xor, b).unwrap();
        assert!(
            terms
                .evaluate_bool(formula, |symbol| symbol == SymbolId(1))
                .unwrap()
        );
        assert!(!terms.evaluate_bool(formula, |_| false).unwrap());
    }

    #[test]
    fn generic_equality_and_ite_preserve_bitvector_sorts() {
        let mut terms = TermStore::new();
        let a = terms.fresh_bitvec(3).unwrap();
        let b = terms.fresh_bitvec(3).unwrap();
        let condition = terms.equal(&[a, b]).unwrap();
        assert_eq!(terms.sort(condition).unwrap(), Sort::Bool);
        let selected = terms.ite(condition, a, b).unwrap();
        assert_eq!(terms.sort(selected).unwrap(), Sort::BitVec(3));
    }

    #[test]
    fn checkpoint_restores_array_demand_and_hash_consing_state() {
        let mut terms = TermStore::new();
        let array_sort = terms.array_sort(Sort::BitVec(1), Sort::BitVec(1)).unwrap();
        let array = terms.fresh_term(Sort::Array(array_sort)).unwrap();
        let index = terms.fresh_term(Sort::BitVec(1)).unwrap();
        let checkpoint = terms.checkpoint();
        let baseline = (
            terms.nodes.len(),
            terms.applications.len(),
            terms.array_axioms.len(),
            terms.array_reads.len(),
            terms.array_semantic_selects.len(),
        );

        let selected = terms.select(array, index).unwrap();
        assert!(terms.array_reads.contains_key(&array));
        assert!(terms.array_semantic_selects.contains(&selected));
        terms.rollback(checkpoint);

        assert_eq!(
            (
                terms.nodes.len(),
                terms.applications.len(),
                terms.array_axioms.len(),
                terms.array_reads.len(),
                terms.array_semantic_selects.len(),
            ),
            baseline
        );
        assert_eq!(terms.select(array, index).unwrap(), selected);
    }

    #[test]
    fn checkpoint_restores_bitvector_application_bit_index() {
        let mut terms = TermStore::new();
        let function = terms
            .declare_function(&[Sort::Bool], Sort::BitVec(2))
            .unwrap();
        let argument = terms.bool_constant(false);
        let checkpoint = terms.checkpoint();

        let application = terms.apply(function, &[argument]).unwrap();
        let bits = terms.bitvec_bits(application).unwrap().to_vec();
        for (index, &bit) in bits.iter().enumerate() {
            assert_eq!(terms.application_for_bit(bit), Some((application, index)));
        }

        terms.rollback(checkpoint);
        for &bit in &bits {
            assert_eq!(terms.application_for_bit(bit), None);
        }

        assert_eq!(terms.apply(function, &[argument]).unwrap(), application);
        for (index, &bit) in bits.iter().enumerate() {
            assert_eq!(terms.application_for_bit(bit), Some((application, index)));
        }
    }
}
