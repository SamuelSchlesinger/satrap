use std::collections::{HashMap, HashSet, VecDeque};

use super::term::{Application, FunctionId, Sort, TermError, TermId, TermStore};
use super::theory::{SignedTerm, Theory, TheoryCheck, TheoryLemma, TheoryPropagation};

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct CongruenceKey {
    function: FunctionId,
    arguments: Vec<ArgumentValue>,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum ArgumentValue {
    Abstract(usize),
    Bool(bool),
    BitVec(Vec<bool>),
}

#[derive(Clone, Debug, Default)]
pub(crate) struct UfModel {
    values: HashMap<TermId, u32>,
}

impl UfModel {
    pub(crate) fn value(&self, term: TermId) -> Option<u32> {
        self.values.get(&term).copied()
    }
}

#[derive(Debug, Default)]
pub(crate) struct UfTheory {
    required: Vec<TermId>,
    assignments: HashMap<TermId, bool>,
    levels: Vec<usize>,
    trail: Vec<(TermId, Option<bool>)>,
}

impl Theory for UfTheory {
    type Model = UfModel;

    fn prepare(
        &mut self,
        terms: &mut TermStore,
        _relevant: &HashSet<TermId>,
    ) -> Result<(), TermError> {
        terms.prepare_arrays()?;
        self.required.clear();
        let mut function_counts = HashMap::<FunctionId, usize>::new();
        for application in terms.applications() {
            *function_counts.entry(application.function).or_default() += 1;
        }
        for application in terms.applications() {
            if function_counts[&application.function] < 2 {
                continue;
            }
            let signature = terms.function_signature(application.function)?.clone();
            if signature
                .domain
                .iter()
                .chain(std::iter::once(&signature.range))
                .any(|sort| matches!(sort, Sort::Int | Sort::Real))
            {
                return Err(TermError::new(
                    "UF/arithmetic combination is not enabled until shared equality is prepared",
                ));
            }
            for (&argument, &sort) in application.arguments.iter().zip(signature.domain.iter()) {
                self.require_lowered_value(terms, argument, sort)?;
            }
            self.require_lowered_value(terms, application.result, signature.range)?;
        }
        self.required.extend(
            terms
                .theory_equalities()
                .iter()
                .map(|equality| equality.term),
        );
        self.required
            .extend(terms.uf_ites().iter().map(|item| item.condition));
        self.required.extend_from_slice(terms.array_axioms());
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
        for &axiom in terms.array_axioms() {
            if !self.value(axiom) {
                return TheoryCheck::Conflict(TheoryLemma {
                    literals: vec![SignedTerm::positive(axiom)],
                });
            }
        }
        let uninterpreted_terms = terms
            .nodes
            .iter()
            .enumerate()
            .filter_map(|(index, _)| {
                let term = TermId::from_index(index)?;
                matches!(
                    terms.sort(term),
                    Ok(Sort::Uninterpreted(_) | Sort::Array(_))
                )
                .then_some(term)
            })
            .collect::<Vec<_>>();
        let mut closure = Closure::new(&uninterpreted_terms);
        for equality in terms.theory_equalities() {
            if self.value(equality.term) {
                closure.union(
                    equality.left,
                    equality.right,
                    vec![SignedTerm::positive(equality.term)],
                );
            }
        }
        for item in terms.uf_ites() {
            let condition = self.value(item.condition);
            closure.union(
                item.result,
                if condition {
                    item.then_term
                } else {
                    item.else_term
                },
                vec![SignedTerm {
                    term: item.condition,
                    positive: condition,
                }],
            );
        }

        loop {
            let mut changed = false;
            let mut representatives = HashMap::<CongruenceKey, usize>::new();
            for (right_index, right) in terms.applications().iter().enumerate() {
                let signature = terms
                    .function_signature(right.function)
                    .expect("applications have declared functions");
                let key = self.congruence_key(terms, right, signature.domain.as_ref(), &closure);
                let Some(&left_index) = representatives.get(&key) else {
                    representatives.insert(key, right_index);
                    continue;
                };
                let left = &terms.applications()[left_index];
                let reason = self
                    .congruence_reason(terms, left, right, signature.domain.as_ref(), &closure)
                    .expect("applications with the same congruence key have equal arguments");
                if matches!(signature.range, Sort::Uninterpreted(_) | Sort::Array(_)) {
                    changed |= closure.union(left.result, right.result, reason);
                } else if let Some(conflict) = self.lowered_result_conflict(
                    terms,
                    left.result,
                    right.result,
                    signature.range,
                    reason,
                ) {
                    return TheoryCheck::Conflict(conflict);
                }
            }
            if !changed {
                break;
            }
        }

        for equality in terms.theory_equalities() {
            if !self.value(equality.term) && closure.equivalent(equality.left, equality.right) {
                let reason = closure.explain(equality.left, equality.right);
                return TheoryCheck::Conflict(conflict_lemma(
                    reason,
                    SignedTerm::positive(equality.term),
                ));
            }
        }

        TheoryCheck::Consistent(closure.model(terms))
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

impl UfTheory {
    fn require_lowered_value(
        &mut self,
        terms: &TermStore,
        term: TermId,
        sort: Sort,
    ) -> Result<(), TermError> {
        match sort {
            Sort::Bool => self.required.push(term),
            Sort::BitVec(_) => self.required.extend_from_slice(terms.bitvec_bits(term)?),
            Sort::Int | Sort::Real => {
                unreachable!("arithmetic applications are rejected during preparation")
            }
            Sort::Uninterpreted(_) | Sort::Array(_) => {}
        }
        Ok(())
    }

    fn value(&self, term: TermId) -> bool {
        self.assignments.get(&term).copied().unwrap_or(false)
    }

    fn congruence_key(
        &self,
        terms: &TermStore,
        application: &Application,
        domain: &[Sort],
        closure: &Closure,
    ) -> CongruenceKey {
        let arguments = application
            .arguments
            .iter()
            .zip(domain)
            .map(|(&argument, &sort)| match sort {
                Sort::Uninterpreted(_) | Sort::Array(_) => {
                    ArgumentValue::Abstract(closure.class(argument))
                }
                Sort::Bool => ArgumentValue::Bool(self.value(argument)),
                Sort::BitVec(_) => ArgumentValue::BitVec(
                    terms
                        .bitvec_bits(argument)
                        .expect("application arguments have their declared sort")
                        .iter()
                        .map(|&bit| self.value(bit))
                        .collect(),
                ),
                Sort::Int | Sort::Real => {
                    unreachable!("arithmetic applications are rejected during preparation")
                }
            })
            .collect();
        CongruenceKey {
            function: application.function,
            arguments,
        }
    }

    fn congruence_reason(
        &self,
        terms: &TermStore,
        left: &Application,
        right: &Application,
        domain: &[Sort],
        closure: &Closure,
    ) -> Option<Vec<SignedTerm>> {
        let mut reason = Vec::new();
        for ((&left, &right), &sort) in left
            .arguments
            .iter()
            .zip(right.arguments.iter())
            .zip(domain)
        {
            match sort {
                Sort::Uninterpreted(_) | Sort::Array(_) => {
                    if !closure.equivalent(left, right) {
                        return None;
                    }
                    reason.extend(closure.explain(left, right));
                }
                Sort::Bool | Sort::BitVec(_) => {
                    let left_bits = lowered_bits(terms, left, sort);
                    let right_bits = lowered_bits(terms, right, sort);
                    for (&left_bit, right_bit) in left_bits.iter().zip(right_bits) {
                        let left_value = self.value(left_bit);
                        let right_value = self.value(right_bit);
                        if left_value != right_value {
                            return None;
                        }
                        reason.push(SignedTerm {
                            term: left_bit,
                            positive: left_value,
                        });
                        reason.push(SignedTerm {
                            term: right_bit,
                            positive: right_value,
                        });
                    }
                }
                Sort::Int | Sort::Real => {
                    unreachable!("arithmetic applications are rejected during preparation")
                }
            }
        }
        deduplicate(&mut reason);
        Some(reason)
    }

    fn lowered_result_conflict(
        &self,
        terms: &TermStore,
        left_result: TermId,
        right_result: TermId,
        range: Sort,
        mut reason: Vec<SignedTerm>,
    ) -> Option<TheoryLemma> {
        let left = lowered_bits(terms, left_result, range);
        let right = lowered_bits(terms, right_result, range);
        for (&left, right) in left.iter().zip(right) {
            let left_value = self.value(left);
            let right_value = self.value(right);
            if left_value != right_value {
                reason.push(SignedTerm {
                    term: right,
                    positive: right_value,
                });
                return Some(conflict_lemma(
                    reason,
                    SignedTerm {
                        term: left,
                        positive: right_value,
                    },
                ));
            }
        }
        None
    }
}

fn lowered_bits(terms: &TermStore, term: TermId, sort: Sort) -> Vec<TermId> {
    match sort {
        Sort::Bool => vec![term],
        Sort::BitVec(_) => terms
            .bitvec_bits(term)
            .expect("congruence terms have their declared sort")
            .to_vec(),
        Sort::Int | Sort::Real => {
            unreachable!("arithmetic applications are rejected during preparation")
        }
        Sort::Uninterpreted(_) | Sort::Array(_) => Vec::new(),
    }
}

fn conflict_lemma(mut explanation: Vec<SignedTerm>, consequence: SignedTerm) -> TheoryLemma {
    deduplicate(&mut explanation);
    let mut literals = explanation
        .into_iter()
        .map(SignedTerm::negate)
        .collect::<Vec<_>>();
    literals.push(consequence);
    deduplicate(&mut literals);
    TheoryLemma { literals }
}

fn deduplicate(terms: &mut Vec<SignedTerm>) {
    let mut seen = HashSet::new();
    terms.retain(|term| seen.insert(*term));
}

#[derive(Clone, Debug)]
struct Edge {
    to: usize,
    reason: Vec<SignedTerm>,
}

#[derive(Debug)]
struct Closure {
    terms: Vec<TermId>,
    indices: HashMap<TermId, usize>,
    parent: Vec<usize>,
    rank: Vec<u8>,
    graph: Vec<Vec<Edge>>,
}

impl Closure {
    fn new(terms: &[TermId]) -> Self {
        let indices = terms
            .iter()
            .enumerate()
            .map(|(index, &term)| (term, index))
            .collect();
        Self {
            terms: terms.to_vec(),
            indices,
            parent: (0..terms.len()).collect(),
            rank: vec![0; terms.len()],
            graph: vec![Vec::new(); terms.len()],
        }
    }

    fn find(&self, mut index: usize) -> usize {
        while self.parent[index] != index {
            index = self.parent[index];
        }
        index
    }

    fn equivalent(&self, left: TermId, right: TermId) -> bool {
        let left = self.indices[&left];
        let right = self.indices[&right];
        self.find(left) == self.find(right)
    }

    fn class(&self, term: TermId) -> usize {
        self.find(self.indices[&term])
    }

    fn union(&mut self, left: TermId, right: TermId, mut reason: Vec<SignedTerm>) -> bool {
        let left = self.indices[&left];
        let right = self.indices[&right];
        let mut left_root = self.find(left);
        let mut right_root = self.find(right);
        if left_root == right_root {
            return false;
        }
        deduplicate(&mut reason);
        self.graph[left].push(Edge {
            to: right,
            reason: reason.clone(),
        });
        self.graph[right].push(Edge { to: left, reason });
        if self.rank[left_root] < self.rank[right_root] {
            std::mem::swap(&mut left_root, &mut right_root);
        }
        self.parent[right_root] = left_root;
        if self.rank[left_root] == self.rank[right_root] {
            self.rank[left_root] = self.rank[left_root].saturating_add(1);
        }
        true
    }

    fn explain(&self, left: TermId, right: TermId) -> Vec<SignedTerm> {
        if left == right {
            return Vec::new();
        }
        let start = self.indices[&left];
        let goal = self.indices[&right];
        let mut queue = VecDeque::from([start]);
        let mut previous = vec![None; self.terms.len()];
        previous[start] = Some((start, 0));
        while let Some(node) = queue.pop_front() {
            if node == goal {
                break;
            }
            for (edge_index, edge) in self.graph[node].iter().enumerate() {
                if previous[edge.to].is_none() {
                    previous[edge.to] = Some((node, edge_index));
                    queue.push_back(edge.to);
                }
            }
        }
        debug_assert!(
            previous[goal].is_some(),
            "equivalent terms need an explanation path"
        );
        let mut explanation = Vec::new();
        let mut node = goal;
        while node != start {
            let (parent, edge_index) = previous[node].expect("path established above");
            explanation.extend(self.graph[parent][edge_index].reason.iter().copied());
            node = parent;
        }
        deduplicate(&mut explanation);
        explanation
    }

    fn model(&self, terms: &TermStore) -> UfModel {
        let mut class_values = HashMap::new();
        let mut next_by_sort = HashMap::<Sort, u32>::new();
        let mut values = HashMap::new();
        for (index, &term) in self.terms.iter().enumerate() {
            let sort = terms.sort(term).expect("closure contains valid terms");
            let root = self.find(index);
            let value = *class_values.entry((sort, root)).or_insert_with(|| {
                let next = next_by_sort.entry(sort).or_default();
                let value = *next;
                *next = next.saturating_add(1);
                value
            });
            values.insert(term, value);
        }
        UfModel { values }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::super::theory::{TheoryCheck, TheoryManager};
    use super::*;

    #[test]
    fn congruence_and_transitivity_produce_a_compact_conflict() {
        let mut terms = TermStore::new();
        let sort = Sort::Uninterpreted(terms.fresh_uninterpreted_sort().unwrap());
        let a = terms.fresh_term(sort).unwrap();
        let b = terms.fresh_term(sort).unwrap();
        let c = terms.fresh_term(sort).unwrap();
        let function = terms.declare_function(&[sort], sort).unwrap();
        let fa = terms.apply(function, &[a]).unwrap();
        let fc = terms.apply(function, &[c]).unwrap();
        let ab = terms.equivalent(a, b).unwrap();
        let bc = terms.equivalent(b, c).unwrap();
        let disequality = terms.equivalent(fa, fc).unwrap();

        let mut manager = TheoryManager::default();
        let required = manager.prepare(&mut terms, &[ab, bc, disequality]).unwrap();
        let mut values = required
            .required
            .into_iter()
            .map(|term| (term, false))
            .collect::<HashMap<_, _>>();
        values.insert(ab, true);
        values.insert(bc, true);
        values.insert(disequality, false);

        let TheoryCheck::Conflict(lemma) = manager.check_model(&terms, &values) else {
            panic!("disequal applications with equal arguments must conflict");
        };
        assert!(lemma.literals.contains(&SignedTerm::positive(ab).negate()));
        assert!(lemma.literals.contains(&SignedTerm::positive(bc).negate()));
        assert!(lemma.literals.contains(&SignedTerm::positive(disequality)));
        assert_eq!(lemma.literals.len(), 3);
    }

    #[test]
    fn uninterpreted_ite_selects_exactly_one_branch() {
        let mut terms = TermStore::new();
        let sort = Sort::Uninterpreted(terms.fresh_uninterpreted_sort().unwrap());
        let condition = terms.fresh_term(Sort::Bool).unwrap();
        let a = terms.fresh_term(sort).unwrap();
        let b = terms.fresh_term(sort).unwrap();
        let selected = terms.ite(condition, a, b).unwrap();
        let equals_a = terms.equivalent(selected, a).unwrap();
        let equals_b = terms.equivalent(selected, b).unwrap();

        let mut manager = TheoryManager::default();
        let required = manager
            .prepare(&mut terms, &[condition, equals_a, equals_b])
            .unwrap();
        let mut values = required
            .required
            .into_iter()
            .map(|term| (term, false))
            .collect::<HashMap<_, _>>();
        values.insert(condition, true);
        values.insert(equals_a, false);
        values.insert(equals_b, true);
        let TheoryCheck::Conflict(lemma) = manager.check_model(&terms, &values) else {
            panic!("a true condition must make the ite equal its then branch");
        };
        assert_eq!(
            lemma.literals,
            [
                SignedTerm::positive(condition).negate(),
                SignedTerm::positive(equals_a)
            ]
        );
    }
}
