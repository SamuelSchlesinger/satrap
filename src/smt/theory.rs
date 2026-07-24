use std::collections::{HashMap, HashSet};

use crate::UnknownReason;

use super::arithmetic::{ArithmeticModel, ArithmeticTheory};
use super::term::{TermError, TermId, TermStore};
use super::uf::{UfModel, UfTheory};

/// A Boolean term used positively or negatively in a theory lemma.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) struct SignedTerm {
    pub(crate) term: TermId,
    pub(crate) positive: bool,
}

impl SignedTerm {
    pub(crate) const fn positive(term: TermId) -> Self {
        Self {
            term,
            positive: true,
        }
    }

    pub(crate) const fn negate(self) -> Self {
        Self {
            term: self.term,
            positive: !self.positive,
        }
    }
}

/// A clause that is valid in a theory and can be learned by the SAT engine.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct TheoryLemma {
    pub(crate) literals: Vec<SignedTerm>,
}

/// A theory propagation together with the assignments that explain it.
///
/// The current model-based integration learns the corresponding clause at a
/// complete Boolean assignment. Keeping propagation explicit in the boundary
/// allows a later trail-level integration without changing a theory solver.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct TheoryPropagation {
    pub(crate) consequence: SignedTerm,
    pub(crate) explanation: Vec<SignedTerm>,
}

#[derive(Clone, Debug)]
pub(crate) enum TheoryCheck<M> {
    Consistent(M),
    Conflict(TheoryLemma),
    Unknown(UnknownReason),
}

#[derive(Clone, Debug, Default)]
pub(crate) struct TheoryModel {
    pub(crate) uf: UfModel,
    pub(crate) arithmetic: ArithmeticModel,
}

impl TheoryModel {
    pub(crate) fn value(&self, term: TermId) -> Option<u32> {
        self.uf.value(term)
    }
}

/// Backtrackable CDCL(T) boundary.
///
/// Assignments are reported as signed Boolean terms. A theory may return
/// propagations, a conflict clause, and a model fragment. The first
/// integration uses a single temporary theory level for each complete SAT
/// model; the API is deliberately trail-shaped so theories do not depend on
/// CDCL internals.
pub(crate) trait Theory {
    type Model;

    fn prepare(
        &mut self,
        terms: &mut TermStore,
        relevant: &HashSet<TermId>,
    ) -> Result<(), TermError>;
    fn required_terms(&self, terms: &TermStore) -> Vec<TermId>;
    fn begin_check(&mut self);
    fn push_level(&mut self);
    fn notify_assignment(&mut self, assignment: SignedTerm);
    fn propagate(&mut self, terms: &TermStore) -> Vec<TheoryPropagation>;
    fn final_check(&mut self, terms: &TermStore) -> TheoryCheck<Self::Model>;
    fn backtrack(&mut self, level: usize);
}

#[derive(Debug, Default)]
pub(crate) struct TheoryManager {
    uf: UfTheory,
    arithmetic: ArithmeticTheory,
    installed_array_axioms: usize,
}

impl TheoryManager {
    pub(crate) fn prepare(
        &mut self,
        terms: &mut TermStore,
        roots: &[TermId],
    ) -> Result<TheoryPreparation, TermError> {
        let relevant = terms.reachable_boolean_terms(roots)?;
        self.uf.prepare(terms, &relevant)?;
        self.arithmetic.prepare(terms, &relevant)?;
        let mut required = self.uf.required_terms(terms);
        required.extend(self.arithmetic.required_terms(terms));
        required.sort_unstable();
        required.dedup();
        let axioms = terms.array_axioms()[self.installed_array_axioms..].to_vec();
        Ok(TheoryPreparation {
            required,
            axioms,
            array_axiom_count: terms.array_axioms().len(),
        })
    }

    pub(crate) fn acknowledge_array_axioms(&mut self, count: usize) {
        self.installed_array_axioms = self.installed_array_axioms.max(count);
    }

    pub(crate) fn check_model(
        &mut self,
        terms: &TermStore,
        values: &HashMap<TermId, bool>,
    ) -> TheoryCheck<TheoryModel> {
        self.uf.begin_check();
        self.arithmetic.begin_check();
        self.uf.push_level();
        self.arithmetic.push_level();
        for (&term, &value) in values {
            let assignment = SignedTerm {
                term,
                positive: value,
            };
            self.uf.notify_assignment(assignment);
            self.arithmetic.notify_assignment(assignment);
        }
        let propagations = self
            .uf
            .propagate(terms)
            .into_iter()
            .chain(self.arithmetic.propagate(terms))
            .collect::<Vec<_>>();
        let result = if let Some(propagation) = propagations.into_iter().next() {
            let mut literals = propagation
                .explanation
                .into_iter()
                .map(SignedTerm::negate)
                .collect::<Vec<_>>();
            literals.push(propagation.consequence);
            TheoryCheck::Conflict(TheoryLemma { literals })
        } else {
            match self.uf.final_check(terms) {
                TheoryCheck::Conflict(conflict) => TheoryCheck::Conflict(conflict),
                TheoryCheck::Unknown(reason) => TheoryCheck::Unknown(reason),
                TheoryCheck::Consistent(uf) => match self.arithmetic.final_check(terms) {
                    TheoryCheck::Conflict(conflict) => TheoryCheck::Conflict(conflict),
                    TheoryCheck::Unknown(reason) => TheoryCheck::Unknown(reason),
                    TheoryCheck::Consistent(arithmetic) => {
                        TheoryCheck::Consistent(TheoryModel { uf, arithmetic })
                    }
                },
            }
        };
        self.uf.backtrack(0);
        self.arithmetic.backtrack(0);
        result
    }
}

/// Boolean terms needed by theory checking and unconditional theory facts that
/// have not yet been installed in the SAT solver.
pub(crate) struct TheoryPreparation {
    pub(crate) required: Vec<TermId>,
    pub(crate) axioms: Vec<TermId>,
    pub(crate) array_axiom_count: usize,
}
