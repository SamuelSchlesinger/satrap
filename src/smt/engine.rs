use std::collections::HashMap;
use std::error::Error;
use std::fmt;

use crate::{IncrementalError, Lit, Model, SolveLimits, SolveResult, Solver, UnknownReason};

use super::encode::BoolEncoder;
use super::term::{TermError, TermStore};
use super::theory::{SignedTerm, TheoryCheck, TheoryManager, TheoryModel};
use super::validate::validate_model;

#[derive(Clone, Debug)]
pub(crate) enum SmtSolveResult {
    Sat { boolean: Model, theory: TheoryModel },
    Unsat,
    Unknown(UnknownReason),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum SmtEngineError {
    Term(TermError),
    Incremental(IncrementalError),
}

impl fmt::Display for SmtEngineError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Term(error) => error.fmt(formatter),
            Self::Incremental(error) => error.fmt(formatter),
        }
    }
}

impl Error for SmtEngineError {}

impl From<TermError> for SmtEngineError {
    fn from(error: TermError) -> Self {
        Self::Term(error)
    }
}

impl From<IncrementalError> for SmtEngineError {
    fn from(error: IncrementalError) -> Self {
        Self::Incremental(error)
    }
}

pub(crate) fn solve(
    terms: &mut TermStore,
    solver: &mut Solver,
    encoder: &mut BoolEncoder,
    theories: &mut TheoryManager,
    roots: &[super::term::TermId],
    assumptions: &[Lit],
    limits: SolveLimits,
) -> Result<SmtSolveResult, SmtEngineError> {
    let preparation = theories.prepare(terms, roots)?;
    for axiom in preparation.axioms {
        let literal = encoder.encode(terms, solver, axiom)?;
        solver.add_theory_clause(&[literal])?;
    }
    theories.acknowledge_array_axioms(preparation.array_axiom_count);
    let validation_terms = preparation.required.clone();
    let required_literals = preparation
        .required
        .iter()
        .map(|&term| Ok((term, encoder.encode(terms, solver, term)?)))
        .collect::<Result<Vec<_>, IncrementalError>>()?;
    let initial_work = solver.work_counters();

    loop {
        let current_work = solver.work_counters();
        let result = solver.solve_assuming_with_limits(
            assumptions,
            remaining_limits(limits, initial_work, current_work),
        );
        let SolveResult::Sat(model) = result else {
            return Ok(match result {
                SolveResult::Unsat => SmtSolveResult::Unsat,
                SolveResult::Unknown(reason) => SmtSolveResult::Unknown(reason),
                SolveResult::Sat(_) => unreachable!("handled above"),
            });
        };
        let values = required_literals
            .iter()
            .map(|&(term, literal)| (term, model.literal_value(literal)))
            .collect::<HashMap<_, _>>();
        match theories.check_model(terms, &values) {
            TheoryCheck::Consistent(theory) => {
                let validation =
                    validate_model(terms, &theory, roots, &validation_terms, |symbol| {
                        encoder
                            .atom_literal(symbol)
                            .is_some_and(|literal| model.literal_value(literal))
                    });
                if validation.is_err() {
                    return Ok(SmtSolveResult::Unknown(
                        UnknownReason::ModelValidationFailure,
                    ));
                }
                return Ok(SmtSolveResult::Sat {
                    boolean: model,
                    theory,
                });
            }
            TheoryCheck::Unknown(reason) => return Ok(SmtSolveResult::Unknown(reason)),
            TheoryCheck::Conflict(lemma) => {
                debug_assert!(
                    lemma
                        .literals
                        .iter()
                        .all(|&literal| !signed_value(terms, encoder, &model, literal)),
                    "a theory conflict lemma must block the current Boolean model"
                );
                let clause = lemma
                    .literals
                    .iter()
                    .map(|literal| {
                        let encoded = encoder.encode(terms, solver, literal.term)?;
                        Ok(if literal.positive { encoded } else { !encoded })
                    })
                    .collect::<Result<Vec<_>, IncrementalError>>()?;
                solver.add_theory_clause(&clause)?;
            }
        }
    }
}

fn signed_value(
    terms: &TermStore,
    encoder: &BoolEncoder,
    model: &Model,
    literal: SignedTerm,
) -> bool {
    let value = terms
        .evaluate_bool(literal.term, |symbol| {
            encoder
                .atom_literal(symbol)
                .is_some_and(|atom| model.literal_value(atom))
        })
        .expect("theory lemmas contain Boolean terms");
    value == literal.positive
}

fn remaining_limits(limits: SolveLimits, initial: (u64, u64), current: (u64, u64)) -> SolveLimits {
    SolveLimits {
        conflicts: limits
            .conflicts
            .map(|limit| limit.saturating_sub(current.0.saturating_sub(initial.0))),
        propagations: limits
            .propagations
            .map(|limit| limit.saturating_sub(current.1.saturating_sub(initial.1))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::SolveResult;
    use crate::smt::term::Sort;

    #[test]
    fn lazy_theory_lemmas_refine_a_boolean_model_to_unsat() {
        let mut terms = TermStore::new();
        let sort = Sort::Uninterpreted(terms.fresh_uninterpreted_sort().unwrap());
        let a = terms.fresh_term(sort).unwrap();
        let b = terms.fresh_term(sort).unwrap();
        let function = terms.declare_function(&[sort], sort).unwrap();
        let fa = terms.apply(function, &[a]).unwrap();
        let fb = terms.apply(function, &[b]).unwrap();
        let arguments_equal = terms.equivalent(a, b).unwrap();
        let results_equal = terms.equivalent(fa, fb).unwrap();
        let results_differ = terms.not(results_equal).unwrap();

        let mut solver = Solver::new();
        let mut encoder = BoolEncoder::default();
        let argument_literal = encoder
            .encode(&terms, &mut solver, arguments_equal)
            .unwrap();
        let result_literal = encoder.encode(&terms, &mut solver, results_differ).unwrap();
        solver.try_add_clause(&[argument_literal]).unwrap();
        solver.try_add_clause(&[result_literal]).unwrap();
        let mut theories = TheoryManager::default();

        assert!(matches!(
            solve(
                &mut terms,
                &mut solver,
                &mut encoder,
                &mut theories,
                &[arguments_equal, results_differ],
                &[],
                SolveLimits::default()
            )
            .unwrap(),
            SmtSolveResult::Unsat
        ));
        assert_eq!(solver.solve(), SolveResult::Unsat);
    }

    #[test]
    fn extensionally_equal_arrays_are_congruent_function_arguments() {
        let mut terms = TermStore::new();
        let array_sort = terms.array_sort(Sort::Int, Sort::Int).unwrap();
        let array = terms.fresh_term(Sort::Array(array_sort)).unwrap();
        let index = terms.fresh_term(Sort::Int).unwrap();
        let selected = terms.select(array, index).unwrap();
        let restored = terms.store(array, index, selected).unwrap();
        let observe = terms
            .declare_function(&[Sort::Array(array_sort)], Sort::Bool)
            .unwrap();
        let observed_array = terms.apply(observe, &[array]).unwrap();
        let observed_restored = terms.apply(observe, &[restored]).unwrap();
        let different = terms.xor(observed_array, observed_restored).unwrap();

        let mut solver = Solver::new();
        let mut encoder = BoolEncoder::default();
        let different_literal = encoder.encode(&terms, &mut solver, different).unwrap();
        solver.try_add_clause(&[different_literal]).unwrap();
        let mut theories = TheoryManager::default();

        assert!(matches!(
            solve(
                &mut terms,
                &mut solver,
                &mut encoder,
                &mut theories,
                &[different],
                &[],
                SolveLimits::default()
            )
            .unwrap(),
            SmtSolveResult::Unsat
        ));
    }
}
