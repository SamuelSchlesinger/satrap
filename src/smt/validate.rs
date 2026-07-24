//! Model checks deliberately separate from the theory-solving algorithms.
//!
//! The arithmetic solver reconstructs a candidate assignment from normalized
//! constraints. This module instead evaluates the original term-store
//! predicates and selected `ite` branches. A disagreement is converted to
//! `unknown`, so an internal reconstruction bug cannot escape as `sat`.

use std::collections::HashSet;

use num_rational::BigRational;
use num_traits::Zero;

use super::arithmetic::ArithmeticVariableId;
use super::term::{Sort, SymbolId, TermError, TermId, TermStore};
use super::theory::TheoryModel;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ModelValidationError {
    Term(TermError),
    FalseRoot(TermId),
    ArithmeticPredicate(TermId),
    ArithmeticIte(TermId),
    NonIntegralVariable(ArithmeticVariableId),
}

impl From<TermError> for ModelValidationError {
    fn from(error: TermError) -> Self {
        Self::Term(error)
    }
}

pub(crate) fn validate_model(
    terms: &TermStore,
    theory: &TheoryModel,
    roots: &[TermId],
    atom_value: impl Fn(SymbolId) -> bool,
) -> Result<(), ModelValidationError> {
    let relevant = terms.reachable_boolean_terms(roots)?;
    validate_integer_values(terms, theory)?;
    validate_arithmetic_ites(terms, theory, &relevant, &atom_value)?;
    validate_arithmetic_predicates(terms, theory, &relevant, &atom_value)?;

    for &root in roots {
        if !terms.evaluate_bool(root, &atom_value)? {
            return Err(ModelValidationError::FalseRoot(root));
        }
    }
    Ok(())
}

fn validate_integer_values(
    terms: &TermStore,
    theory: &TheoryModel,
) -> Result<(), ModelValidationError> {
    for (index, &sort) in terms.arithmetic_variable_sorts().iter().enumerate() {
        if sort != Sort::Int {
            continue;
        }
        let variable = ArithmeticVariableId(
            u32::try_from(index).expect("arithmetic variable indices are bounded by u32"),
        );
        if !theory.arithmetic.variable_value(variable).is_integer() {
            return Err(ModelValidationError::NonIntegralVariable(variable));
        }
    }
    Ok(())
}

fn validate_arithmetic_predicates(
    terms: &TermStore,
    theory: &TheoryModel,
    relevant: &HashSet<TermId>,
    atom_value: &impl Fn(SymbolId) -> bool,
) -> Result<(), ModelValidationError> {
    let zero = BigRational::zero();
    for predicate in terms
        .arithmetic_predicates()
        .iter()
        .filter(|predicate| relevant.contains(&predicate.term))
    {
        let expression = terms.arithmetic_expression(predicate.expression)?;
        let value = theory.arithmetic.expression_value(expression);
        let expected = if predicate.strict {
            value < zero
        } else {
            value <= zero
        };
        let actual = terms.evaluate_bool(predicate.term, atom_value)?;
        if actual != expected {
            return Err(ModelValidationError::ArithmeticPredicate(predicate.term));
        }
    }
    Ok(())
}

fn validate_arithmetic_ites(
    terms: &TermStore,
    theory: &TheoryModel,
    relevant: &HashSet<TermId>,
    atom_value: &impl Fn(SymbolId) -> bool,
) -> Result<(), ModelValidationError> {
    let mut variables = terms
        .arithmetic_predicates()
        .iter()
        .filter(|predicate| relevant.contains(&predicate.term))
        .flat_map(|predicate| {
            terms
                .arithmetic_expression(predicate.expression)
                .expect("arithmetic predicate expressions belong to the term store")
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
            let result = terms.arithmetic_expression_for_term(item.result)?;
            if !result
                .coefficients
                .keys()
                .any(|variable| variables.contains(variable))
            {
                continue;
            }
            selected.insert(index);
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

    for index in selected {
        let item = terms.arithmetic_ites()[index];
        let selected_branch = if terms.evaluate_bool(item.condition, atom_value)? {
            item.then_term
        } else {
            item.else_term
        };
        let result = theory
            .arithmetic
            .expression_value(terms.arithmetic_expression_for_term(item.result)?);
        let branch = theory
            .arithmetic
            .expression_value(terms.arithmetic_expression_for_term(selected_branch)?);
        if result != branch {
            return Err(ModelValidationError::ArithmeticIte(item.result));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::smt::term::TermKind;

    #[test]
    fn validates_predicates_against_exact_expression_values() {
        let mut terms = TermStore::new();
        let x = terms.fresh_term(Sort::Real).unwrap();
        let zero = terms.arithmetic_real(BigRational::zero()).unwrap();
        let less_equal = terms.arithmetic_le(x, zero).unwrap();
        let strict = terms.arithmetic_lt(x, zero).unwrap();
        let TermKind::ArithmeticPredicate(le_symbol, _, _) = terms.node(less_equal).kind else {
            panic!("comparison must be an arithmetic predicate");
        };
        let TermKind::ArithmeticPredicate(strict_symbol, _, _) = terms.node(strict).kind else {
            panic!("comparison must be an arithmetic predicate");
        };
        let model = TheoryModel::default();

        assert!(
            validate_model(&terms, &model, &[less_equal], |symbol| symbol == le_symbol).is_ok()
        );
        assert_eq!(
            validate_model(&terms, &model, &[strict], |symbol| symbol == strict_symbol),
            Err(ModelValidationError::ArithmeticPredicate(strict))
        );
    }

    #[test]
    fn rejects_a_reconstructed_ite_value_from_the_wrong_branch() {
        let mut terms = TermStore::new();
        let (condition_symbol, condition) = terms.fresh_bool_atom();
        let zero = terms.arithmetic_real(BigRational::zero()).unwrap();
        let one = terms
            .arithmetic_real(BigRational::from_integer(1.into()))
            .unwrap();
        let selected = terms.ite(condition, one, zero).unwrap();
        let nonnegative = terms.arithmetic_ge(selected, zero).unwrap();
        let TermKind::ArithmeticPredicate(predicate_symbol, _, _) = terms.node(nonnegative).kind
        else {
            panic!("comparison must be an arithmetic predicate");
        };

        assert!(matches!(
            validate_model(
                &terms,
                &TheoryModel::default(),
                &[nonnegative],
                |symbol| symbol == condition_symbol || symbol == predicate_symbol,
            ),
            Err(ModelValidationError::ArithmeticIte(term)) if term == selected
        ));
    }
}
