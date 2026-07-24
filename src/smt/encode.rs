use std::collections::HashMap;

use crate::{IncrementalError, Lit, Solver};

use super::term::{SymbolId, TermId, TermKind, TermStore};

#[derive(Debug, Default)]
pub(crate) struct BoolEncoder {
    term_literals: HashMap<TermId, Lit>,
    atom_literals: HashMap<SymbolId, Lit>,
    truth_literal: Option<Lit>,
}

impl BoolEncoder {
    pub(crate) fn encode(
        &mut self,
        terms: &TermStore,
        solver: &mut Solver,
        term: TermId,
    ) -> Result<Lit, IncrementalError> {
        if let Some(&literal) = self.term_literals.get(&term) {
            return Ok(literal);
        }
        let kind = terms.node(term).kind.clone();
        let literal = match kind {
            TermKind::Bool(value) => {
                let truth = self.truth_literal(terms, solver)?;
                if value { truth } else { !truth }
            }
            TermKind::Atom(symbol)
            | TermKind::TheoryEquality(symbol, _, _)
            | TermKind::ArithmeticPredicate(symbol, _, _) => {
                if let Some(&literal) = self.atom_literals.get(&symbol) {
                    literal
                } else {
                    let literal = Lit::positive(solver.new_variable()?);
                    self.atom_literals.insert(symbol, literal);
                    literal
                }
            }
            TermKind::Not(inner) => !self.encode(terms, solver, inner)?,
            TermKind::And(items) => {
                let inputs = items
                    .iter()
                    .map(|&item| self.encode(terms, solver, item))
                    .collect::<Result<Vec<_>, _>>()?;
                let output = Lit::positive(solver.new_variable()?);
                for &input in &inputs {
                    solver.add_encoding_clause(&[!output, input])?;
                }
                let mut backward = Vec::with_capacity(inputs.len() + 1);
                backward.push(output);
                backward.extend(inputs.iter().map(|&input| !input));
                solver.add_encoding_clause(&backward)?;
                output
            }
            TermKind::Or(items) => {
                let inputs = items
                    .iter()
                    .map(|&item| self.encode(terms, solver, item))
                    .collect::<Result<Vec<_>, _>>()?;
                let output = Lit::positive(solver.new_variable()?);
                for &input in &inputs {
                    solver.add_encoding_clause(&[!input, output])?;
                }
                let mut backward = Vec::with_capacity(inputs.len() + 1);
                backward.push(!output);
                backward.extend_from_slice(&inputs);
                solver.add_encoding_clause(&backward)?;
                output
            }
            TermKind::Xor(left, right) => {
                let left = self.encode(terms, solver, left)?;
                let right = self.encode(terms, solver, right)?;
                let output = Lit::positive(solver.new_variable()?);
                for clause in [
                    [left, right, !output],
                    [!left, !right, !output],
                    [left, !right, output],
                    [!left, right, output],
                ] {
                    solver.add_encoding_clause(&clause)?;
                }
                output
            }
            TermKind::Iff(left, right) => {
                let left = self.encode(terms, solver, left)?;
                let right = self.encode(terms, solver, right)?;
                let output = Lit::positive(solver.new_variable()?);
                for clause in [
                    [left, right, output],
                    [!left, !right, output],
                    [left, !right, !output],
                    [!left, right, !output],
                ] {
                    solver.add_encoding_clause(&clause)?;
                }
                output
            }
            TermKind::Ite(condition, then_term, else_term) => {
                let condition = self.encode(terms, solver, condition)?;
                let then_term = self.encode(terms, solver, then_term)?;
                let else_term = self.encode(terms, solver, else_term)?;
                let output = Lit::positive(solver.new_variable()?);
                for clause in [
                    [!condition, !then_term, output],
                    [!condition, then_term, !output],
                    [condition, !else_term, output],
                    [condition, else_term, !output],
                ] {
                    solver.add_encoding_clause(&clause)?;
                }
                output
            }
            TermKind::UfConstant(_)
            | TermKind::UfApplication(_, _)
            | TermKind::UfIte(_, _, _)
            | TermKind::Arithmetic(_)
            | TermKind::ArrayConst(_)
            | TermKind::ArrayStore(_, _, _)
            | TermKind::BitVec(_) => {
                unreachable!("only Boolean terms can be encoded as SAT literals")
            }
        };
        self.term_literals.insert(term, literal);
        Ok(literal)
    }

    pub(crate) fn atom_literal(&self, symbol: SymbolId) -> Option<Lit> {
        self.atom_literals.get(&symbol).copied()
    }

    fn truth_literal(
        &mut self,
        _terms: &TermStore,
        solver: &mut Solver,
    ) -> Result<Lit, IncrementalError> {
        if let Some(literal) = self.truth_literal {
            return Ok(literal);
        }
        let literal = Lit::positive(solver.new_variable()?);
        solver.add_encoding_clause(&[literal])?;
        self.truth_literal = Some(literal);
        Ok(literal)
    }
}

#[cfg(test)]
mod tests {
    use crate::{SolveResult, Solver};

    use super::BoolEncoder;
    use crate::smt::term::{SymbolId, TermStore};

    #[test]
    fn tseitin_encoding_matches_boolean_semantics() {
        let mut terms = TermStore::new();
        let a = terms.atom(SymbolId(0));
        let b = terms.atom(SymbolId(1));
        let xor = terms.xor(a, b).unwrap();
        let formula = terms.iff(xor, terms.bool_constant(true)).unwrap();
        let mut solver = Solver::new();
        let mut encoder = BoolEncoder::default();
        let formula_literal = encoder.encode(&terms, &mut solver, formula).unwrap();
        let a_literal = encoder.atom_literal(SymbolId(0)).unwrap();
        let b_literal = encoder.atom_literal(SymbolId(1)).unwrap();

        assert!(
            solver
                .solve_assuming(&[formula_literal, a_literal, !b_literal])
                .is_sat()
        );
        assert_eq!(
            solver.solve_assuming(&[formula_literal, a_literal, b_literal]),
            SolveResult::Unsat
        );
    }
}
