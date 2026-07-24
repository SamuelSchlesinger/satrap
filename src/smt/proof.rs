use std::collections::{HashMap, HashSet};
use std::error::Error;
use std::fmt;
use std::io::{self, Write};
use std::sync::{Arc, Mutex};

use crate::{Lit, SolveResult, Solver};

use super::term::{SymbolId, TermId, TermKind, TermStore};

#[derive(Clone, Debug)]
pub(crate) struct BooleanRefutation {
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
            "(satrap-edrat :version 1 :logic QF_BOOL :variables {} \
             :premises ({premises}) :clauses ({clauses}) :drat {})",
            self.variable_count,
            quote_string(&drat)
        )
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

/// Re-encodes one active QF_BOOL query in a fresh, non-incremental SAT solver.
///
/// Turning every active assertion into a permanent unit avoids the unsound
/// "global empty clause under temporary assumptions" problem. SMT-LIB permits
/// `get-proof` only after a check with an empty explicit assumption set. A
/// proof-specific canonical Boolean DAG makes the CNF independent of term-ID
/// allocation history, so a separate checker can reconstruct it from the
/// original SMT-LIB query before validating the DRAT suffix.
pub(crate) fn prove_boolean_unsat(
    terms: &TermStore,
    roots: &[TermId],
    premises: &[String],
    symbol_names: &HashMap<SymbolId, String>,
) -> Result<BooleanRefutation, ProofError> {
    if roots.len() != premises.len() {
        return Err(ProofError::new(
            "SMT proof roots and rendered premises are inconsistent",
        ));
    }

    let mut canonicalizer = Canonicalizer::default();
    let roots = roots
        .iter()
        .map(|&root| canonicalizer.convert(terms, root, symbol_names))
        .collect::<Result<Vec<_>, _>>()?;

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
    let clauses = solver
        .proof_input()
        .expect("proof recording was enabled")
        .to_vec();
    if let Some(clause) = clauses.iter().find(|clause| {
        !matches!(
            clause.kind,
            crate::solver::ProofClauseKind::Formula | crate::solver::ProofClauseKind::Encoding
        )
    }) {
        return Err(ProofError::new(format!(
            "QF_BOOL proof replay produced an unsupported {:?} clause",
            clause.kind
        )));
    }
    solver.enable_drat_proof(output.clone());

    match solver.solve() {
        SolveResult::Unsat => {}
        SolveResult::Sat(_) => {
            return Err(ProofError::new(
                "fresh Boolean proof replay unexpectedly found a model",
            ));
        }
        SolveResult::Unknown(reason) => {
            return Err(ProofError::new(format!(
                "fresh Boolean proof replay stopped with {reason:?}"
            )));
        }
    }
    if let Some(error) = solver.proof_error() {
        return Err(ProofError::new(format!(
            "could not finish Boolean DRAT proof: {error}"
        )));
    }

    Ok(BooleanRefutation {
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
    Atom(String),
    Not(BoolExpr),
    And(Vec<BoolExpr>),
    Or(Vec<BoolExpr>),
    Xor(BoolExpr, BoolExpr),
    Iff(BoolExpr, BoolExpr),
    Ite(BoolExpr, BoolExpr, BoolExpr),
}

impl BoolExpr {
    fn node(&self) -> &BoolNode {
        &self.0
    }
}

#[derive(Debug, Default)]
struct Canonicalizer {
    converted: HashMap<TermId, BoolExpr>,
    interned: HashMap<BoolNode, BoolExpr>,
}

impl Canonicalizer {
    fn convert(
        &mut self,
        terms: &TermStore,
        term: TermId,
        symbol_names: &HashMap<SymbolId, String>,
    ) -> Result<BoolExpr, ProofError> {
        if let Some(expression) = self.converted.get(&term) {
            return Ok(expression.clone());
        }
        let expression = match terms.node(term).kind.clone() {
            TermKind::Bool(false) => self.intern(BoolNode::False),
            TermKind::Bool(true) => self.intern(BoolNode::True),
            TermKind::Atom(symbol) => {
                let name = symbol_names.get(&symbol).ok_or_else(|| {
                    ProofError::new(format!(
                        "Boolean proof atom {} has no active declaration",
                        symbol.0
                    ))
                })?;
                self.intern(BoolNode::Atom(name.clone()))
            }
            TermKind::Not(inner) => {
                let inner = self.convert(terms, inner, symbol_names)?;
                self.not(inner)
            }
            TermKind::And(items) => {
                let items = items
                    .iter()
                    .map(|&item| self.convert(terms, item, symbol_names))
                    .collect::<Result<Vec<_>, _>>()?;
                self.junction(items, true)
            }
            TermKind::Or(items) => {
                let items = items
                    .iter()
                    .map(|&item| self.convert(terms, item, symbol_names))
                    .collect::<Result<Vec<_>, _>>()?;
                self.junction(items, false)
            }
            TermKind::Xor(left, right) => {
                let left = self.convert(terms, left, symbol_names)?;
                let right = self.convert(terms, right, symbol_names)?;
                self.xor(left, right)
            }
            TermKind::Iff(left, right) => {
                let left = self.convert(terms, left, symbol_names)?;
                let right = self.convert(terms, right, symbol_names)?;
                self.iff(left, right)
            }
            TermKind::Ite(condition, then_term, else_term) => {
                let condition = self.convert(terms, condition, symbol_names)?;
                let then_term = self.convert(terms, then_term, symbol_names)?;
                let else_term = self.convert(terms, else_term, symbol_names)?;
                self.ite(condition, then_term, else_term)
            }
            TermKind::TheoryEquality(_, _, _)
            | TermKind::ArithmeticPredicate(_, _, _)
            | TermKind::UfConstant(_)
            | TermKind::UfApplication(_, _)
            | TermKind::UfIte(_, _, _)
            | TermKind::Arithmetic(_)
            | TermKind::ArrayConst(_)
            | TermKind::ArrayStore(_, _, _)
            | TermKind::BitVec(_) => {
                return Err(ProofError::new(
                    "QF_BOOL proof replay encountered a non-Boolean-theory node",
                ));
            }
        };
        self.converted.insert(term, expression.clone());
        Ok(expression)
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
        let names = HashMap::from([(a_symbol, "a".to_owned()), (b_symbol, "b".to_owned())]);

        let proof = prove_boolean_unsat(
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
            let names = HashMap::from([(a_symbol, "a".to_owned()), (b_symbol, "b".to_owned())]);
            prove_boolean_unsat(
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
