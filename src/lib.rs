//! A performance-oriented conflict-driven clause-learning SAT solver.
//!
//! The crate deliberately keeps the hot path dependency-free. [`Solver`] is a
//! conventional CDCL engine with two-watched-literal propagation, first-UIP
//! learning, EVSIDS/VMTF variable selection, phase saving, ablatable static,
//! dynamic, focused, and stable search regimes, learned-clause reduction,
//! reusable assumption queries, and activation-literal clause scopes.
//! [`dimacs`] contains a strict DIMACS CNF parser.

pub mod dimacs;
mod proof;
pub mod smt;
mod solver;
mod types;

pub use solver::{
    IncrementalError, Interrupter, Model, RestartPolicy, RestartTrailReuse, SearchStrategy,
    SolveLimits, SolveResult, Solver, SolverConfig, SolverStats, UnknownReason,
};
pub use types::{Lit, Var};

#[cfg(test)]
mod tests {
    use super::{Lit, SolveResult, Solver, Var};

    #[test]
    fn public_api_solves_a_tiny_formula() {
        let x = Lit::positive(Var::new(0));
        let y = Lit::positive(Var::new(1));
        let mut solver = Solver::new();
        solver.add_clause(&[x, y]);
        solver.add_clause(&[!x, y]);
        solver.add_clause(&[x, !y]);

        let SolveResult::Sat(model) = solver.solve() else {
            panic!("formula should be satisfiable");
        };
        assert!(model.value(Var::new(0)));
        assert!(model.value(Var::new(1)));
    }
}
