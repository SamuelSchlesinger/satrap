# sat

A performance-oriented CDCL SAT solver and an emerging interactive SMT solver,
written in Rust.

The project has two front ends:

- `sat` solves DIMACS CNF with a modern, incremental CDCL engine.
- `smt` runs a streaming SMT-LIB 2.7 session on top of the same reusable SAT
  kernel.

This is an active solver-research project. The SAT engine is extensively
tested, proof-producing, and benchmarkable. The SMT engine already supports
useful Boolean, bit-vector, uninterpreted-function, and array fragments, but it
is not yet a general or state-of-the-art SMT solver. The
[research roadmap](docs/ROADMAP.md) states the remaining gates and defines
“world class” in measurable terms.

## Highlights

- Incremental CDCL with assumptions, scopes, failed-assumption extraction,
  first-UIP learning, recursive minimization, restarts, and multiple branching
  strategies.
- Compact hot-path data structures: packed watches and reasons, separate binary
  storage, and a contiguous long-clause arena.
- SAT models and streaming DRAT proofs, with independent validation in the
  benchmark workflow.
- Interactive SMT-LIB with `push`/`pop`, `check-sat-assuming`, models, values,
  assignments, named unsat cores, resource limits, and interruption.
- Complete fixed-width QF_BV lowering, congruence closure for QF_UF, and
  extensional arrays, including QF_UFBV, QF_ABV, and QF_AUFBV combinations.
- A typed Rust API for constructing reusable SAT and SMT contexts, including
  exact integer and rational-real terms.
- Reproducible experiment and benchmark tooling that records inputs, versions,
  machine metadata, validation results, and solver disagreements.

See [Architecture](docs/ARCHITECTURE.md) for implementation details and
[SAT implementation and research notes](docs/SAT_RESEARCH.md) for the full
history of retained, promoted, and rejected experiments.

## Quick start

The crate requires Rust 1.85 or newer.

```sh
cargo build --release
cargo test --all-targets
make install-oracles
make install-hooks
```

Solve a DIMACS file:

```sh
target/release/sat example.cnf
```

Read DIMACS from standard input:

```sh
target/release/sat --stats < example.cnf
```

Write a DRAT proof for an UNSAT instance:

```sh
target/release/sat --proof result.drat example.cnf
```

The SAT executable follows competition conventions: exit code `10` means SAT,
`20` means UNSAT, and `1` means an input or runtime error. Run
`target/release/sat --help` for all search and ablation options.

## Interactive SMT

Run an SMT-LIB script:

```sh
target/release/smt < query.smt2
```

Or talk to the solver interactively:

```smt2
(set-option :produce-models true)
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= (bvadd x #x01) #x2a))
(check-sat)
(get-value (x))
(exit)
```

The process responds after each complete command and keeps reading after
recoverable command errors, so it can be used as a long-lived subprocess.

Current SMT coverage includes Core, QF_BV, QF_UF, QF_UFBV, QF_ABV, and
QF_AUFBV, plus experimental exact QF_IDL, QF_LIA, QF_RDL, and QF_LRA.
The corresponding QF_UFIDL, QF_UFLIA, QF_UFLRA, and QF_AUFLIA combinations
are also implemented. Protocol edge cases, proof production,
fragment-complete independent validation, fuzzing, and competition-scale
performance remain open.

## Rust API

The SAT kernel is available directly:

```rust
use sat::{Lit, SolveResult, Solver, Var};

let x = Lit::positive(Var::new(0));
let y = Lit::positive(Var::new(1));
let mut solver = Solver::new();
solver.add_clause(&[x, y]);
solver.add_clause(&[!x, y]);

assert!(matches!(solver.solve(), SolveResult::Sat(_)));
```

The `sat::smt` module provides typed Boolean, bit-vector, exact Int/Real, UF,
and array terms plus a reusable context API.

## Validation and benchmarking

Run the local quality gate with:

```sh
make check
```

For the gate breakdown, lint rationale, and small-commit procedure, see the
[quality policy](docs/QUALITY.md).

Deterministic tests cover the SAT kernel against brute force and exercise the
implemented SMT fragments against pinned Z3, cvc5, and Bitwuzla releases.
Arithmetic models are replayed independently through both Z3 and cvc5. Run
`make install-oracles` once per clone before `make check`; the shared integration
gate requires exact versions of all three solvers and never silently skips an
oracle. These generated tests are correctness evidence, not representative
performance benchmarks.

For controlled solver comparisons:

```sh
python3 tools/benchmark.py \
  --instances /path/to/cnf-corpus \
  --timeout 300 \
  --repeat 3 \
  --solver "ours=target/release/sat" \
  --solver "reference=/path/to/reference-solver" \
  --output results/run.jsonl
```

Read [Benchmarking](docs/BENCHMARKING.md) before interpreting results. The
project deliberately distinguishes a development result, a held-out result,
and an independently verified claim.

## Repository guide

- `src/solver.rs` — CDCL search and hot data structures
- `src/smt/` — terms, lowering, theories, SMT-LIB session, and typed API
- `src/dimacs.rs` — strict DIMACS parser
- `src/main.rs` — SAT command-line interface
- `src/bin/smt.rs` — streaming SMT-LIB command-line interface
- `tests/` — differential and end-to-end correctness tests
- `tools/` — corpus, proof, and benchmark utilities
- `docs/` — architecture, quality policy, benchmarking protocol, research
  notes, and roadmap

## Contributing

Contributions are welcome. Please preserve the distinction between a
hypothesis, a measured result, and an independently verified claim; see
[CONTRIBUTING.md](CONTRIBUTING.md).

Licensed under the [MIT License](LICENSE).
