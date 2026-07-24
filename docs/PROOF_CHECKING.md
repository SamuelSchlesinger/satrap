# Proof checking

The SAT executable emits textual DRAT for UNSAT DIMACS inputs. Proof checking
is a release gate, not an optional after-the-fact inspection: the shared
integration script generates certificates with the release binary and submits
them to a separately built DRAT-trim executable.

## Reproducible checker

Install the repository-pinned checker with:

```sh
make install-proof-checkers
```

The installer downloads DRAT-trim commit
`2e5e29cb0019d5cfd547d4208dca1b3ec290349f`, verifies the source archive
against its checked-in SHA-256 digest, compiles only `drat-trim.c`, and records
the revision next to the cached binary. `make check-proofs` refuses any other
revision.

The checker is kept under the ignored `.cache/proof-checkers` directory. The
pre-push hook and hosted CI both invoke the same proof gate through
`scripts/ci.sh`; repository hygiene tests prevent that wiring from being
silently removed. They also run the benchmark smoke path in strict proof mode,
so the runner-to-checker integration cannot silently degrade while the
standalone proof suite remains green.

## Mandatory proof suite

The bounded suite checks a baseline search proof, deep chronological
backtracking, and proofs produced while each proof-sensitive SAT mode is
enabled:

- failed-literal probing;
- original-clause vivification;
- subsumption and self-subsuming resolution;
- binary-resolution minimization;
- bounded variable elimination;
- exact-neighborhood bounded variable addition; and
- the guarded macro factorization policy.

Each case is solved by `target/release/sat`, must report UNSAT with exit code
20, and must end in a certificate that DRAT-trim reports as verified against
the original DIMACS input.

The same gate also exercises online QF_BOOL and QF_BV queries with named
assertions, active scopes, definitions, resets, Boolean conditions, and the
supported Boolean and fixed-width bit-vector operations. With
`:produce-proofs true`, `get-proof` returns a versioned `satrap-edrat`
S-expression. The proof producer rebuilds the active assertion context and
bit-blast as a fresh permanent formula, so internal activation selectors
cannot masquerade as part of a global empty-clause proof.

SMT-LIB 2.7 permits `get-proof` only when the most recent check had an empty
set of explicit assumptions. Satrap therefore rejects `get-proof` after a
nonempty `check-sat-assuming` call. A plain `check-sat`, or
`check-sat-assuming ()`, remains proof-eligible; assertions in active
`push`/`pop` scopes and `:named` assertions are part of that context.

`tools/check_smt_proof.py` is a separate implementation of the proof-bearing
QF_BOOL and QF_BV front ends, bit-vector lowering, and canonical encoder.
Given the original script, it:

1. reconstructs declarations, definitions, `let` bindings, scopes, resets,
   assertions, and checked queries;
2. requires the certificate's premise list to match an actual
   standards-eligible `get-proof` site, including intervening mutation and
   reset state;
3. independently lowers every supported fixed-width bit-vector operation,
   normalizes the resulting Boolean DAG, and regenerates every formula and
   Tseitin clause;
4. rejects solver errors plus a changed variable count, premise, clause,
   origin, duplicate field, or unsupported theory clause; and
5. submits the DRAT suffix and reconstructed CNF to pinned DRAT-trim.

The required QF_BV corpus includes a compact arithmetic contradiction, a
scoped/reset script, and an operator-surface script covering binary, hex, and
indexed literals; arithmetic and bitwise operators; signed and unsigned
division; shifts and comparisons; overflow predicates; concatenation,
extraction, extension, repetition, and rotation; n-ary equality/distinct; and
bit-vector `ite`. Separate unit tests exhaustively compare the checker
lowering with integer semantics for every pair of width-one through width-four
values. Repository hygiene rejects a missing or empty canonical proof-corpus
file, so deleting one case cannot silently weaken the push gate.

Run that path directly with:

```sh
make smt-proof-smoke
```

Run the suite directly with:

```sh
make check-proofs
```

For one formula or experimental configuration:

```sh
python3 tools/proof_smoke.py \
  --solver target/release/sat \
  --solver-arg=--probe \
  --checker .cache/proof-checkers/bin/drat-trim \
  --formula benchmarks/smoke/probe-unsat.cnf
```

## Boundary

This gate establishes that representative SAT proof paths remain accepted by
an independent checker on every normal push. `tools/benchmark.py` can retain
one proof per run, check it independently, and reject every unchecked UNSAT
result with `--require-unsat-proofs`. Claim-bearing benchmark configurations
must enable that flag and configure a checker for every participating solver.
This does not replace longer proof campaigns or establish proof production for
the advertised SMT theories.

In particular, the live incremental SAT stream deliberately does not append a
global empty DRAT clause for assumption-only UNSAT, and the SMT-LIB layer
rejects `get-proof` after a nonempty explicit assumption set. QF_BOOL and QF_BV
use the query-specific replay above for the active assertion context. UF,
arrays, and arithmetic still need checkable theory-lemma certificates. Proof
mode therefore rejects every logic outside QF_BOOL and QF_BV rather than
emitting a certificate that silently trusts such lemmas. The general SMT proof
gate remains open.
