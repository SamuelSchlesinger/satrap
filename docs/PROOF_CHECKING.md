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

The same gate also exercises online QF_BOOL, QF_BV, QF_UF, QF_UFBV, QF_ABV,
QF_AUFBV, QF_IDL, QF_LIA, QF_RDL, and QF_LRA queries with named assertions,
active scopes, definitions, resets, Boolean conditions, and the supported
Boolean, fixed-width bit-vector, ground-UF, non-nested-array, and exact
linear-arithmetic operations. With
`:produce-proofs true`, `get-proof` returns a versioned `satrap-edrat`
S-expression. The proof producer rebuilds the active assertion context and
lowering as fresh permanent formulas, so internal activation selectors and
native-theory state cannot masquerade as part of a global empty-clause proof.

SMT-LIB 2.7 permits `get-proof` only when the most recent check had an empty
set of explicit assumptions. Satrap therefore rejects `get-proof` after a
nonempty `check-sat-assuming` call. A plain `check-sat`, or
`check-sat-assuming ()`, remains proof-eligible; assertions in active
`push`/`pop` scopes and `:named` assertions are part of that context.

`tools/check_smt_proof.py` is a separate implementation of the proof-bearing
QF_BOOL, QF_BV, QF_UF, QF_UFBV, QF_ABV, QF_AUFBV, QF_IDL, QF_LIA, QF_RDL,
and QF_LRA front ends, lowerings, and canonical encoder. Given the original
script, it:

1. reconstructs declarations, definitions, `let` bindings, scopes, resets,
   assertions, and checked queries;
2. requires the certificate's premise list to match an actual
   standards-eligible `get-proof` site, including intervening mutation and
   reset state;
3. independently lowers every supported fixed-width bit-vector operation,
   ground UF term, and ground array term; reconstructs exact affine predicates
   and arithmetic `ite` definitions; normalizes the resulting Boolean DAG; and
   regenerates every formula, theory axiom, and Tseitin clause;
4. rejects solver errors plus a changed variable count, premise, clause,
   origin, duplicate field, forbidden theory clause, or unsupported term; and
5. submits the DRAT suffix and reconstructed CNF to pinned DRAT-trim.

Ground UF uses a finite, source-canonical reduction. For each uninterpreted
sort, every reachable ground constant and application is assigned a bit-vector
class label with enough bits to represent a separate class for every such term;
labels are not required to differ. UF equality becomes bitwise label equality,
UF-valued `ite` selects a label, and a canonical pairwise Ackermann axiom for
each observed pair of applications enforces equal arguments imply equal
results. Boolean and bit-vector arguments and results are compared at their
native bit level. This is equisatisfiable for a ground query: any model induces
labels for the finitely many observed terms, and any satisfying labeling
extends to a UF interpretation by assigning unobserved argument tuples
arbitrarily. The checker reconstructs this reduction from source rather than
accepting theory clauses on trust.

Ground arrays extend that reduction without trusting the live array engine.
Each reachable non-`ite` array term receives a finite class label. Select is a
canonical typed application, so the same Ackermann congruence rule enforces
equal arrays and indices have equal results. For every reachable read, the
reduction adds the applicable constant-array, read-over-write, or
array-valued-`ite` equation. For each pair of ground array terms `A` and `B`,
it creates a canonical witness index `k` and adds
`A = B or select(A, k) != select(B, k)`. This is the finite ground
extensionality instance needed for that pair. The complete select/witness
closure is computed before class widths or Boolean clauses are generated, and
both producer and checker reject any later attempt to grow it. The resulting
reduction is equisatisfiable for the supported quantifier-free, non-nested
QF_ABV/QF_AUFBV boundary.

QF_IDL, QF_LIA, QF_RDL, and QF_LRA use a different theory-certificate layer.
Arithmetic variables and predicates are canonicalized by source name and exact
rational coefficients; an arithmetic `ite` is represented structurally by its
condition and two affine branches. A discovery replay enumerates Boolean
candidates. For each theory-inconsistent candidate it emits one clause blocking
the complete assignment of all relevant arithmetic predicates and `ite`
conditions. The producer accepts a difference-logic clause only after exact
Bellman-Ford negative-cycle detection: integer strict bounds are folded with
exact floor/ceiling arithmetic, while real strict bounds use a lexicographic
infinitesimal component. QF_LIA uses exact Cooper elimination: inequalities are
normalized over integers and introduced divisibility constraints preserve
parity and general modular contradictions. QF_LRA uses exact rational
Fourier-Motzkin elimination and propagates open bounds through every
elimination pair.

The independent checker reparses the arithmetic source and repeats that
calculation. It requires every arithmetic theory clause to cover exactly the
canonical required Boolean variables, recovers the assignment that the clause
blocks, rebuilds the selected predicates and `ite` equalities, and independently
finds the required negative cycle, Cooper contradiction, or Fourier-Motzkin
contradiction. A clause that blocks even one theory-satisfiable assignment is
rejected before DRAT-trim runs. The final DRAT suffix proves that the validated
theory clauses and reconstructed Boolean encoding suffice for UNSAT.

This first arithmetic format favors a small trusted story over proof size: a
lemma blocks a complete required assignment rather than carrying a compact
cycle or elimination witness, so proof discovery can be exponential in the
number of relevant predicates; Cooper candidate periods can be large; and
Fourier-Motzkin can grow quadratically at each eliminated variable. The
producer and checker therefore enforce synchronized deterministic QF_LIA
ceilings of 512 variables and 1,000,000 Cooper work steps, failing explicitly
instead of hanging or trusting an unchecked lemma. This format certifies the
four scalar arithmetic boundaries but is not yet a competitive certificate
format for theory combinations.

The required QF_BV corpus includes a compact arithmetic contradiction, a
scoped/reset script, and an operator-surface script covering binary, hex, and
indexed literals; arithmetic and bitwise operators; signed and unsigned
division; shifts and comparisons; overflow predicates; concatenation,
extraction, extension, repetition, and rotation; n-ary equality/distinct; and
bit-vector `ite`. Separate unit tests exhaustively compare the checker
lowering with integer semantics for every pair of width-one through width-four
values. The QF_UF/QF_UFBV corpus adds congruence contradictions, nested and
Boolean-valued applications, Boolean and bit-vector arguments/results,
UF-valued `ite`, definitions, scopes, resets, global declarations, sort
aliases, and named assertions. The QF_ABV/QF_AUFBV corpus adds extensional
disequality, constant arrays, read-over-write, array-valued `ite`, UF-sorted
indices and elements, and functions over arrays. Unit tests include both
refutable and satisfiable array reductions, so the gate checks against an
over-strong encoding as well as a weak one. The arithmetic corpus adds integer
negative cycles, general integer parity contradictions, strict real cycles,
exact decimal/rational bounds, general linear-real contradictions, and
arithmetic `ite` relevance. Producer and checker Cooper implementations each
match bounded exhaustive search on 624 two-variable systems. Adversarial unit
tests mutate a theory clause to block a satisfiable assignment and verify that
the independent checker rejects it. Repository hygiene rejects a missing or
empty canonical proof-corpus file and checks that producer/checker work limits
agree, so deleting one case or drifting only one implementation cannot silently
change the push gate.

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
This does not replace longer proof campaigns or establish proof production
outside the explicitly listed ground fragments.

In particular, the live incremental SAT stream deliberately does not append a
global empty DRAT clause for assumption-only UNSAT, and the SMT-LIB layer
rejects `get-proof` after a nonempty explicit assumption set. QF_BOOL, QF_BV,
QF_UF, QF_UFBV, QF_ABV, QF_AUFBV, QF_IDL, QF_LIA, QF_RDL, and QF_LRA use the
query-specific replay above for the active assertion context. This certifies
ground UF and non-nested extensional arrays through an independently rebuilt
finite reduction, integer and real difference logic through independently
checked negative-cycle lemmas, and linear integer/real arithmetic through
independently checked exact elimination. It is not a certificate for
quantifiers, nested arrays, or arithmetic theory combinations. Proof mode
rejects those remaining boundaries rather than emitting a certificate that
silently trusts their lemmas. The general SMT proof gate remains open.
