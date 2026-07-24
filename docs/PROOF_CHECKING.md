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
This does not replace longer proof campaigns or establish SMT proof
production.

In particular, an assumption-only UNSAT query deliberately does not append a
global empty DRAT clause because the permanent formula may still be
satisfiable. The interactive proof container must record query assumptions and
active scopes explicitly. UF, array, and arithmetic lemmas also need
independently checkable theory certificates. Until that container and those
certificates exist, `get-proof` remains unsupported and the SMT proof gate is
open.
