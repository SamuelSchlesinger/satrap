# Fuzzing

Fuzzing is a correctness tool here, not a coverage percentage or a claim of
completeness. The checked-in gate uses libFuzzer with sanitizers and deterministic
seeds so every ordinary push exercises the same bounded campaigns as hosted CI.

## Targets

| Target | Surface | Independent invariant |
| --- | --- | --- |
| `smt_session_bytes` | Arbitrary bytes through the public streaming SMT-LIB session | The parser and command loop must return without memory unsafety or an uncontrolled panic |
| `smt_structured_session` | Valid command streams with scopes, assumptions, resets, models, cores, and mixed theories | Stateful combinations and recoverable command errors must remain safe across a long-lived session |
| `sat_proof` | Small generated CNFs through SAT solving and DRAT emission | Brute force agrees with the result, SAT models satisfy the input, and UNSAT proof output is syntactically bounded and ends in the empty clause |

The structured target rotates through QF_BV, QF_UF, finite QF_AUFBV, QF_LIA,
QF_LRA, QF_UFLIA, QF_AUFLIA, and QF_UFIDL fragments. Seed corpora preserve
representative raw, incremental, malformed, theory-combination, and
nontrivial-UNSAT cases.

## Install and run the push gate

```sh
make install-fuzz-tools
make check-fuzz
```

The installer pins the nightly toolchain, its Rust source, Rustfmt, and Clippy
components, plus the cargo-fuzz version. The gate first rejects an out-of-date
fuzz lockfile, then applies strict formatting and Clippy checks,
sanitizer-builds the fuzz workspace, copies seeds into temporary writable
corpora, and runs 256 iterations per target with fixed resource limits. Set
`FUZZ_RUNS` to raise the iteration count without changing the checked-in
policy:

```sh
FUZZ_RUNS=10000 make check-fuzz
```

The bounded push gate is intentionally short. Before a release or after changes
to parsing, incremental state, theory combination, model construction, or proof
emission, run the affected target for time:

```sh
cargo +nightly-2026-06-01 fuzz run smt_session_bytes \
  fuzz/corpus/smt_session_bytes -- -max_total_time=3600 \
  -dict=fuzz/smtlib.dict
cargo +nightly-2026-06-01 fuzz run smt_structured_session \
  fuzz/corpus/smt_structured_session -- -max_total_time=3600
cargo +nightly-2026-06-01 fuzz run sat_proof \
  fuzz/corpus/sat_proof -- -max_total_time=3600
```

## Failures and corpus policy

libFuzzer writes a reproducer under `fuzz/artifacts/<target>/` during a direct
campaign. The push/CI wrapper instead uses a temporary artifact root; hosted CI
uploads that directory when the gate fails. Reproduce a saved input with:

```sh
cargo +nightly-2026-06-01 fuzz run <target> <artifact>
```

Minimize the input, add it to the corresponding checked-in corpus with a
descriptive name, and include the regression in the same small commit as its
fix. Do not commit generated corpora wholesale: seeds should each represent a
durable behavior or past defect. A clean bounded run does not establish that a
fragment is complete, a model is independently valid, or an UNSAT proof is
semantically checkable; those are separate roadmap gates.
