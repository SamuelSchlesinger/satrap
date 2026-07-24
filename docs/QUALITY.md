# Quality policy

The solver's first obligation is to avoid wrong answers. Code quality exists to
make that obligation sustainable: invariants should be visible, changes should
be reviewable, and every claim should have evidence at the same level as the
claim.

## Working principles

- Correctness comes before coverage, and coverage comes before speed.
- Unsupported or exhausted reasoning returns `unknown`; it never guesses.
- Prefer explicit invariants and ordinary control flow over clever compression.
- Optimize a hot path only after profiling it, then retain the measurement.
- Comments explain an invariant, tradeoff, or surprising constraint rather than
  narrating syntax or preserving obsolete history.
- Keep dependency and abstraction cost out of the search path unless evidence
  justifies it.
- Use scoped lint exceptions only when the code is clearer with the exception.
  Every exception needs a reason close to the code.

## Executable gates

| Gate | Command | Purpose |
| --- | --- | --- |
| Commit | `make check-fast` | Rust/Python formatting and lint, compilation, shell syntax, and repository hygiene |
| Quality | `make quality` | Strict Clippy, rustdoc, Ruff, ShellCheck, Actionlint, lockfile, and structural checks |
| Fuzz | `make check-fuzz` | Locked format/Clippy/sanitizer build plus bounded parser, incremental SMT, and SAT proof campaigns |
| Proof | `make check-proofs` | Release SAT certificates plus query-bound Boolean/BV/UF/array/difference-logic certificates reconstructed independently and checked by pinned DRAT-trim |
| Integration | `make check` | Quality plus required three-oracle differential/model checks, Rust/Python tests, fuzz smoke, proof-checked benchmark smoke, and a release build |
| Compatibility | `make check-msrv` | Full tests on the declared minimum Rust version |
| Dependencies | `make audit` | RustSec advisory audit; requires `cargo-audit` and network access |

The pre-commit hook runs the commit gate. The pre-push hook refuses a normal
push unless integration, compatibility, and dependency gates all pass. Hosted
CI independently calls the same integration and compatibility scripts and
runs the RustSec audit on every push and pull request, plus weekly, so a newly
published advisory is caught even when the repository is unchanged.

The pre-push gate requires `cargo-audit`, ShellCheck, Actionlint, Ruff 0.15.22,
Z3 4.16.0, cvc5 1.3.3, Bitwuzla 0.9.1, nightly-2026-06-01, cargo-fuzz 0.13.2,
and DRAT-trim commit `2e5e29cb0019d5cfd547d4208dca1b3ec290349f`.
The Python lint/format checks, three SMT oracles, all three fuzz targets, and
the independent SAT proof checks are mandatory here even though a direct
`cargo test` does not require them: neither the local integration gate nor
hosted CI may silently lose one. Install the tools with:

```sh
cargo install cargo-audit --version 0.22.2 --locked
brew install actionlint shellcheck  # macOS; use your package manager elsewhere
make install-python-tools
make install-oracles
make install-fuzz-tools
make install-proof-checkers
```

`make install-python-tools` creates an ignored repository-local virtual
environment and installs Ruff from a platform wheel whose version and SHA-256
digest are checked in. Both the fast commit gate and full quality gate require
that exact version, run the selected correctness-oriented lint families, and
verify canonical formatting across every Python tool and test.

`make install-oracles` downloads official release archives into the ignored
`.cache/smt-oracles` directory and verifies every SHA-256 digest before making
the binaries available to the gate. It currently supports Apple Silicon macOS
and x86-64 Linux. Bitwuzla also needs GMP and MPFR runtime libraries. Hosted CI
installs those libraries, invokes the same oracle installer, and pins Actionlint
to `v1.7.12` and cargo-audit to `0.22.2`.

The fuzz gate builds with sanitizers and runs 256 deterministic libFuzzer
iterations per target. This is a bounded regression smoke test suitable for
every push, not a substitute for sustained campaigns. Failure artifacts are
kept outside the checked-in corpus and uploaded by hosted CI. Target scope,
long-running commands, corpus policy, and reproduction steps are in
[Fuzzing](FUZZING.md).

The proof gate builds the release solver and validates certificates for the
baseline plus each proof-sensitive preprocessing and minimization mode. The
checker source archive is hash-pinned and its declared revision is synchronized
by the hygiene gate. The integration gate also drives the real benchmark runner
in strict mode: all nine UNSAT smoke rows must retain a proof long enough for
independent checking, while the SAT row must pass model validation. Scope,
assumptions, SMT theory certificates, and the difference between a push smoke
suite and a claim-bearing benchmark campaign are documented in
[Proof checking](PROOF_CHECKING.md).

The proof gate additionally runs the release SMT executable online and
reconstructs active QF_BOOL, QF_BV, QF_UF, QF_UFBV, QF_ABV, QF_AUFBV, QF_IDL,
QF_LIA, QF_RDL, and QF_LRA queries in an independent Python implementation. It
repeats fixed-width bit-vector lowering, finite ground-UF class/congruence
lowering, ground extensional-array lowering, exact difference-logic
negative-cycle, linear-integer Cooper, and linear-real Fourier-Motzkin
validation, plus canonical CNF generation before checking the embedded DRAT
suffix. Nested arrays and arithmetic theory combinations remain outside that
claim and are rejected when proof production is requested.

`tools/check_hygiene.py` enforces the small but easy-to-forget invariants:
UTF-8/LF text, final newlines, no trailing whitespace, valid local Markdown
links, executable scripts, synchronized MSRV/oracle/fuzz-tool declarations, and
synchronized Ruff declarations. It verifies identical top-level CI/pre-push
entrypoints and that the integration script still includes the quality and
fuzz gates, all three oracle version checks, every fuzz target, the
proof-checked benchmark smoke, and that the security workflow remains wired to
RustSec. It also requires every canonical QF_BOOL, QF_BV, QF_UF, QF_UFBV,
QF_ABV, QF_AUFBV, QF_IDL, QF_LIA, QF_RDL, and QF_LRA proof-corpus file to
remain present and nonempty. It also requires the Rust producer and Python
checker to declare identical QF_LIA variable and Cooper-work ceilings.

The ordinary gate deliberately does not enable every `clippy::pedantic` or
`clippy::nursery` lint. Solver code contains exact numeric conversions,
deliberately dense algorithms, and large state machines for which those groups
produce more exceptions than signal. A lint graduates into the gate when it
identifies a concrete recurring defect with few false positives.

## Review procedure

Review each change in this order:

1. **Answer integrity:** Could it produce a wrong result, stale result, scope
   leak, invalid model, invalid proof, or unjustified core?
2. **State and errors:** Are incremental transitions, cancellation, limits,
   malformed input, and unsupported cases explicit and recoverable?
3. **Tests:** Is the smallest reproducer deterministic, and does it exercise
   the public behavior rather than only the implementation?
4. **Structure:** Are ownership, names, module boundaries, and invariants clear
   without reading the entire solver?
5. **Performance:** Does the change add allocation, copying, hashing, or
   indirection to a hot path? If so, what measurement supports it?
6. **Claims:** Do documentation and experiment records say exactly what was
   checked, without turning differential evidence into a proof?

## Small-commit procedure

Commit whenever one coherent change is green. A good commit can be reverted,
reviewed, and bisected independently; formatting-only changes, mechanical
refactors, correctness fixes, and performance experiments should not be mixed.
Include the regression test in the same commit as its fix whenever practical.

Before committing, inspect `git diff --check` and the staged diff, then let the
pre-commit hook run. Before pushing, leave enough time for the full hook rather
than bypassing it. Repository policy forbids `git push --no-verify`: if a gate
is wrong, repair the gate and retain a regression test instead of silently
skipping it.

## Repository health and tone

Keep the repository calm and evidence-based:

- put durable work in the roadmap or an issue instead of ambient `TODO` piles;
- delete dead experiments only after their negative result is recorded;
- avoid drive-by renaming or formatting in functional changes;
- treat a flaky test as a bug in the gate, not background noise;
- keep generated artifacts and local benchmark output out of version control;
- label experimental support as experimental until its complete validation
  gate passes; and
- periodically remove expired exceptions, stale claims, and redundant helpers.

Security audits are repeated weekly because the advisory database changes even
when this repository does not. Performance and correctness claims follow the
stronger release gates in the [roadmap](ROADMAP.md) and
[benchmarking protocol](BENCHMARKING.md); a green code-quality gate alone does
not make a solver result trustworthy.
