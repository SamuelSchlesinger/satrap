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
| Commit | `make check-fast` | Formatting, compilation, shell syntax, and repository hygiene |
| Quality | `make quality` | Strict Clippy, rustdoc, ShellCheck, Actionlint, lockfile, and structural checks |
| Integration | `make check` | Quality plus required Z3 differential/model checks, Rust/Python tests, and a release build |
| Compatibility | `make check-msrv` | Full tests on the declared minimum Rust version |
| Dependencies | `make audit` | RustSec advisory audit; requires `cargo-audit` and network access |

The pre-commit hook runs the commit gate. The pre-push hook refuses a normal
push unless integration, compatibility, and dependency gates all pass. Hosted
CI independently calls the same integration and compatibility scripts and
runs the RustSec audit on every push and pull request, plus weekly, so a newly
published advisory is caught even when the repository is unchanged.

The pre-push gate requires `cargo-audit`, ShellCheck, Actionlint, and Z3. Z3 is
mandatory here even though a direct `cargo test` can skip its differential
tests: neither the local integration gate nor hosted CI may silently lose the
second solver. On macOS, install the tools with:

```sh
cargo install cargo-audit --version 0.22.2 --locked
brew install actionlint shellcheck z3
```

Use the corresponding package manager on other platforms. Hosted CI installs
its own copies and pins Actionlint to `v1.7.12` and cargo-audit to `0.22.2`.

`tools/check_hygiene.py` enforces the small but easy-to-forget invariants:
UTF-8/LF text, final newlines, no trailing whitespace, valid local Markdown
links, executable scripts, synchronized MSRV declarations, and identical
top-level CI/pre-push entrypoints. It also verifies that the integration script
still includes the quality gate and that the security workflow remains wired
to RustSec.

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
