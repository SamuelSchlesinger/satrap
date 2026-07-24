# Contributing

Correctness comes before speed, and measured speed comes before novelty claims.

Install the checked-in Git hooks once per clone:

```sh
cargo install cargo-audit --version 0.22.2 --locked
brew install actionlint shellcheck  # macOS; use your package manager elsewhere
make install-python-tools
make install-oracles
make install-fuzz-tools
make install-proof-checkers
make install-hooks
```

The pre-commit hook runs the fast Rust/Python formatting, lint, and compile
gate. The pre-push hook runs the same full gate as the main CI job followed by
the Rust 1.85 MSRV suite and RustSec audit. It rejects a dirty checkout or a
ref that is not the checked-out `HEAD`, so the revision Git publishes is the
revision that was actually tested. The integration gate requires
hash-verified Ruff installed by `make install-python-tools`, the pinned Z3,
cvc5, and Bitwuzla differential oracles installed by `make install-oracles`,
the pinned fuzz toolchain installed by `make install-fuzz-tools`, and the
pinned DRAT-trim checker installed by `make install-proof-checkers`. Hosted CI
independently reruns all three gates, including the SAT proof-mode matrix and
strict proof-checked benchmark smoke. The shared entrypoints live in
`scripts/`, and the hygiene checker rejects broken gate wiring, so local hooks
and GitHub Actions cannot drift silently.

Make regular, small commits at coherent green points. Each commit should have
one purpose, keep unrelated formatting or refactors separate, and include its
own regression test when practical. Before submitting a change, run
`make check`; use `make quality` for the non-test lint and documentation gate,
and `make check-msrv` when changing dependencies or compiler-sensitive code.
The complete review order, lint rationale, exception policy, and repository
maintenance procedure live in the [quality policy](docs/QUALITY.md).

Any heuristic or data-structure change that claims performance improvement
should also include:

1. an experiment record based on `experiments/template.toml`;
2. the exact before/after revisions and build flags;
3. corpus hashes and the train/dev/held-out role of each corpus;
4. per-instance raw results, including timeouts and failures;
5. model/proof validation status; and
6. an ablation that isolates the change.

Do not tune on the held-out set. Do not discard timeouts, crashes, invalid
models, or regressions from aggregate results. A new UNSAT result is not a
solved instance until an independently checked proof is available.

Keep dependencies out of the propagation/search path unless profiling shows a
clear net benefit. Unsafe Rust is currently forbidden at the crate level. If a
future optimization truly needs it, it should arrive as a separately reviewed
change with a safety argument, fuzz coverage, and benchmark evidence.
