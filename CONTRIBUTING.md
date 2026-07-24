# Contributing

Correctness comes before speed, and measured speed comes before novelty claims.

Install the checked-in Git hooks once per clone:

```sh
make install-hooks
```

The pre-commit hook runs the fast formatting and compile gate. The pre-push
hook runs the same full gate as the main CI job followed by the Rust 1.85 MSRV
suite. The shared entrypoints live in `scripts/`, so local hooks and GitHub
Actions cannot drift silently.

Make regular, small commits at coherent green points. Each commit should have
one purpose, keep unrelated formatting or refactors separate, and include its
own regression test when practical. Before submitting a change, run
`make check`; use `make check-msrv` when changing dependencies or
compiler-sensitive code.

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
