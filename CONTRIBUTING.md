# Contributing

Correctness comes before speed, and measured speed comes before novelty claims.

Before submitting a change, run `make check`. A solver change should include a
small regression test when possible. Any heuristic or data-structure change
that claims performance improvement should also include:

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
