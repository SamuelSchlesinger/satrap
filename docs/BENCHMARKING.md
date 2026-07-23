# Benchmarking protocol

SAT and SMT runtimes are heavy-tailed and extremely sensitive to instance mix,
hardware, compiler flags, and solver configuration. Treat raw benchmark rows as
the artifact and summaries as views over that artifact.

## Corpus discipline

Keep three disjoint roles:

- **training** for implementation and heuristic tuning;
- **development** for choosing among already specified variants; and
- **held-out** for the final evaluation of a research claim.

Deduplicate by content hash, including across renamed or lightly transformed
instances. Preserve source and license metadata next to corpus manifests, but do
not commit third-party benchmark files unless their license permits it. Include
both satisfiable and unsatisfiable instances and report results by source/family
as well as globally.

## Build and machine controls

- pin exact solver revisions/configurations and retain binary hashes;
- use the same architecture-specific optimization policy for comparable native
  solvers;
- record CPU, OS, compiler, memory limit, time limit, and thread count;
- disable competing workloads and avoid thermal throttling;
- randomize solver/instance execution order with a recorded seed; and
- repeat short or noisy runs; do not repeatedly spend the full limit on every
  clearly timed-out instance unless the protocol requires it.

Containerization improves reproducibility but can alter scheduling and hardware
counter access. Record it rather than assuming it is neutral.

## Correctness

- Validate every SAT model against the original input.
- Validate every UNSAT proof with an independent checker once proof emission is
  available.
- Treat crashes, malformed output, disagreement, invalid models, missing proof
  artifacts, and timeouts as first-class outcomes.
- Never resolve a solver disagreement by silently dropping the instance.

`tools/benchmark.py` checks DIMACS SAT models with a streaming, constant-memory
formula pass, rejects unexpected process exits, and flags cross-solver status
disagreement. UNSAT rows are currently marked `unchecked`; this is a known
blocker for any “newly solved” claim unless a separate checker validates the
retained proof artifact.

## Metrics

Use solved count at the fixed resource limit as the primary competition-style
metric. Also report PAR-2, median and geometric-mean time over an explicitly
defined set, cactus plots, and per-family wins/losses. Runtime averages over only
jointly solved instances are useful but biased if shown alone.

For a proposed algorithmic change, use paired per-instance comparisons and a
bootstrap confidence interval or another predeclared paired analysis. Report
the feature's overhead on easy instances separately from its benefit on hard
ones.

## Runner output

The benchmark runner emits one JSON object per run. Each includes solver and
instance identifiers, command, hashes, UTC time, wall time, timeout, exit code,
reported status, validation state, host metadata, run index, seed, and current
Git revision when available. The output path must not already exist, which helps
prevent accidental destruction of prior results.

The checked-in `benchmarks/smoke` files test plumbing only. They say nothing
about solver performance.

`benchmarks/manifests/satcomp-2025-development.json` defines a bounded real-world
development slice. Fetch it with `python3 tools/fetch_corpus.py`; the downloader
verifies both compressed and decompressed SHA-256 hashes. Its eight instances
are useful for early plumbing and ablations but are far too small to support a
state-of-the-art claim.

`benchmarks/manifests/satcomp-2025-heldout-selection.json` freezes the initial
held-out selection before solver execution. It was generated from an official
GBD metadata snapshot by `tools/select_heldout.py`: SHA-256 ranking with a
fixed seed, quotas of 6 SAT / 6 UNSAT / 4 database-UNKNOWN instances, one
instance per family, and complete exclusion of development-set families.
`satcomp-2025-heldout.json` adds independently computed compressed and CNF
hashes, sizes, and headers. The 16-instance slice is an initial promotion gate,
not representative of the full 400-instance Main Track.

The database `UNKNOWN` label is metadata, not an assertion that no current
solver can decide the instance. In this gate, pinned Kissat 4.0.4 solved the
selected `reg-n` case as UNSAT in every repeat, and DRAT-trim independently
verified its retained proof. Treat any prospective “previously unsolved” case
as a separate provenance investigation followed by model/proof checking.

The 2026-07-23 Z3 head-to-head is a worked synthetic example, not a promotion
gate. On 32 uniform random 3-SAT formulas at ratio 4.267, three repeats and five
seconds gave median solved counts of 8 for the Rust solver and 6 for Z3 4.16.0.
Rust uniquely solved two UNSAT seeds and lowered PAR-2 by 5.31%; one unique
solve has a backward- and strict-forward-verified DRAT proof. Z3 nevertheless
had a 3.99× geometric-mean speed advantage on the six jointly solved formulas.
All 24 formulas at 500 variables and above were double timeouts, so the result
locates an interesting random-CNF crossover but does not support a broad SAT or
SMT comparison. Exact hashes and raw paths are in
`experiments/2026-07-23-random-3sat-z3-head-to-head.toml`.

Do not change a heuristic using results from that held-out manifest. A rejected
candidate returns to training/development work, and the next claim requires a
new quarantined evaluation sample.
