# Reference baselines

The first engineering references are pinned public releases, built locally from
their official repositories:

| Solver | Tag | Commit |
| --- | --- | --- |
| Kissat | `rel-4.0.4` | `8af8e56f174b778aef3aa45af9f739b2a5f492c2` |
| CaDiCaL | `rel-3.0.1` | `c60730422e758ef1cebe7aeddf2dda31c996bf04` |

Both were configured at build time with `./configure --competition` and built
using `make -j8` on Apple arm64. The resulting binaries are invoked without a
runtime `--competition` argument; the competition builds intentionally reject
that as an option. These are stable public baselines, not substitutes for the exact SAT
Competition 2025 submissions. The official 2025 results identify AE-Kissat-MAB
as the overall sequential winner and CaDiCaL-SC2025 as the UNSAT leader; exact
competition packages will be added after resource limits, proof handling, and
the corpus pipeline are ready.

Example source acquisition:

```sh
git clone --depth 1 --branch rel-4.0.4 \
  https://github.com/arminbiere/kissat.git /path/to/kissat
git clone --depth 1 --branch rel-3.0.1 \
  https://github.com/arminbiere/cadical.git /path/to/cadical
```

Verify `git rev-parse HEAD` against the table before building. Record the final
binary SHA-256 in every experiment; compiler and host differences mean a binary
hash is intentionally not part of this source manifest.

Reference sources:

- <https://github.com/arminbiere/kissat/releases/tag/rel-4.0.4>
- <https://github.com/arminbiere/cadical/releases/tag/rel-3.0.1>
- <https://satcompetition.github.io/2025/satcomp25slides.pdf>

For proof development, DRAT-trim is pinned at tag `v05.22.2023`, commit
`2e5e29cb0019d5cfd547d4208dca1b3ec290349f`. After building it with `make`, run
`make proof-smoke DRAT_TRIM=/path/to/drat-trim`.

The default learned-clause reducer follows Cai, Zhang, Shi, Tao, and Xu,
“Rethinking Clause Management for CDCL SAT Solvers,” arXiv:2602.20829v2
(2026): <https://arxiv.org/abs/2602.20829>. The implementation was checked
against their public MiniSat variant at commit
`a77eccdc188be0700a3a80d8c9f04c78e596a71a`:
<https://github.com/RethinkingClauseManagement/RethinkingClauseManagement>.
Its score initialization, BCP/analysis increments, 2,048-conflict decay,
two-stage positive-score/length reduction, growing deletion fraction, and
square-root schedule are established prior art. The local adaptation keeps
the host solver's learned binaries permanent and uses stable clause-reference
tie-breaking. No novelty claim is made for this mechanism.

Bounded variable addition and formula factoring are established preprocessing
techniques. The implementation behind `--factor` was mechanism-checked against
Kissat 4.0.4 at commit `8af8e56f174b778aef3aa45af9f739b2a5f492c2`,
especially
<https://github.com/arminbiere/kissat/blob/8af8e56f174b778aef3aa45af9f739b2a5f492c2/src/factor.c>.
The REGN benchmark construction and its regular-resolution motivation are
described in “Simplified and Randomized Formula REGN,” SAT Competition 2024,
pages 44–45:
<https://helda.helsinki.fi/server/api/core/bitstreams/3f1f286b-3def-49e9-98ba-f887b1bc250e/content>.
The local pass is an original Rust implementation with a deliberately narrower
complete-neighborhood policy. Its extension variables and RAT proof steps are
correctness infrastructure, not a novelty claim.

The `--factor-macro` density and product-size predicates are likewise
training-derived deployment heuristics, not a new proof system or factoring
algorithm. Their frozen experiment is retained because it exposes a harder REGN
solve while avoiding sparse-formula scans, but it failed its per-case latency
gate. Neither that threshold choice nor the resulting pinned-baseline win is
claimed as novel or as evidence that the instance was previously unsolved.

The `--nonregular-retention` experiment sits at the intersection of resolution
proof analysis and online clause management. Repeated-pivot regularization of
completed proofs is established by RecyclePivots and its successors:
<https://ofers.dds.technion.ac.il/publications/sttt10.pdf> and
<https://www.cse.iitb.ac.in/~akg/papers/resProof-atva12.pdf>. Kokkala and
Nordström analyze completed solver proofs and final-core membership offline:
<https://jakobnordstrom.se/docs/publications/UsingProofs_CP.pdf>. Recent Dual
Implication Points introduce extensions from a conflict implication graph:
<https://ar5iv.labs.arxiv.org/html/2406.14190>. CaDiCaL-FX globally factors
original and learned clauses into XOR, ITE, and OR gates:
<https://drops.dagstuhl.de/storage/00lipics/lipics-vol377-sat2026/LIPIcs.SAT.2026.28/LIPIcs.SAT.2026.28.pdf>.
These directions preclude broad claims about proof regularity, conflict-graph
extensions, learned-clause factoring, or offline proof-core prediction.

The narrower provisional distinction is to propagate a bounded exact sample of
transitive pivot ancestry during live CDCL and use a witnessed repeated pivot
only as an online fixed-quota deletion tie-breaker. A targeted primary-source
and source-oriented search found no exact collision, but that is not a
scholarly novelty or priority proof. More importantly, the frozen policy failed
its general performance gate. It is retained as a mixed, proof-capable
candidate mechanism with no novelty claim, no default status, and no permission
to tune the same sample on the revealed corpora.

The implementation reference for `--search=lrb` is MapleSAT master:
`Solver.cc` at `e9fc4a36f44efde8f7c025a74eed8df40b48b5ac`,
`Solver.h` at `eeea7f16325095396f69d25a5eaec99e8625c23f`, and
`SolverTypes.h` at `3c9836945ddbd0c39424f5fe7cc9e7ae8c975188`.
The algorithmic reference is Liang, Ganesh, Poupart, and Czarnecki,
“Learning Rate Based Branching Heuristic for SAT Solvers,” SAT 2016. These are
prior-art references, not performance competitors or novelty evidence.

The algorithmic reference for `--search=chb` is Liang, Ganesh, Poupart, and
Czarnecki, “Exponential Recency Weighted Average Branching Heuristic for SAT
Solvers,” AAAI 2016:
<https://cs.uwaterloo.ca/~ppoupart/publications/sat/sat-erwa.pdf>. The
implementation follows Algorithm 1's propagation-round reward order rather
than treating CHB as an informal conflict-activity variant.

Adaptive selection between branching regimes is also established prior art.
Cherif, Habet, and Terrioux combine VSIDS and CHB at restart boundaries in
“Combining VSIDS and CHB Using Restarts in SAT,” CP 2021:
<https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CP.2021.20>.
Liang, Cherif, and Li explicitly account for variable restart duration in “Not
All Restarts Are Equal: MAB-Learning at the Right Time Scale for SAT,” CP
2026: <https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CP.2026.39>.
A basic UCB switch or duration-normalized restart reward is therefore a
reference baseline, not a novel contribution.

The `--search=transfer` experiment also has adjacent—but not identical—prior
art that constrains any research claim:

- MapleCOMSPS and MapleGlucose already combine LRB and VSIDS:
  <https://maplesat.github.io/>.
- CausalSAT studies how branching choice affects future learned-clause utility,
  including propagation and conflict-analysis use:
  <https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.SAT.2023.28>.
- LBD-free clause-management work counts and ages use in BCP and conflict
  analysis for retention: <https://arxiv.org/abs/2602.20829>.
- parallel clause-sharing work tests whether producer clauses remain useful to
  a distinct consumer search:
  <https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.SAT.2024.17>.

The experiment's provisional distinction was a sequential feedback loop:
origin-tag a learned clause by EVSIDS or LRB, count only its later use by the
opposite live regime, and use that delayed transfer signal to select the
producer. A targeted search found no exact collision, but the frozen mechanism
failed its performance gates and no novelty or priority claim is made. Hybrid
branching, restart-level selection, clause-use counting, and cross-search
clause transfer each remain established ideas.

The `--scan-debt-reduction` experiment is constrained by additional
clause-management prior art:

- Gstrein et al., “Learn to Unlearn,” retain recently used clauses and compare
  established size/LBD deletion policies:
  <https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.SAT.2025.14>.
- Iser and Balyo use runtime stability statistics to select watched literals:
  <https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CP.2021.6>.
- the DeepSAT patent ranks long clauses using elapsed time since propagation
  multiplied by clause length, and separately removes a clause while testing
  BCP implicativity:
  <https://patents.google.com/patent/US10650109B1/en>.
- Savický formalizes UCP-equivalence and UCP-irredundancy:
  <https://arxiv.org/abs/2309.01750>.

These sources rule out claims that propagation cost, watched-literal runtime
statistics, or remove-and-BCP clause redundancy tests are new. The local
experiment's provisional distinction was narrower: accumulate the exact
logical watch-processing work incurred after a clause's last beneficial use
and let that negative evidence alter a fixed-cardinality reduction set. The
mechanism failed its frozen performance gate, so no novelty or priority claim
is made. The earlier bounded RUP/re-derivability deletion idea was abandoned
before implementation because DeepSAT directly collides with its core
intervention.

The `--shadow-reactivation` experiment has close prior art on every major
ingredient:

- Audemard et al. detach and later reactivate learned clauses using a saved
  polarity relevance signal in “On Freezing and Reactivating Learnt Clauses”:
  <https://doi.org/10.1007/978-3-642-21581-0_14>.
- GpuShareSat tests absent remote clauses against assignment snapshots and
  imports clauses that would propagate or conflict:
  <https://arxiv.org/abs/2012.03119>.
- PriPro partitions watch lists to prioritize propagation:
  <https://ceur-ws.org/Vol-3545/paper2.pdf>.
- duplicate learned-clause retention is studied in
  <https://doi.org/10.3233/FAIA200111>.
- CausalSAT studies the downstream utility of branching choices and learned
  clauses: <https://doi.org/10.4230/LIPIcs.SAT.2023.28>.

Freezing/reactivation, would-propagate tests, propagation partitions, duplicate
retention, causal utility analysis, and recent-use clause management are
therefore established. The local experiment's narrower combination was to
observe this same sequential solver's selected deletions inline while
preventing them from influencing the observation epoch, then feed a trigger
back only after a root boundary. A targeted search found no exact collision,
but the mechanism failed its frozen coverage, aggregate, per-case, endpoint,
and designated-proof gates. No novelty, priority, or performance claim is made.

The `--counterfactual-phase` successor is adjacent to several additional
phase-selection results:

- Pipatsrisawat and Darwiche introduced phase saving:
  <https://doi.org/10.1007/978-3-540-72788-0_20>.
- Chen computes polarity preferences from literals implied by trial BCP:
  <https://arxiv.org/abs/1208.1613>.
- Shaw and Meel's DPS and LSIDS use recent assignments and learned-clause
  literal scores for phase selection:
  <https://arxiv.org/abs/2005.04850>.
- Wang, Xu, and Wu's VDALCD feeds learned-clause deletion into variable
  activity:
  <https://doi.org/10.11896/jsjkx.201000142>.

Propagation-informed polarity, learned-clause-informed literal scores, and
deletion-conditioned branching feedback are therefore established. The local
experiment's narrower distinction was to leave control-selected clauses
deleted, test a bounded priority sample only under the actual pre-restart
assignment, and apply unanimous unique-unit literals only to saved phase. A
targeted audit found no exact collision, but the treatment produced zero unit
votes on completed development cases and failed coverage and aggregate gates.
No novelty or priority claim is made, and the frozen policy remains disabled.
