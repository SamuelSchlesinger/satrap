# Research roadmap

The objective is not to accumulate SAT features. It is to reach a verified,
competitive baseline and then run a disciplined search for algorithmic advances
that solve materially harder instances.

## Gate 0: trustworthy executable — complete for the initial baseline

- working CDCL, watched propagation, first-UIP learning, EVSIDS, restarts, and
  learned-clause deletion;
- strict DIMACS input and conventional SAT/UNSAT output;
- structured tests plus deterministic differential testing against brute force;
- release/profiling builds, CI configuration, and a metadata-rich comparison
  runner.

Passing this gate means “worth iterating on,” not “competitive.”

## Gate 1: competition-grade correctness

- assumption solving, implication-graph failed subsets, learned-state reuse,
  monotone post-query clause addition, and activation-literal scopes are
  implemented and differentially checked against brute force; scope-aware
  irreversible preprocessing and an incremental proof container remain;
- the textual DRAT stream includes deletion steps, and the baseline plus every
  proof-sensitive SAT mode is checked by pinned DRAT-trim on every push;
  the benchmark runner now allocates and retains per-run proof artifacts,
  records checker evidence, and can reject every unchecked UNSAT row in strict
  mode; claim-bearing full-corpus campaigns remain to be run under that mode;
- model checking integrated into every benchmark run;
- named core subsets now have deterministic independent replay cases in every
  advertised fragment, including a combined core/assumption query; integrating
  replay into every retained benchmark core and expanding generated coverage
  remain;
- deterministic coverage-guided smoke campaigns now exercise raw SMT-LIB
  parsing, structured incremental sessions across the implemented theory
  combinations, and SAT model/proof invariants; sustained campaigns, coverage
  targets, corpus minimization, and a reproducible bug corpus remain;
- deterministic differential testing now requires pinned Z3, cvc5, and
  Bitwuzla releases; expanding every oracle across every supported fragment
  and representative malformed sessions remains;
- a reusable `Unknown` path, deterministic CDCL conflict/propagation limits,
  and a thread-safe interruption handle are implemented; charging one-time
  preprocessing, OS signal wiring, and end-to-end malformed interactive input
  behavior remain; and
- reproducible bug corpus with minimized instances.

No claim about a previously unsolved UNSAT instance passes this gate without a
checked proof artifact.

## Gate 2: modern single-threaded SAT baseline

Implement and ablate, roughly in this order:

1. recursive learned-clause minimization and an additional one-hop
   binary-resolution pass are implemented and proof-checked; the latter
   remains opt-in after regressing both hard development endpoints, while
   bounded transitive binary reachability remains future work;
2. the compact clause arena and binary propagation fast path are implemented;
   reduction-synchronous physical arena compaction is implemented and
   proof-checked but remains opt-in after a flat runtime ablation; separate
   packed binary storage, 4-byte tagged reasons, and sparse learned-binary
   activities are implemented and promoted after an exact-trajectory,
   proof-byte, runtime, storage, and peak-RSS gate;
3. usage-aged tiered retention and LBD promotion are implemented and ablatable,
   but the first development experiment rejected them as defaults. The
   published 2026 LBD-free BCP/analysis-usage policy is implemented,
   proof-checked, and promoted after raising two-second coverage from 3/8 to
   5/8 and improving both hard endpoints; the exact former LBD/activity reducer
   remains available for ablation. This is an established baseline, not the
   repository's novel contribution. The first candidate intervention,
   post-use watch-scan debt, is implemented and proof-checked behind
   `--scan-debt-reduction`; it tied coverage but regressed every repeated
   nontrivial case and preferentially deleted still-positive high-exposure
   clauses, so it is a recorded negative result rather than a contribution.
   Sampled nonregular-derivation retention is also implemented behind
   `--nonregular-retention`. It added one dense-macro REGN solve with tens of
   thousands of changed deletion choices, but lost no-factor and development
   coverage and exceeded two regression ceilings. It is a mixed diagnostic
   result, not a promoted contribution. Exact counterfactual observation of
   selected deletions is implemented behind `--shadow-reactivation`; its
   noncausal trigger measurement worked, but five delayed reactivations
   catastrophically worsened Break and the frozen policy lost development
   coverage. It is a closed negative result, not a promoted contribution;
4. VMTF branching, focused LBD-EMA restarts, reluctant stable search, and
   focused/stable alternation are implemented and ablatable; the first
   100-conflict focused probe failed its held-out promotion gate;
   100-level chronological backtracking is implemented and promoted after a
   42.2 percent repeated development median gain on Break_12_50; deterministic
   best/inverted/original rephasing is implemented but rejected after large
   development regressions; EVSIDS restart trail reuse is implemented and
   strongly complementary across development families; the first
   action-conditioned online gate was preregistered and rejected because its
   propagation/LBD reward made the harmful family worse than either fixed
   action; local-walk-informed phase selection remains;
5. preprocessing and inprocessing: proof-checked bounded failed-literal and
   conservative original-clause vivification passes are implemented and
   ablatable, but both were rejected as defaults after mixed development
   results; bounded occurrence-indexed subsumption/self-subsuming resolution is
   also implemented and proof-checked, but retained as opt-in after a 57%
   regression on one solved development case exposed an underspecified
   promotion gate; zero-growth bounded variable elimination with proof logging
   and reverse model extension is now implemented, but a preregistered gate
   rejected its sharply family-dependent performance. Exact-neighborhood
   bounded variable addition is also proof- and model-checked: it raised
   five-second REGN coverage from 1/6 to 4/6 and matched pinned Kissat on that
   targeted family, but lost a mixed-family development solve and remains
   opt-in. Its frozen dense/macro deployment guard restored development
   coverage and raised reused REGN coverage to 5/6, but violated a 10% per-case
   ceiling with a 41.31% regression and also remains opt-in. Blocked-clause
   elimination, binary-root/hyper-binary probing, learned-clause vivification,
   and repeated inprocessing remain;
6. full LRB with reason-side rewards and lazy anti-exploration is implemented,
   proof-checked, and retained behind `--search=lrb`; it added a development
   solve and cut 6s268 by 75.4%, but timed out on the Break endpoint and was
   rejected as the default. Full CHB is also implemented and retained behind
   `--search=chb`; it tied development coverage but regressed every completed
   nontrivial comparison and timed out on 6s268, so it too was rejected. The
   first candidate new selector, `--search=transfer`, kept EVSIDS and LRB warm
   and rewarded only opposite-regime use of producer-tagged learned clauses.
   It was correctness- and proof-checked but solved only 3/8 development
   instances, selected the wrong arm on 6s268, and failed both endpoint
   ceilings. Cross-regime clause-use rate is therefore a rejected signal, not
   a domain-sensitive solution; and
7. profiling-driven memory-layout and propagation optimizations.

Parity means comparable solved counts and time distributions on multiple
held-out families, not a win on hand-selected instances.

The first propagation-allocation pass is complete: safe in-place watch-list
compaction retained exact search counters and improved repeated development
medians by 16–31 percent. Eight-byte packed watch entries are also complete and
added 4–9 percent on the nontrivial repeated cases. Physical clause-arena
compaction now preserves those counters and can reclaim millions of logical
literal slots, but it missed a preregistered two-percent runtime floor and stays
opt-in. Separate packed binary storage plus sparse learned-only activity is now
complete: it retained exact trajectories and proof bytes, cut 6s268's logical
clause/reason payload by 34.67 percent, and reduced newly repeated median peak
RSS by 13.99 percent versus the frozen legacy representation. The first
variable-width watch attempt also retained exact behavior and saved 6.99 MB,
but its indexed blocker lookup regressed every nontrivial repeated median by
8–13 percent and was reverted. Direct-literal binary reasons and more detailed
hardware-counter profiling remain separate possibilities.

Exact BVA isolated one unusually large baseline gap, and the completed
`--factor-macro` follow-up shows both sides of it: structural guards eliminate
the sparse-corpus overhead and expose a fifth REGN solve, but product size alone
still fails to predict search cost. Threshold retuning on these revealed
families is closed. The first online proof-regularity experiment is now also
complete: a bottom-four exact pivot-ancestry sample exposed real nonregular
reuse and added a sixth macro-REGN solve, but unconditional retention was not
robust. Sample-size, ranking, and activation retuning on these families are
closed. The next baseline/research choice must introduce independent
information or intervention semantics rather than turn the observed family
split into a post-hoc selector.

Full LRB has joined restart-trail reuse
as a sharply complementary regime: it improved the repeated gm24 and 6s268
medians by 29.6% and 75.4%, respectively, but made Break more than eight times
slower at the preregistered censoring point. CHB did not add another favorable
development regime: it regressed gm24, 6s299, and Break by 143–347% and timed
out on 6s268. A plain restart-level or duration-aware multi-armed-bandit switch
is already prior art, so any selector pursued here must distinguish its credit
assignment or intervention semantics rather than relabel an established
VSIDS/CHB policy. Broader preprocessing/inprocessing and a novel
clause-management intervention on top of the promoted usage baseline remain
independent options before using more held-out data. Failed
focused-probe, tiered retention, rephasing, online trail-reuse, bounded
failed-literal, and
conservative root-vivification gates are recorded negative results, not
invitations to tune parameters on revealed families. The subsumption/SSR
minimum gate passed but omitted a per-instance bound for the rest of the solved
slice, so it remains opt-in. Reduction-synchronous clause-arena compaction also
remains opt-in after a flat speed result despite exact trajectory preservation.
Zero-growth bounded variable elimination is likewise retained as proof/model
infrastructure after improving 6s268 by 29.3% but regressing Break by 336.9%
under one frozen schedule. The rejected indexed variable-width watch result is
likewise not permission to retrofit direct-literal reasons after seeing its
timings; that larger design needs its own preregistration if profiling makes it
the best next target.

Exact-neighborhood BVA adds a different boundary. Clause-count reduction alone
does not predict search benefit: 1,056 valid `3 × 3` rewrites on Break reduced
2,112 clauses yet more than tripled conflicts, while large REGN products
removed 28,345–818,929 net clauses and changed timeouts into subsecond proofs.
Changing the frozen threshold after seeing those cases would be post-hoc
tuning. Any product-size guard is a new deployment experiment and must retain
the exact unrestricted mode as its control.

The cross-regime transfer experiment adds another firm boundary: learned
clauses that remain useful under an opposite branching trajectory are
measurable, but their normalized use rate did not predict which trajectory
would solve faster. A successor needs a more action-specific counterfactual or
structural signal; changing the smoothing or probe cadence after seeing these
families would only tune a falsified proxy.

The scan-debt experiment adds a clause-management boundary. Exact work
accounting is cheap enough to exercise and deterministic, but raw work since
last use is not marginal cost: the most exposed useful clauses also accumulate
the most debt. Its debt-first comparator displaced 20,349 control choices on
Break, deleted 17,776 positive-score clauses, and increased both conflicts and
learned literals. Normalizing or thresholding that same signal now would be
post-hoc tuning. A separate bounded RUP/re-derivability deletion proposal was
also rejected during collision review because DeepSAT already removes a clause
and tests implicativity with BCP. A successor needs genuinely new information
or intervention semantics, not either proxy with adjusted constants.

The sampled-regularity experiment adds a proof-shape boundary. Exact sampled
pivot collisions survive learned-clause ancestry and can materially change
database reduction, but “retain every witnessed nonregular clause” is not a
general utility model. Its strong dense-REGN interaction does not authorize a
formula-family gate, a larger sample, or a different witness weight on the
revealed data. A successor must change what the proof-shape information does
or obtain a separately justified signal, then preregister before evaluation.

The shadow-reactivation experiment adds a causal boundary. A clause selected
for deletion can be observed without affecting the search, and becoming unit
under that counterfactual trajectory is exact evidence that the deleted clause
would have participated. It is not evidence that returning the clause after a
delay improves the next epoch. On Break, only five reactivations were enough to
increase conflicts 2.67-fold; on gm24, merely enabling state checks imposed a
28.79% repeated regression without starting a shadow. Capacity, horizon,
trigger, restored score, and ranking retuning on these results is closed. A
successor must either use the observation without restoring the clause or ask
a different counterfactual question, with a new hot-path overhead design and a
fresh preregistration.

The counterfactual-phase experiment tested that non-restorative route with no
ordinary-BCP branch. It kept the control deletion set exact and inspected a
64-reference priority sample only at existing root restarts. The observer was
cheap enough to keep endpoint regressions below 5.25% and all logical counters
exact, but it observed zero unit clauses or phase changes on every completed
development case. The signal seen by inline shadows did not survive until the
restart boundary. Capacity, rank, snapshot placement, unanimity, and phase
application are therefore closed to retuning on these results. A successor
must capture different information or justify a new observation event rather
than moving this scan slightly earlier on the same revealed traces.

## Gate 3: interactive SMT foundation and QF_BV

Build the streaming SMT-LIB 2.7 command state machine, typed/hash-consed terms,
sort checking, rewriting, Boolean lowering, model reconstruction, incremental
proof container, and the public context API on the reusable SAT kernel. The
first complete theory track is QF_BV: bit-blast every required operation with
checked encodings, reconstruct total bit-vector models, and pass independent
single-query and incremental validation before performance promotion.

**Status (2026-07-24): partial.** The streaming session, typed Rust API,
hash-consed terms, complete fixed-width operator lowering, models, values,
scopes, assumptions, cores, and deterministic resource limits are implemented.
Exhaustive small-width semantics and 544 deterministic incremental queries
agree with Z3 4.16.0, cvc5 1.3.3, and Bitwuzla 0.9.1. QF_BOOL and QF_BV now
have a query-specific eDRAT-style container: a separate checker reconstructs
active scopes, definitions, resets, assertions, and the complete supported
fixed-width bit-vector lowering from the original script, regenerates the
canonical CNF, and invokes pinned DRAT-trim. Its small-width arithmetic
semantics are exhaustively tested. Standard `get-proof` requests after
nonempty explicit assumption sets are rejected. Fragment-complete independent
model validation, full protocol conformance, sustained fuzzing, and
representative performance evaluation are not complete, so this gate remains
open.

## Gate 4: general CDCL(T) coverage

Add a theory-neutral assignment/propagation/explanation/backtrack/model
interface, then implement QF_UF, extensional arrays, integer and real difference
logic, linear real arithmetic, and linear integer arithmetic. Validate the
required combinations QF_UFBV, QF_ABV, QF_AUFBV, QF_UFIDL, QF_UFLIA,
QF_UFLRA, and QF_AUFLIA. A theory advances only with scoped incremental tests,
independently validated SAT models, independently checked UNSAT artifacts, and
family-disjoint benchmarks.

**Status (2026-07-24): partial.** The theory boundary, model-based explained
congruence closure, QF_UF, QF_UFBV, extensional arrays, QF_ABV, and QF_AUFBV are
implemented. Demand-driven array semantics and permanent theory lemmas agree
with Z3 on 640 UF/UFBV and 384 array/array-combination incremental queries.
Exact QF_IDL uses arbitrary-precision difference constraints; QF_RDL and QF_LRA
use exact rational Fourier–Motzkin elimination. QF_LIA keeps difference logic
as a fast path, enumerates provably finite domains when available, and otherwise
uses exact Cooper elimination with divisibility constraints. Another 1,408
deterministic incremental arithmetic queries agree with Z3, including 384
general LIA queries and arithmetic-`ite` relevance regressions. The typed API
exposes exact Int/Real construction and values. An in-process evaluator rejects
inconsistent arithmetic candidates before `sat`. Shared equality arrangements
now combine arithmetic with congruence closure and extensional arrays for
QF_UFIDL, QF_UFLIA, QF_UFLRA, and QF_AUFLIA. Another 640 generated combination
queries agree with Z3 and cvc5 in scoped sessions. Seventy-two scalar arithmetic
models are replayed as exact bindings through both solvers, while 16 combination
models are replayed in full through both, including function and array
interpretations. Across all implemented fragments, 3,872 deterministic
incremental queries are checked: Z3 covers the full corpus, cvc5 covers every
corpus except 128 custom-sort constant-array queries, and Bitwuzla covers 800
finite QF_BV/QF_AUFBV queries. The
custom-sort/constant-array exclusion records an oracle capability boundary;
`unknown` is never accepted as agreement. Fragment-complete independent model
and proof validation and trail-level theory propagation remain open. These
generated corpora are not a complete validation argument.

## Gate 5: algorithmic research and world-class evaluation

Candidate directions below are hypotheses, not novelty claims. Each first needs
a literature and implementation collision check.

- **Counterfactual propagation credit.** Occasionally sample an alternate
  backtrack/branch action, cheaply estimate propagation avoided or conflicts
  exposed, and use that signal to update branching or restart policy. Test
  whether the extra information beats activity-only proxies after accounting
  for overhead. The rejected trail-reuse gate shows that passive
  propagation/LBD reward is insufficient, and the rejected scan-debt gate
  shows that raw observed work confounds cost with exposure. The rejected
  shadow gate further shows that exact would-propagate evidence does not
  justify delayed clause restoration. A future attempt needs a different
  action, credit target, and low-overhead observation path.
- **Explanation-aware SMT retention.** Score learned clauses using both Boolean
  glue and the stability/cost of their theory explanations. The hypothesis is
  that a clause with modest LBD can still be disproportionately valuable when
  it compresses an expensive recurring theory conflict.
- **Online regime selection with structural context.** Switch among search
  regimes using low-cost dynamic features such as trail locality, glue trend,
  implication depth, and theory-conflict mix. The research question is whether
  contextual selection generalizes across held-out families better than a fixed
  schedule—not whether a bandit can overfit a training corpus. The rejected
  transfer-credit experiment rules out raw opposite-regime clause-use rate as
  a sufficient context-free reward.
- **Adaptive representation boundaries.** Promote/demote constraint fragments
  between native theory handling, bit-blasting, and cached lemmas based on
  measured explanation and propagation cost. This is most promising where the
  same substructure recurs under many contexts.

For each direction: preregister the hypothesis and primary metric, implement a
feature flag, run one-factor ablations, measure overhead separately, test on a
quarantined corpus, and publish negative results. A direction advances only if
its gain survives family breakdowns and repeated runs.

## Definition of success

A performance result is credible when exact source revisions, compiler flags,
competitor binaries, hardware, limits, corpus hashes, raw per-instance results,
and validation artifacts are retained. A novel contribution additionally needs
prior-art review and an ablation showing that the proposed mechanism—not an
uncontrolled bundle—caused the gain.
