# SAT implementation and research notes

`sat` is a Rust research platform for building genuinely competitive SAT and
SMT solvers. It now has a proof-checked modern CDCL baseline, a streaming
interactive SMT foundation, and one targeted SAT family on which a frozen
treatment matches the pinned reference solver's solved count. The SMT layer
currently covers Core, QF_BV, QF_UF, QF_UFBV, QF_ABV, and QF_AUFBV. That is
substantial implementation progress, not a claim of general or
state-of-the-art SMT performance.

The long-term standard is deliberately demanding: reproducible wins against
pinned versions of leading solvers, independently checked answers, held-out
benchmarks, and algorithmic improvements that survive ablation. “Solved a new
instance” will mean a model or proof artifact that another tool can verify.

## What works now

- compact literals, 4-byte tagged clause references and reasons, 8-byte packed
  watches, separate packed binary-clause storage with sparse learned-only
  activity, a contiguous long-clause arena, optional stable-reference arena
  compaction, allocation-free watch-list scans, and a dependency-free hot path;
- two-watched-literal Boolean constraint propagation;
- first-UIP clause learning, recursive learned-clause minimization, and
  non-chronological backjumping with a 100-level chronological guard against
  destructive long jumps;
- reusable assumption queries with implication-graph failed-assumption
  extraction, learned-state retention, monotone clause addition between
  queries, and activation-literal `push`/`pop` scopes;
- deterministic per-query conflict/propagation limits and a thread-safe
  interruption handle that return `Unknown` without poisoning the reusable
  context;
- a streaming SMT-LIB 2.7 command session plus a typed Rust API, with scoped
  declarations/assertions, `check-sat-assuming`, models, values, assignments,
  assertions, named unsat cores, failed assumptions, deterministic limits, and
  continued command processing after recoverable command errors;
- typed, hash-consed Core and bit-vector terms with complete fixed-width
  QF_BV lowering, including division-by-zero, signed corner cases, rotations,
  extensions, extraction, and the SMT-LIB 2.7 overflow predicates;
- a theory-neutral assignment/explanation/backtrack/model boundary with
  model-based congruence closure for QF_UF and mixed Bool/bit-vector function
  signatures;
- extensional arrays with constant arrays, functional stores, demand-driven
  reads, read-over-write axioms, extensionality witnesses, and combinations
  with UF and bit-vectors;
- one-hop binary-resolution learned-clause minimization behind
  `--binary-minimize` (proof-checked and retained as a non-default ablation);
- EVSIDS, full learning-rate branching (LRB), CHB, VMTF, and an instrumented
  dual-warm EVSIDS/LRB transfer controller, phase saving,
  Luby/reluctant/LBD-EMA restart regimes, focused/stable scheduling
  experiments, LBD scoring, and a usage-driven LBD-free learned-clause
  reducer by default;
- exact post-use learned-clause watch-scan debt behind
  `--scan-debt-reduction` (retained as a proof-checked negative research
  result, not the default);
- noncausal observation of selected clause deletions behind
  `--shadow-reactivation` (retained as a proof-checked negative causal
  diagnostic, not the default);
- restart-boundary would-unit phase voting over already-deleted clauses behind
  `--counterfactual-phase` (retained as a proof-checked negative low-overhead
  diagnostic, not the default);
- specialized binary-clause propagation with ablation switches for both new
  mechanisms;
- instrumented usage-aged learned-clause tiers and dynamic LBD promotion behind
  `--tiers` / `--no-lbd-promotion` (disabled by default after a negative
  development ablation);
- best/inverted/original systematic rephasing behind `--rephase` (disabled by
  default after a negative development ablation);
- score-based EVSIDS restart trail reuse behind `--reuse-trail` (a
  complementary development regime, not the default);
- an action-conditioned online reuse gate behind `--reuse-trail=adaptive`
  (retained as a reproducible negative result, not the default);
- one-pass bounded failed-literal probing behind `--probe`, with phase-isolated
  temporary assumptions and DRAT-checked root units (retained as a
  reproducible negative default-promotion result);
- conservative bounded original-clause vivification behind `--vivify`, with
  stable lazy replacement and DRAT-checked RUP strengthenings (also retained
  as a mixed, non-default experiment);
- one-pass sparse-occurrence short-clause subsumption and self-subsuming
  resolution behind `--subsume`, with proof-checked fresh-clause
  strengthenings (retained as a non-default preprocessing baseline);
- one-pass zero-growth bounded variable elimination behind `--eliminate`, with
  DRAT-checked resolvents and reverse SAT-model reconstruction (retained as a
  non-default preprocessing baseline);
- exact short-clause quotient-neighborhood bounded variable addition behind
  `--factor`, with fresh internal variables, projected SAT models, and
  independently checked RAT proofs (a major REGN win retained as opt-in because
  unconditional use lost a development solve);
- dense-input and macro-product deployment gates behind `--factor-macro`
  (retained as a mixed opt-in result after adding one REGN solve but violating a
  frozen per-case latency ceiling);
- strict DIMACS CNF parsing that still accepts the fused `c=====` comment and
  SATLIB `%` trailer styles found in benchmark corpora;
- SAT Competition output and exit codes (`10` for SAT, `20` for UNSAT);
- streaming textual DRAT output, including clause deletion steps, for
  independently checkable UNSAT results;
- deterministic differential tests against brute force; and
- a benchmark runner that hashes inputs, records machine/run metadata, checks
  SAT models with a constant-memory streaming validator, rejects abnormal
  solver exits, detects solver disagreement, and emits JSONL.

The SMT implementation is deliberately pre-competition. Deterministic
differential corpora currently agree with Z3 4.16.0 on 544 QF_BV, 384 QF_UF,
256 QF_UFBV, 256 QF_ABV, 128 QF_AUFBV, and 1,024 exact QF_IDL/QF_RDL/QF_LRA
incremental queries. This is only one external solver, generated corpora are
not representative benchmarks, SMT models do not yet pass an independent model
validator, and theory UNSAT results do not yet carry independently checkable
proofs. General LIA, required arithmetic combinations, complete protocol
conformance, signal-driven interruption, fuzzing, and the world-class benchmark
gates remain open and are tracked candidly in [the roadmap](ROADMAP.md).

The SAT proof stream has been checked with DRAT-trim on smoke and real
competition instances. A targeted REGN comparison is now competitive with
pinned Kissat 4.0.4, but the small corpus and a failed mixed-family promotion
gate do not support a general competitiveness claim. The benchmark runner also
does not yet validate every UNSAT row.

## Build and run

```sh
cargo test --all-targets
RUSTFLAGS="-C target-cpu=native" cargo build --release
target/release/sat --stats path/to/instance.cnf
target/release/sat --proof result.drat path/to/unsat-instance.cnf
target/release/smt < path/to/query.smt2
```

Input can also be read from standard input. Use `--no-model` to suppress a SAT
assignment and `--help` for the complete interface.

Luby restarts remain the default because the first controlled LBD ablation was
mixed and timed out on a development instance that Luby solved. The dynamic
policy remains reproducible with `--restart=lbd`; its deep-trail guard can be
ablated with `--no-block-restarts`.

The search regimes are reproducible with `--search`. In particular,
`probe-evsids` runs 100 conflicts of focused VMTF/LBD-EMA search before
continuing with warm EVSIDS. It produced large development-set gains, but the
first outcome-blind, family-disjoint held-out gate found no solved-count gain
and a repeatable regression on its jointly solved large SAT case. It therefore
remains an experiment; plain EVSIDS/Luby remains the default.

`--search=lrb` implements the published learning-rate reward, reason-side-rate
extension, decreasing ERWA step size, and lazy anti-exploration decay. Its
frozen development gate exposed unusually strong complementarity: it raised
validated two-second coverage from 3/8 to 4/8, improved the jointly solved
pooled median by 6.50%, cut gm24 by 29.61%, and cut 6s268 by 75.40%. But it
regressed 6s299 by 18.31% and timed out in all three 25-second Break_12_50
runs, where EVSIDS had a 3.07-second median. A 1.55 MB 6s268 DRAT proof was
independently verified. LRB is therefore retained as an established opt-in
baseline, not promoted as the default and not claimed as novel.

`--search=chb` implements the published Conflict History-Based Branching
algorithm: propagation-round ERWA score updates, the 1.0/0.9 conflict
multiplier, inverse conflict-age rewards, and the decreasing 0.4-to-0.06 step
size. Its frozen gate tied EVSIDS at 3/8 validated two-second solves and added
only 0.03% pooled smoke overhead, but the completed nontrivial comparisons all
regressed: gm24 by 142.74%, 6s299 by 200.94%, and Break_12_50 by 346.88%.
Every 6s268 treatment run timed out at 25 seconds. DRAT-trim independently
verified a complete 468 KB CHB proof on gm24; the designated 6s268 proof gate
necessarily failed with the timeouts. CHB is retained as an established
opt-in reference, not promoted and not claimed as novel.

`--search=transfer` is the first new credit-assignment experiment built on the
complementary EVSIDS/LRB baselines. It keeps independent EVSIDS and LRB heaps
warm, tags each learned non-unit clause by its producing regime, and credits
that producer only when the opposite regime later uses the clause for
propagation, conflict, or first-UIP analysis. A preregistered bootstrap,
probe/exploit schedule selects the producer with the greater smoothed
cross-regime use rate. Optional origin/epoch metadata lives in side arrays, so
the pure modes retain their exact layouts and trajectories.

The signal was real but badly misaligned with performance. The frozen
treatment solved 3/8 two-second development instances versus LRB's 4/8 and
regressed 43.54% on 6s299 and 119.24% on gm24 against the faster pure arm.
On the complementary endpoints it chose EVSIDS for 396 of 444 started epochs
on 6s268, taking 18.72 seconds where pure LRB took 1.22 seconds, while all
three Break runs timed out at 25 seconds where EVSIDS took 3.07 seconds. Both
credit directions were heavily exercised, smoke overhead was only 0.78%, pure
EVSIDS/LRB counters remained exact, and DRAT-trim verified the complete 17.7 MB
6s268 proof. The mode is retained as a reproducible negative result; it is not
promoted, tuned on these families, or claimed as novel.

Learned-clause retention now defaults to the published LBD-free policy from
Cai et al., “Rethinking Clause Management for CDCL SAT Solvers” (2026).
Learned long clauses start with a saturating usage score of one; unit
propagation and first-UIP traversal increment it, and every 2,048 conflicts
ages positive scores by one. Reduction first protects locked and positive-score
clauses, then deletes a growing fraction of the longest zero-score clauses.
Learned binaries remain permanent. `--no-lbd-free-reduction` restores the
former LBD/activity reducer exactly.

This established mechanism passed its frozen local gate: validated two-second
coverage rose from 3/8 to 5/8 without a lost solve, Break_12_50's repeated
median fell 58.8%, and 6s268r_Iter94's fell 88.4%. The two already-jointly
solved nontrivial cases each regressed by less than 9%, while pooled smoke
overhead was 0.44%. All SAT models validated, deterministic counters repeated,
and DRAT-trim verified the complete 6s268 proof. These are development results,
not a state-of-the-art or novelty claim; no post-promotion held-out result is
claimed yet.

`--scan-debt-reduction` is the first preregistered intervention on that
promoted policy. An optional `u64` side array charges each learned long clause
for the blocker, other-watch, and replacement-literal tests it triggers after
its latest useful propagation or first-UIP use. Reduction keeps the published
schedule and exact deletion count but orders all unlocked clauses by debt,
then score and length. With every debt zero, its deletion set is exactly the
published control.

The hypothesis failed cleanly. Both variants solved 5/8 development instances,
but the sum of four repeated per-instance medians regressed 11.31%; the two
endpoint medians regressed 4.05% and 18.95%, for a 14.19% pooled regression.
Easy overhead was 1.25%, every SAT model validated, and DRAT-trim verified the
complete 6s268 proof. The counters expose the cause: debt-first ranking
displaced 20,349 baseline deletions on Break and deleted 17,776 clauses whose
usage score was still positive. Raw scan debt therefore confounds avoidable
cost with exposure to active search. The mode remains diagnostic; it will not
be promoted or tuned on these revealed families.

Usage-aged LBD tiers are likewise experimental. The first controlled ablation
increased conflicts sharply on the only development case that exercised
database reduction, without changing solved count across the full slice.
`--tiers --no-lbd-free-reduction` retains the legacy tier mechanism for
research. The contiguous clause arena, by contrast,
preserved identical conflict trajectories and improved every nontrivial
repeated development median. Reusing each watch list's allocation with
in-place read/write compaction preserved those trajectories again and improved
the three nontrivial repeated medians by 16–31 percent. Packing each watch from
16 to 8 bytes then added 4–9 percent on those cases without changing search.

Binary clauses now bypass long-clause metadata and literal-arena storage. A
tagged 4-byte clause reference keeps their stable identities usable by watches,
reasons, proofs, reduction, and every optional preprocessing pass. Original
binary clauses carry only an activity sentinel; exact `f64` activity values are
allocated densely for learned binaries. Against the frozen pre-split binary,
the combined representation preserved every inspected deterministic counter
and a byte-identical DRAT-trim-verified 6s268 proof. It tied the 3/8
two-second development coverage, improved all four nontrivial repeated
medians, reduced the measured logical clause/reason payload by 34.67%, and
reduced newly repeated median peak RSS from 323,043,328 to 277,856,256 bytes
(13.99%). It therefore passed its preregistered gate and is the default.

A follow-up one-word/two-word watch stream kept binary clause indices in its
4-byte entries and derived blockers from the split literal array. It preserved
every inspected counter and proof byte, saved another 6.99 MB of logical watch
payload, and reduced median RSS by 3.77%. The extra indirection nevertheless
raised retired instructions by 9.57% and regressed all four nontrivial repeated
medians by 7.95–12.57%, so the exact design was rejected and the 8-byte packed
watch restored. This does not test Kissat-style direct-literal binary reasons,
which would be a separate semantic change.

Physical literal-arena collection is available with `--compact-arena`. After a
productive database reduction it slides the live suffix downward in stable
clause-reference order, updates only arena offsets, and retains vector capacity
for later learned clauses. Watches and reasons therefore need no relocation.
The frozen ablation preserved every inspected search counter and produced a
byte-identical verified 6s268 proof. It reclaimed 17.8 million literal slots on
Break_12_50, but the only triggered jointly solved case regressed 0.18% instead
of meeting the preregistered 2% improvement floor. The mode remains an opt-in
memory-growth control rather than the default.

Chronological backtracking is enabled by default and can be isolated with
`--no-chrono`. Following the pinned Kissat/CaDiCaL rule, a learned non-unit
clause backtracks only one level when the ordinary first-UIP jump would discard
more than 100 additional levels. On the development corpus this preserved the
same 3/8 short-cutoff solve count and cut the repeated Break_12_50 median from
9.177 s to 5.304 s; a crafted deep-UNSAT proof exercising the path was
independently checked with DRAT-trim.

Systematic rephasing remains available with `--rephase`. It records phases at
the deepest trail seen and cycles best, inverted, best, and original phases on
a 1,000-conflict `n log^3 n` schedule. This intentionally omits Kissat's
local-walk phase. The first ablation kept 3/8 short-cutoff coverage but
regressed Break_12_50 by 58 percent and the large hardware case by 34 percent,
so it is not the default.

Restart trail reuse is also explicit rather than global. At a restart,
`--reuse-trail` keeps the longest prefix of EVSIDS decision levels whose
decisions still outrank the best unassigned variable. It added a verified
fourth 2-second development solve and finished 6s268r_Iter94 in a 0.634 s
repeat median while pinned Kissat and CaDiCaL timed out at 10 seconds, but it
also slowed Break_12_50 from 3.611 s to 19.389 s. The result motivates guarded
online regime selection; it does not justify changing the default.

The first guarded policy has also been tested and rejected without held-out
tuning. `--reuse-trail=adaptive` compares the most recent root and reuse epochs
using conflict yield normalized by propagation work and learned-clause LBD,
with deterministic power-of-two reuse probes. It exactly retained the two
beneficial reuse events on 6s268r_Iter94, but timed out in all three 25-second
Break_12_50 runs; a direct run needed 835,182 conflicts, worse than both root
and always-reuse controls. The mode remains available so the negative result is
reproducible. Root restarts remain the default.

Bounded failed-literal probing is available with `--probe`. It runs once after
initial root propagation, tests saved and opposite phases without changing
phase memory, and emits the negation of every conflicting assumption as a RUP
unit. The frozen pass tied the default at 3/8 development solves and improved
Break_12_50 from a 3.294 s median to 2.243 s, but it found no unit on that
instance: the gain came from incidental watch reordering. On the two UNSAT
cases where it did find units, it regressed gm24sparrc from 147 to 1,280
conflicts and 6s268r_Iter94 from 5.566 s to 8.055 s. DRAT-trim verified both a
crafted proof and the real gm24sparrc proof beginning with the derived units.
The mechanism therefore remains opt-in rather than becoming the default.

Conservative root vivification is available with `--vivify`. It examines at
most 5,000 shortest original clauses, ignores the clause under test, preserves
phase state, and installs only strict current-order prefix or root-simplified
RUP clauses. This machinery produced a real large win: gm24sparrc fell from
0.307 s and 147 search conflicts to 0.043 s and no search conflicts after 24
clauses lost 29 literals and yielded five root units; its 194-byte DRAT proof
was independently verified. It also improved 6s268r_Iter94 by 8.8%. However,
Break_12_50 regressed from a 3.278 s median to 13.051 s after one literal was
removed, violating the frozen promotion gate. The exact schedule therefore
remains opt-in while its proof-safe clause-replacement path is reused for
future simplifiers.

Bounded short-clause subsumption and self-subsuming resolution are available
with `--subsume`. The pass snapshots at most 5,000 shortest original clauses
of length 2–8, builds a sparse occurrence index, and considers original targets
of length at most 64 under a literal-touch budget. Pure supersets are deleted;
an SSR target is proof-logged as a RUP strengthening and installed through the
same stable fresh-clause path as vivification. Both a crafted proof and a real
6s268r_Iter94 proof containing SSR lemmas were independently verified.

The frozen pass passed its explicit minimum gates: 3/8 development solves were
preserved, Break_12_50 improved 1.45%, 6s268r_Iter94 regressed only 1.10%, and
smoke overhead was below noise. It nevertheless remains opt-in because the
gate omitted a per-instance bound for the rest of the solved slice:
6s299b685_Iter22 regressed from 0.314 s to 0.493 s while 2,950 SSR
strengthenings increased search conflicts from 3,205 to 3,600. The result is
recorded as an underspecified promotion gate, not retroactively forced into a
pass/fail threshold.

Zero-growth bounded variable elimination is available with `--eliminate`. The
pass builds complete original-clause occurrence lists, visits root-unassigned
variables once in increasing occurrence order, and resolves positive against
negative occurrences. Mixed pivots are capped at 100 occurrences, resolvents
at 100 literals, and total work at one million antecedent-literal touches.
Every accepted pivot installs no more resolvents than the clauses it removes.
Removed clauses are retained in a reverse extension stack so SAT models cover
the original CNF; resolvents are emitted as RUP additions before arena clauses
are deleted lazily.

The implementation passed 2,000-formula brute-force differential testing,
original-CNF model validation, and independent DRAT-trim checks on a crafted
case and gm24sparrc. The frozen performance gate rejected it as a default. It
tied the control at 3/8 two-second development solves, but the repeated
gm24/6s299 pooled median regressed 8.2%, 6s299 alone regressed 15.5%, and
Break_12_50 regressed from 3.204 s to 13.996 s. Conversely, eliminating 51,745
variables cut 6s268r_Iter94 from 5.354 s to 3.784 s. That split is evidence of
a strong structural interaction, not permission to tune a selector on the
revealed families; the exact pass remains opt-in.

Exact quotient-neighborhood bounded variable addition is available with
`--factor`. At level zero it snapshots active non-learned clauses of
root-simplified length 2–5. Literals with identical complete quotient
neighborhoods form an exact Cartesian product `(f_i ∨ Q_j)`. A strictly
reducing `m × n` product is replaced by `m` clauses `(x ∨ f_i)` and `n` clauses
`(¬x ∨ Q_j)` over a fresh internal variable. The new variable is omitted from
emitted SAT models. Divider and quotient clauses are logged with the fresh
literal first as the RAT pivot; the original matrix remains in the proof
stream.

This closes a concrete baseline gap. On six hash-pinned, family-disjoint REGN
training instances at five seconds, the frozen treatment raised coverage from
1/6 to 4/6, matching pinned Kissat 4.0.4. The smallest case fell from 4.45 s to
0.015 s; a medium case that the control timed out on solved in 0.53 s after
removing a net 818,929 clauses. DRAT-trim forward-verified its real REGN proof,
including 4,230 RAT lemmas in the core.

Unconditional promotion nevertheless failed. Development coverage fell from
5/8 to 4/8: 1,056 accepted `3 × 3` products changed Break_12_50 from 37,717 to
131,742 conflicts and its repeated 25-second median from 1.21 s to 5.71 s.
Even 6s268, where no product was accepted and the search counters stayed
identical, regressed about 50% from snapshot scanning. The exact pass therefore
remains a proof-checked opt-in capability. Its established BVA mechanism is not
claimed as novel; deployment gating and later proof-regularity research are
separate experiments.

`--factor-macro` is the frozen deployment follow-up. It enters snapshot
construction only above 16 normalized short input clauses per external variable
and accepts only products satisfying `mn ≥ 2(m+n)`. The guard restored the
promoted 5/8 development coverage, reproduced the disabled search trajectory on
all five solved development cases, and raised reused REGN coverage from 4/6 to
5/6. The added K4-L2 case solved in a 3.43-second median while the pinned Rust,
Kissat 4.0.4, and CaDiCaL 3.0.1 controls timed out at five seconds. It is not a
promotion: K3-L3-Seed25 regressed 41.31%, violating the preregistered 10% ceiling,
and the large K4-L2 DRAT certificate has now been independently verified. A
smaller guarded REGN proof with 3,206 RAT lemmas also passed strict forward
verification. This is training-derived deployment engineering, not a novelty
or previously-unsolved-instance claim.

`--nonregular-retention` is the first proof-shape research intervention on top
of the promoted LBD-free reducer. When enabled, each clause carries an optional
bottom-four deterministic sample of resolution pivots from its learned-clause
ancestry. Reusing a sampled pivot gives an exact witness that some represented
ancestry path is nonregular; omitted pivots can cause false negatives, not
false positives. At a reduction, witnessed zero-use clauses are deleted after
otherwise equivalent regular clauses without changing the deletion quota.

The frozen result is a useful but rejected split. Combined with
`--factor-macro`, it raised five-second REGN coverage from 5/6 to 6/6 and
deterministically solved K4-L2-Seed35 in a 3.27-second median. On that case it
observed 841 exact sampled repeats and displaced 36,232 baseline deletions.
But no-factor REGN coverage fell from 1/6 to 0/6, development coverage fell
from 5/8 to 4/8, K4-L2-Seed20 regressed 27.54%, and gm24 regressed 29.42%.
The unchanged policy therefore remains disabled and will not be retuned on
these revealed families.

A 250,058-byte treatment proof for K3-L1 passed strict forward DRAT-trim
verification, including 3,206 RAT lemmas. DRAT-trim has now also independently
verified the 261,458,395-byte certificate for the added Seed35 solve against
the original 3,306,240-clause CNF. Its backward core contained all input
clauses and 222,971 of 376,358 proof lemmas, including 211,468 RAT lemmas, and
used 4,468,616 resolution steps in 6,149.682 seconds. Seed35 is therefore a
certified UNSAT result, but it is only a win against the pinned frozen controls
at the declared cutoff—not evidence that the instance was historically or
globally unsolved. The online sampled-ancestry signal is provisionally
distinct after a targeted audit, but no novelty or priority claim is made.

`--shadow-reactivation` tests a different clause-management question. At each
LBD-free reduction it keeps up to 64 control-selected deletions attached as
noncausal shadows. A shadow maintains its own watches and records an exact
would-propagate or would-conflict event, but it cannot enqueue, conflict,
become a reason, earn usage, or otherwise change that observation epoch. After
at least 256 conflicts, a root restart deletes untriggered shadows and
reactivates triggered ones with usage score one.

The frozen experiment showed that the evidence is real but the intervention is
wrong. A real pre-reactivation diagnostic observed two triggers while matching
97 comparable control counters exactly. On Break_12_50, however, five delayed
reactivations increased conflicts from 37,717 to 100,740 and the repeated
endpoint median from 1.294 to 4.529 seconds. Development coverage fell from
5/8 to 4/8, the jointly solved aggregate regressed 11.42%, and gm24 paid 28.79%
enabled-path overhead despite starting no shadows. Easy overhead was 0.65%.
The policy therefore remains disabled and must not be retuned on these revealed
families.

A 240,386-byte pigeonhole treatment proof that exercised a trigger,
reactivation, and expiry passed strict forward DRAT-trim verification. The
stricter designated gate still failed: neither completed UNSAT development
case exercised both a trigger and reactivation. This result is useful evidence
against treating “would have propagated” as sufficient future-utility credit;
it is neither a performance contribution nor a novelty claim.

`--counterfactual-phase` tested the non-restorative successor. Every
control-selected deletion remained deleted; a 64-entry priority reservoir held
only stable references. Immediately before each existing root restart, the
solver classified those clauses under the actual assignment and, after the
root backtrack, would have copied unanimous would-unit literals into phase
saving. It added no watch, clause, reason, literal, or per-clause metadata and
no branch to ordinary BCP.

The signal vanished at that boundary. Break_12_50 scanned 768 samples and
6s268 scanned 128, but every clause was satisfied or still had at least two
unassigned literals. No completed development case produced a unit vote or
phase write, so all logical trajectories remained exact. Even so, development
coverage fell from 5/8 to 4/8 on cutoff overhead, the jointly solved aggregate
regressed 4.69%, and easy overhead was 1.38%. A strict-forward checker verified
the unchanged-trajectory 240,386-byte pigeonhole proof, but the designated
exercised-proof gate necessarily failed. The policy remains disabled and is
closed to snapshot, capacity, or vote retuning on these revealed families.

One-hop binary-resolution learned-clause minimization is available with
`--binary-minimize`. After recursive minimization, learned clauses of length at
most 30 and LBD at most 6 scan only the asserting literal's packed watch list.
A binary clause `(asserting ∨ q)` resolves away `¬q` from the learned clause.
The final shortened lemma remains RUP; DRAT-trim verified both a crafted
pigeonhole proof and a 64 MB real 6s268r_Iter94 proof.

The frozen gate rejected this established mechanism as the default. It kept
3/8 short-cutoff solves, improved the repeated 6s299b685_Iter22 median by
14.5%, moved gm24sparrc by only 1.0%, and added 0.9% pooled smoke overhead.
But 69 removals regressed Break_12_50 by 33.6%, while 6,263 removals raised
6s268r_Iter94 from 78,479 to 484,878 conflicts and turned three 5.36 s control
solves into three 25 s timeouts. The exact eligibility rule remains
reproducible; it will not be tuned on these revealed families.

The native-CPU flag is intentionally opt-in: it is useful for a controlled
local comparison but produces a non-portable binary. The checked-in release
profile enables fat LTO, one codegen unit, and abort-on-panic.

Run every local quality gate with:

```sh
make check
```

## Compare solvers

Build the release binary, obtain a licensed benchmark corpus, pin the exact
competitor binaries, then run:

```sh
python3 tools/benchmark.py \
  --instances /path/to/cnf-corpus \
  --timeout 300 \
  --repeat 3 \
  --solver "ours=target/release/sat" \
  --solver "reference=/path/to/reference-solver" \
  --output results/run.jsonl
```

The runner never invokes a shell. A command containing spaces is parsed with
shell-like quoting; `{instance}` may be used to place the input path somewhere
other than the final argument. See [benchmarking](BENCHMARKING.md) before
interpreting results.

An exploratory single-threaded comparison against Z3 4.16.0 used 32
deterministically generated random 3-SAT formulas at ratio 4.267, three repeats,
and a five-second cutoff. The Rust solver won median solved count 8–6 and PAR-2
7.936–8.382 seconds. It uniquely solved two UNSAT seeds; a 10.2 MB DRAT proof
for one passed both backward and strict-forward independent verification. The
result is deliberately narrow: all solves were at 250 variables, both solvers
timed out on every 500–1,000-variable seed, and Z3 was 3.99× faster by geometric
mean on the six jointly solved formulas. This is evidence of complementary
behavior on random CNF, not a claim that the Rust solver beats Z3 generally or
implements competitive SMT.

An eight-instance, mixed-family development slice from SAT Competition 2025 can
be fetched and hash-verified without committing third-party instances:

```sh
python3 tools/fetch_corpus.py
```

Its manifest explicitly marks it as a small development set, not a held-out or
representative competition corpus.

The initial held-out gate is independently selected from the official 2025
Main Track metadata. Reproduce the selection and fetch its 16 hash-pinned
instances with:

```sh
python3 tools/select_heldout.py \
  --database /path/to/meta.db \
  --exclude-manifest benchmarks/manifests/satcomp-2025-development.json
python3 tools/fetch_corpus.py \
  --manifest benchmarks/manifests/satcomp-2025-heldout.json \
  --output benchmarks/downloaded/satcomp-2025-heldout
```

This is a small initial generalization check, not a representative substitute
for the full 400-instance track and not a state-of-the-art claim.

## How SMT is being built on SAT

SMT is not one algorithm or one leaderboard. This project layers typed terms,
Boolean/bit-vector lowering, and theory explanations over the reusable SAT
kernel. The present UF/array integration checks complete Boolean models and
learns permanent explained lemmas; its interface is trail-shaped, but native
theory propagation is not yet connected to the live CDCL trail. That
distinction matters: the current solver is interactive and semantically useful,
but arithmetic coverage, proof production, conformance, and competition-scale
performance still separate it from a general world-class SMT solver.

## Repository map

- `src/solver.rs`: CDCL search and hot data structures.
- `src/smt/`: typed terms, SMT-LIB session, Rust API, lowering, theory boundary,
  UF congruence closure, and extensional arrays.
- `src/dimacs.rs`: DIMACS parser.
- `src/main.rs`: competition-compatible command-line interface.
- `src/bin/smt.rs`: streaming SMT-LIB command-line interface.
- `tests/`: differential, structured, and end-to-end correctness tests.
- `tools/benchmark.py`: reproducible head-to-head runner.
- `tools/summarize_benchmark.py`: repeated-run solved-count, PAR-2, and paired
  head-to-head summaries.
- `tools/fetch_corpus.py`: manifest-driven, hash-checked corpus acquisition.
- `tools/generate_random_ksat.py`: deterministic uniform random k-SAT
  generation.
- `tools/generate_pigeonhole.py`: deterministic structured CNF generation for
  regression and proof tests.
- `tools/select_heldout.py`: deterministic, family-disjoint corpus selection.
- `experiments/`: preregistration template for algorithmic experiments.
- `docs/`: architecture, benchmarking protocol, and staged research roadmap.

Contributions should preserve the distinction between a hypothesis, a measured
result, and an independently verified claim. See
[CONTRIBUTING.md](../CONTRIBUTING.md).
