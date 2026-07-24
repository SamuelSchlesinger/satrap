# Architecture

The runtime architecture is paired with three validation layers: deterministic
unit/integration tests, pinned differential oracles, and sanitizer-backed
coverage-guided targets. The latter exercise raw SMT-LIB parsing, structured
incremental theory combinations, and SAT model/proof invariants; see
[Fuzzing](FUZZING.md) for the precise boundary.

## Current Boolean kernel

Literals use a packed `u32`: the high bits identify a variable and the low bit
is its sign. Negation is an XOR and literal-indexed arrays can address watch
lists without hashing. Assignments use `i8` values (`-1`, `0`, `1`) in dense
variable-indexed vectors.

Long clauses of length at least three live in one contiguous literal arena.
Stable long-clause metadata stores an arena offset and packed length; the first
two positions in each slice are its active watches. The default arena is
append-only, while `--compact-arena` can reclaim deleted payloads after database
reduction. This removes one heap allocation and pointer chase per long clause
without invalidating watch or reason references.

Binary clauses use separate struct-of-arrays storage: two packed literals, one
byte of learned/deleted flags, and a `u32` activity index per clause. Original
binaries store the sentinel `u32::MAX`; learned binaries index a dense `f64`
activity vector. Clause activity arithmetic and rescaling are therefore exact
without allocating a permanent zero-valued `f64` for every original binary.
A 4-byte nonzero `ClauseRef` tags binary versus long storage in its high bit
and leaves 31 bits for the index. `Option<ClauseRef>` remains four bytes, so
variable reasons need no separate tag or pointer.

Each 8-byte watch packs that tagged reference and a 32-bit blocking literal.
Binary entries directly imply their blocker; longer clauses use the general
watch search. Propagation takes ownership of one watch list while scanning it,
compacts retained entries with separate read/write indices in the same
allocation, and then returns it. Conflict exits shift only the unread suffix,
preserving watch order and therefore the exact search trajectory. Deleted
clauses disappear lazily from watch lists.

The split representation and its sparse activity refinement preserved all
inspected deterministic counters and a byte-identical independently verified
6s268 proof. On that instance it reduced the logical clause/reason payload
from a legacy-equivalent 84,797,376 bytes to 55,396,131 bytes and newly measured
median peak RSS from 323,043,328 to 277,856,256 bytes. The exact 13.987929%
RSS reduction passed the preregistered 10% promotion threshold.

The retained watch remains fixed at eight bytes. A subsequent variable-width
stream encoded binary clause indices in one word and long watches in two. It
preserved exact trajectories and proof bytes and saved 6,994,936 logical watch
bytes on 6s268, but recovering every binary blocker through the clause index
increased retired instructions by 9.57% and regressed all four nontrivial
repeated medians by 7.95–12.57%. The implementation was reverted unchanged.
A direct-other-literal watch coupled to direct-literal binary reasons, as in
Kissat, is a materially different future experiment rather than a permissible
post-result tweak.

Arena collection remembers the earliest clause reference and literal offset
deleted since the preceding pass. It preserves the prefix before that offset,
then visits metadata in stable reference order, skips deleted entries, slides
each live literal slice downward with `copy_within`, and updates only its
offset. Clause metadata indices stay fixed, so watches and reasons need no
relocation. Truncation reclaims logical slots but deliberately retains vector
capacity for subsequent learned clauses. The pass is reduction-synchronous and
does nothing when a reduction deletes no clause.

This mode is proof-checked but non-default. On the frozen development slice it
preserved all inspected deterministic counters, and its real 6s268 proof was
byte-identical to the control. It reclaimed 17.8 million literal slots on
Break, but produced no runtime win on the triggered jointly solved case and
therefore failed its preregistered promotion floor.

Search maintains these invariants:

- every literal on the trail is true under the current assignment;
- conflict analysis identifies a reason's implied literal by variable (the
  binary fast path deliberately avoids rewriting clause positions);
- `trail_limits[n]` is the start of decision level `n + 1`;
- the variable heap contains every variable that can become a future decision,
  possibly plus assigned variables that are discarded lazily; and
- a learned clause returned by conflict analysis is asserting after its
  selected backtrack.

Conflict analysis resolves backward through the implication graph until the
first unique implication point. It bumps variable/clause activity, places the
highest lower-level literal in watch position one, recursively removes literals
whose reasons are covered by the rest of the learned clause, computes LBD,
backtracks, and immediately enqueues the asserting literal.

The default backtrack policy combines ordinary non-chronological first-UIP
jumps with the pinned Kissat/CaDiCaL chronological guard. If a non-unit learned
clause would jump over more than 100 levels, search removes only the current
level and enqueues the asserting literal at the preceding one. Every other
literal in a first-UIP clause is still assigned false below the conflict level,
so the clause remains unit. Learned units always jump to level zero. The
`--no-chrono` ablation restores unconditionally non-chronological backjumping;
counters report both guarded conflicts and the total levels retained.

Restart policies share the same search loop. The default uses a base-100 Luby
schedule. The experimental LBD policy compares the last 50 learned-clause LBDs
with the global mean and can clear that local window when the current trail is
more than 1.4 times its 5,000-conflict moving average after a 10,000-conflict
warm-up. Both the policy and blocking rule are command-line ablations. Luby
remains the default because the initial development corpus showed a large SAT
regression under the dynamic policy despite a strong gain on another family.

Root backtracking remains the default restart behavior. With
`--reuse-trail`, EVSIDS peeks at the best currently unassigned variable and
preserves the longest decision-level prefix whose decision variables have at
least that priority. Assigned heap entries are discarded lazily during the
peek, just as they are during ordinary branching. This implements the
score-based core of CaDiCaL's restart trail reuse without approximating a VMTF
ordering. Its first ablation was sharply complementary across two development
families, so the mode remains explicit.

`--reuse-trail=adaptive` is a rejected online gate retained for reproducibility.
For each restart epoch it records conflicts, propagations, and the sum of
analyzed-clause LBDs. It compares root and reuse actions using
`conflicts^2 / (propagations * LBD-sum)` by saturating integer cross
multiplication, remembers only the latest epoch for each action, and forces
reuse probes on power-of-two eligible events. The default and always-reuse
paths do not accumulate this reward state. The gate preserved the 6s268
development win but made the Break trajectory worse than either fixed action,
showing that cheap within-epoch productivity was not a reliable proxy for
eventual search progress.

Branching regimes are also explicit ablations. EVSIDS uses a lazy activity
heap. VMTF uses an intrusive stamped queue and moves variables encountered in
conflict analysis to the front while preserving their relative recency.
Focused mode couples VMTF with bias-corrected fast/slow LBD exponential
averages; stable mode couples EVSIDS with a reluctant-doubling restart
sequence. The `focused-stable` experiment alternates those modes using
conflict effort, while the two `probe-*` experiments stop focused search after
exactly 100 conflicts and continue under a conventional regime. The
`probe-evsids` variant warms EVSIDS during its probe instead of starting its
second phase cold.

`--search=lrb` uses the published full learning-rate branching policy. Every
assignment records the current learned-clause counter and resets per-variable
participation and reason-side counters. First-UIP analysis credits each
distinct variable on the conflict/learned side; after minimization, it also
credits the union of reason-clause variables adjacent to the final learned
clause, excluding learned variables themselves. On unassignment, the score is
updated by an exponential recency weighted average of
`(participated + reasoned) / interval`. The step size starts at 0.4, decreases
by one millionth per analyzed conflict, and clamps at 0.06.

LRB's locality extension multiplies stale unassigned scores by `0.95^age`.
Doing that eagerly would scan all variables after every conflict, so the
implementation timestamps cancellation and applies the decay only when a
variable is assigned or reaches the heap root. Because a reward can move a
score in either direction, the heap supports both upward and downward repair.
The LRB arrays are allocated only for pure LRB or the explicit dual-warm
transfer experiment, and its three exercise counters remain zero under pure
EVSIDS.

The frozen LRB experiment was correctness- and proof-checked but rejected as
the default. It added a two-second solve and reduced 6s268 from 78,479 to
18,362 conflicts, yet raised Break_12_50 from 118,557 to 870,879 conflicts and
missed every 25-second endpoint limit. The mode is retained because this
complementarity is useful for controlled regime-selection research; it does
not justify tuning LRB parameters on the revealed families.

`--search=transfer` keeps the ordinary activity array and heap as a warm
EVSIDS arm while maintaining a second activity array and heap for full LRB.
Every conflict updates both arms: first-UIP variables bump EVSIDS, while
assignment intervals, participation, reason-side rewards, step-size decay, and
lazy anti-exploration update LRB even when it is not selecting decisions.
Unassignment returns each variable to both heaps. Switching at a root Luby
restart changes only which heap supplies the next decision; phases, clauses,
scores, and interval history remain shared and warm.

Learned non-unit clauses receive an origin tag identifying the active producer
arm. Original clauses and learned units have no origin. A clause earns at most
one transfer credit per restart epoch when it forces propagation, becomes the
propagation conflict, or is traversed by first-UIP while the opposite arm is
active. Credit belongs to the producer, not the consumer. The controller
normalizes distinct credits by epoch conflicts, maintains a 0.25-smoothed
estimate per producer, and uses one unscored EVSIDS bootstrap, eight
alternating scored epochs, then repeating EVSIDS probe, LRB probe, and eight
winner epochs. Exact ties select EVSIDS.

Origin and last-credit epochs are optional side arrays aligned with long and
binary clause indices. They are empty outside transfer mode, so `Clause`,
binary flags, watches, and reasons retain their promoted sizes. Under the
root-restart schedule, every reason clause traversed by analysis was already a
qualifying propagation in that epoch; once-per-epoch deduplication therefore
made the analysis-first counter zero in completed benchmark runs.

The frozen experiment rejected cross-regime use rate as a selector. Both
directions accumulated tens of thousands of credits on 6s268, but the
controller selected EVSIDS for 396 of 444 epochs and took 18.72 seconds versus
LRB's 1.22 seconds. It also timed out on Break and regressed both repeated
jointly solved cases. Pure EVSIDS and LRB counters remained exact, smoke
overhead was 0.78%, and DRAT-trim verified the treatment proof, isolating the
failure to signal alignment rather than correctness or bookkeeping overhead.

`--search=chb` is an independent implementation of the published
Conflict History-Based Branching algorithm. Search begins with zero scores and
zero conflict timestamps. A propagation round collects the variable just
decided or asserted plus every newly propagated variable. Before the current
conflict counter advances, each collected variable receives
`multiplier / (conflicts - last_conflict + 1)`, with multiplier 1.0 for a
conflicting round and 0.9 otherwise, and its score is updated by ERWA. The step
size begins at 0.4, decreases by one millionth at every analyzed conflict, and
clamps at 0.06. First-UIP analysis timestamps every distinct non-root variable
encountered before minimization.

CHB reuses the ordinary maximum heap, but every score update can move in either
direction, so it invokes bidirectional repair. Its conflict timestamps and
propagation-round play vector are allocated only in CHB mode. Three diagnostic
counters distinguish all score updates, score updates ending in conflict, and
conflict-history timestamps; all remain zero under EVSIDS.

The frozen CHB experiment was correctness-checked and retained, but rejected as
the default. It tied the 3/8 development solved count while regressing the
jointly solved pooled median by 170.8%. Break rose from a 3.130-second to a
13.986-second median, and all three 6s268 runs timed out at 25 seconds. A
complete gm24 DRAT proof was independently verified; the designated 6s268
proof requirement failed because no treatment run completed. Unlike LRB, this
CHB baseline exposed no favorable nontrivial development endpoint.

Phase saving is the default. The `--rephase` experiment additionally records
the saved-phase vector whenever backtracking exposes a new maximum trail, then
cycles best, inverted, best, and original phases. Its first reset is after
1,000 conflicts; later intervals use the pinned Kissat
`count * log10(count + 9)^3` scaling. The local-search/walking entries in
Kissat's schedule are deliberately omitted because that mechanism is not
implemented here. This narrower schedule regressed the development cases that
actually triggered it and therefore stays disabled.

`--probe` enables one bounded failed-literal preprocessing pass after initial
root propagation. Variables are visited in index order; their saved phase and
then its complement are temporarily enqueued at decision level one. The same
watched-literal engine propagates each assumption, but const-generic enqueue
and backtrack paths prevent temporary assignments from changing saved phases
or the best-phase snapshot. A conflict proves the opposite unit by RUP, so the
solver logs that unit, installs it at level zero, and propagates its
consequences. The pass stops between attempts after processing
`min(100000, 2 * variables)` probe/root trail literals. It deliberately omits
binary-root scheduling, hyper-binary resolution, and repeated inprocessing.

The first development ablation rejected this pass as a default. Its Break gain
occurred with zero failed literals and therefore came from the propagator's
incidental watch reordering. Conversely, 14 derived units on 6s268 changed the
deterministic search from 5.57 s to 8.06 s, and two units on gm24sparrc
increased conflicts from 147 to 1,280. The root-unit proof path was
independently verified with DRAT-trim; the mode remains useful as a correctness
foundation for stronger simplifiers, not as a promoted heuristic.

`--vivify` adds a separate conservative root-vivification pass. It snapshots
at most 5,000 shortest active original clauses, keeps their current literal
order, and gives the pass at most one million propagated trail literals (or
the initial arena length when smaller). Root-false literals can be removed
directly. Otherwise the pass successively assumes negated clause literals,
with the candidate clause ignored; a BCP conflict or an already-implied
positive literal proves the processed prefix by RUP. Temporary enqueue,
propagation, and backtracking are monomorphized separately from search and do
not update saved or best phases.

A strict strengthening is proof-logged before the old arena clause is marked
deleted, and the deletion emits a `d` step so checkers can drop the old
clause. The replacement receives a fresh stable clause reference and its own
watches; stale watches of the old clause disappear lazily. Units are installed
at level zero and propagated immediately. This is a conservative subset of
modern vivification: there is no conflict analysis, decision-prefix reuse,
learned-clause selection, or repeated inprocessing.

The frozen pass is not the default. It turned gm24sparrc into a
preprocessing-only UNSAT solve with a verified 194-byte DRAT proof and improved
6s268 by 8.8%, but one strengthening and the surrounding watch perturbations
made Break_12_50 about four times slower. The clause replacement and proof
invariants are retained for occurrence-based subsumption and future,
separately gated vivification work.

`--subsume` runs one bounded occurrence-indexed subsumption and
self-subsuming-resolution pass after the other optional root simplifiers.
Active original clauses of length 2–8 are sorted by length and stable
reference, capped at 5,000, and used as the schedule. A single scan builds
occurrence lists only for literals in that schedule; original targets longer
than 64 literals and learned clauses are excluded. Candidate pairs are
deduplicated and charged `|subsuming| + |target|` literal touches, with a cap
of the smaller of five million and the active original non-unit literal count.

Literal marking classifies a target as a pure superset or as an SSR
strengthening with exactly one complementary pivot. Pure supersets are lazily
deleted. SSR clauses are proof-logged before the target is deleted, then
installed at a fresh stable reference; replacements are deliberately absent
from this pass's frozen index and schedule. A unit strengthening is installed
and propagated at level zero. The proof checker independently accepted both a
crafted unit-SSR stream and a real 6s268 stream whose first lemma came from the
preprocessing pass.

This exact schedule is not the default. It met its explicit minimum gate and
was neutral on the two preregistered hard endpoints, but 2,950 SSR
strengthenings on 6s299 increased conflicts from 3,205 to 3,600 and wall time
by 57%. Because the preregistration did not bound every jointly solved case,
the result is retained as an opt-in baseline and the omission is carried
forward into future gate design.

`--eliminate` runs one zero-growth bounded-variable-elimination pass after
every other enabled root simplifier and before search. It indexes every active
non-learned arena clause by literal and schedules root-unassigned variables by
their initial total occurrence count. Pure variables have no occurrence cap;
a mixed pivot may occur at most 100 times. Every positive/negative pair is
resolved after dropping the pivot and root-false literals. Root-satisfied and
tautological pairs produce no clause, while surviving resolvents are
canonicalized and capped at 100 literals.

A pivot commits only when the number of surviving resolvents is no greater
than the number of removed clauses. Pair work is charged by both antecedent
lengths and the entire pass stops at the smaller of one million touches and
the initial active original-clause literal count. Resolvents are proof-logged
before their parents are lazily deleted. Non-units receive fresh stable clause
references, units are installed and propagated at level zero, and generated
clauses are appended to the occurrence lists for later scheduled pivots.

Every accepted pivot and all of its removed clauses are saved. Search assigns
the eliminated variable only to keep it out of the branch heap; after a SAT
result, reverse model extension flips a pivot whenever a saved clause is false
on all non-pivot literals. Installed resolvents prevent simultaneous opposite
requirements. The implementation passed deterministic brute-force
differential testing and original-formula model validation. DRAT-trim verified
both a crafted proof beginning with an elimination resolvent and a real gm24
proof with 2,547 generated resolvents.

The frozen policy remains non-default. It eliminated 51,745 variables and
reduced 6s268 from 78,479 to 52,849 conflicts, improving its repeated median
by 29.3%. But 1,239 eliminations raised Break from 118,557 to 454,296
conflicts and regressed its median by 336.9%; 6s299 also crossed the
preregistered per-case ceiling. This is a sound preprocessing foundation with
a strong family interaction, not a generally beneficial schedule.

`--factor` runs exact quotient-neighborhood bounded variable addition after
the other enabled root simplifiers and zero-growth variable elimination. A
whole-round snapshot canonicalizes every active non-learned clause whose
root-simplified length is 2–5. For each literal `f`, its neighborhood is the
sorted unique set of those clauses with `f` removed. Hash summaries only
identify possible matches; full quotient vectors are compared before a plan is
accepted.

An exact group of `m ≥ 2` factor literals with `n ≥ 2` identical quotients is
the Cartesian matrix `f_i ∨ Q_j`. The pass accepts it only when `mn > m+n`,
orders plans by descending reduction and stable lexical ties, and skips
same-round overlap. It allocates a fresh internal variable `x`, installs
`x ∨ f_i` and `¬x ∨ Q_j`, then lazily deletes the matrix. Rebuilding up to
eight snapshots permits transformations exposed by earlier rounds. Work is
charged by candidate and materialized quotient literals and is bounded by 16
times the first snapshot, clamped to one million–100 million touches.

The replacement is existentially equivalent because the original matrix is
`(∧_i f_i) ∨ (∧_j Q_j)`. Models are built over all internal variables, extended
for eliminated input variables, and finally truncated to the original variable
count. For proofs, every divider is RAT on fresh `x`; every quotient clause is
RAT on `¬x` because resolving it against a divider yields a still-present
matrix clause. The proof writer places that fresh pivot first. DRAT-trim
forward-verified a crafted stream with six RAT steps and a real REGN stream
with 4,230 RAT lemmas in its core.

The frozen unconditional policy is opt-in. It raised five-second REGN coverage
from 1/6 to 4/6 and matched pinned Kissat on that targeted corpus, but reduced
mixed-family development coverage from 5/8 to 4/8. Small `3 × 3` products on
Break changed the search trajectory catastrophically, while full snapshot
scans imposed a roughly 50% cost on 6s268 despite accepting no product. The
mechanism is established preprocessing infrastructure; a conservative
deployment rule requires a separate preregistered experiment.

`--factor-macro` implements that frozen deployment experiment. It requires at
least 16 normalized short input clauses per external variable before snapshot
construction and `mn ≥ 2(m+n)` after exact product verification. All eight
development inputs skip the snapshot, restoring 5/8 coverage and the disabled
search counters on the five completed cases. Reused REGN coverage rises from
exact BVA's 4/6 to 5/6, including one K4-L2 case missed by all pinned
five-second controls, but one already-solved K3-L3 case regresses 41.31%.
Consequently the guarded mode also remains opt-in. Its K3-L1 proof and a crafted
gate-boundary proof are independently verified; the 315 MB K4-L2 proof is
recorded but not yet certified.

`--nonregular-retention` augments only the promoted LBD-free reduction policy.
It allocates parallel ancestry arrays for long and binary clause references:
four `u32` pivot slots and one state byte per clause, or 17 logical bytes.
Those arrays remain empty when the feature is disabled, so the default clause,
watch, and reason layouts are unchanged. Original clauses begin with an empty
sample. Learned binaries are permanent but retain ancestry because later
learned clauses may use them as reasons.

During first-UIP analysis, the conflict clause initializes an ancestry
accumulator. At each non-UIP resolution step, the accumulator merges the
reason clause's sample, records the current pivot, and keeps the four distinct
variables with the smallest deterministic SplitMix64 ranks. If the pivot was
already in either exact sample, the new clause receives a nonregular witness;
it also inherits any witness already carried by a parent. Recursive and binary
learned-clause minimization steps are not added to the sample. That omission
can miss repeats, but every retained pivot and reported collision still comes
from the represented derivation ancestry.

Reduction first computes the same locks, positive-use protections, zero-use
pool, schedule, and deletion count as the promoted policy. It then orders
regular zero-use clauses before witnessed clauses, preserving the existing
length-descending and stable-reference ties within each class. Thus the
treatment changes clause identity, never the quota at a fixed solver state;
when no witness exists its deletion order is exactly the control order.

The frozen experiment exercised the intended mechanism on K4-L2-Seed35:
159,605 tracked pivots produced 841 exact repeat events, 31,071 witnessed
learned clauses, and 36,232 deletion-set displacements. Two executions were
counter-identical apart from wall time. With dense macro BVA the mode added a
sixth five-second REGN solve, but it lost both the no-factor REGN and
mixed-family development coverage gates and exceeded two per-case regression
ceilings. It therefore remains a diagnostic opt-in rather than a promoted
policy. Its bottom-four ancestry signal is not to be resized, reweighted, or
selectively activated from these revealed results.

The 261,458,395-byte K4-L2-Seed35 DRAT certificate was independently verified
against the original 3,306,240-clause CNF. Standard backward DRAT-trim checking
put all input clauses and 222,971 of 376,358 lemmas in the core, including
211,468 RAT lemmas, and used 4,468,616 resolution steps in 6,149.682 seconds.
This certifies the UNSAT answer without trusting the prototype solver; it does
not change the failed performance gate or establish a historically new solve.

`--shadow-reactivation` is a frozen causal diagnostic over the promoted
LBD-free reducer. It computes exactly the control's locked clauses,
positive-score protections, length/reference order, deletion quota, and
would-delete set. Up to 64 lowest SplitMix-ranked members of that set become
shadows; all others are permanently deleted. A shadow leaves the active
learned count and is excluded from later reductions, but its existing watch
entries remain attached.

Ordinary BCP maintains a shadow's blocker, other watch, and replacement watch
exactly as for an active long clause. The shadow may transition from observing
to triggered when it first becomes unit or false, but it never enqueues,
returns a conflict, becomes a reason, earns usage/activity, or enters conflict
analysis. After at least 256 analyzed conflicts, the next root restart expires
an untriggered shadow or restores a triggered shadow with usage score one.
Reactivated clauses are scanned under the root assignment before the next
decision so root units and conflicts are not skipped. Optional aligned
`u8`-state and `u64`-epoch arrays stay empty when disabled; clause, watch,
reason, and literal layouts are unchanged.

The noncausality boundary was observed directly. On pigeonhole 8-into-7 plus
the root unit `-32`, treatment saw ten shadows and two would-unit events but
finished before eligible finalization. It matched control in all 97 comparable
pre-existing non-accounting counters: 4,066 decisions, 48,195 propagations,
3,643 conflicts, 18 restarts, 3,638 learned clauses, 58,249 learned literals,
and three reductions. Permanent-deletion and optional-storage accounting
differed exactly as preregistered.

The delayed feedback nevertheless failed. Five reactivations on Break_12_50
raised conflicts from 37,717 to 100,740 and the endpoint median by 250.08%.
Even when no shadow started, enabled-path state and the hot watch-state check
regressed gm24 by 28.79%. The policy lost development coverage and regressed
the jointly solved aggregate by 11.42%, so it remains disabled and closed to
retuning on these families. A treatment pigeonhole proof exercising
observation, reactivation, and expiry passed strict forward DRAT verification;
no completed UNSAT development case both triggered and reactivated, so the
designated proof gate failed.

`--counterfactual-phase` removes the shadow hot path and clause restoration.
The LBD-free reducer first computes and applies exactly the promoted deletion
set. Each deleted long-clause reference is then offered to a 64-entry
deterministic priority reservoir covering the interval until the next root
restart. The reservoir keeps the lowest SplitMix rank tuples and requires no
per-clause side state; clause-arena compaction is disabled so deleted payloads
and references remain stable.

Before an existing root restart cancels its assignment, the observer scans
each sampled clause once and classifies it as satisfied, open, unit, or false.
Unit clauses vote for their unique unassigned literal. Votes are grouped by
variable; opposite votes cancel, while a unanimous polarity is written to
phase saving after the root backtrack if the variable is root-unassigned. All
samples are then discarded. The scan cannot enqueue, conflict, become a
reason, alter activity, or change the formula.

The frozen run never reached the phase-write path outside unit tests. On
6s268, 1,577 deletion offers yielded 128 boundary scans: 2 clauses were
satisfied and 126 open. All 99 pre-existing non-time counters matched control
exactly. Break scanned 768 clauses, of which 677 were satisfied and 91 open,
again with an exact logical trajectory. The repeated jointly solved aggregate
regressed 4.69% and coverage fell from 5/8 to 4/8 solely from observer
overhead. This closes restart-boundary unit voting on the revealed corpus: the
inline shadow signal was transient and did not survive until the root boundary.

`--binary-minimize` adds a separate one-hop binary-resolution step to conflict
analysis. After recursive reason-graph minimization, a first-UIP clause is
eligible when its length is 2–30 and its LBD is at most 6. The solver epoch
marks every non-asserting learned variable, scans the asserting literal's
existing packed watch list once, and ignores non-binary and deleted entries.
For each active binary clause `(asserting ∨ q)`, a marked learned `¬q` is
removed. Multiple removals are successive resolution steps sharing the
asserting literal. No transitive graph traversal, propagation, binary-clause
generation, or retry is performed.

The mark array is allocated only when the mode is enabled and uses a wrapping
epoch, so the pass allocates nothing per conflict. The LBD and backtrack level
are computed from the final clause, and only that clause is proof-logged.
DRAT-trim verified a crafted proof and a real 6s268 proof whose first changed
lemma removed one literal by this resolution.

The frozen policy remains non-default. Its two-second coverage and
jointly-solved tests passed, including a 14.5% 6s299 gain, but Break regressed
33.6% and 6s268 rose from 78,479 to 484,878 conflicts and timed out in all
three 25-second endpoint runs. This is a proof-safe baseline mechanism with a
strong family interaction, not a promoted heuristic.

These mechanisms are implemented and tested, but none is promoted merely for
existing. The 100-conflict probe had a strong non-additive gain on the
development slice and then failed to improve solved count on the first
family-disjoint held-out slice; it also slowed the one nontrivial jointly
solved held-out SAT instance. EVSIDS with Luby restarts therefore remains the
default.

Learned-clause reduction defaults to the published LBD-free usage policy from
Cai et al. Every learned long clause receives a `u32` score of one in an
optional side array. A clause earns a saturating increment when it forces unit
propagation and whenever first-UIP traverses it as the conflict or a reason;
both events count when both occur. Every 2,048 conflicts, each positive score
of an active learned long clause is decremented. Learned binaries remain
permanent and unscored.

The first reduction occurs at conflict 1,000. After one-indexed reduction
`r`, the next threshold advances by `floor(1000 * sqrt(r))`. Reduction protects
locked and positive-score clauses, sorts the remaining zero-score clauses by
descending length and stable reference, and deletes
`floor((0.90 - 0.40 / log10(r + 9)) * candidates)`. LBD is still computed for
restart policies and diagnostics; “LBD-free” describes retention only. The
default path neither bumps nor decays unused floating clause activity.

The frozen development gate promoted this policy after it added two
two-second solves, improved the repeated Break and 6s268 endpoints by 58.8%
and 88.4%, added 0.44% pooled smoke overhead, repeated exact counters, and
produced a DRAT-trim-verified 6s268 proof. This is an implementation of
established 2026 work, not a novel mechanism. `--no-lbd-free-reduction`
restores the former aggressive activity/LBD policy exactly. Combining that
legacy reducer with `--tiers` enables fixed LBD 2/6 tiers with a three-step
usage age; their first isolated ablation increased search conflicts, so they
remain experimental. Counters expose both reducers' decisions and peak active
learned clauses.

`--scan-debt-reduction` installs an experimental ranking layer over the
LBD-free reducer. A separate `u64` entry aligned with each long-clause
reference counts deterministic logical literal tests in ordinary learned
long-clause propagation: the blocker, the other watch when needed, and each
candidate examined for a replacement. Unit propagation and first-UIP use reset
nonzero debt. Probe and vivification propagation, originals, binaries, and
deleted clauses are excluded.

The reduction schedule, zero-score pool, deletion fraction, and resulting
deletion count stay unchanged. The treatment orders every unlocked learned
long clause by debt descending, usage score ascending, length descending, and
stable reference. A separately computed control set records how many choices
were displaced. When all debts are zero, zero-score clauses form the same
length/reference prefix as the promoted policy, proving exact fallback
equivalence.

The frozen ablation rejected this policy. It tied coverage but regressed the
four-case repeated pooled median by 11.31% and the endpoint pooled median by
14.19%. Break accumulated 151.6 million charged tests; the treatment displaced
20,349 control deletions and deleted 17,776 positive-score clauses, increasing
conflicts from 37,717 to 42,616. The signal tracks high exposure as well as
waste, so this exact comparator remains an opt-in negative result rather than
a default or a novelty claim.

When enabled, each minimized learned clause is streamed as a textual DRAT
addition, every clause deletion is streamed as a `d` step so checkers can
drop deleted clauses instead of carrying them through the remaining proof,
and an UNSAT result appends the empty clause. Proof I/O errors are retained
by the solver and must be checked by the caller.

## Module boundary

```text
 DIMACS CLI                         SMT-LIB session / typed Rust API
      |                                         |
      |                              typed hash-consed terms
      |                                  /             \
      |                         Boolean/BV lowering   UF/arrays
      |                                  \             /
      +----------------------------> clause + theory lemmas
                                             |
                                             v
                                  CDCL search and propagation
                                     |                  ^
                                     v                  |
                               branch/restart      learned clauses
                               heuristics          and explanations
```

The clause API is reusable. `solve_assuming` installs temporary literals as
aligned decision levels, retains globally valid learned clauses across queries,
and walks the implication graph to return a failed subset without making the
permanent context inconsistent. Exact repeated queries are cached. A distinct
query first returns to level zero, so an assumption-only conflict cannot leak
assignments into the next check.

Permanent clauses and variables can be added between queries. New clauses are
evaluated against the existing root closure before their watches are installed,
which prevents already-propagated root literals from hiding a new unit or
conflict. Activation literals implement nested `push`/`pop`: clauses in a frame
contain the negated frame selector, active selectors are query assumptions, and
pop permanently asserts their negations. Learned clauses therefore remain valid
after a frame disappears. Random operation sequences are differentially checked
against brute force.

Bounded variable elimination and variable addition are currently one-shot
equisatisfiable transformations. The fallible incremental API rejects mutation
after either configured pass rather than risking an invalid reconstructed model
or collision with an extension variable. Making those passes scope-aware is a
remaining preprocessing task.

Per-query conflict and propagation budgets cover the main CDCL search, and a
thread-safe interruption token is polled between search iterations and
propagated trail literals. Exhaustion returns `Unknown`, backtracks to the root,
and leaves the context reusable. One-time preprocessing is not yet charged to
those two logical-work budgets.

DRAT additions and deletions remain globally valid across assumption queries,
but an assumption-only UNSAT deliberately does not append the empty clause.
For QF_BOOL, QF_BV, QF_UF, QF_UFBV, QF_ABV, QF_AUFBV, QF_IDL, QF_RDL, and
QF_LRA, `get-proof` instead starts a fresh replay of the active assertion
context and returns a versioned `satrap-edrat` container. Boolean declarations,
named bit positions, sorts, constants, applications, array operations,
extensional witnesses, and affine predicates are canonical proof terms,
independent of internal allocation history. An independent checker reconstructs
the scoped source query, repeats the appropriate finite reduction,
negative-cycle check, or exact Fourier-Motzkin elimination and canonical
Tseitin encoding, then gives the DRAT suffix to pinned DRAT-trim. In accordance
with SMT-LIB 2.7, `get-proof` is rejected after a nonempty
`check-sat-assuming` call. Nested arrays, linear integer arithmetic, and
arithmetic theory combinations remain outside this proof boundary.

## Implemented SMT boundary

`src/smt/term.rs` owns typed, hash-consed Core, bit-vector, uninterpreted, and
array terms. Core is Tseitin-encoded permanently; fixed-width bit-vectors are
lowered to shared Boolean circuits. The public Rust context and streaming
SMT-LIB session share this representation and the same incremental SAT solver.

`Theory` has preparation, required-assignment, level, assignment notification,
propagation, final-check, explanation, backtrack, and model responsibilities.
The current engine gives it one temporary level for each complete SAT model.
UF then builds an explained congruence closure, hashes applications by their
current argument values/classes, and returns either a model fragment or a
blocking lemma. The interface is ready for trail-level use, but the current
integration does not yet propagate theory facts during CDCL search.

Arrays use a hidden select function per structural array sort. Every observed
read stays an application so UF congruence applies. Constant-array and
read-over-write semantics are installed as permanent theory axioms.
Extensional equality introduces a fresh index witness. Read demand propagates
only across array equalities, array-valued `ite`s, and potentially congruent
array-valued applications; it does not build a global array-by-index Cartesian
product.

Arithmetic terms are canonical affine expressions with arbitrary-precision
integer and rational coefficients. Integer difference constraints normalize to
weighted graph edges and use Bellman–Ford negative-cycle detection. General
linear integer arithmetic first enumerates variables with provably finite
constant bounds, then falls back to terminating Cooper elimination; scaling and
explicit divisibility constraints preserve modular contradictions exactly.
Real difference logic and general linear real arithmetic use exact
Fourier–Motzkin elimination with open-bound tracking and reverse model
reconstruction. Arithmetic checking follows the full relevance closure through
selected arithmetic-`ite` conditions while excluding popped formulas.

UF and arithmetic exchange explicit shared equalities. SAT assigns each
relevant equality, the arithmetic solver checks the assignment exactly, and
congruence closure consumes the same literal as an explainable class merge.
The arrangement covers arithmetic arguments and results of uninterpreted
functions as well as array indices and elements. Relevance is recomputed from
active roots and permanent array axioms, so applications left only by popped
assertions do not keep expanding the current arrangement.

Before an arithmetic candidate escapes as `sat`, a separate evaluator checks
the original active roots, exact predicate truth values, integer integrality,
and every relevant selected arithmetic-`ite` branch. Failure is reported as
`unknown`, and model inspection is available only after `sat`; resource or
incompleteness results never manufacture a placeholder model. The integration
suite additionally checks deterministic results against pinned Z3, cvc5, and
Bitwuzla releases. Z3 covers all 3,872 generated queries, cvc5 covers 3,744,
and Bitwuzla covers the 800 finite QF_BV/QF_AUFBV queries within its supported
fragment. It also replays 72 deterministic IDL/LIA/RDL/LRA models as exact
constant bindings through both Z3 and cvc5 and replays 16
arithmetic-combination models in full through both, including function and
array definitions. Each replay requires the original formula to remain
satisfiable. This external corpus is useful independent evidence, not yet a
fragment-complete model-validation architecture.

The implemented layering is:

```text
SMT-LIB parser and typed terms
            |
      rewriting / lowering
            |
  +---------+----------+
  |                    |                    |
bit-vector encoding  UF + extensional arrays  exact linear arithmetic
  |                    |                    |
  +------------------> CDCL <---------------+
             |
       model / proof data
```

Theory lemmas and unconditional axioms are permanent because term definitions
are permanent even when the assertion that first exposed them is scoped.
Proof replay is separate from this live theory path. Ground UF/array replay
assigns finite class bits to canonical ground constants, applications, and
non-`ite` array terms reachable from the query; equality is class-bit equality,
and canonical pairwise congruence implications constrain applications.
UF-valued and array-valued `ite` terms select class labels. Array replay closes
the reachable hidden-select applications, adds constant/read-over-write/`ite`
semantics, and creates one canonical extensional witness for each pair of
ground array terms. Boolean and bit-vector arguments/results retain their
native encodings. The closure is frozen before Boolean lowering and the entire
finite reduction is independently reconstructed before DRAT checking.

Difference-logic replay canonicalizes declared variables, exact affine
predicates, and arithmetic `ite` variables by source structure. A discovery
solver blocks each Boolean candidate whose selected constraints have an exact
negative cycle. The final proof input contains those full-assignment theory
clauses before DRAT search begins. The independent checker recovers every
blocked assignment, repeats integer floor/ceiling or real infinitesimal
negative-cycle detection, and rejects any clause that blocks a satisfiable
assignment.

Resource limits currently charge SAT conflicts/propagations, not parsing,
lowering, theory preparation, proof replay, or final checking. Trail-level
propagation, fragment-complete independent SMT model validation, and
independently checkable proofs for general arithmetic and theory combinations
remain future work.

## Performance policy

Optimize from profiles and hardware counters. Prefer representation changes
that remove cache misses, branches, or allocations over source-level cleverness.
Every optimization must retain the differential suite, and large changes need
a controlled benchmark record. Native CPU instructions are a build-time
choice, never an undocumented source assumption.
