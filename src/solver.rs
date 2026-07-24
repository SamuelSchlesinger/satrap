use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::fmt;
use std::io::Write;
use std::num::NonZeroU32;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering as AtomicOrdering};

use crate::proof::DratWriter;
use crate::types::MAX_VARIABLES;
use crate::{Lit, Var};

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
struct ClauseRef(NonZeroU32);

impl ClauseRef {
    const BINARY_BIT: u32 = 1 << 31;
    const INDEX_MASK: u32 = Self::BINARY_BIT - 1;

    fn long(index: usize) -> Self {
        Self::new(index, false)
    }

    fn binary(index: usize) -> Self {
        Self::new(index, true)
    }

    fn new(index: usize, binary: bool) -> Self {
        let index = u32::try_from(index).expect("clause reference does not fit u32");
        assert!(
            index < Self::INDEX_MASK,
            "clause reference exceeds packed 31-bit range"
        );
        let packed = index | if binary { Self::BINARY_BIT } else { 0 };
        Self(NonZeroU32::new(packed + 1).expect("packed clause reference must be nonzero"))
    }

    fn from_packed(packed: u32) -> Self {
        assert_ne!(packed, u32::MAX, "reserved packed clause reference");
        Self(NonZeroU32::new(packed + 1).expect("packed clause reference must be nonzero"))
    }

    fn packed(self) -> u32 {
        self.0.get() - 1
    }

    fn index(self) -> usize {
        (self.packed() & Self::INDEX_MASK) as usize
    }

    fn is_binary(self) -> bool {
        self.packed() & Self::BINARY_BIT != 0
    }
}

const UNASSIGNED: i8 = 0;
const TRUE: i8 = 1;
const FALSE: i8 = -1;
const NO_POSITION: usize = usize::MAX;

/// A complete satisfying assignment.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Model {
    values: Vec<bool>,
}

impl Model {
    /// Number of variables in the model.
    #[must_use]
    pub fn len(&self) -> usize {
        self.values.len()
    }

    /// Whether the model contains no variables.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
    }

    /// Returns a variable's assigned Boolean value.
    ///
    /// # Panics
    ///
    /// Panics when `variable` was not present in the solved formula.
    #[must_use]
    pub fn value(&self, variable: Var) -> bool {
        self.values[variable.index()]
    }

    /// Returns a literal's value under this model.
    ///
    /// # Panics
    ///
    /// Panics when the literal's variable was not present in the formula.
    #[must_use]
    pub fn literal_value(&self, literal: Lit) -> bool {
        self.value(literal.var()) == literal.is_positive()
    }

    /// Iterates over values in ascending variable order.
    pub fn iter(&self) -> impl ExactSizeIterator<Item = bool> + '_ {
        self.values.iter().copied()
    }
}

/// The result of a SAT solve.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SolveResult {
    /// The formula is satisfiable, with a complete model.
    Sat(Model),
    /// The formula is unsatisfiable.
    Unsat,
    /// Search stopped without a satisfiability conclusion.
    Unknown(UnknownReason),
}

impl SolveResult {
    /// Returns whether the result is satisfiable.
    #[must_use]
    pub const fn is_sat(&self) -> bool {
        matches!(self, Self::Sat(_))
    }

    /// Returns whether the result is unsatisfiable.
    #[must_use]
    pub const fn is_unsat(&self) -> bool {
        matches!(self, Self::Unsat)
    }

    /// Returns whether search stopped without a conclusion.
    #[must_use]
    pub const fn is_unknown(&self) -> bool {
        matches!(self, Self::Unknown(_))
    }
}

/// Why a solve returned [`SolveResult::Unknown`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum UnknownReason {
    /// An external interruption token was set.
    Interrupted,
    /// The per-query conflict budget was exhausted.
    ConflictLimit,
    /// The per-query propagation budget was exhausted.
    PropagationLimit,
    /// A theory combination or operator was parsed safely but its complete
    /// decision procedure is not implemented.
    IncompleteTheory,
    /// A candidate theory model failed the solver's exact validation pass and
    /// was therefore not returned as satisfiable.
    ModelValidationFailure,
}

/// Deterministic CDCL work limits for one query.
///
/// Limits count main-search conflicts and propagated trail literals. One-time
/// root preprocessing is deliberately outside these counters.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct SolveLimits {
    /// Maximum conflicts analyzed by this query.
    pub conflicts: Option<u64>,
    /// Maximum trail literals propagated by this query.
    pub propagations: Option<u64>,
}

/// A thread-safe handle that can interrupt a running [`Solver`].
#[derive(Clone, Debug)]
pub struct Interrupter {
    flag: Arc<AtomicBool>,
}

impl Interrupter {
    /// Requests interruption. The solver observes this at bounded points in
    /// propagation and between search iterations.
    pub fn interrupt(&self) {
        self.flag.store(true, AtomicOrdering::Release);
    }

    /// Clears a previous request so the context can be queried again.
    pub fn clear(&self) {
        self.flag.store(false, AtomicOrdering::Release);
    }

    /// Whether interruption is currently requested.
    #[must_use]
    pub fn is_interrupted(&self) -> bool {
        self.flag.load(AtomicOrdering::Acquire)
    }
}

/// A safe failure from an incremental mutation of a solver context.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum IncrementalError {
    /// A one-shot equisatisfiable preprocessing pass has already transformed
    /// the permanent formula, so adding clauses could invalidate its model
    /// reconstruction or reuse an internal extension variable.
    IrreversiblePreprocessing,
    /// More variables were requested than fit in the packed literal format.
    VariableLimit,
    /// The process could not reserve storage for an incremental mutation.
    ResourceExhausted,
    /// More scopes were popped than are currently active.
    ScopeUnderflow,
}

impl fmt::Display for IncrementalError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::IrreversiblePreprocessing => formatter.write_str(
                "incremental mutation is unavailable after variable elimination or addition",
            ),
            Self::VariableLimit => formatter.write_str("packed Boolean variable limit exceeded"),
            Self::ResourceExhausted => {
                formatter.write_str("insufficient memory for incremental mutation")
            }
            Self::ScopeUnderflow => formatter.write_str("cannot pop beyond the base scope"),
        }
    }
}

impl std::error::Error for IncrementalError {}

/// Search mechanisms that can be ablated without maintaining divergent code.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SolverConfig {
    /// Recursively remove literals implied by the rest of each learned clause.
    pub minimize_learned_clauses: bool,
    /// Further minimize short low-LBD learned clauses by direct binary resolution.
    pub binary_resolution_minimization: bool,
    /// Physically reclaim deleted literal payloads after database reduction.
    pub compact_clause_arena: bool,
    /// Run one zero-growth bounded variable-elimination pass before search.
    pub bounded_variable_elimination: bool,
    /// Factor exact short-clause products through fresh extension variables.
    pub bounded_variable_addition: bool,
    /// Gate BVA on dense input and retain only macro-scale exact products.
    pub macro_bounded_variable_addition: bool,
    /// Run one bounded failed-literal probing pass before the first decision.
    pub failed_literal_probing: bool,
    /// Run one bounded original-clause vivification pass before search.
    pub clause_vivification: bool,
    /// Run one bounded short-clause subsumption and SSR pass before search.
    pub clause_subsumption: bool,
    /// Propagate binary clauses without entering the general-clause watch path.
    pub binary_fast_path: bool,
    /// Policy used to decide when the search should restart from level zero.
    pub restart_policy: RestartPolicy,
    /// Defer LBD restarts while the current trail is unusually deep.
    pub block_lbd_restarts: bool,
    /// Branching and restart regime used by the main search loop.
    pub search_strategy: SearchStrategy,
    /// Protect low-LBD learned clauses and age a middle retention tier.
    pub tiered_clause_management: bool,
    /// Replace LBD/activity reduction with decaying clause-usage scores.
    pub lbd_free_clause_management: bool,
    /// Rank a fixed LBD-free deletion quota by post-use propagation scan debt.
    pub scan_debt_clause_management: bool,
    /// Retain zero-use clauses carrying sampled nonregular derivation witnesses.
    pub nonregular_clause_retention: bool,
    /// Observe a bounded sample of deleted clauses and reactivate real triggers.
    pub shadow_clause_reactivation: bool,
    /// Let unanimous would-unit literals from sampled deletions update saved phases.
    pub counterfactual_phase_voting: bool,
    /// Recompute and lower a learned clause's LBD when analysis reuses it.
    pub promote_clause_lbd: bool,
    /// Preserve intermediate decision levels after exceptionally long backjumps.
    pub chronological_backtracking: bool,
    /// Periodically reset saved decision phases using a deterministic schedule.
    pub systematic_rephasing: bool,
    /// Policy for preserving high-priority EVSIDS decision prefixes at restarts.
    pub restart_trail_reuse: RestartTrailReuse,
}

impl Default for SolverConfig {
    fn default() -> Self {
        Self {
            minimize_learned_clauses: true,
            binary_resolution_minimization: false,
            compact_clause_arena: false,
            bounded_variable_elimination: false,
            bounded_variable_addition: false,
            macro_bounded_variable_addition: false,
            failed_literal_probing: false,
            clause_vivification: false,
            clause_subsumption: false,
            binary_fast_path: true,
            restart_policy: RestartPolicy::Luby,
            block_lbd_restarts: true,
            search_strategy: SearchStrategy::Evsids,
            tiered_clause_management: false,
            lbd_free_clause_management: true,
            scan_debt_clause_management: false,
            nonregular_clause_retention: false,
            shadow_clause_reactivation: false,
            counterfactual_phase_voting: false,
            promote_clause_lbd: true,
            chronological_backtracking: true,
            systematic_rephasing: false,
            restart_trail_reuse: RestartTrailReuse::Never,
        }
    }
}

/// Restart policies available for controlled experiments.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RestartPolicy {
    /// Static universal schedule with a base interval of 100 conflicts.
    Luby,
    /// Restart when the recent learned-clause LBD average degrades relative
    /// to the global average.
    Lbd,
}

/// Policies for reusing a score-valid prefix of the assignment trail.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RestartTrailReuse {
    /// Always restart to decision level zero.
    Never,
    /// Always retain the longest EVSIDS prefix ahead of the score frontier.
    Always,
    /// Select root or reused restarts from recent action-conditioned productivity.
    Adaptive,
}

/// High-level search strategies available for controlled experiments.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SearchStrategy {
    /// A single EVSIDS regime governed by [`SolverConfig::restart_policy`].
    Evsids,
    /// Learning-rate branching with reason-side rewards and anti-exploration.
    Lrb,
    /// Dual-warm EVSIDS/LRB search selected by cross-regime clause transfer.
    Transfer,
    /// Conflict-history branching with propagation-round ERWA rewards.
    Chb,
    /// A single VMTF regime governed by [`SolverConfig::restart_policy`].
    Vmtf,
    /// VMTF branching with fast/slow LBD exponential-average restarts.
    Focused,
    /// Run 100 focused conflicts, then continue with warm-started EVSIDS.
    ProbeEvsids,
    /// Run 100 focused conflicts, then keep VMTF under the configured restart policy.
    ProbeVmtf,
    /// Alternate focused VMTF/EMA search with stable EVSIDS/reluctant search.
    FocusedStable,
}

/// Cumulative counters from a solver run.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct SolverStats {
    /// Branching decisions made.
    pub decisions: u64,
    /// Trail literals processed by Boolean constraint propagation.
    pub propagations: u64,
    /// Conflicts encountered.
    pub conflicts: u64,
    /// Search restarts performed.
    pub restarts: u64,
    /// Restarts that retained at least one decision level.
    pub trail_reuse_restarts: u64,
    /// Decision levels retained across all reused restarts.
    pub trail_reuse_levels: u64,
    /// Restarts at which the ordinary score-frontier reuse level was nonzero.
    pub trail_reuse_eligible_restarts: u64,
    /// Adaptive reuse actions forced by the logarithmic probe schedule.
    pub adaptive_reuse_probes: u64,
    /// Adaptive reuse actions selected by measured epoch quality.
    pub adaptive_reuse_quality_accepts: u64,
    /// Adaptive root actions selected by measured epoch quality.
    pub adaptive_reuse_quality_rejects: u64,
    /// Root-action epochs sampled by the adaptive policy.
    pub adaptive_root_epochs: u64,
    /// Reuse-action epochs sampled by the adaptive policy.
    pub adaptive_reuse_epochs: u64,
    /// Conflicts that used a one-level chronological backtrack.
    pub chronological_backtracks: u64,
    /// Decision levels retained instead of discarded by chronological backtracking.
    pub chronological_levels_preserved: u64,
    /// Systematic phase resets performed.
    pub rephases: u64,
    /// Phase resets that restored the best recorded trail.
    pub best_rephases: u64,
    /// Phase resets that selected the inverted initial phase.
    pub inverted_rephases: u64,
    /// Phase resets that selected the original initial phase.
    pub original_rephases: u64,
    /// Deeper trails copied into the best-phase snapshot.
    pub best_phase_updates: u64,
    /// LBD restart signals suppressed by an unusually deep trail.
    pub blocked_restarts: u64,
    /// Switches between focused and stable search modes.
    pub mode_switches: u64,
    /// Conflicts analyzed while focused search was active.
    pub focused_conflicts: u64,
    /// Conflicts analyzed while stable search was active.
    pub stable_conflicts: u64,
    /// Decisions made while focused search was active.
    pub focused_decisions: u64,
    /// Decisions made while stable search was active.
    pub stable_decisions: u64,
    /// Restarts performed in focused search.
    pub focused_restarts: u64,
    /// Restarts performed in stable search.
    pub stable_restarts: u64,
    /// Assigned-to-unassigned intervals that updated an LRB score.
    pub lrb_unassign_updates: u64,
    /// Distinct reason-side variables rewarded by LRB.
    pub lrb_reason_side_rewards: u64,
    /// Stale LRB scores lazily decayed by anti-exploration.
    pub lrb_anti_exploration_decays: u64,
    /// Transfer-controller epochs that began with EVSIDS active.
    pub transfer_evsids_epochs: u64,
    /// Transfer-controller epochs that began with LRB active.
    pub transfer_lrb_epochs: u64,
    /// Transfer-controller changes of the active branching regime.
    pub transfer_mode_switches: u64,
    /// Distinct cross-regime uses credited to EVSIDS-origin clauses.
    pub transfer_evsids_origin_credits: u64,
    /// Distinct cross-regime uses credited to LRB-origin clauses.
    pub transfer_lrb_origin_credits: u64,
    /// Cross-regime credits first observed during Boolean propagation.
    pub transfer_bcp_credits: u64,
    /// Cross-regime credits first observed during conflict analysis.
    pub transfer_analysis_credits: u64,
    /// Decided, propagated, or asserted variables whose CHB scores were updated.
    pub chb_score_updates: u64,
    /// CHB score updates whose propagation round ended in conflict.
    pub chb_conflict_score_updates: u64,
    /// Variables whose latest CHB conflict-analysis timestamp was updated.
    pub chb_conflict_history_updates: u64,
    /// Learned non-unit clauses allocated.
    pub learned_clauses: u64,
    /// Literals retained across all learned clauses, including learned units.
    pub learned_literals: u64,
    /// Literals removed by recursive learned-clause minimization.
    pub minimized_literals: u64,
    /// Short low-LBD learned clauses scanned for direct binary resolution.
    pub binary_minimization_clauses: u64,
    /// Watch entries inspected by direct binary-resolution minimization.
    pub binary_minimization_watch_visits: u64,
    /// Learned literals removed by direct binary resolution.
    pub binary_minimized_literals: u64,
    /// Reduction-synchronous physical clause-arena compactions performed.
    pub arena_compactions: u64,
    /// Live literal slots physically moved by clause-arena compaction.
    pub arena_moved_literals: u64,
    /// Deleted literal slots reclaimed by clause-arena compaction.
    pub arena_reclaimed_literals: u64,
    /// Maximum logical clause-arena length while compaction was enabled.
    pub peak_arena_literals: u64,
    /// Current logical clause-arena length while compaction is enabled.
    pub arena_literals: u64,
    /// Current unreclaimed deleted literal slots while compaction is enabled.
    pub arena_garbage_literals: u64,
    /// Root-unassigned variables removed by bounded variable elimination.
    pub eliminated_variables: u64,
    /// Positive/negative clause pairs considered during elimination.
    pub elimination_pairs: u64,
    /// Clause-literal touches charged to elimination effort.
    pub elimination_literal_touches: u64,
    /// Pivot clauses removed by accepted eliminations.
    pub elimination_removed_clauses: u64,
    /// Non-tautological resolvents installed by accepted eliminations.
    pub elimination_resolvents: u64,
    /// Unit resolvents installed at level zero.
    pub elimination_units: u64,
    /// Candidate variables rejected by occurrence, growth, size, or effort limits.
    pub elimination_rejections: u64,
    /// Clauses saved for reverse SAT-model reconstruction.
    pub elimination_extension_clauses: u64,
    /// Literals saved for reverse SAT-model reconstruction.
    pub elimination_extension_literals: u64,
    /// Whole-snapshot exact-neighborhood factoring rounds attempted.
    pub factorization_rounds: u64,
    /// Short original clauses indexed across all factoring rounds.
    pub factorization_candidate_clauses: u64,
    /// Root-simplified literals and quotient entries charged to factoring.
    pub factorization_literal_touches: u64,
    /// Fresh extension variables introduced by accepted factorizations.
    pub factored_variables: u64,
    /// Original matrix clauses removed by accepted factorizations.
    pub factorization_clauses_removed: u64,
    /// Divider and quotient clauses installed by accepted factorizations.
    pub factorization_clauses_added: u64,
    /// Net clause-count decrease across accepted factorizations.
    pub factorization_clause_reduction: u64,
    /// Largest factor set in an accepted exact product.
    pub factorization_peak_factors: u64,
    /// Largest quotient neighborhood in an accepted exact product.
    pub factorization_peak_quotients: u64,
    /// Normalized input clauses of length two through five.
    pub factorization_input_short_clauses: u64,
    /// Dense-macro input eligibility checks.
    pub factorization_density_checks: u64,
    /// Dense-macro checks that skipped snapshot construction.
    pub factorization_density_skips: u64,
    /// Exact products rejected because they removed less than half the matrix.
    pub factorization_macro_rejections: u64,
    /// Temporary literal assumptions tested during root-level probing.
    pub failed_literal_probes: u64,
    /// Root-level units proved by failed-literal probing.
    pub failed_literal_units: u64,
    /// Trail literals propagated by probes and their derived root units.
    pub probing_propagations: u64,
    /// Original clauses examined by root-level vivification.
    pub vivification_checks: u64,
    /// Original clauses replaced by a strict vivified strengthening.
    pub vivified_clauses: u64,
    /// Literals removed across all installed vivified clauses.
    pub vivified_literals: u64,
    /// Vivified clauses that became root-level units.
    pub vivified_units: u64,
    /// Trail literals propagated while vivifying clauses.
    pub vivification_propagations: u64,
    /// Unique short-clause/target pairs classified for subsumption or SSR.
    pub subsumption_checks: u64,
    /// Clause-literal touches charged to bounded subsumption work.
    pub subsumption_literal_touches: u64,
    /// Entries stored in the temporary sparse occurrence index.
    pub subsumption_occurrences: u64,
    /// Original clauses removed because another clause subsumed them.
    pub subsumed_clauses: u64,
    /// Original clauses strengthened by self-subsuming resolution.
    pub self_subsumed_clauses: u64,
    /// Literals removed by self-subsuming resolution.
    pub self_subsumed_literals: u64,
    /// Self-subsuming resolutions that produced a root unit.
    pub self_subsumed_units: u64,
    /// Binary watch entries handled by the specialized propagation path.
    pub binary_watch_visits: u64,
    /// Binary clauses represented in the separate compact storage.
    pub stored_binary_clauses: u64,
    /// Clauses of length at least three represented in the long-clause arena.
    pub stored_long_clauses: u64,
    /// Logical bytes occupied by binary literals, activities, and flags.
    pub binary_storage_bytes: u64,
    /// Logical bytes occupied by long-clause metadata and literal payloads.
    pub long_storage_bytes: u64,
    /// Logical bytes occupied by compact per-variable reason references.
    pub reason_storage_bytes: u64,
    /// Logical bytes the same clauses and reasons used in the legacy layout.
    pub legacy_equivalent_storage_bytes: u64,
    /// Learned clauses removed from the active database.
    pub deleted_clauses: u64,
    /// Learned-clause database reductions performed.
    pub reductions: u64,
    /// Learned clauses created directly in the strongest LBD <= 2 tier.
    pub learned_tier1_clauses: u64,
    /// Learned clauses created directly in the aging 3 <= LBD <= 6 tier.
    pub learned_tier2_clauses: u64,
    /// Learned clauses whose LBD improved when reused during analysis.
    pub promoted_clauses: u64,
    /// Tier-one clauses protected across database reductions.
    pub tier1_protections: u64,
    /// Recently used tier-two clauses protected across database reductions.
    pub tier2_protections: u64,
    /// Learned long-clause usage increments caused by unit propagation.
    pub clause_usage_bcp_increments: u64,
    /// Learned long-clause usage increments caused by first-UIP traversal.
    pub clause_usage_analysis_increments: u64,
    /// Periodic passes that aged all active learned long-clause usage scores.
    pub clause_usage_decay_passes: u64,
    /// Positive learned long-clause scores decremented by usage aging.
    pub clause_usage_scores_decayed: u64,
    /// Unlocked learned long clauses retained because their usage score was positive.
    pub clause_usage_positive_protections: u64,
    /// Unlocked zero-score learned long clauses considered by length-only reduction.
    pub clause_usage_zero_candidates: u64,
    /// Learned long-clause literal tests charged as post-use propagation debt.
    pub clause_scan_debt_literal_checks: u64,
    /// Beneficial uses that reset a nonzero learned-clause scan debt.
    pub clause_scan_debt_nonzero_resets: u64,
    /// Maximum post-use scan debt observed for any learned long clause.
    pub clause_scan_debt_peak: u64,
    /// Treatment deletions absent from the promoted zero-score/length deletion set.
    pub clause_scan_debt_selection_displacements: u64,
    /// Positive-score learned clauses deleted by the scan-debt treatment.
    pub clause_scan_debt_positive_deletions: u64,
    /// Zero-score baseline deletions retained because of scan-debt displacement.
    pub clause_scan_debt_zero_rescues: u64,
    /// First-UIP resolution pivots incorporated into ancestry samples.
    pub regularity_resolution_pivots: u64,
    /// Resolution pivots exactly found in a tracked parent-ancestry sample.
    pub regularity_sampled_repeat_witnesses: u64,
    /// Learned non-unit clauses born with or inheriting a nonregular witness.
    pub regularity_nonregular_learned_clauses: u64,
    /// Witnessed nonregular clauses entering the unlocked zero-score pool.
    pub regularity_nonregular_zero_candidates: u64,
    /// Treatment deletions absent from the promoted length-only deletion set.
    pub regularity_selection_displacements: u64,
    /// Witnessed baseline deletions retained by regular-first ordering.
    pub regularity_nonregular_rescues: u64,
    /// Witnessed clauses deleted after the regular candidate pool was exhausted.
    pub regularity_nonregular_deletions: u64,
    /// Logical bytes used by optional pivot samples and state arrays.
    pub regularity_metadata_bytes: u64,
    /// Learned clauses removed from active propagation as counterfactual shadows.
    pub shadow_clauses_started: u64,
    /// Maximum number of simultaneously observing or triggered shadows.
    pub shadow_active_peak: u64,
    /// Shadow watch entries processed by ordinary search propagation.
    pub shadow_watch_visits: u64,
    /// Shadow literals tested while maintaining noncausal watches.
    pub shadow_literal_checks: u64,
    /// Observing shadows that first became unit under the actual search.
    pub shadow_unit_triggers: u64,
    /// Observing shadows that first became false under the actual search.
    pub shadow_conflict_triggers: u64,
    /// Triggered shadows restored to active propagation at a root boundary.
    pub shadow_reactivated_clauses: u64,
    /// Untriggered shadows permanently deleted after their observation horizon.
    pub shadow_expired_clauses: u64,
    /// Reactivated clauses that were unit under the root assignment.
    pub shadow_root_units: u64,
    /// Reactivated clauses that were false under the root assignment.
    pub shadow_root_conflicts: u64,
    /// Baseline deletions not shadowed because the frozen capacity was full.
    pub shadow_capacity_skips: u64,
    /// Active-database removals, including both shadows and immediate deletions.
    pub shadow_effective_removals: u64,
    /// Sum of analyzed-conflict ages of all finalized shadows.
    pub shadow_observation_conflicts: u64,
    /// Logical bytes used by optional shadow state, epochs, and live references.
    pub shadow_metadata_bytes: u64,
    /// Control-selected deletions offered to the restart-interval priority sample.
    pub counterfactual_phase_deletion_offers: u64,
    /// Deleted-clause references admitted to the priority sample.
    pub counterfactual_phase_sample_insertions: u64,
    /// Existing samples displaced by a lower-ranked deletion.
    pub counterfactual_phase_sample_replacements: u64,
    /// Maximum number of sampled deleted clauses held simultaneously.
    pub counterfactual_phase_sample_peak: u64,
    /// Sampled deleted clauses still awaiting a root-restart snapshot.
    pub counterfactual_phase_live_samples: u64,
    /// Root-restart boundaries at which the observer ran.
    pub counterfactual_phase_snapshots: u64,
    /// Sampled deleted clauses classified at restart snapshots.
    pub counterfactual_phase_clauses_scanned: u64,
    /// Sampled-clause literals inspected at restart snapshots.
    pub counterfactual_phase_literal_checks: u64,
    /// Sampled clauses already satisfied at their restart snapshot.
    pub counterfactual_phase_satisfied_clauses: u64,
    /// Sampled clauses with at least two unassigned literals and no true literal.
    pub counterfactual_phase_open_clauses: u64,
    /// Sampled clauses with exactly one unassigned literal and all others false.
    pub counterfactual_phase_unit_clauses: u64,
    /// Sampled clauses whose literals were all false.
    pub counterfactual_phase_conflict_clauses: u64,
    /// Raw unique-literal polarity votes contributed by unit sampled clauses.
    pub counterfactual_phase_unit_votes: u64,
    /// Variables whose sampled-clause votes unanimously selected one polarity.
    pub counterfactual_phase_unanimous_variables: u64,
    /// Variables receiving both positive and negative sampled-clause votes.
    pub counterfactual_phase_disagreeing_variables: u64,
    /// Unanimous suggestions skipped because the variable remained root-assigned.
    pub counterfactual_phase_root_assigned_skips: u64,
    /// Unanimous suggestions written to root-unassigned saved-phase entries.
    pub counterfactual_phase_writes: u64,
    /// Saved-phase writes that changed the prior polarity.
    pub counterfactual_phase_changes: u64,
    /// Maximum logical bytes used by the bounded deleted-clause reference sample.
    pub counterfactual_phase_metadata_bytes: u64,
    /// Maximum number of active learned non-unit clauses.
    pub peak_active_learned_clauses: u64,
}

/// Origin of a permanent clause retained for an independently checkable SMT
/// proof.
///
/// DRAT can validate the propositional refutation only after every non-Boolean
/// premise has been justified. Keeping theory clauses distinct prevents a
/// proof consumer from accidentally treating them as ordinary CNF input.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ProofClauseKind {
    Formula,
    Encoding,
    Theory,
    Administrative,
}

/// One normalized clause in the proof input accumulated by an incremental
/// solver.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ProofInputClause {
    pub(crate) kind: ProofClauseKind,
    pub(crate) literals: Vec<Lit>,
}

#[derive(Debug)]
struct Clause {
    start: usize,
    length: u32,
    activity: f64,
    lbd: u32,
    learned: bool,
    deleted: bool,
    used: u8,
}

const PIVOT_SAMPLE_CAPACITY: usize = 4;
const EMPTY_PIVOT_SAMPLE_SLOT: u32 = u32::MAX;
const PIVOT_SAMPLE_COUNT_MASK: u8 = 0x07;
const NONREGULAR_DERIVATION_BIT: u8 = 0x80;
const SHADOW_ACTIVE: u8 = 0;
const SHADOW_OBSERVING: u8 = 1;
const SHADOW_TRIGGERED: u8 = 2;

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct CounterfactualPhaseSample {
    rank: u64,
    reduction: u64,
    clause: ClauseRef,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct DerivationAncestry {
    sample: [u32; PIVOT_SAMPLE_CAPACITY],
    state: u8,
}

impl DerivationAncestry {
    const fn empty() -> Self {
        Self {
            sample: [EMPTY_PIVOT_SAMPLE_SLOT; PIVOT_SAMPLE_CAPACITY],
            state: 0,
        }
    }

    fn from_storage(sample: [u32; PIVOT_SAMPLE_CAPACITY], state: u8) -> Self {
        debug_assert!(usize::from(state & PIVOT_SAMPLE_COUNT_MASK) <= PIVOT_SAMPLE_CAPACITY);
        Self { sample, state }
    }

    fn sample_len(self) -> usize {
        usize::from(self.state & PIVOT_SAMPLE_COUNT_MASK)
    }

    fn is_nonregular(self) -> bool {
        self.state & NONREGULAR_DERIVATION_BIT != 0
    }

    fn set_nonregular(&mut self) {
        self.state |= NONREGULAR_DERIVATION_BIT;
    }

    fn set_sample_len(&mut self, length: usize) {
        debug_assert!(length <= PIVOT_SAMPLE_CAPACITY);
        self.state = (self.state & !PIVOT_SAMPLE_COUNT_MASK)
            | u8::try_from(length).expect("pivot sample length fits u8");
    }

    fn contains(self, variable: Var) -> bool {
        self.sample[..self.sample_len()].contains(&variable.raw())
    }

    fn insert(&mut self, variable: Var) {
        if self.contains(variable) {
            return;
        }

        let raw = variable.raw();
        let length = self.sample_len();
        let insertion = (0..length)
            .find(|&index| compare_pivot_rank(raw, self.sample[index]) == Ordering::Less)
            .unwrap_or(length);
        if insertion == PIVOT_SAMPLE_CAPACITY {
            return;
        }

        let new_length = (length + 1).min(PIVOT_SAMPLE_CAPACITY);
        for index in (insertion + 1..new_length).rev() {
            self.sample[index] = self.sample[index - 1];
        }
        self.sample[insertion] = raw;
        self.set_sample_len(new_length);
    }

    fn merge(&mut self, other: Self) {
        for index in 0..other.sample_len() {
            self.insert(Var::new(other.sample[index]));
        }
    }

    fn resolve_with(&mut self, pivot: Var, parent: Self) -> bool {
        let repeated = self.contains(pivot) || parent.contains(pivot);
        if parent.is_nonregular() || repeated {
            self.set_nonregular();
        }
        self.merge(parent);
        self.insert(pivot);
        repeated
    }
}

fn pivot_rank(variable: u32) -> u64 {
    let mut value = u64::from(variable).wrapping_add(0x9e37_79b9_7f4a_7c15);
    value = (value ^ (value >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    value = (value ^ (value >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    value ^ (value >> 31)
}

fn compare_pivot_rank(left: u32, right: u32) -> Ordering {
    pivot_rank(left)
        .cmp(&pivot_rank(right))
        .then_with(|| left.cmp(&right))
}

fn shadow_clause_rank(reference: usize, reduction: u64) -> u64 {
    let reference = u64::try_from(reference).unwrap_or(u64::MAX);
    let mut value = reference ^ reduction.wrapping_shl(32);
    value = value.wrapping_add(0x9e37_79b9_7f4a_7c15);
    value = (value ^ (value >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    value = (value ^ (value >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    value ^ (value >> 31)
}

const BINARY_LEARNED: u8 = 1;
const BINARY_DELETED: u8 = 2;
const NO_BINARY_ACTIVITY: u32 = u32::MAX;

#[derive(Debug)]
struct EliminationRecord {
    variable: Var,
    clauses: Vec<Vec<Lit>>,
}

#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
struct FactorNeighborhoodSummary {
    count: u32,
    sum1: u64,
    sum2: u64,
    xor: u64,
}

#[derive(Debug)]
struct FactorCandidate {
    reference: ClauseRef,
    literals: Vec<Lit>,
}

#[derive(Debug)]
struct FactorSnapshot {
    clauses: Vec<FactorCandidate>,
    occurrences: Vec<Vec<usize>>,
    summaries: Vec<FactorNeighborhoodSummary>,
    literal_touches: u64,
}

#[derive(Debug)]
struct FactorPlan {
    factors: Vec<Lit>,
    quotients: Vec<Vec<Lit>>,
    matrix: Vec<ClauseRef>,
    reduction: usize,
}

impl Clause {
    fn original(start: usize, length: u32) -> Self {
        Self {
            start,
            length,
            activity: 0.0,
            lbd: 0,
            learned: false,
            deleted: false,
            used: 0,
        }
    }

    fn learned(start: usize, length: u32, lbd: u32) -> Self {
        Self {
            start,
            length,
            activity: 0.0,
            lbd,
            learned: true,
            deleted: false,
            used: MAX_CLAUSE_USAGE,
        }
    }

    fn len(&self) -> usize {
        self.length as usize
    }

    fn range(&self) -> std::ops::Range<usize> {
        self.start..self.start + self.len()
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Watch(u64);

impl Watch {
    fn new(clause: ClauseRef, blocker: Lit) -> Self {
        Self((u64::from(clause.packed()) << 32) | u64::from(blocker.raw()))
    }

    fn clause(self) -> ClauseRef {
        ClauseRef::from_packed((self.0 >> 32) as u32)
    }

    fn blocker(self) -> Lit {
        Lit::from_raw(self.0 as u32)
    }

    fn is_binary(self) -> bool {
        self.clause().is_binary()
    }
}

const LBD_RESTART_WINDOW: usize = 50;
const TRAIL_RESTART_WINDOW: usize = 5_000;
const BLOCKING_RESTART_MIN_CONFLICTS: u64 = 10_000;
const INITIAL_MODE_CONFLICTS: u64 = 1_000;
const STABLE_RESTART_PERIOD: u64 = 1_024;
const STABLE_RESTART_LIMIT: u64 = 1 << 20;
const FOCUSED_PROBE_CONFLICTS: u64 = 100;
const TIER1_LBD: u32 = 2;
const TIER2_LBD: u32 = 6;
const MAX_CLAUSE_USAGE: u8 = 3;
const CHRONO_LEVEL_LIMIT: u32 = 100;
const TRANSFER_WARMUP_EPOCHS: u64 = 9;
const TRANSFER_PROBE_EPOCHS: u64 = 2;
const TRANSFER_EXPLOIT_EPOCHS: u64 = 8;
const TRANSFER_EWMA_ALPHA: f64 = 0.25;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum TransferRegime {
    Evsids,
    Lrb,
}

impl TransferRegime {
    fn index(self) -> usize {
        match self {
            Self::Evsids => 0,
            Self::Lrb => 1,
        }
    }

    fn opposite(self) -> Self {
        match self {
            Self::Evsids => Self::Lrb,
            Self::Lrb => Self::Evsids,
        }
    }
}

#[derive(Clone, Copy, Debug)]
struct TransferClauseMetadata {
    origin: Option<TransferRegime>,
    last_credited_epoch: u64,
}

impl TransferClauseMetadata {
    fn original() -> Self {
        Self {
            origin: None,
            last_credited_epoch: 0,
        }
    }

    fn learned(origin: TransferRegime) -> Self {
        Self {
            origin: Some(origin),
            last_credited_epoch: 0,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum TransferUse {
    Propagation,
    Analysis,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ClauseUsageUse {
    Propagation,
    Analysis,
}

#[derive(Debug)]
struct TransferSearchState {
    active: TransferRegime,
    epoch: u64,
    epoch_start_conflicts: u64,
    epoch_credits: [u64; 2],
    estimates: [f64; 2],
    observations: [u64; 2],
    winner: TransferRegime,
}

impl Default for TransferSearchState {
    fn default() -> Self {
        Self {
            active: TransferRegime::Evsids,
            epoch: 1,
            epoch_start_conflicts: 0,
            epoch_credits: [0; 2],
            estimates: [0.0; 2],
            observations: [0; 2],
            winner: TransferRegime::Evsids,
        }
    }
}

impl TransferSearchState {
    fn record_credit(&mut self, origin: TransferRegime) {
        let index = origin.index();
        self.epoch_credits[index] = self.epoch_credits[index].saturating_add(1);
    }

    fn finish_epoch(&mut self, conflicts: u64) -> (TransferRegime, TransferRegime) {
        let completed_regime = self.active;
        if self.epoch > 1 {
            let producer = completed_regime.opposite();
            let producer_index = producer.index();
            let epoch_conflicts = conflicts.saturating_sub(self.epoch_start_conflicts).max(1);
            let sample =
                1_000.0 * self.epoch_credits[producer_index] as f64 / epoch_conflicts as f64;
            if self.observations[producer_index] == 0 {
                self.estimates[producer_index] = sample;
            } else {
                self.estimates[producer_index] = (1.0 - TRANSFER_EWMA_ALPHA)
                    * self.estimates[producer_index]
                    + TRANSFER_EWMA_ALPHA * sample;
            }
            self.observations[producer_index] = self.observations[producer_index].saturating_add(1);
        }

        if self.epoch > TRANSFER_WARMUP_EPOCHS {
            let position = (self.epoch - TRANSFER_WARMUP_EPOCHS - 1)
                % (TRANSFER_PROBE_EPOCHS + TRANSFER_EXPLOIT_EPOCHS);
            if position == TRANSFER_PROBE_EPOCHS - 1 {
                self.winner = if self.estimates[TransferRegime::Lrb.index()]
                    .total_cmp(&self.estimates[TransferRegime::Evsids.index()])
                    .is_gt()
                {
                    TransferRegime::Lrb
                } else {
                    TransferRegime::Evsids
                };
            }
        }

        self.epoch = self.epoch.saturating_add(1);
        self.epoch_start_conflicts = conflicts;
        self.epoch_credits = [0; 2];
        self.active = self.regime_for_epoch(self.epoch);
        (completed_regime, self.active)
    }

    fn regime_for_epoch(&self, epoch: u64) -> TransferRegime {
        if epoch <= TRANSFER_WARMUP_EPOCHS {
            return if epoch % 2 == 1 {
                TransferRegime::Evsids
            } else {
                TransferRegime::Lrb
            };
        }
        let position = (epoch - TRANSFER_WARMUP_EPOCHS - 1)
            % (TRANSFER_PROBE_EPOCHS + TRANSFER_EXPLOIT_EPOCHS);
        match position {
            0 => TransferRegime::Evsids,
            1 => TransferRegime::Lrb,
            _ => self.winner,
        }
    }
}

#[derive(Debug)]
struct LbdRestartState {
    recent: [u32; LBD_RESTART_WINDOW],
    recent_next: usize,
    recent_len: usize,
    recent_sum: u64,
    global_sum: u64,
    conflicts: u64,
}

impl Default for LbdRestartState {
    fn default() -> Self {
        Self {
            recent: [0; LBD_RESTART_WINDOW],
            recent_next: 0,
            recent_len: 0,
            recent_sum: 0,
            global_sum: 0,
            conflicts: 0,
        }
    }
}

impl LbdRestartState {
    fn observe(&mut self, lbd: u32) {
        self.global_sum = self.global_sum.saturating_add(u64::from(lbd));
        self.conflicts = self.conflicts.saturating_add(1);

        if self.recent_len == LBD_RESTART_WINDOW {
            self.recent_sum -= u64::from(self.recent[self.recent_next]);
        } else {
            self.recent_len += 1;
        }
        self.recent[self.recent_next] = lbd;
        self.recent_sum += u64::from(lbd);
        self.recent_next = (self.recent_next + 1) % LBD_RESTART_WINDOW;
    }

    fn should_restart(&self) -> bool {
        if !self.is_full() || self.conflicts == 0 {
            return false;
        }

        // 0.8 * recent_average > global_average, compared exactly without
        // floating-point rounding or overflow in realistic runs.
        u128::from(self.recent_sum) * 4 * u128::from(self.conflicts)
            > u128::from(self.global_sum) * 5 * (LBD_RESTART_WINDOW as u128)
    }

    fn is_full(&self) -> bool {
        self.recent_len == LBD_RESTART_WINDOW
    }

    fn clear_recent(&mut self) {
        self.recent_next = 0;
        self.recent_len = 0;
        self.recent_sum = 0;
    }
}

#[derive(Debug, Default)]
struct TrailRestartState {
    recent: Vec<usize>,
    recent_next: usize,
    recent_sum: u128,
}

impl TrailRestartState {
    fn observe(&mut self, trail_length: usize) {
        if self.recent.len() == TRAIL_RESTART_WINDOW {
            self.recent_sum -= self.recent[self.recent_next] as u128;
            self.recent[self.recent_next] = trail_length;
            self.recent_next = (self.recent_next + 1) % TRAIL_RESTART_WINDOW;
        } else {
            self.recent.push(trail_length);
        }
        self.recent_sum += trail_length as u128;
    }

    fn unusually_deep(&self, trail_length: usize) -> bool {
        !self.recent.is_empty()
            && (trail_length as u128) * 5 * (self.recent.len() as u128) > self.recent_sum * 7
    }
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
enum RestartAction {
    #[default]
    Root,
    Reuse,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct RestartEpochQuality {
    conflicts: u64,
    propagations: u64,
    lbd_sum: u64,
}

impl RestartEpochQuality {
    fn at_least(self, other: Self) -> bool {
        // Compare
        //
        //   conflicts^2 / (propagations * lbd_sum)
        //
        // without division. Saturation gives a deterministic conservative tie
        // for counters far beyond realistic restart epochs.
        let left = u128::from(self.conflicts)
            .saturating_mul(u128::from(self.conflicts))
            .saturating_mul(u128::from(other.propagations.max(1)))
            .saturating_mul(u128::from(other.lbd_sum.max(1)));
        let right = u128::from(other.conflicts)
            .saturating_mul(u128::from(other.conflicts))
            .saturating_mul(u128::from(self.propagations.max(1)))
            .saturating_mul(u128::from(self.lbd_sum.max(1)));
        left >= right
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum AdaptiveReuseChoice {
    Probe,
    QualityAccept,
    QualityReject,
}

#[derive(Debug, Default)]
struct AdaptiveTrailReuseState {
    epoch_action: RestartAction,
    epoch_start_conflicts: u64,
    epoch_start_propagations: u64,
    epoch_lbd_sum: u64,
    root_quality: Option<RestartEpochQuality>,
    reuse_quality: Option<RestartEpochQuality>,
    eligible_events: u64,
}

impl AdaptiveTrailReuseState {
    fn observe_lbd(&mut self, lbd: u32) {
        self.epoch_lbd_sum = self.epoch_lbd_sum.saturating_add(u64::from(lbd));
    }

    fn finish_epoch(&mut self, stats: &mut SolverStats) {
        let quality = RestartEpochQuality {
            conflicts: stats.conflicts.saturating_sub(self.epoch_start_conflicts),
            propagations: stats
                .propagations
                .saturating_sub(self.epoch_start_propagations),
            lbd_sum: self.epoch_lbd_sum,
        };
        match self.epoch_action {
            RestartAction::Root => {
                self.root_quality = Some(quality);
                stats.adaptive_root_epochs = stats.adaptive_root_epochs.saturating_add(1);
            }
            RestartAction::Reuse => {
                self.reuse_quality = Some(quality);
                stats.adaptive_reuse_epochs = stats.adaptive_reuse_epochs.saturating_add(1);
            }
        }
    }

    fn choose(&mut self) -> AdaptiveReuseChoice {
        self.eligible_events = self.eligible_events.saturating_add(1);
        if self.reuse_quality.is_none()
            || self.root_quality.is_none()
            || self.eligible_events.is_power_of_two()
        {
            return AdaptiveReuseChoice::Probe;
        }
        if self
            .reuse_quality
            .expect("checked above")
            .at_least(self.root_quality.expect("checked above"))
        {
            AdaptiveReuseChoice::QualityAccept
        } else {
            AdaptiveReuseChoice::QualityReject
        }
    }

    fn begin_epoch(&mut self, action: RestartAction, stats: SolverStats) {
        self.epoch_action = action;
        self.epoch_start_conflicts = stats.conflicts;
        self.epoch_start_propagations = stats.propagations;
        self.epoch_lbd_sum = 0;
    }
}

#[derive(Debug)]
struct ExponentialMovingAverage {
    value: f64,
    biased: f64,
    alpha: f64,
    beta: f64,
    exponent: f64,
}

impl ExponentialMovingAverage {
    fn new(window: u32) -> Self {
        let alpha = 1.0 / f64::from(window);
        Self {
            value: 0.0,
            biased: 0.0,
            alpha,
            beta: 1.0 - alpha,
            exponent: 1.0,
        }
    }

    fn update(&mut self, sample: u32) {
        self.biased += self.alpha * (f64::from(sample) - self.biased);
        if self.exponent != 0.0 {
            let next_exponent = self.exponent * self.beta;
            if next_exponent == self.exponent {
                self.exponent = 0.0;
                self.value = self.biased;
            } else {
                self.exponent = next_exponent;
                self.value = self.biased / (1.0 - next_exponent);
            }
        } else {
            self.value = self.biased;
        }
    }
}

#[derive(Debug)]
struct ReluctantRestart {
    period: u64,
    limit: u64,
    wait: u64,
    u: u64,
    v: u64,
    triggered: bool,
}

impl Default for ReluctantRestart {
    fn default() -> Self {
        let mut state = Self {
            period: STABLE_RESTART_PERIOD,
            limit: STABLE_RESTART_LIMIT,
            wait: 0,
            u: 1,
            v: 1,
            triggered: false,
        };
        state.reset();
        state
    }
}

impl ReluctantRestart {
    fn reset(&mut self) {
        self.wait = self.period;
        self.u = 1;
        self.v = 1;
        self.triggered = false;
    }

    fn tick(&mut self) {
        if self.triggered {
            return;
        }
        self.wait -= 1;
        if self.wait != 0 {
            return;
        }

        if self.u & self.u.wrapping_neg() == self.v {
            self.u = self.u.saturating_add(1);
            self.v = 1;
        } else {
            self.v = self.v.saturating_mul(2);
        }
        self.wait = self.v.saturating_mul(self.period);
        if self.wait > self.limit {
            self.u = 1;
            self.v = 1;
            self.wait = self.period;
        }
        self.triggered = true;
    }

    fn take_trigger(&mut self) -> bool {
        std::mem::take(&mut self.triggered)
    }
}

#[derive(Debug)]
struct HybridSearchState {
    stable: bool,
    mode_count: u64,
    mode_start_propagations: u64,
    mode_conflict_limit: u64,
    mode_propagation_limit: u64,
    focused_restart_limit: u64,
    fast_lbd: ExponentialMovingAverage,
    slow_lbd: ExponentialMovingAverage,
    reluctant: ReluctantRestart,
}

impl Default for HybridSearchState {
    fn default() -> Self {
        Self {
            stable: false,
            mode_count: 0,
            mode_start_propagations: 0,
            mode_conflict_limit: INITIAL_MODE_CONFLICTS,
            mode_propagation_limit: 0,
            focused_restart_limit: 1,
            fast_lbd: ExponentialMovingAverage::new(33),
            slow_lbd: ExponentialMovingAverage::new(100_000),
            reluctant: ReluctantRestart::default(),
        }
    }
}

impl HybridSearchState {
    fn observe_conflict(&mut self, lbd: u32) {
        if self.stable {
            self.reluctant.tick();
        } else {
            self.fast_lbd.update(lbd);
            self.slow_lbd.update(lbd);
        }
    }

    fn should_switch(&self, stats: SolverStats) -> bool {
        if self.stable {
            stats.propagations >= self.mode_propagation_limit
        } else {
            stats.conflicts >= self.mode_conflict_limit
        }
    }

    fn switch(&mut self, stats: SolverStats) {
        self.mode_count += 1;
        if self.stable {
            self.stable = false;
            let count = (self.mode_count / 2).max(1);
            let logarithm = ((count + 9) as f64).log10();
            let scaled = (count as f64 * logarithm.powi(4)) as u64;
            let interval = INITIAL_MODE_CONFLICTS.saturating_mul(scaled.max(1));
            self.mode_conflict_limit = stats.conflicts.saturating_add(interval);
            self.focused_restart_limit = stats.conflicts.saturating_add(1);
        } else {
            self.stable = true;
            let effort = stats
                .propagations
                .saturating_sub(self.mode_start_propagations)
                .max(1);
            self.mode_propagation_limit = stats.propagations.saturating_add(effort);
            self.reluctant.reset();
        }
        self.mode_start_propagations = stats.propagations;
    }

    fn should_restart(&self, stats: SolverStats) -> bool {
        if self.stable {
            self.reluctant.triggered
        } else {
            stats.conflicts >= self.focused_restart_limit
                && self.fast_lbd.value >= 1.1 * self.slow_lbd.value
        }
    }

    fn restarted(&mut self, stats: SolverStats) {
        if self.stable {
            let triggered = self.reluctant.take_trigger();
            debug_assert!(triggered);
        } else {
            let delta = ((stats.restarts.saturating_add(9)) as f64).log10().floor() as u64;
            self.focused_restart_limit = stats.conflicts.saturating_add(delta.max(1));
        }
    }
}

/// A reusable CDCL solver with temporary assumption queries.
///
/// Add all permanent clauses, then call [`Solver::solve`] or
/// [`Solver::solve_assuming`]. Learned clauses and heuristic state are retained
/// across queries, and permanent clauses may be added between completed
/// queries.
#[derive(Debug)]
pub struct Solver {
    config: SolverConfig,
    proof: DratWriter,
    external_variable_count: usize,
    clauses: Vec<Clause>,
    clause_arena: Vec<Lit>,
    binary_literals: Vec<[Lit; 2]>,
    binary_activity_index: Vec<u32>,
    learned_binary_activity: Vec<f64>,
    binary_flags: Vec<u8>,
    watches: Vec<Vec<Watch>>,
    assignments: Vec<i8>,
    levels: Vec<u32>,
    reasons: Vec<Option<ClauseRef>>,
    phase: Vec<bool>,
    best_phase: Vec<bool>,
    best_assigned: usize,
    trail: Vec<Lit>,
    trail_limits: Vec<usize>,
    propagation_head: usize,
    activity: Vec<f64>,
    variable_increment: f64,
    variable_decay: f64,
    lrb_assigned_at: Vec<u64>,
    lrb_participated: Vec<u64>,
    lrb_reasoned: Vec<u64>,
    lrb_canceled_at: Vec<u64>,
    lrb_marks: Vec<u32>,
    lrb_mark_epoch: u32,
    lrb_step_size: f64,
    transfer_lrb_activity: Vec<f64>,
    transfer_lrb_order: VarOrder,
    transfer_long_clause_metadata: Vec<TransferClauseMetadata>,
    transfer_binary_clause_metadata: Vec<TransferClauseMetadata>,
    clause_usage_scores: Vec<u32>,
    clause_scan_debt: Vec<u64>,
    regularity_long_samples: Vec<[u32; PIVOT_SAMPLE_CAPACITY]>,
    regularity_long_states: Vec<u8>,
    regularity_binary_samples: Vec<[u32; PIVOT_SAMPLE_CAPACITY]>,
    regularity_binary_states: Vec<u8>,
    shadow_clause_states: Vec<u8>,
    shadow_clause_started_at: Vec<u64>,
    shadow_clauses: Vec<usize>,
    shadow_deferred_root_conflict: Option<ClauseRef>,
    counterfactual_phase_samples: Vec<CounterfactualPhaseSample>,
    transfer: TransferSearchState,
    chb_last_conflict: Vec<u64>,
    chb_plays: Vec<Var>,
    chb_step_size: f64,
    clause_increment: f64,
    clause_decay: f64,
    order: VarOrder,
    vmtf: VmtfOrder,
    seen: Vec<bool>,
    level_marks: Vec<u32>,
    level_mark: u32,
    binary_minimize_marks: Vec<u32>,
    binary_minimize_epoch: u32,
    consistent: bool,
    started: bool,
    scope_selectors: Vec<Lit>,
    interrupt_flag: Arc<AtomicBool>,
    search_limits: SolveLimits,
    search_start_conflicts: u64,
    search_start_propagations: u64,
    search_control_active: bool,
    stop_reason: Option<UnknownReason>,
    cached_assumptions: Vec<Lit>,
    cached_result: Option<SolveResult>,
    failed_assumptions: Vec<Lit>,
    original_clause_count: usize,
    proof_input: Option<Vec<ProofInputClause>>,
    stats: SolverStats,
    conflicts_since_restart: u64,
    restart_index: u32,
    restart_limit: u64,
    lbd_restart: LbdRestartState,
    trail_restart: TrailRestartState,
    adaptive_trail_reuse: AdaptiveTrailReuseState,
    hybrid: HybridSearchState,
    probe_finished: bool,
    next_reduction: u64,
    active_learned_clauses: u64,
    arena_garbage_literals: usize,
    arena_garbage_clause: usize,
    arena_garbage_start: usize,
    elimination_records: Vec<EliminationRecord>,
    next_rephase: u64,
}

impl Default for Solver {
    fn default() -> Self {
        Self::new()
    }
}

impl Solver {
    const RESTART_BASE: u64 = 100;
    const FIRST_REDUCTION: u64 = 2_000;
    const REDUCTION_INTERVAL: u64 = 1_500;
    const LBD_FREE_FIRST_REDUCTION: u64 = 1_000;
    const LBD_FREE_REDUCTION_BASE: u64 = 1_000;
    const LBD_FREE_DECAY_INTERVAL: u64 = 2_048;
    const REPHASE_BASE: u64 = 1_000;
    const LRB_INITIAL_STEP_SIZE: f64 = 0.4;
    const LRB_MINIMUM_STEP_SIZE: f64 = 0.06;
    const LRB_STEP_SIZE_DECREMENT: f64 = 0.000_001;
    const LRB_ANTI_EXPLORATION_DECAY: f64 = 0.95;
    const CHB_INITIAL_STEP_SIZE: f64 = 0.4;
    const CHB_MINIMUM_STEP_SIZE: f64 = 0.06;
    const CHB_STEP_SIZE_DECREMENT: f64 = 0.000_001;
    const CHB_CONFLICT_MULTIPLIER: f64 = 1.0;
    const CHB_NON_CONFLICT_MULTIPLIER: f64 = 0.9;
    const FAILED_LITERAL_PROBE_PROPAGATION_CAP: u64 = 100_000;
    const VIVIFICATION_PROPAGATION_CAP: u64 = 1_000_000;
    const VIVIFICATION_SCHEDULE_CAP: usize = 5_000;
    const SUBSUMPTION_SUBSUMER_MAX_LENGTH: usize = 8;
    const SUBSUMPTION_TARGET_MAX_LENGTH: usize = 64;
    const SUBSUMPTION_SCHEDULE_CAP: usize = 5_000;
    const SUBSUMPTION_LITERAL_TOUCH_CAP: u64 = 5_000_000;
    const BINARY_MINIMIZATION_MAX_LENGTH: usize = 30;
    const BINARY_MINIMIZATION_MAX_LBD: u32 = 6;
    const ELIMINATION_OCCURRENCE_LIMIT: usize = 100;
    const ELIMINATION_RESOLVENT_LENGTH_LIMIT: usize = 100;
    const ELIMINATION_LITERAL_TOUCH_CAP: u64 = 1_000_000;
    const FACTORIZATION_MAX_CLAUSE_LENGTH: usize = 5;
    const FACTORIZATION_MAX_ROUNDS: usize = 8;
    const FACTORIZATION_LITERAL_TOUCH_CAP: u64 = 100_000_000;
    const FACTORIZATION_DENSITY_NUMERATOR: u64 = 16;
    const SHADOW_CAPACITY: usize = 64;
    const SHADOW_OBSERVATION_CONFLICTS: u64 = 256;
    const COUNTERFACTUAL_PHASE_CAPACITY: usize = 64;

    /// Creates an empty solver.
    #[must_use]
    pub fn new() -> Self {
        Self::with_config(SolverConfig::default())
    }

    /// Creates an empty solver with an explicit, reproducible configuration.
    #[must_use]
    pub fn with_config(config: SolverConfig) -> Self {
        assert!(
            !config.scan_debt_clause_management || config.lbd_free_clause_management,
            "scan-debt clause management requires LBD-free clause management"
        );
        assert!(
            !config.nonregular_clause_retention || config.lbd_free_clause_management,
            "nonregular clause retention requires LBD-free clause management"
        );
        assert!(
            !config.nonregular_clause_retention || !config.scan_debt_clause_management,
            "nonregular clause retention is incompatible with scan-debt clause management"
        );
        assert!(
            !config.shadow_clause_reactivation || config.lbd_free_clause_management,
            "shadow clause reactivation requires LBD-free clause management"
        );
        assert!(
            !config.shadow_clause_reactivation || !config.scan_debt_clause_management,
            "shadow clause reactivation is incompatible with scan-debt clause management"
        );
        assert!(
            !config.shadow_clause_reactivation || !config.nonregular_clause_retention,
            "shadow clause reactivation is incompatible with nonregular retention"
        );
        assert!(
            !config.shadow_clause_reactivation
                || config.restart_trail_reuse == RestartTrailReuse::Never,
            "shadow clause reactivation requires root restarts"
        );
        assert!(
            !config.shadow_clause_reactivation || !config.compact_clause_arena,
            "shadow clause reactivation is incompatible with clause-arena compaction"
        );
        assert!(
            !config.counterfactual_phase_voting || config.lbd_free_clause_management,
            "counterfactual phase voting requires LBD-free clause management"
        );
        assert!(
            !config.counterfactual_phase_voting || !config.scan_debt_clause_management,
            "counterfactual phase voting is incompatible with scan-debt clause management"
        );
        assert!(
            !config.counterfactual_phase_voting || !config.nonregular_clause_retention,
            "counterfactual phase voting is incompatible with nonregular retention"
        );
        assert!(
            !config.counterfactual_phase_voting || !config.shadow_clause_reactivation,
            "counterfactual phase voting is incompatible with shadow clause reactivation"
        );
        assert!(
            !config.counterfactual_phase_voting
                || config.restart_trail_reuse == RestartTrailReuse::Never,
            "counterfactual phase voting requires root restarts"
        );
        assert!(
            !config.counterfactual_phase_voting || !config.compact_clause_arena,
            "counterfactual phase voting is incompatible with clause-arena compaction"
        );
        assert!(
            !config.counterfactual_phase_voting || !config.systematic_rephasing,
            "counterfactual phase voting is incompatible with systematic rephasing"
        );
        assert!(
            !config.macro_bounded_variable_addition || config.bounded_variable_addition,
            "macro BVA requires bounded variable addition"
        );
        let next_reduction = if config.lbd_free_clause_management {
            Self::LBD_FREE_FIRST_REDUCTION
        } else {
            Self::FIRST_REDUCTION
        };
        Self {
            config,
            proof: DratWriter::disabled(),
            external_variable_count: 0,
            clauses: Vec::new(),
            clause_arena: Vec::new(),
            binary_literals: Vec::new(),
            binary_activity_index: Vec::new(),
            learned_binary_activity: Vec::new(),
            binary_flags: Vec::new(),
            watches: Vec::new(),
            assignments: Vec::new(),
            levels: Vec::new(),
            reasons: Vec::new(),
            phase: Vec::new(),
            best_phase: Vec::new(),
            best_assigned: 0,
            trail: Vec::new(),
            trail_limits: Vec::new(),
            propagation_head: 0,
            activity: Vec::new(),
            variable_increment: 1.0,
            variable_decay: 0.95,
            lrb_assigned_at: Vec::new(),
            lrb_participated: Vec::new(),
            lrb_reasoned: Vec::new(),
            lrb_canceled_at: Vec::new(),
            lrb_marks: Vec::new(),
            lrb_mark_epoch: 0,
            lrb_step_size: Self::LRB_INITIAL_STEP_SIZE,
            transfer_lrb_activity: Vec::new(),
            transfer_lrb_order: VarOrder::default(),
            transfer_long_clause_metadata: Vec::new(),
            transfer_binary_clause_metadata: Vec::new(),
            clause_usage_scores: Vec::new(),
            clause_scan_debt: Vec::new(),
            regularity_long_samples: Vec::new(),
            regularity_long_states: Vec::new(),
            regularity_binary_samples: Vec::new(),
            regularity_binary_states: Vec::new(),
            shadow_clause_states: Vec::new(),
            shadow_clause_started_at: Vec::new(),
            shadow_clauses: Vec::new(),
            shadow_deferred_root_conflict: None,
            counterfactual_phase_samples: Vec::new(),
            transfer: TransferSearchState::default(),
            chb_last_conflict: Vec::new(),
            chb_plays: Vec::new(),
            chb_step_size: Self::CHB_INITIAL_STEP_SIZE,
            clause_increment: 1.0,
            clause_decay: 0.999,
            order: VarOrder::default(),
            vmtf: VmtfOrder::default(),
            seen: Vec::new(),
            level_marks: Vec::new(),
            level_mark: 0,
            binary_minimize_marks: Vec::new(),
            binary_minimize_epoch: 0,
            consistent: true,
            started: false,
            scope_selectors: Vec::new(),
            interrupt_flag: Arc::default(),
            search_limits: SolveLimits::default(),
            search_start_conflicts: 0,
            search_start_propagations: 0,
            search_control_active: false,
            stop_reason: None,
            cached_assumptions: Vec::new(),
            cached_result: None,
            failed_assumptions: Vec::new(),
            original_clause_count: 0,
            proof_input: None,
            stats: SolverStats::default(),
            conflicts_since_restart: 0,
            restart_index: 0,
            restart_limit: Self::RESTART_BASE,
            lbd_restart: LbdRestartState::default(),
            trail_restart: TrailRestartState::default(),
            adaptive_trail_reuse: AdaptiveTrailReuseState::default(),
            hybrid: HybridSearchState::default(),
            probe_finished: false,
            next_reduction,
            active_learned_clauses: 0,
            arena_garbage_literals: 0,
            arena_garbage_clause: usize::MAX,
            arena_garbage_start: usize::MAX,
            elimination_records: Vec::new(),
            next_rephase: Self::REPHASE_BASE,
        }
    }

    /// Ensures that variables `0..variable_count` exist, including variables
    /// that do not occur in a clause.
    ///
    /// # Panics
    ///
    /// Panics if `variable_count` exceeds the packed literal limit or an
    /// irreversible preprocessing configuration has already been run. Use
    /// [`Solver::try_reserve_variables`] to handle those errors explicitly.
    pub fn reserve_variables(&mut self, variable_count: usize) {
        self.try_reserve_variables(variable_count)
            .expect("cannot reserve variables in the current solver state");
    }

    /// Fallible form of [`Solver::reserve_variables`] for interactive clients.
    pub fn try_reserve_variables(&mut self, variable_count: usize) -> Result<(), IncrementalError> {
        if variable_count <= self.external_variable_count {
            return Ok(());
        }
        if variable_count > MAX_VARIABLES {
            return Err(IncrementalError::VariableLimit);
        }
        self.try_reserve_variable_capacity(variable_count)?;
        self.prepare_incremental_mutation()?;
        self.external_variable_count = variable_count;
        self.grow_variables(variable_count);
        Ok(())
    }

    fn try_reserve_variable_capacity(
        &mut self,
        variable_count: usize,
    ) -> Result<(), IncrementalError> {
        let literal_count = variable_count
            .checked_mul(2)
            .ok_or(IncrementalError::VariableLimit)?;
        try_reserve_len(&mut self.assignments, variable_count)?;
        try_reserve_len(&mut self.levels, variable_count)?;
        try_reserve_len(&mut self.reasons, variable_count)?;
        try_reserve_len(&mut self.phase, variable_count)?;
        if self.config.systematic_rephasing {
            try_reserve_len(&mut self.best_phase, variable_count)?;
        }
        try_reserve_len(&mut self.activity, variable_count)?;
        if self.maintains_lrb_scores() {
            try_reserve_len(&mut self.lrb_assigned_at, variable_count)?;
            try_reserve_len(&mut self.lrb_participated, variable_count)?;
            try_reserve_len(&mut self.lrb_reasoned, variable_count)?;
            try_reserve_len(&mut self.lrb_canceled_at, variable_count)?;
            try_reserve_len(&mut self.lrb_marks, variable_count)?;
        }
        if self.uses_transfer_branching() {
            try_reserve_len(&mut self.transfer_lrb_activity, variable_count)?;
            self.transfer_lrb_order.try_reserve(variable_count)?;
        }
        if self.uses_chb_branching() {
            try_reserve_len(&mut self.chb_last_conflict, variable_count)?;
        }
        try_reserve_len(&mut self.seen, variable_count)?;
        if self.config.binary_resolution_minimization {
            try_reserve_len(&mut self.binary_minimize_marks, variable_count)?;
        }
        try_reserve_len(&mut self.watches, literal_count)?;
        self.order.try_reserve(variable_count)?;
        self.vmtf.try_reserve(variable_count)?;
        Ok(())
    }

    fn grow_variables(&mut self, variable_count: usize) {
        if variable_count <= self.assignments.len() {
            return;
        }
        debug_assert!(variable_count <= MAX_VARIABLES);

        let old_count = self.assignments.len();
        self.assignments.resize(variable_count, UNASSIGNED);
        self.levels.resize(variable_count, 0);
        self.reasons.resize(variable_count, None);
        self.phase.resize(variable_count, true);
        if self.config.systematic_rephasing {
            self.best_phase.resize(variable_count, true);
        }
        self.activity.resize(variable_count, 0.0);
        if self.maintains_lrb_scores() {
            self.lrb_assigned_at.resize(variable_count, 0);
            self.lrb_participated.resize(variable_count, 0);
            self.lrb_reasoned.resize(variable_count, 0);
            self.lrb_canceled_at.resize(variable_count, 0);
            self.lrb_marks.resize(variable_count, 0);
        }
        if self.uses_transfer_branching() {
            self.transfer_lrb_activity.resize(variable_count, 0.0);
            self.transfer_lrb_order
                .grow(old_count, variable_count, &self.transfer_lrb_activity);
        }
        if self.uses_chb_branching() {
            self.chb_last_conflict.resize(variable_count, 0);
        }
        self.seen.resize(variable_count, false);
        if self.config.binary_resolution_minimization {
            self.binary_minimize_marks.resize(variable_count, 0);
        }
        self.watches.resize_with(variable_count * 2, Vec::new);
        self.order.grow(old_count, variable_count, &self.activity);
        self.vmtf.grow(old_count, variable_count);
    }

    /// Adds a clause. Duplicate literals are removed and tautologies ignored.
    ///
    /// When a scope is active, the clause belongs to the innermost scope.
    ///
    /// Returns `false` when the clauses added so far are already inconsistent.
    ///
    /// # Panics
    ///
    /// Panics when an irreversible preprocessing configuration has already
    /// been run. Use [`Solver::try_add_clause`] to handle that error.
    pub fn add_clause(&mut self, literals: &[Lit]) -> bool {
        self.try_add_clause(literals)
            .expect("cannot add a clause in the current solver state")
    }

    /// Fallible form of [`Solver::add_clause`] for interactive clients.
    pub fn try_add_clause(&mut self, literals: &[Lit]) -> Result<bool, IncrementalError> {
        self.add_clause_internal(literals, true, true, ProofClauseKind::Formula)
    }

    /// Adds a permanent encoding lemma even when a user assertion scope is
    /// active. SMT lowering uses this for definitional Tseitin clauses whose
    /// meaning is independent of assertion lifetime.
    pub(crate) fn add_encoding_clause(
        &mut self,
        literals: &[Lit],
    ) -> Result<bool, IncrementalError> {
        self.add_clause_internal(literals, false, false, ProofClauseKind::Encoding)
    }

    /// Adds a permanent SMT theory lemma and records its origin separately
    /// from Boolean encoding clauses.
    pub(crate) fn add_theory_clause(&mut self, literals: &[Lit]) -> Result<bool, IncrementalError> {
        self.add_clause_internal(literals, false, false, ProofClauseKind::Theory)
    }

    fn add_clause_internal(
        &mut self,
        literals: &[Lit],
        guard_with_scope: bool,
        count_as_input: bool,
        proof_kind: ProofClauseKind,
    ) -> Result<bool, IncrementalError> {
        self.prepare_incremental_mutation()?;
        if count_as_input {
            self.original_clause_count += 1;
        }

        let mut normalized = literals.to_vec();
        if guard_with_scope {
            if let Some(&selector) = self.scope_selectors.last() {
                normalized.push(!selector);
            }
        }
        if let Some(maximum) = normalized.iter().map(|literal| literal.var().index()).max() {
            let required = maximum
                .checked_add(1)
                .ok_or(IncrementalError::VariableLimit)?;
            if required > self.external_variable_count {
                if required > MAX_VARIABLES {
                    return Err(IncrementalError::VariableLimit);
                }
                self.external_variable_count = required;
                self.grow_variables(required);
            }
        }
        normalized.sort_unstable_by_key(|literal| literal.index());
        let mut write = 0;
        for read in 0..normalized.len() {
            if write > 0 {
                let previous = normalized[write - 1];
                let current = normalized[read];
                if previous == current {
                    continue;
                }
                if previous.var() == current.var() {
                    return Ok(self.consistent);
                }
            }
            normalized[write] = normalized[read];
            write += 1;
        }
        normalized.truncate(write);
        if let Some(proof_input) = &mut self.proof_input {
            proof_input.push(ProofInputClause {
                kind: proof_kind,
                literals: normalized.clone(),
            });
        }
        if self.config.bounded_variable_addition
            && (2..=Self::FACTORIZATION_MAX_CLAUSE_LENGTH).contains(&normalized.len())
        {
            self.stats.factorization_input_short_clauses = self
                .stats
                .factorization_input_short_clauses
                .saturating_add(1);
        }

        if self.started {
            if !self.consistent || self.propagate().is_some() {
                self.consistent = false;
                return Ok(false);
            }
            if normalized
                .iter()
                .any(|&literal| self.literal_value(literal) == TRUE)
            {
                return Ok(true);
            }
            normalized.sort_unstable_by_key(|&literal| {
                if self.literal_value(literal) == UNASSIGNED {
                    0
                } else {
                    1
                }
            });
            let unassigned = normalized
                .iter()
                .take_while(|&&literal| self.literal_value(literal) == UNASSIGNED)
                .count();
            if unassigned == 0 {
                self.consistent = false;
                return Ok(false);
            }

            if normalized.len() == 1 {
                let enqueued = self.enqueue(normalized[0], None);
                debug_assert!(enqueued, "new root unit must be unassigned");
            } else {
                let unit = (unassigned == 1).then_some(normalized[0]);
                let clause = self.allocate_clause(normalized, 0, false);
                self.attach_clause(clause);
                if let Some(unit) = unit {
                    let enqueued = self.enqueue(unit, Some(clause));
                    debug_assert!(enqueued, "new root-unit clause must imply its live literal");
                }
            }
            if self.propagate().is_some() {
                self.consistent = false;
            }
            return Ok(self.consistent);
        }

        match normalized.len() {
            0 => self.consistent = false,
            1 => {
                if !self.enqueue(normalized[0], None) {
                    self.consistent = false;
                }
            }
            _ => {
                let clause = self.allocate_clause(normalized, 0, false);
                self.attach_clause(clause);
            }
        }
        Ok(self.consistent)
    }

    fn prepare_incremental_mutation(&mut self) -> Result<(), IncrementalError> {
        if self.started
            && (self.config.bounded_variable_elimination || self.config.bounded_variable_addition)
        {
            return Err(IncrementalError::IrreversiblePreprocessing);
        }
        if self.started {
            self.cancel_until(0);
        }
        self.cached_result = None;
        self.cached_assumptions.clear();
        self.failed_assumptions.clear();
        Ok(())
    }

    /// Number of variables currently known to the solver.
    #[must_use]
    pub fn variable_count(&self) -> usize {
        self.external_variable_count
    }

    /// Returns a deterministic total Boolean assignment for protocol-level
    /// model inspection after an inconclusive query.
    ///
    /// SMT-LIB permits model inspection after `unknown`, without requiring
    /// that model to satisfy the current assertions. Keeping this constructor
    /// inside the solver preserves [`Model`]'s total-assignment invariant.
    pub(crate) fn arbitrary_model(&self) -> Model {
        Model {
            values: vec![false; self.external_variable_count],
        }
    }

    /// Number of input clauses passed to [`Solver::add_clause`].
    #[must_use]
    pub const fn original_clause_count(&self) -> usize {
        self.original_clause_count
    }

    /// Allocates one new Boolean variable at the end of the current namespace.
    pub fn new_variable(&mut self) -> Result<Var, IncrementalError> {
        if self.external_variable_count == MAX_VARIABLES {
            return Err(IncrementalError::VariableLimit);
        }
        let variable = Var::new(
            u32::try_from(self.external_variable_count)
                .map_err(|_| IncrementalError::VariableLimit)?,
        );
        self.try_reserve_variables(self.external_variable_count + 1)?;
        Ok(variable)
    }

    /// Opens a clause scope implemented by a fresh activation variable.
    ///
    /// Clauses added before the matching [`Solver::pop`] remain permanent;
    /// clauses added afterward and before the pop are active only while this
    /// scope is active. Scope activation variables count toward
    /// [`Solver::variable_count`] but callers need not mention them.
    pub fn push(&mut self) -> Result<(), IncrementalError> {
        self.push_levels(1)
    }

    /// Atomically opens `levels` clause scopes.
    ///
    /// The complete variable and selector capacity is checked before any
    /// logical solver state changes, so a packed-variable or allocation limit
    /// leaves the original scope stack intact.
    pub fn push_levels(&mut self, levels: usize) -> Result<(), IncrementalError> {
        self.check_push_levels(levels)?;
        if levels == 0 {
            return Ok(());
        }
        let old_count = self.external_variable_count;
        let variable_count = old_count
            .checked_add(levels)
            .expect("bulk scope capacity checked before mutation");
        self.try_reserve_variable_capacity(variable_count)?;
        self.scope_selectors
            .try_reserve(levels)
            .map_err(|_| IncrementalError::ResourceExhausted)?;

        self.prepare_incremental_mutation()?;
        self.external_variable_count = variable_count;
        self.grow_variables(variable_count);
        self.scope_selectors
            .extend((old_count..variable_count).map(|index| {
                let variable = Var::new(
                    u32::try_from(index).expect("variable count checked before scope growth"),
                );
                Lit::positive(variable)
            }));
        Ok(())
    }

    pub(crate) fn check_push_levels(&self, levels: usize) -> Result<(), IncrementalError> {
        if levels == 0 {
            return Ok(());
        }
        if self.config.bounded_variable_elimination || self.config.bounded_variable_addition {
            return Err(IncrementalError::IrreversiblePreprocessing);
        }
        let variable_count = self
            .external_variable_count
            .checked_add(levels)
            .ok_or(IncrementalError::VariableLimit)?;
        if variable_count > MAX_VARIABLES {
            return Err(IncrementalError::VariableLimit);
        }
        Ok(())
    }

    /// Closes `levels` innermost scopes and permanently disables their clauses.
    pub fn pop(&mut self, levels: usize) -> Result<(), IncrementalError> {
        if levels > self.scope_selectors.len() {
            return Err(IncrementalError::ScopeUnderflow);
        }
        if levels == 0 {
            return Ok(());
        }
        if self.config.bounded_variable_elimination || self.config.bounded_variable_addition {
            return Err(IncrementalError::IrreversiblePreprocessing);
        }
        self.prepare_incremental_mutation()?;
        for _ in 0..levels {
            let selector = self
                .scope_selectors
                .pop()
                .expect("scope count checked above");
            self.add_clause_internal(&[!selector], false, false, ProofClauseKind::Administrative)?;
        }
        Ok(())
    }

    /// Starts retaining normalized input clauses for query-specific SMT proof
    /// construction.
    ///
    /// Proof recording must be selected before the session creates any SAT
    /// variables or clauses, matching SMT-LIB's start-mode requirement for
    /// `:produce-proofs`.
    pub(crate) fn enable_smt_proof_recording(&mut self) {
        assert!(
            !self.started && self.external_variable_count == 0 && self.proof_input.is_none(),
            "SMT proof recording must be enabled before encoding begins"
        );
        self.proof_input = Some(Vec::new());
    }

    pub(crate) fn proof_input(&self) -> Option<&[ProofInputClause]> {
        self.proof_input.as_deref()
    }

    /// Number of currently active clause scopes.
    #[must_use]
    pub fn scope_depth(&self) -> usize {
        self.scope_selectors.len()
    }

    /// Current cumulative search statistics.
    #[must_use]
    pub fn stats(&self) -> SolverStats {
        fn bytes(count: usize, element_size: usize) -> u64 {
            u64::try_from(count.saturating_mul(element_size)).unwrap_or(u64::MAX)
        }

        let mut stats = self.stats;
        stats.stored_binary_clauses = u64::try_from(self.binary_literals.len()).unwrap_or(u64::MAX);
        stats.stored_long_clauses = u64::try_from(self.clauses.len()).unwrap_or(u64::MAX);
        let regularity_binary_bytes = bytes(
            self.regularity_binary_samples.len(),
            std::mem::size_of::<[u32; PIVOT_SAMPLE_CAPACITY]>(),
        )
        .saturating_add(bytes(
            self.regularity_binary_states.len(),
            std::mem::size_of::<u8>(),
        ));
        let regularity_long_bytes = bytes(
            self.regularity_long_samples.len(),
            std::mem::size_of::<[u32; PIVOT_SAMPLE_CAPACITY]>(),
        )
        .saturating_add(bytes(
            self.regularity_long_states.len(),
            std::mem::size_of::<u8>(),
        ));
        stats.regularity_metadata_bytes =
            regularity_binary_bytes.saturating_add(regularity_long_bytes);
        let shadow_metadata_bytes =
            bytes(self.shadow_clause_states.len(), std::mem::size_of::<u8>())
                .saturating_add(bytes(
                    self.shadow_clause_started_at.len(),
                    std::mem::size_of::<u64>(),
                ))
                .saturating_add(bytes(
                    self.shadow_clauses.len(),
                    std::mem::size_of::<usize>(),
                ));
        stats.shadow_metadata_bytes = shadow_metadata_bytes;
        stats.counterfactual_phase_live_samples =
            u64::try_from(self.counterfactual_phase_samples.len()).unwrap_or(u64::MAX);
        stats.counterfactual_phase_metadata_bytes =
            stats.counterfactual_phase_sample_peak.saturating_mul(
                u64::try_from(std::mem::size_of::<CounterfactualPhaseSample>()).unwrap_or(u64::MAX),
            );
        stats.binary_storage_bytes =
            bytes(self.binary_literals.len(), std::mem::size_of::<[Lit; 2]>())
                .saturating_add(bytes(
                    self.binary_activity_index.len(),
                    std::mem::size_of::<u32>(),
                ))
                .saturating_add(bytes(
                    self.learned_binary_activity.len(),
                    std::mem::size_of::<f64>(),
                ))
                .saturating_add(bytes(self.binary_flags.len(), std::mem::size_of::<u8>()))
                .saturating_add(regularity_binary_bytes);
        stats.long_storage_bytes = bytes(self.clauses.len(), std::mem::size_of::<Clause>())
            .saturating_add(bytes(self.clause_arena.len(), std::mem::size_of::<Lit>()))
            .saturating_add(bytes(
                self.clause_usage_scores.len(),
                std::mem::size_of::<u32>(),
            ))
            .saturating_add(bytes(
                self.clause_scan_debt.len(),
                std::mem::size_of::<u64>(),
            ))
            .saturating_add(regularity_long_bytes)
            .saturating_add(shadow_metadata_bytes);
        stats.reason_storage_bytes =
            bytes(self.reasons.len(), std::mem::size_of::<Option<ClauseRef>>());
        let legacy_clause_count = self
            .clauses
            .len()
            .saturating_add(self.binary_literals.len());
        let legacy_arena_literals = self
            .clause_arena
            .len()
            .saturating_add(self.binary_literals.len().saturating_mul(2));
        stats.legacy_equivalent_storage_bytes =
            bytes(legacy_clause_count, std::mem::size_of::<Clause>())
                .saturating_add(bytes(legacy_arena_literals, std::mem::size_of::<Lit>()))
                .saturating_add(bytes(
                    self.reasons.len(),
                    std::mem::size_of::<Option<usize>>(),
                ));
        stats
    }

    pub(crate) const fn work_counters(&self) -> (u64, u64) {
        (self.stats.conflicts, self.stats.propagations)
    }

    /// Streams learned clauses to `output` as a textual DRAT proof.
    ///
    /// Clause deletions are emitted as `d` steps so checkers do not carry
    /// every deleted clause through the remaining proof, and the final empty
    /// clause is emitted for an UNSAT result. Proof output is optional and
    /// has no cost beyond one branch per learned clause when disabled. Call
    /// [`Solver::proof_error`] after solving.
    ///
    /// # Panics
    ///
    /// Panics if solving has already started.
    pub fn enable_drat_proof<W: Write + Send + 'static>(&mut self, output: W) {
        self.assert_not_started();
        self.proof.enable(output);
    }

    /// Returns a proof write or flush failure detected during solving.
    #[must_use]
    pub fn proof_error(&self) -> Option<&str> {
        self.proof.error()
    }

    /// Solves all permanent clauses.
    ///
    /// This is equivalent to calling [`Solver::solve_assuming`] with no
    /// assumptions.
    pub fn solve(&mut self) -> SolveResult {
        self.solve_assuming(&[])
    }

    /// Solves all permanent clauses under deterministic per-query limits.
    pub fn solve_with_limits(&mut self, limits: SolveLimits) -> SolveResult {
        self.solve_assuming_with_limits(&[], limits)
    }

    /// Solves all permanent clauses under temporary literal assumptions.
    ///
    /// Assumptions are applied as isolated decision levels and are removed
    /// after an unsatisfiable query or before the next distinct query. Learned
    /// clauses and heuristic state remain available to later calls. When the
    /// result is [`SolveResult::Unsat`] but the permanent clauses are still
    /// consistent, [`Solver::failed_assumptions`] returns an unsatisfiable
    /// subset of `assumptions`.
    ///
    /// # Panics
    ///
    /// Panics when an assumption references a variable that has not already
    /// been introduced by [`Solver::reserve_variables`] or
    /// [`Solver::add_clause`].
    pub fn solve_assuming(&mut self, assumptions: &[Lit]) -> SolveResult {
        self.solve_assuming_with_limits(assumptions, SolveLimits::default())
    }

    /// Limited form of [`Solver::solve_assuming`].
    pub fn solve_assuming_with_limits(
        &mut self,
        assumptions: &[Lit],
        limits: SolveLimits,
    ) -> SolveResult {
        for &assumption in assumptions {
            assert!(
                assumption.var().index() < self.external_variable_count,
                "assumptions must reference variables already known to the solver"
            );
        }

        let mut query_assumptions =
            Vec::with_capacity(self.scope_selectors.len().saturating_add(assumptions.len()));
        query_assumptions.extend_from_slice(&self.scope_selectors);
        query_assumptions.extend_from_slice(assumptions);

        if self.cached_assumptions == query_assumptions {
            if let Some(result) = &self.cached_result {
                return result.clone();
            }
        }

        let first_query = !self.started;
        if first_query {
            self.started = true;
        } else {
            self.cancel_until(0);
        }
        self.failed_assumptions.clear();

        let root_conflict = !self.consistent || self.propagate().is_some();
        let probing_conflict = first_query
            && !root_conflict
            && self.config.failed_literal_probing
            && !self.probe_failed_literals();
        let vivification_conflict = first_query
            && !root_conflict
            && !probing_conflict
            && self.config.clause_vivification
            && !self.vivify_original_clauses();
        let subsumption_conflict = first_query
            && !root_conflict
            && !probing_conflict
            && !vivification_conflict
            && self.config.clause_subsumption
            && !self.subsume_original_clauses();
        let elimination_conflict = first_query
            && !root_conflict
            && !probing_conflict
            && !vivification_conflict
            && !subsumption_conflict
            && self.config.bounded_variable_elimination
            && !self.eliminate_variables();
        let factorization_enabled = first_query
            && !root_conflict
            && !probing_conflict
            && !vivification_conflict
            && !subsumption_conflict
            && !elimination_conflict
            && self.config.bounded_variable_addition
            && (!self.config.macro_bounded_variable_addition
                || self.factorization_density_eligible());
        let factorization_conflict = factorization_enabled && !self.factor_exact_neighborhoods();
        let result = if root_conflict
            || probing_conflict
            || vivification_conflict
            || subsumption_conflict
            || elimination_conflict
            || factorization_conflict
        {
            self.consistent = false;
            SolveResult::Unsat
        } else if self.interrupt_flag.load(AtomicOrdering::Acquire) {
            SolveResult::Unknown(UnknownReason::Interrupted)
        } else {
            self.begin_search_control(limits);
            let result = self.search(&query_assumptions);
            self.search_control_active = false;
            result
        };
        if result.is_unsat() && !self.consistent {
            self.proof.add_clause(&[]);
        }
        self.proof.finish();
        if (result.is_unsat() && self.consistent) || result.is_unknown() {
            self.cancel_until(0);
        }
        if result.is_unsat() && self.consistent {
            self.failed_assumptions
                .retain(|literal| assumptions.contains(literal));
        } else if result.is_unknown() {
            self.failed_assumptions.clear();
        }
        if result.is_unknown() {
            self.cached_assumptions.clear();
            self.cached_result = None;
        } else {
            self.cached_assumptions.clear();
            self.cached_assumptions
                .extend_from_slice(&query_assumptions);
            self.cached_result = Some(result.clone());
        }
        result
    }

    /// Returns the failed subset from the most recent assumption-UNSAT query.
    ///
    /// The slice is empty after SAT and after the permanent clause set itself
    /// is found UNSAT.
    #[must_use]
    pub fn failed_assumptions(&self) -> &[Lit] {
        &self.failed_assumptions
    }

    /// Returns a cloneable thread-safe interruption handle.
    #[must_use]
    pub fn interrupter(&self) -> Interrupter {
        Interrupter {
            flag: Arc::clone(&self.interrupt_flag),
        }
    }

    fn begin_search_control(&mut self, limits: SolveLimits) {
        self.search_limits = limits;
        self.search_start_conflicts = self.stats.conflicts;
        self.search_start_propagations = self.stats.propagations;
        self.stop_reason = None;
        self.search_control_active = true;
    }

    fn poll_search_stop(&mut self) -> Option<UnknownReason> {
        if !self.search_control_active {
            return None;
        }
        if let Some(reason) = self.stop_reason {
            return Some(reason);
        }
        let reason = if self.interrupt_flag.load(AtomicOrdering::Acquire) {
            Some(UnknownReason::Interrupted)
        } else if self.search_limits.conflicts.is_some_and(|limit| {
            self.stats
                .conflicts
                .saturating_sub(self.search_start_conflicts)
                >= limit
        }) {
            Some(UnknownReason::ConflictLimit)
        } else if self.search_limits.propagations.is_some_and(|limit| {
            self.stats
                .propagations
                .saturating_sub(self.search_start_propagations)
                >= limit
        }) {
            Some(UnknownReason::PropagationLimit)
        } else {
            None
        };
        self.stop_reason = reason;
        reason
    }

    fn search(&mut self, assumptions: &[Lit]) -> SolveResult {
        if self.uses_chb_branching() {
            // Root propagation and optional preprocessing are outside the CHB
            // search loop described by Algorithm 1. Do not let their
            // assignments leak into the first propagation-round reward.
            self.chb_plays.clear();
        }
        if self.uses_transfer_branching() {
            self.stats.transfer_evsids_epochs = self.stats.transfer_evsids_epochs.saturating_add(1);
        }
        loop {
            if let Some(reason) = self.poll_search_stop() {
                return SolveResult::Unknown(reason);
            }
            let conflict = self.propagate();
            if let Some(reason) = self.poll_search_stop() {
                return SolveResult::Unknown(reason);
            }
            if self.uses_chb_branching() {
                self.chb_finish_propagation(conflict.is_some());
            }
            if let Some(conflict) = conflict {
                self.stats.conflicts += 1;
                if self.config.lbd_free_clause_management
                    && Self::should_decay_clause_usage(self.stats.conflicts)
                {
                    self.decay_clause_usage_scores();
                }
                self.conflicts_since_restart += 1;
                if self.decision_level() == 0 {
                    self.consistent = false;
                    return SolveResult::Unsat;
                }
                if self.uses_chb_branching() {
                    self.chb_decrease_step_size();
                }

                if self.uses_focused_restarts() {
                    if self.hybrid.stable {
                        self.stats.stable_conflicts += 1;
                    } else {
                        self.stats.focused_conflicts += 1;
                    }
                }

                if !self.uses_focused_restarts() && self.config.restart_policy == RestartPolicy::Lbd
                {
                    let trail_length = self.trail.len();
                    self.trail_restart.observe(trail_length);
                    if self.config.block_lbd_restarts
                        && self.stats.conflicts > BLOCKING_RESTART_MIN_CONFLICTS
                        && self.lbd_restart.is_full()
                        && self.trail_restart.unusually_deep(trail_length)
                    {
                        self.lbd_restart.clear_recent();
                        self.stats.blocked_restarts += 1;
                    }
                }

                let (learned, backtrack_level, lbd, derivation_ancestry) = self.analyze(conflict);
                if self.uses_adaptive_trail_reuse() {
                    self.adaptive_trail_reuse.observe_lbd(lbd);
                }
                if self.uses_focused_restarts() {
                    self.hybrid.observe_conflict(lbd);
                } else if self.config.restart_policy == RestartPolicy::Lbd {
                    self.lbd_restart.observe(lbd);
                }
                self.proof.add_clause(&learned);
                let actual_backtrack_level =
                    self.determine_backtrack_level(backtrack_level, learned.len());
                self.cancel_until(actual_backtrack_level);

                if learned.len() == 1 {
                    let enqueued = self.enqueue(learned[0], None);
                    debug_assert!(enqueued, "first-UIP unit must be assertive");
                } else {
                    let asserting = learned[0];
                    let clause = self.allocate_clause(learned, lbd, true);
                    if let Some(ancestry) = derivation_ancestry {
                        self.set_clause_derivation_ancestry(clause, ancestry);
                        if ancestry.is_nonregular() {
                            self.stats.regularity_nonregular_learned_clauses = self
                                .stats
                                .regularity_nonregular_learned_clauses
                                .saturating_add(1);
                        }
                    }
                    self.attach_clause(clause);
                    self.stats.learned_clauses += 1;
                    if lbd <= TIER1_LBD {
                        self.stats.learned_tier1_clauses += 1;
                    } else if lbd <= TIER2_LBD {
                        self.stats.learned_tier2_clauses += 1;
                    }
                    self.active_learned_clauses += 1;
                    self.stats.peak_active_learned_clauses = self
                        .stats
                        .peak_active_learned_clauses
                        .max(self.active_learned_clauses);
                    let enqueued = self.enqueue(asserting, Some(clause));
                    debug_assert!(enqueued, "first-UIP clause must be assertive");
                }

                self.decay_activities();
                if self.stats.conflicts >= self.next_reduction {
                    self.reduce_database();
                    self.next_reduction = if self.config.lbd_free_clause_management {
                        self.stats
                            .conflicts
                            .saturating_add(Self::lbd_free_reduction_interval(
                                self.stats.reductions,
                            ))
                    } else {
                        self.next_reduction.saturating_add(Self::REDUCTION_INTERVAL)
                    };
                }
                if self.should_rephase() {
                    self.rephase();
                } else if self.config.search_strategy == SearchStrategy::FocusedStable
                    && self.hybrid.should_switch(self.stats)
                {
                    self.hybrid.switch(self.stats);
                    self.stats.mode_switches += 1;
                    if !self.hybrid.stable {
                        self.vmtf.reset_search(&self.assignments);
                    }
                } else if self.is_active_probe() && self.stats.conflicts >= FOCUSED_PROBE_CONFLICTS
                {
                    self.finish_focused_probe();
                } else if self.should_restart() && self.decision_level() > 0 {
                    self.restart();
                }
            } else if (self.decision_level() as usize) < assumptions.len() {
                let assumption = assumptions[self.decision_level() as usize];
                match self.literal_value(assumption) {
                    TRUE => {
                        // Preserve one level per assumption even when an
                        // earlier assumption or root propagation already made
                        // this literal true. This keeps level i aligned with
                        // assumptions[i - 1] for failed-core extraction.
                        self.trail_limits.push(self.trail.len());
                    }
                    FALSE => {
                        self.failed_assumptions =
                            self.analyze_failed_assumption(assumption, assumptions);
                        return SolveResult::Unsat;
                    }
                    UNASSIGNED => {
                        self.trail_limits.push(self.trail.len());
                        let enqueued = self.enqueue_internal::<false>(assumption, None);
                        debug_assert!(enqueued, "unassigned assumption must enqueue");
                    }
                    _ => unreachable!("assignments only contain -1, 0, or 1"),
                }
            } else if let Some(decision) = self.pick_branch_literal() {
                self.trail_limits.push(self.trail.len());
                self.stats.decisions += 1;
                if self.uses_focused_restarts() {
                    if self.hybrid.stable {
                        self.stats.stable_decisions += 1;
                    } else {
                        self.stats.focused_decisions += 1;
                    }
                }
                let enqueued = self.enqueue(decision, None);
                debug_assert!(enqueued, "branch variable must be unassigned");
            } else {
                let mut values = self
                    .assignments
                    .iter()
                    .map(|&value| value == TRUE)
                    .collect::<Vec<_>>();
                self.extend_model(&mut values);
                values.truncate(self.external_variable_count);
                return SolveResult::Sat(Model { values });
            }
        }
    }

    fn analyze_failed_assumption(&mut self, failed: Lit, assumptions: &[Lit]) -> Vec<Lit> {
        debug_assert_eq!(self.literal_value(failed), FALSE);

        // Construct a clause over negated assumption decisions by walking
        // backward from the literal that contradicts `failed`. This is the
        // final-conflict analysis used by incremental SAT solvers: reason
        // literals are expanded until only root facts and decision literals
        // remain.
        let mut conflict = vec![!failed];
        let failed_variable = failed.var();
        self.seen[failed_variable.index()] = true;

        if self.decision_level() > 0 {
            let first_assumption_trail = self.trail_limits[0];
            for index in (first_assumption_trail..self.trail.len()).rev() {
                let assigned = self.trail[index];
                let variable = assigned.var();
                if !self.seen[variable.index()] {
                    continue;
                }
                self.seen[variable.index()] = false;

                if let Some(reason) = self.reasons[variable.index()] {
                    let literal_count = self.clause_len(reason);
                    for reason_index in 0..literal_count {
                        let antecedent = self.clause_literal(reason, reason_index);
                        if antecedent.var() != variable && self.levels[antecedent.var().index()] > 0
                        {
                            self.seen[antecedent.var().index()] = true;
                        }
                    }
                } else {
                    debug_assert!(self.levels[variable.index()] > 0);
                    conflict.push(!assigned);
                }
            }
        }
        self.seen[failed_variable.index()] = false;

        // Return assumptions, rather than the negated conflict clause, in the
        // caller's stable order. Duplicate assumptions do not add information
        // to an unsatisfiable subset.
        let mut failed_assumptions = Vec::new();
        for &assumption in assumptions {
            if conflict.contains(&!assumption) && !failed_assumptions.contains(&assumption) {
                failed_assumptions.push(assumption);
            }
        }
        debug_assert!(failed_assumptions.contains(&failed));
        failed_assumptions
    }

    fn assert_not_started(&self) {
        assert!(
            !self.started,
            "clauses cannot be added after solve() starts"
        );
    }

    fn decision_level(&self) -> u32 {
        u32::try_from(self.trail_limits.len()).expect("decision level exceeds u32")
    }

    // After a chronological backtrack the asserting literal is recorded at the
    // preserved level rather than at `jump_level`, the level that actually
    // implies it. The over-approximation is sound: recorded levels only ever
    // exceed true implication levels, every conflict clause still contains a
    // literal at the recorded current level, and the trail stays partitioned
    // by `trail_limits`. The cost is that a later backjump between the two
    // levels unassigns the literal without re-propagating its clause (the
    // implication is re-derived on demand) and that recorded LBDs can be
    // inflated. Assigning the true level instead would require out-of-order
    // trail maintenance and re-propagation as in CaDiCaL.
    fn determine_backtrack_level(&mut self, jump_level: u32, learned_length: usize) -> u32 {
        if !self.config.chronological_backtracking || learned_length == 1 {
            return jump_level;
        }

        let chronological_level = self.decision_level().saturating_sub(1);
        let preserved_levels = chronological_level.saturating_sub(jump_level);
        if preserved_levels <= CHRONO_LEVEL_LIMIT {
            return jump_level;
        }

        self.stats.chronological_backtracks = self.stats.chronological_backtracks.saturating_add(1);
        self.stats.chronological_levels_preserved = self
            .stats
            .chronological_levels_preserved
            .saturating_add(u64::from(preserved_levels));
        chronological_level
    }

    fn should_rephase(&self) -> bool {
        self.config.systematic_rephasing && self.stats.conflicts >= self.next_rephase
    }

    fn rephase(&mut self) {
        self.cancel_until(0);
        match self.stats.rephases % 4 {
            0 | 2 => {
                self.phase.clone_from(&self.best_phase);
                self.best_assigned = 0;
                self.stats.best_rephases = self.stats.best_rephases.saturating_add(1);
            }
            1 => {
                self.phase.fill(false);
                self.stats.inverted_rephases = self.stats.inverted_rephases.saturating_add(1);
            }
            3 => {
                self.phase.fill(true);
                self.stats.original_rephases = self.stats.original_rephases.saturating_add(1);
            }
            _ => unreachable!("four-entry rephase schedule"),
        }
        self.stats.rephases = self.stats.rephases.saturating_add(1);
        self.next_rephase = self
            .stats
            .conflicts
            .saturating_add(Self::rephase_interval(self.stats.rephases));
    }

    fn rephase_interval(count: u64) -> u64 {
        let logarithm = ((count.saturating_add(9)) as f64).log10();
        let scaled = (Self::REPHASE_BASE as f64) * (count as f64) * logarithm.powi(3);
        (scaled as u64).max(Self::REPHASE_BASE)
    }

    fn uses_vmtf_branching(&self) -> bool {
        match self.config.search_strategy {
            SearchStrategy::Evsids
            | SearchStrategy::Lrb
            | SearchStrategy::Transfer
            | SearchStrategy::Chb => false,
            SearchStrategy::Vmtf | SearchStrategy::Focused | SearchStrategy::ProbeVmtf => true,
            SearchStrategy::ProbeEvsids => !self.probe_finished,
            SearchStrategy::FocusedStable => !self.hybrid.stable,
        }
    }

    fn uses_lrb_branching(&self) -> bool {
        self.config.search_strategy == SearchStrategy::Lrb
    }

    fn uses_transfer_branching(&self) -> bool {
        self.config.search_strategy == SearchStrategy::Transfer
    }

    fn maintains_lrb_scores(&self) -> bool {
        self.uses_lrb_branching() || self.uses_transfer_branching()
    }

    fn transfer_uses_lrb_for_decisions(&self) -> bool {
        self.uses_transfer_branching() && self.transfer.active == TransferRegime::Lrb
    }

    fn uses_chb_branching(&self) -> bool {
        self.config.search_strategy == SearchStrategy::Chb
    }

    fn uses_adaptive_trail_reuse(&self) -> bool {
        self.config.restart_trail_reuse == RestartTrailReuse::Adaptive
            && self.config.search_strategy == SearchStrategy::Evsids
    }

    fn uses_focused_restarts(&self) -> bool {
        matches!(
            self.config.search_strategy,
            SearchStrategy::Focused | SearchStrategy::FocusedStable
        ) || self.is_active_probe()
    }

    fn is_active_probe(&self) -> bool {
        !self.probe_finished
            && matches!(
                self.config.search_strategy,
                SearchStrategy::ProbeEvsids | SearchStrategy::ProbeVmtf
            )
    }

    fn finish_focused_probe(&mut self) {
        debug_assert!(self.is_active_probe());
        self.probe_finished = true;
        self.stats.mode_switches += 1;
        self.conflicts_since_restart = 0;
        self.restart_index = 0;
        self.restart_limit = Self::RESTART_BASE;
        self.lbd_restart = LbdRestartState::default();
        self.trail_restart = TrailRestartState::default();
    }

    fn should_restart(&self) -> bool {
        if self.uses_focused_restarts() {
            return self.hybrid.should_restart(self.stats);
        }
        match self.config.restart_policy {
            RestartPolicy::Luby => self.conflicts_since_restart >= self.restart_limit,
            RestartPolicy::Lbd => self.lbd_restart.should_restart(),
        }
    }

    fn restart(&mut self) {
        let stable = self.uses_focused_restarts() && self.hybrid.stable;
        let counterfactual_phase_votes = if self.config.counterfactual_phase_voting {
            self.observe_counterfactual_phases_before_root_restart()
        } else {
            Vec::new()
        };
        let reuse_level = self.restart_reuse_level();
        self.cancel_until(reuse_level);
        if self.config.counterfactual_phase_voting {
            debug_assert_eq!(reuse_level, 0);
            self.apply_counterfactual_phase_votes_at_root(&counterfactual_phase_votes);
        }
        if self.config.shadow_clause_reactivation {
            debug_assert_eq!(reuse_level, 0);
            self.finalize_shadow_clauses_at_root();
        }
        self.stats.restarts += 1;
        if reuse_level > 0 {
            self.stats.trail_reuse_restarts = self.stats.trail_reuse_restarts.saturating_add(1);
            self.stats.trail_reuse_levels = self
                .stats
                .trail_reuse_levels
                .saturating_add(u64::from(reuse_level));
        }
        self.conflicts_since_restart = 0;
        if self.uses_transfer_branching() {
            self.finish_transfer_epoch();
        }
        if self.uses_focused_restarts() {
            if stable {
                self.stats.stable_restarts += 1;
            } else {
                self.stats.focused_restarts += 1;
            }
            self.hybrid.restarted(self.stats);
            return;
        }
        match self.config.restart_policy {
            RestartPolicy::Luby => {
                self.restart_index = self.restart_index.saturating_add(1);
                self.restart_limit = Self::RESTART_BASE.saturating_mul(luby(self.restart_index));
            }
            RestartPolicy::Lbd => self.lbd_restart.clear_recent(),
        }
    }

    fn observe_counterfactual_phases_before_root_restart(&mut self) -> Vec<(Var, bool)> {
        debug_assert!(self.config.counterfactual_phase_voting);
        debug_assert!(self.decision_level() > 0);
        self.stats.counterfactual_phase_snapshots =
            self.stats.counterfactual_phase_snapshots.saturating_add(1);

        let mut samples = std::mem::take(&mut self.counterfactual_phase_samples);
        samples.sort_unstable();
        let mut votes = Vec::new();
        for sample in samples {
            debug_assert!(!sample.clause.is_binary());
            debug_assert!(self.clause_learned(sample.clause));
            debug_assert!(self.clause_deleted(sample.clause));
            self.stats.counterfactual_phase_clauses_scanned = self
                .stats
                .counterfactual_phase_clauses_scanned
                .saturating_add(1);

            let clause = &self.clauses[sample.clause.index()];
            let start = clause.start;
            let end = start.saturating_add(clause.len());
            let mut satisfied = false;
            let mut unassigned = None;
            let mut multiple_unassigned = false;
            for position in start..end {
                let literal = self.clause_arena[position];
                self.stats.counterfactual_phase_literal_checks = self
                    .stats
                    .counterfactual_phase_literal_checks
                    .saturating_add(1);
                match self.literal_value(literal) {
                    TRUE => {
                        satisfied = true;
                        break;
                    }
                    FALSE => {}
                    UNASSIGNED => {
                        if unassigned.is_some() {
                            multiple_unassigned = true;
                        } else {
                            unassigned = Some(literal);
                        }
                    }
                    _ => unreachable!("assignments only contain -1, 0, or 1"),
                }
            }

            if satisfied {
                self.stats.counterfactual_phase_satisfied_clauses = self
                    .stats
                    .counterfactual_phase_satisfied_clauses
                    .saturating_add(1);
            } else if multiple_unassigned {
                self.stats.counterfactual_phase_open_clauses = self
                    .stats
                    .counterfactual_phase_open_clauses
                    .saturating_add(1);
            } else if let Some(literal) = unassigned {
                self.stats.counterfactual_phase_unit_clauses = self
                    .stats
                    .counterfactual_phase_unit_clauses
                    .saturating_add(1);
                self.stats.counterfactual_phase_unit_votes =
                    self.stats.counterfactual_phase_unit_votes.saturating_add(1);
                votes.push((literal.var(), literal.is_positive()));
            } else {
                self.stats.counterfactual_phase_conflict_clauses = self
                    .stats
                    .counterfactual_phase_conflict_clauses
                    .saturating_add(1);
            }
        }

        votes.sort_unstable_by_key(|&(variable, positive)| (variable.index(), positive));
        let mut unanimous = Vec::new();
        let mut start = 0;
        while start < votes.len() {
            let variable = votes[start].0;
            let polarity = votes[start].1;
            let mut end = start + 1;
            let mut agrees = true;
            while end < votes.len() && votes[end].0 == variable {
                agrees &= votes[end].1 == polarity;
                end += 1;
            }
            if agrees {
                self.stats.counterfactual_phase_unanimous_variables = self
                    .stats
                    .counterfactual_phase_unanimous_variables
                    .saturating_add(1);
                unanimous.push((variable, polarity));
            } else {
                self.stats.counterfactual_phase_disagreeing_variables = self
                    .stats
                    .counterfactual_phase_disagreeing_variables
                    .saturating_add(1);
            }
            start = end;
        }
        unanimous
    }

    fn apply_counterfactual_phase_votes_at_root(&mut self, votes: &[(Var, bool)]) {
        debug_assert!(self.config.counterfactual_phase_voting);
        debug_assert_eq!(self.decision_level(), 0);
        for &(variable, positive) in votes {
            let index = variable.index();
            if self.assignments[index] != UNASSIGNED {
                self.stats.counterfactual_phase_root_assigned_skips = self
                    .stats
                    .counterfactual_phase_root_assigned_skips
                    .saturating_add(1);
                continue;
            }
            self.stats.counterfactual_phase_writes =
                self.stats.counterfactual_phase_writes.saturating_add(1);
            if self.phase[index] != positive {
                self.stats.counterfactual_phase_changes =
                    self.stats.counterfactual_phase_changes.saturating_add(1);
            }
            self.phase[index] = positive;
        }
    }

    fn finalize_shadow_clauses_at_root(&mut self) {
        debug_assert!(self.config.shadow_clause_reactivation);
        debug_assert_eq!(self.decision_level(), 0);

        let mut retained = Vec::with_capacity(self.shadow_clauses.len());
        let mut reactivated = Vec::new();
        for reference in std::mem::take(&mut self.shadow_clauses) {
            let age = self
                .stats
                .conflicts
                .saturating_sub(self.shadow_clause_started_at[reference]);
            if age < Self::SHADOW_OBSERVATION_CONFLICTS {
                retained.push(reference);
                continue;
            }

            self.stats.shadow_observation_conflicts =
                self.stats.shadow_observation_conflicts.saturating_add(age);
            self.shadow_clause_started_at[reference] = 0;
            if self.shadow_clause_states[reference] == SHADOW_TRIGGERED {
                self.shadow_clause_states[reference] = SHADOW_ACTIVE;
                self.clause_usage_scores[reference] = 1;
                self.active_learned_clauses = self.active_learned_clauses.saturating_add(1);
                self.stats.shadow_reactivated_clauses =
                    self.stats.shadow_reactivated_clauses.saturating_add(1);
                reactivated.push(reference);
            } else {
                debug_assert_eq!(self.shadow_clause_states[reference], SHADOW_OBSERVING);
                self.shadow_clause_states[reference] = SHADOW_ACTIVE;
                self.mark_clause_deleted(ClauseRef::long(reference));
                self.stats.deleted_clauses = self.stats.deleted_clauses.saturating_add(1);
                self.stats.shadow_expired_clauses =
                    self.stats.shadow_expired_clauses.saturating_add(1);
            }
        }
        self.shadow_clauses = retained;

        let mut root_units = Vec::new();
        for reference in reactivated {
            let clause = ClauseRef::long(reference);
            let literals = self.clause_literals(clause).to_vec();
            let mut unit = None;
            let mut multiple_unassigned = false;
            let mut satisfied = false;
            for literal in literals {
                match self.literal_value(literal) {
                    TRUE => {
                        satisfied = true;
                        break;
                    }
                    UNASSIGNED if unit.is_none() => unit = Some(literal),
                    UNASSIGNED => multiple_unassigned = true,
                    FALSE => {}
                    _ => unreachable!("assignments only contain -1, 0, or 1"),
                }
            }
            if satisfied || multiple_unassigned {
                continue;
            }
            if let Some(unit) = unit {
                root_units.push((unit, clause));
            } else {
                self.stats.shadow_root_conflicts =
                    self.stats.shadow_root_conflicts.saturating_add(1);
                self.shadow_deferred_root_conflict.get_or_insert(clause);
            }
        }

        for (unit, clause) in root_units {
            if self.enqueue(unit, Some(clause)) {
                self.stats.shadow_root_units = self.stats.shadow_root_units.saturating_add(1);
            } else {
                self.stats.shadow_root_conflicts =
                    self.stats.shadow_root_conflicts.saturating_add(1);
                self.shadow_deferred_root_conflict.get_or_insert(clause);
            }
        }
    }

    fn finish_transfer_epoch(&mut self) {
        debug_assert!(self.uses_transfer_branching());
        let (previous, next) = self.transfer.finish_epoch(self.stats.conflicts);
        match next {
            TransferRegime::Evsids => {
                self.stats.transfer_evsids_epochs =
                    self.stats.transfer_evsids_epochs.saturating_add(1);
            }
            TransferRegime::Lrb => {
                self.stats.transfer_lrb_epochs = self.stats.transfer_lrb_epochs.saturating_add(1);
            }
        }
        if previous != next {
            self.stats.transfer_mode_switches = self.stats.transfer_mode_switches.saturating_add(1);
        }
    }

    fn restart_reuse_level(&mut self) -> u32 {
        if self.config.search_strategy != SearchStrategy::Evsids
            || self.config.restart_trail_reuse == RestartTrailReuse::Never
        {
            return 0;
        }
        if self.uses_adaptive_trail_reuse() {
            self.adaptive_trail_reuse.finish_epoch(&mut self.stats);
        }

        let reusable = self.restart_reuse_candidate();
        if reusable > 0 {
            self.stats.trail_reuse_eligible_restarts =
                self.stats.trail_reuse_eligible_restarts.saturating_add(1);
        }

        if self.config.restart_trail_reuse == RestartTrailReuse::Always {
            return reusable;
        }

        debug_assert!(self.uses_adaptive_trail_reuse());
        let (level, action) = if reusable == 0 {
            (0, RestartAction::Root)
        } else {
            match self.adaptive_trail_reuse.choose() {
                AdaptiveReuseChoice::Probe => {
                    self.stats.adaptive_reuse_probes =
                        self.stats.adaptive_reuse_probes.saturating_add(1);
                    (reusable, RestartAction::Reuse)
                }
                AdaptiveReuseChoice::QualityAccept => {
                    self.stats.adaptive_reuse_quality_accepts =
                        self.stats.adaptive_reuse_quality_accepts.saturating_add(1);
                    (reusable, RestartAction::Reuse)
                }
                AdaptiveReuseChoice::QualityReject => {
                    self.stats.adaptive_reuse_quality_rejects =
                        self.stats.adaptive_reuse_quality_rejects.saturating_add(1);
                    (0, RestartAction::Root)
                }
            }
        };
        self.adaptive_trail_reuse.begin_epoch(action, self.stats);
        level
    }

    fn restart_reuse_candidate(&mut self) -> u32 {
        let Some(next_decision) = self.order.peek_max(&self.assignments, &self.activity) else {
            return 0;
        };

        let mut reusable = 0;
        for level in 1..=self.decision_level() {
            let trail_index = self.trail_limits[level as usize - 1];
            let decision = self.trail[trail_index].var();
            debug_assert!(self.reasons[decision.index()].is_none());
            if higher_priority(next_decision, decision, &self.activity) {
                break;
            }
            reusable = level;
        }
        reusable
    }

    fn literal_value(&self, literal: Lit) -> i8 {
        value_of(&self.assignments, literal)
    }

    fn enqueue(&mut self, literal: Lit, reason: Option<ClauseRef>) -> bool {
        self.enqueue_internal::<true>(literal, reason)
    }

    fn enqueue_internal<const SAVE_PHASE: bool>(
        &mut self,
        literal: Lit,
        reason: Option<ClauseRef>,
    ) -> bool {
        let variable = literal.var();
        match self.literal_value(literal) {
            TRUE => true,
            FALSE => false,
            UNASSIGNED => {
                if self.maintains_lrb_scores() {
                    self.lrb_on_assign(variable);
                }
                if self.uses_chb_branching() {
                    self.chb_plays.push(variable);
                }
                self.assignments[variable.index()] =
                    if literal.is_positive() { TRUE } else { FALSE };
                self.levels[variable.index()] = self.decision_level();
                self.reasons[variable.index()] = reason;
                if SAVE_PHASE {
                    self.phase[variable.index()] = literal.is_positive();
                }
                self.trail.push(literal);
                true
            }
            _ => unreachable!("assignments only contain -1, 0, or 1"),
        }
    }

    fn lrb_on_assign(&mut self, variable: Var) {
        debug_assert!(self.maintains_lrb_scores());
        self.lrb_decay_stale_score(variable);
        let index = variable.index();
        self.lrb_assigned_at[index] = self.stats.conflicts;
        self.lrb_participated[index] = 0;
        self.lrb_reasoned[index] = 0;
    }

    fn lrb_decay_stale_score(&mut self, variable: Var) -> bool {
        debug_assert!(self.maintains_lrb_scores());
        let index = variable.index();
        let age = self
            .stats
            .conflicts
            .saturating_sub(self.lrb_canceled_at[index]);
        if age == 0 {
            return false;
        }

        let exponent = i32::try_from(age).unwrap_or(i32::MAX);
        let decay = Self::LRB_ANTI_EXPLORATION_DECAY.powi(exponent);
        if self.uses_transfer_branching() {
            let old_activity = self.transfer_lrb_activity[index];
            self.transfer_lrb_activity[index] *= decay;
            self.transfer_lrb_order
                .update(variable, old_activity, &self.transfer_lrb_activity);
        } else {
            let old_activity = self.activity[index];
            self.activity[index] *= decay;
            self.order.update(variable, old_activity, &self.activity);
        }
        self.lrb_canceled_at[index] = self.stats.conflicts;
        self.stats.lrb_anti_exploration_decays =
            self.stats.lrb_anti_exploration_decays.saturating_add(1);
        true
    }

    fn chb_finish_propagation(&mut self, conflict: bool) {
        debug_assert!(self.uses_chb_branching());
        let multiplier = if conflict {
            Self::CHB_CONFLICT_MULTIPLIER
        } else {
            Self::CHB_NON_CONFLICT_MULTIPLIER
        };
        let mut plays = std::mem::take(&mut self.chb_plays);
        for &variable in &plays {
            let index = variable.index();
            let conflict_age = self
                .stats
                .conflicts
                .saturating_sub(self.chb_last_conflict[index])
                .saturating_add(1);
            let reward = multiplier / conflict_age as f64;
            let old_activity = self.activity[index];
            self.activity[index] =
                (1.0 - self.chb_step_size) * old_activity + self.chb_step_size * reward;
            self.order.update(variable, old_activity, &self.activity);
            self.stats.chb_score_updates = self.stats.chb_score_updates.saturating_add(1);
            if conflict {
                self.stats.chb_conflict_score_updates =
                    self.stats.chb_conflict_score_updates.saturating_add(1);
            }
        }
        plays.clear();
        self.chb_plays = plays;
    }

    fn chb_decrease_step_size(&mut self) {
        debug_assert!(self.uses_chb_branching());
        self.chb_step_size =
            (self.chb_step_size - Self::CHB_STEP_SIZE_DECREMENT).max(Self::CHB_MINIMUM_STEP_SIZE);
    }

    fn propagate(&mut self) -> Option<ClauseRef> {
        if let Some(conflict) = self.shadow_deferred_root_conflict.take() {
            return Some(conflict);
        }
        self.propagate_internal::<true, false, false, false>(None)
    }

    fn propagate_probe<const SAVE_PHASE: bool>(&mut self) -> Option<ClauseRef> {
        self.propagate_internal::<SAVE_PHASE, true, false, false>(None)
    }

    fn propagate_vivification<const SAVE_PHASE: bool>(
        &mut self,
        ignored_clause: Option<ClauseRef>,
    ) -> Option<ClauseRef> {
        match ignored_clause {
            Some(clause) => self.propagate_internal::<SAVE_PHASE, false, true, true>(Some(clause)),
            None => self.propagate_internal::<SAVE_PHASE, false, true, false>(None),
        }
    }

    fn propagate_internal<
        const SAVE_PHASE: bool,
        const COUNT_AS_PROBING: bool,
        const COUNT_AS_VIVIFICATION: bool,
        const IGNORE_CLAUSE: bool,
    >(
        &mut self,
        ignored_clause: Option<ClauseRef>,
    ) -> Option<ClauseRef> {
        while self.propagation_head < self.trail.len() {
            if self.poll_search_stop().is_some() {
                return None;
            }
            let propagated = self.trail[self.propagation_head];
            self.propagation_head += 1;
            self.stats.propagations += 1;
            if COUNT_AS_PROBING {
                self.stats.probing_propagations += 1;
            }
            if COUNT_AS_VIVIFICATION {
                self.stats.vivification_propagations += 1;
            }
            let falsified = !propagated;
            let watch_index = falsified.index();
            let mut pending = std::mem::take(&mut self.watches[watch_index]);
            let mut read = 0;
            let mut retained = 0;

            while read < pending.len() {
                let watch = pending[read];
                read += 1;
                let clause = watch.clause();
                let blocker = watch.blocker();
                let binary = watch.is_binary();
                let shadow = !binary && self.clause_is_shadow(clause);
                if self.clause_deleted(clause) {
                    continue;
                }
                if IGNORE_CLAUSE && Some(clause) == ignored_clause {
                    pending[retained] = watch;
                    retained += 1;
                    continue;
                }
                if binary && self.config.binary_fast_path {
                    self.stats.binary_watch_visits += 1;
                    pending[retained] = watch;
                    retained += 1;
                    match self.literal_value(blocker) {
                        TRUE => continue,
                        FALSE => {
                            let unscanned = pending.len() - read;
                            pending.copy_within(read.., retained);
                            retained += unscanned;
                            pending.truncate(retained);
                            self.watches[watch_index] = pending;
                            if !COUNT_AS_PROBING && !COUNT_AS_VIVIFICATION {
                                self.observe_transfer_clause_use(clause, TransferUse::Propagation);
                            }
                            return Some(clause);
                        }
                        UNASSIGNED => {
                            if !COUNT_AS_PROBING && !COUNT_AS_VIVIFICATION {
                                self.observe_transfer_clause_use(clause, TransferUse::Propagation);
                            }
                            let enqueued =
                                self.enqueue_internal::<SAVE_PHASE>(blocker, Some(clause));
                            debug_assert!(
                                enqueued,
                                "binary implication must enqueue its other literal"
                            );
                            continue;
                        }
                        _ => unreachable!("assignments only contain -1, 0, or 1"),
                    }
                }
                let blocker_value = self.literal_value(blocker);
                if shadow && !COUNT_AS_PROBING && !COUNT_AS_VIVIFICATION {
                    self.stats.shadow_watch_visits =
                        self.stats.shadow_watch_visits.saturating_add(1);
                    self.charge_shadow_literal_checks(1);
                }
                if !COUNT_AS_PROBING && !COUNT_AS_VIVIFICATION && !binary {
                    self.charge_clause_scan_debt(clause, 1);
                }
                if blocker_value == TRUE {
                    pending[retained] = watch;
                    retained += 1;
                    continue;
                }
                if binary {
                    let literals = &mut self.binary_literals[clause.index()];
                    if literals[0] == falsified {
                        literals.swap(0, 1);
                    }
                    debug_assert_eq!(literals[1], falsified);
                    let other = literals[0];
                    pending[retained] = Watch::new(clause, other);
                    retained += 1;
                    if self.literal_value(other) == FALSE {
                        let unscanned = pending.len() - read;
                        pending.copy_within(read.., retained);
                        retained += unscanned;
                        pending.truncate(retained);
                        self.watches[watch_index] = pending;
                        if !COUNT_AS_PROBING && !COUNT_AS_VIVIFICATION {
                            self.observe_transfer_clause_use(clause, TransferUse::Propagation);
                        }
                        return Some(clause);
                    }
                    if !COUNT_AS_PROBING && !COUNT_AS_VIVIFICATION {
                        self.observe_transfer_clause_use(clause, TransferUse::Propagation);
                    }
                    let enqueued = self.enqueue_internal::<SAVE_PHASE>(other, Some(clause));
                    debug_assert!(enqueued, "binary clause must enqueue its other literal");
                    continue;
                }

                {
                    let range = self.clauses[clause.index()].range();
                    let literals = &mut self.clause_arena[range];
                    if literals[0] == falsified {
                        literals.swap(0, 1);
                    }
                    debug_assert_eq!(literals[1], falsified);
                }

                let other = self.clause_arena[self.clauses[clause.index()].start];
                if shadow && !COUNT_AS_PROBING && !COUNT_AS_VIVIFICATION {
                    self.charge_shadow_literal_checks(1);
                }
                if !COUNT_AS_PROBING && !COUNT_AS_VIVIFICATION {
                    self.charge_clause_scan_debt(clause, 1);
                }
                if self.literal_value(other) == TRUE {
                    pending[retained] = Watch::new(clause, other);
                    retained += 1;
                    continue;
                }

                let replacement = {
                    let metadata = &self.clauses[clause.index()];
                    let literals = &self.clause_arena[metadata.range()];
                    (2..literals.len())
                        .find(|&index| value_of(&self.assignments, literals[index]) != FALSE)
                };
                if !COUNT_AS_PROBING && !COUNT_AS_VIVIFICATION {
                    let replacement_checks = match replacement {
                        Some(index) => index - 1,
                        None => self.clauses[clause.index()].len().saturating_sub(2),
                    };
                    self.charge_clause_scan_debt(clause, replacement_checks);
                    if shadow {
                        self.charge_shadow_literal_checks(replacement_checks);
                    }
                }
                if let Some(replacement) = replacement {
                    let new_watch = {
                        let range = self.clauses[clause.index()].range();
                        let literals = &mut self.clause_arena[range];
                        literals.swap(1, replacement);
                        literals[1]
                    };
                    self.watches[new_watch.index()].push(Watch::new(clause, other));
                    continue;
                }

                pending[retained] = Watch::new(clause, other);
                retained += 1;
                let other_value = self.literal_value(other);
                if shadow {
                    if !COUNT_AS_PROBING && !COUNT_AS_VIVIFICATION {
                        self.trigger_shadow_clause(clause, other_value == FALSE);
                    }
                    continue;
                }
                if other_value == FALSE {
                    let unscanned = pending.len() - read;
                    pending.copy_within(read.., retained);
                    retained += unscanned;
                    pending.truncate(retained);
                    self.watches[watch_index] = pending;
                    if !COUNT_AS_PROBING && !COUNT_AS_VIVIFICATION {
                        self.observe_transfer_clause_use(clause, TransferUse::Propagation);
                    }
                    return Some(clause);
                }

                if !COUNT_AS_PROBING && !COUNT_AS_VIVIFICATION {
                    self.observe_transfer_clause_use(clause, TransferUse::Propagation);
                    self.bump_clause_usage(clause, ClauseUsageUse::Propagation);
                }
                let enqueued = self.enqueue_internal::<SAVE_PHASE>(other, Some(clause));
                debug_assert!(enqueued, "unit clause must enqueue its unwatched literal");
            }
            pending.truncate(retained);
            self.watches[watch_index] = pending;
        }
        None
    }

    fn failed_literal_probe_budget(&self) -> u64 {
        u64::try_from(self.assignments.len())
            .unwrap_or(u64::MAX)
            .saturating_mul(2)
            .min(Self::FAILED_LITERAL_PROBE_PROPAGATION_CAP)
    }

    fn probe_failed_literals(&mut self) -> bool {
        debug_assert_eq!(self.decision_level(), 0);
        debug_assert_eq!(self.propagation_head, self.trail.len());

        let budget = self.failed_literal_probe_budget();
        let started_at = self.stats.probing_propagations;

        for index in 0..self.assignments.len() {
            if self.assignments[index] != UNASSIGNED {
                continue;
            }
            let variable =
                Var::new(u32::try_from(index).expect("variable count checked when reserved"));
            let saved_phase = self.phase[index];

            for positive in [saved_phase, !saved_phase] {
                if self.assignments[index] != UNASSIGNED {
                    break;
                }
                if self.stats.probing_propagations.saturating_sub(started_at) >= budget {
                    return true;
                }

                let assumption = Lit::new(variable, positive);
                self.stats.failed_literal_probes =
                    self.stats.failed_literal_probes.saturating_add(1);
                self.trail_limits.push(self.trail.len());
                let enqueued = self.enqueue_internal::<false>(assumption, None);
                debug_assert!(enqueued, "probe variable must be root-unassigned");
                let failed = self.propagate_probe::<false>().is_some();
                self.cancel_until_internal::<false>(0);

                if !failed {
                    continue;
                }

                let unit = !assumption;
                self.stats.failed_literal_units = self.stats.failed_literal_units.saturating_add(1);
                self.proof.add_clause(&[unit]);
                if !self.enqueue(unit, None) || self.propagate_probe::<true>().is_some() {
                    return false;
                }
            }
        }
        true
    }

    fn vivification_budget(&self) -> u64 {
        let logical_literals = self
            .clause_arena
            .len()
            .saturating_add(self.binary_literals.len().saturating_mul(2));
        u64::try_from(logical_literals)
            .unwrap_or(u64::MAX)
            .min(Self::VIVIFICATION_PROPAGATION_CAP)
    }

    fn vivification_schedule(&self) -> Vec<ClauseRef> {
        let mut schedule = self
            .clauses
            .iter()
            .enumerate()
            .filter_map(|(reference, clause)| {
                (!clause.deleted && !clause.learned && clause.len() >= 3)
                    .then_some(ClauseRef::long(reference))
            })
            .collect::<Vec<_>>();
        schedule
            .sort_unstable_by_key(|&reference| (self.clauses[reference.index()].len(), reference));
        schedule.truncate(Self::VIVIFICATION_SCHEDULE_CAP);
        schedule
    }

    fn vivify_original_clauses(&mut self) -> bool {
        debug_assert_eq!(self.decision_level(), 0);
        debug_assert_eq!(self.propagation_head, self.trail.len());

        let budget = self.vivification_budget();
        let started_at = self.stats.vivification_propagations;
        let schedule = self.vivification_schedule();

        for clause in schedule {
            if self
                .stats
                .vivification_propagations
                .saturating_sub(started_at)
                >= budget
            {
                break;
            }
            if self.clauses[clause.index()].deleted {
                continue;
            }

            self.stats.vivification_checks = self.stats.vivification_checks.saturating_add(1);
            let original_length = self.clauses[clause.index()].len();
            let Some(strengthened) =
                self.vivify_clause(clause, started_at, budget, original_length)
            else {
                continue;
            };
            debug_assert!(strengthened.len() < original_length);
            if !self.install_vivified_clause(clause, strengthened, original_length) {
                return false;
            }
        }
        true
    }

    fn vivify_clause(
        &mut self,
        clause: ClauseRef,
        started_at: u64,
        budget: u64,
        original_length: usize,
    ) -> Option<Vec<Lit>> {
        let mut candidate = Vec::with_capacity(original_length);
        for &literal in &self.clause_arena[self.clauses[clause.index()].range()] {
            match self.literal_value(literal) {
                TRUE => return None,
                FALSE => {}
                UNASSIGNED => candidate.push(literal),
                _ => unreachable!("assignments only contain -1, 0, or 1"),
            }
        }
        debug_assert!(!candidate.is_empty());

        let mut kept = Vec::with_capacity(candidate.len());
        for literal in candidate {
            if self
                .stats
                .vivification_propagations
                .saturating_sub(started_at)
                >= budget
            {
                self.cancel_until_internal::<false>(0);
                return None;
            }

            match self.literal_value(literal) {
                TRUE => {
                    // The kept prefix implies this literal, so the clause
                    // truncated after it is a RUP consequence.
                    kept.push(literal);
                    self.cancel_until_internal::<false>(0);
                    return (kept.len() < original_length).then_some(kept);
                }
                // Propagation of the kept prefix falsified this literal, so
                // dropping it is a self-subsuming RUP strengthening.
                FALSE => continue,
                UNASSIGNED => {}
                _ => unreachable!("assignments only contain -1, 0, or 1"),
            }

            kept.push(literal);
            self.trail_limits.push(self.trail.len());
            let enqueued = self.enqueue_internal::<false>(!literal, None);
            debug_assert!(enqueued, "vivification literal must be unassigned");
            if self.propagate_vivification::<false>(Some(clause)).is_some() {
                self.cancel_until_internal::<false>(0);
                return (kept.len() < original_length).then_some(kept);
            }
        }

        self.cancel_until_internal::<false>(0);
        (kept.len() < original_length).then_some(kept)
    }

    fn install_vivified_clause(
        &mut self,
        original: ClauseRef,
        strengthened: Vec<Lit>,
        original_length: usize,
    ) -> bool {
        debug_assert!(!strengthened.is_empty());
        debug_assert!(strengthened.len() < original_length);

        self.proof.add_clause(&strengthened);
        self.mark_clause_deleted(original);
        self.stats.vivified_clauses = self.stats.vivified_clauses.saturating_add(1);
        self.stats.vivified_literals = self.stats.vivified_literals.saturating_add(
            u64::try_from(original_length - strengthened.len()).unwrap_or(u64::MAX),
        );

        if strengthened.len() == 1 {
            self.stats.vivified_units = self.stats.vivified_units.saturating_add(1);
            return self.enqueue(strengthened[0], None)
                && self.propagate_vivification::<true>(None).is_none();
        }

        let replacement = self.allocate_clause(strengthened, 0, false);
        self.attach_clause(replacement);
        true
    }

    fn subsumption_schedule(
        &self,
        long_clause_limit: usize,
        binary_clause_limit: usize,
    ) -> Vec<ClauseRef> {
        let mut schedule = (0..long_clause_limit)
            .map(ClauseRef::long)
            .chain((0..binary_clause_limit).map(ClauseRef::binary))
            .filter(|&reference| {
                !self.clause_deleted(reference)
                    && !self.clause_learned(reference)
                    && (2..=Self::SUBSUMPTION_SUBSUMER_MAX_LENGTH)
                        .contains(&self.clause_len(reference))
            })
            .collect::<Vec<_>>();
        schedule.sort_unstable_by_key(|&reference| (self.clause_len(reference), reference));
        schedule.truncate(Self::SUBSUMPTION_SCHEDULE_CAP);
        schedule
    }

    fn subsumption_literal_touch_budget(
        &self,
        long_clause_limit: usize,
        binary_clause_limit: usize,
    ) -> u64 {
        let active_original_literals = (0..long_clause_limit)
            .map(ClauseRef::long)
            .chain((0..binary_clause_limit).map(ClauseRef::binary))
            .filter_map(|reference| {
                (!self.clause_deleted(reference) && !self.clause_learned(reference))
                    .then_some(self.clause_len(reference))
            })
            .fold(0_u64, |total, length| {
                total.saturating_add(u64::try_from(length).unwrap_or(u64::MAX))
            });
        Self::bounded_subsumption_literal_touch_budget(active_original_literals)
    }

    fn bounded_subsumption_literal_touch_budget(active_original_literals: u64) -> u64 {
        active_original_literals.min(Self::SUBSUMPTION_LITERAL_TOUCH_CAP)
    }

    fn subsume_original_clauses(&mut self) -> bool {
        debug_assert_eq!(self.decision_level(), 0);
        debug_assert_eq!(self.propagation_head, self.trail.len());

        let long_clause_limit = self.clauses.len();
        let binary_clause_limit = self.binary_literals.len();
        let schedule = self.subsumption_schedule(long_clause_limit, binary_clause_limit);
        if schedule.is_empty() {
            return true;
        }
        let budget = self.subsumption_literal_touch_budget(long_clause_limit, binary_clause_limit);

        let mut occurrence_slot = vec![NO_POSITION; self.watches.len()];
        let mut occurrences = Vec::<Vec<ClauseRef>>::new();
        for &clause in &schedule {
            for &literal in self.clause_literals(clause) {
                let slot = &mut occurrence_slot[literal.index()];
                if *slot == NO_POSITION {
                    *slot = occurrences.len();
                    occurrences.push(Vec::new());
                }
            }
        }

        for reference in (0..long_clause_limit)
            .map(ClauseRef::long)
            .chain((0..binary_clause_limit).map(ClauseRef::binary))
        {
            if self.clause_deleted(reference)
                || self.clause_learned(reference)
                || self.clause_len(reference) > Self::SUBSUMPTION_TARGET_MAX_LENGTH
            {
                continue;
            }
            for index in 0..self.clause_len(reference) {
                let literal = self.clause_literal(reference, index);
                let slot = occurrence_slot[literal.index()];
                if slot != NO_POSITION {
                    occurrences[slot].push(reference);
                    self.stats.subsumption_occurrences =
                        self.stats.subsumption_occurrences.saturating_add(1);
                }
            }
        }

        let mut target_seen = vec![0_u32; long_clause_limit + binary_clause_limit];
        let mut target_epoch = 0_u32;
        let mut literal_marks = vec![false; self.watches.len()];
        let mut exhausted = false;

        for subsumer in schedule {
            if exhausted {
                break;
            }
            if self.clause_deleted(subsumer) {
                continue;
            }

            target_epoch = target_epoch.wrapping_add(1);
            if target_epoch == 0 {
                target_seen.fill(0);
                target_epoch = 1;
            }

            let subsumer_literals = self.clause_literals(subsumer).to_vec();
            let mut occurrence_order = subsumer_literals.clone();
            occurrence_order.sort_unstable_by_key(|literal| {
                occurrences[occurrence_slot[literal.index()]].len()
            });

            'occurrences: for literal in occurrence_order {
                let slot = occurrence_slot[literal.index()];
                for &target in &occurrences[slot] {
                    if self.stats.subsumption_literal_touches >= budget {
                        exhausted = true;
                        break 'occurrences;
                    }
                    let target_slot = if target.is_binary() {
                        long_clause_limit + target.index()
                    } else {
                        target.index()
                    };
                    if target == subsumer || target_seen[target_slot] == target_epoch {
                        continue;
                    }
                    target_seen[target_slot] = target_epoch;

                    if self.clause_deleted(target)
                        || self.clause_learned(target)
                        || self.clause_len(target) < subsumer_literals.len()
                    {
                        continue;
                    }

                    let target_literals = self.clause_literals(target).to_vec();
                    let touches = u64::try_from(
                        subsumer_literals
                            .len()
                            .saturating_add(target_literals.len()),
                    )
                    .unwrap_or(u64::MAX);
                    self.stats.subsumption_literal_touches = self
                        .stats
                        .subsumption_literal_touches
                        .saturating_add(touches);
                    self.stats.subsumption_checks = self.stats.subsumption_checks.saturating_add(1);

                    for &target_literal in &target_literals {
                        literal_marks[target_literal.index()] = true;
                    }
                    let mut missing = None;
                    let mut multiple_missing = false;
                    for &candidate_literal in &subsumer_literals {
                        if literal_marks[candidate_literal.index()] {
                            continue;
                        }
                        if missing.replace(candidate_literal).is_some() {
                            multiple_missing = true;
                            break;
                        }
                    }
                    let self_subsuming_pivot = (!multiple_missing)
                        .then_some(missing)
                        .flatten()
                        .filter(|&pivot| literal_marks[(!pivot).index()]);
                    for &target_literal in &target_literals {
                        literal_marks[target_literal.index()] = false;
                    }

                    if !multiple_missing && missing.is_none() {
                        self.mark_clause_deleted(target);
                        self.stats.subsumed_clauses = self.stats.subsumed_clauses.saturating_add(1);
                    } else if let Some(pivot) = self_subsuming_pivot {
                        let complement = !pivot;
                        let strengthened = target_literals
                            .into_iter()
                            .filter(|&target_literal| target_literal != complement)
                            .collect::<Vec<_>>();
                        if !self.install_self_subsumed_clause(target, strengthened) {
                            return false;
                        }
                    }
                }
            }
        }
        true
    }

    fn install_self_subsumed_clause(
        &mut self,
        original: ClauseRef,
        strengthened: Vec<Lit>,
    ) -> bool {
        debug_assert!(!strengthened.is_empty());
        debug_assert_eq!(strengthened.len() + 1, self.clause_len(original));

        self.proof.add_clause(&strengthened);
        self.mark_clause_deleted(original);
        self.stats.self_subsumed_clauses = self.stats.self_subsumed_clauses.saturating_add(1);
        self.stats.self_subsumed_literals = self.stats.self_subsumed_literals.saturating_add(1);

        if strengthened.len() == 1 {
            self.stats.self_subsumed_units = self.stats.self_subsumed_units.saturating_add(1);
            return self.enqueue(strengthened[0], None) && self.propagate().is_none();
        }

        let replacement = self.allocate_clause(strengthened, 0, false);
        self.attach_clause(replacement);
        true
    }

    fn factorization_density_eligible(&mut self) -> bool {
        self.stats.factorization_density_checks =
            self.stats.factorization_density_checks.saturating_add(1);
        let variables = u64::try_from(self.external_variable_count).unwrap_or(u64::MAX);
        let threshold = variables.saturating_mul(Self::FACTORIZATION_DENSITY_NUMERATOR);
        let eligible = variables > 0 && self.stats.factorization_input_short_clauses >= threshold;
        if !eligible {
            self.stats.factorization_density_skips =
                self.stats.factorization_density_skips.saturating_add(1);
        }
        eligible
    }

    fn factor_hash(mut value: u64) -> u64 {
        value ^= value >> 30;
        value = value.wrapping_mul(0xbf58_476d_1ce4_e5b9);
        value ^= value >> 27;
        value = value.wrapping_mul(0x94d0_49bb_1331_11eb);
        value ^ (value >> 31)
    }

    fn factor_quotient_hash(literals: &[Lit], removed: usize, salt: u64) -> u64 {
        let mut hash = Self::factor_hash(
            salt ^ u64::try_from(literals.len().saturating_sub(1)).unwrap_or(u64::MAX),
        );
        for (index, literal) in literals.iter().enumerate() {
            if index == removed {
                continue;
            }
            hash = Self::factor_hash(hash ^ u64::from(literal.raw()).wrapping_add(salt));
        }
        hash
    }

    fn factor_snapshot(&self) -> FactorSnapshot {
        let references = self.clause_references().collect::<Vec<_>>();
        let mut clauses = Vec::new();
        let mut literal_touches = 0_u64;

        for reference in references {
            if self.clause_deleted(reference) || self.clause_learned(reference) {
                continue;
            }
            let mut satisfied = false;
            let mut literals = Vec::with_capacity(self.clause_len(reference));
            for &literal in self.clause_literals(reference) {
                match self.literal_value(literal) {
                    TRUE => {
                        satisfied = true;
                        break;
                    }
                    FALSE => {}
                    UNASSIGNED => literals.push(literal),
                    _ => unreachable!("assignments only contain -1, 0, or 1"),
                }
            }
            if satisfied
                || literals.len() < 2
                || literals.len() > Self::FACTORIZATION_MAX_CLAUSE_LENGTH
            {
                continue;
            }
            literals.sort_unstable_by_key(|literal| literal.index());
            literals.dedup();
            if literals.len() < 2 {
                continue;
            }
            literal_touches =
                literal_touches.saturating_add(u64::try_from(literals.len()).unwrap_or(u64::MAX));
            clauses.push(FactorCandidate {
                reference,
                literals,
            });
        }

        let mut occurrences = vec![Vec::new(); self.watches.len()];
        let mut summaries = vec![FactorNeighborhoodSummary::default(); self.watches.len()];
        for (candidate_index, candidate) in clauses.iter().enumerate() {
            for (removed, &factor) in candidate.literals.iter().enumerate() {
                occurrences[factor.index()].push(candidate_index);
                let hash1 =
                    Self::factor_quotient_hash(&candidate.literals, removed, 0x243f_6a88_85a3_08d3);
                let hash2 =
                    Self::factor_quotient_hash(&candidate.literals, removed, 0x1319_8a2e_0370_7344);
                let summary = &mut summaries[factor.index()];
                summary.count = summary.count.saturating_add(1);
                summary.sum1 = summary.sum1.wrapping_add(hash1);
                summary.sum2 = summary.sum2.wrapping_add(hash2);
                summary.xor ^= hash1.rotate_left((hash2 & 63) as u32);
            }
        }

        FactorSnapshot {
            clauses,
            occurrences,
            summaries,
            literal_touches,
        }
    }

    fn factor_neighborhood(
        snapshot: &FactorSnapshot,
        factor: Lit,
    ) -> (Vec<Vec<Lit>>, Vec<ClauseRef>, u64) {
        let mut entries = Vec::with_capacity(snapshot.occurrences[factor.index()].len());
        let mut touches = 0_u64;
        for &candidate_index in &snapshot.occurrences[factor.index()] {
            let candidate = &snapshot.clauses[candidate_index];
            touches =
                touches.saturating_add(u64::try_from(candidate.literals.len()).unwrap_or(u64::MAX));
            let quotient = candidate
                .literals
                .iter()
                .copied()
                .filter(|&literal| literal != factor)
                .collect::<Vec<_>>();
            entries.push((quotient, candidate.reference));
        }
        entries.sort_unstable_by(|left, right| {
            left.0.cmp(&right.0).then_with(|| left.1.cmp(&right.1))
        });

        let mut quotients = Vec::with_capacity(entries.len());
        let mut references = Vec::with_capacity(entries.len());
        for (quotient, reference) in entries {
            if quotients.last() == Some(&quotient) {
                continue;
            }
            quotients.push(quotient);
            references.push(reference);
        }
        (quotients, references, touches)
    }

    fn exact_factor_plans(
        &mut self,
        snapshot: &FactorSnapshot,
        budget: u64,
    ) -> Option<Vec<FactorPlan>> {
        let mut summary_groups = BTreeMap::<FactorNeighborhoodSummary, Vec<Lit>>::new();
        for (literal_index, &summary) in snapshot.summaries.iter().enumerate() {
            if summary.count < 2 {
                continue;
            }
            let literal = Lit::from_raw(
                u32::try_from(literal_index).expect("literal index must fit packed literal"),
            );
            summary_groups.entry(summary).or_default().push(literal);
        }

        let mut plans = Vec::new();
        for factors in summary_groups.into_values() {
            if factors.len() < 2 {
                continue;
            }
            let mut exact = BTreeMap::<Vec<Vec<Lit>>, Vec<(Lit, Vec<ClauseRef>)>>::new();
            for factor in factors {
                let (quotients, references, touches) = Self::factor_neighborhood(snapshot, factor);
                if self
                    .stats
                    .factorization_literal_touches
                    .saturating_add(touches)
                    > budget
                {
                    return None;
                }
                self.stats.factorization_literal_touches = self
                    .stats
                    .factorization_literal_touches
                    .saturating_add(touches);
                if quotients.len() < 2 {
                    continue;
                }
                exact
                    .entry(quotients)
                    .or_default()
                    .push((factor, references));
            }

            for (quotients, mut members) in exact {
                if members.len() < 2 {
                    continue;
                }
                members.sort_unstable_by_key(|member| member.0.index());
                let factors = members.iter().map(|member| member.0).collect::<Vec<_>>();
                if quotients
                    .iter()
                    .any(|quotient| quotient.iter().any(|literal| factors.contains(literal)))
                {
                    continue;
                }

                let before = factors.len().saturating_mul(quotients.len());
                let after = factors.len().saturating_add(quotients.len());
                let reduction = before.saturating_sub(after);
                if reduction == 0 {
                    continue;
                }
                if self.config.macro_bounded_variable_addition && before < after.saturating_mul(2) {
                    self.stats.factorization_macro_rejections =
                        self.stats.factorization_macro_rejections.saturating_add(1);
                    continue;
                }
                let matrix = members
                    .into_iter()
                    .flat_map(|(_, references)| references)
                    .collect::<Vec<_>>();
                if matrix.len() != before {
                    continue;
                }
                let mut unique = matrix.clone();
                unique.sort_unstable();
                unique.dedup();
                if unique.len() != matrix.len() {
                    continue;
                }
                plans.push(FactorPlan {
                    factors,
                    quotients,
                    matrix,
                    reduction,
                });
            }
        }

        plans.sort_unstable_by(|left, right| {
            right
                .reduction
                .cmp(&left.reduction)
                .then_with(|| left.factors.cmp(&right.factors))
                .then_with(|| left.quotients.cmp(&right.quotients))
        });
        Some(plans)
    }

    fn install_factored_clause(&mut self, pivot: Lit, mut literals: Vec<Lit>) {
        debug_assert!(literals.len() >= 2);
        debug_assert!(literals.contains(&pivot));
        literals.sort_unstable_by_key(|literal| literal.index());
        let mut proof_clause = Vec::with_capacity(literals.len());
        proof_clause.push(pivot);
        proof_clause.extend(literals.iter().copied().filter(|&literal| literal != pivot));
        self.proof.add_clause(&proof_clause);
        let clause = self.allocate_clause(literals, 0, false);
        self.attach_clause(clause);
    }

    fn apply_factor_plan(&mut self, plan: FactorPlan) -> bool {
        if plan
            .matrix
            .iter()
            .any(|&reference| self.clause_deleted(reference) || self.clause_learned(reference))
        {
            return false;
        }

        let variable_index = self.assignments.len();
        self.grow_variables(variable_index.saturating_add(1));
        let variable =
            Var::new(u32::try_from(variable_index).expect("extension variable must fit u32"));
        let fresh = Lit::positive(variable);

        for &factor in &plan.factors {
            self.install_factored_clause(fresh, vec![fresh, factor]);
        }
        for quotient in &plan.quotients {
            let mut clause = Vec::with_capacity(quotient.len() + 1);
            clause.push(!fresh);
            clause.extend_from_slice(quotient);
            self.install_factored_clause(!fresh, clause);
        }
        for &reference in &plan.matrix {
            self.mark_clause_deleted(reference);
        }

        let removed = u64::try_from(plan.matrix.len()).unwrap_or(u64::MAX);
        let added = u64::try_from(plan.factors.len().saturating_add(plan.quotients.len()))
            .unwrap_or(u64::MAX);
        self.stats.factored_variables = self.stats.factored_variables.saturating_add(1);
        self.stats.factorization_clauses_removed = self
            .stats
            .factorization_clauses_removed
            .saturating_add(removed);
        self.stats.factorization_clauses_added =
            self.stats.factorization_clauses_added.saturating_add(added);
        self.stats.factorization_clause_reduction = self
            .stats
            .factorization_clause_reduction
            .saturating_add(removed.saturating_sub(added));
        self.stats.factorization_peak_factors = self
            .stats
            .factorization_peak_factors
            .max(u64::try_from(plan.factors.len()).unwrap_or(u64::MAX));
        self.stats.factorization_peak_quotients = self
            .stats
            .factorization_peak_quotients
            .max(u64::try_from(plan.quotients.len()).unwrap_or(u64::MAX));
        true
    }

    fn factor_exact_neighborhoods(&mut self) -> bool {
        debug_assert_eq!(self.decision_level(), 0);
        debug_assert_eq!(self.propagation_head, self.trail.len());

        let mut snapshot = self.factor_snapshot();
        let budget = snapshot
            .literal_touches
            .saturating_mul(16)
            .clamp(1_000_000, Self::FACTORIZATION_LITERAL_TOUCH_CAP);

        for round in 0..Self::FACTORIZATION_MAX_ROUNDS {
            if round > 0 {
                snapshot = self.factor_snapshot();
            }
            if snapshot.clauses.is_empty()
                || self
                    .stats
                    .factorization_literal_touches
                    .saturating_add(snapshot.literal_touches)
                    > budget
            {
                break;
            }
            self.stats.factorization_rounds = self.stats.factorization_rounds.saturating_add(1);
            self.stats.factorization_candidate_clauses = self
                .stats
                .factorization_candidate_clauses
                .saturating_add(u64::try_from(snapshot.clauses.len()).unwrap_or(u64::MAX));
            self.stats.factorization_literal_touches = self
                .stats
                .factorization_literal_touches
                .saturating_add(snapshot.literal_touches);

            let Some(plans) = self.exact_factor_plans(&snapshot, budget) else {
                break;
            };
            let mut applied = 0_usize;
            for plan in plans {
                if self.apply_factor_plan(plan) {
                    applied += 1;
                }
            }
            if applied == 0 {
                break;
            }
        }
        true
    }

    fn elimination_literal_touch_budget(&self) -> u64 {
        self.clause_references()
            .filter(|&clause| !self.clause_deleted(clause) && !self.clause_learned(clause))
            .fold(0_u64, |total, clause| {
                total.saturating_add(u64::try_from(self.clause_len(clause)).unwrap_or(u64::MAX))
            })
            .min(Self::ELIMINATION_LITERAL_TOUCH_CAP)
    }

    fn active_elimination_occurrences(
        &self,
        occurrences: &[Vec<ClauseRef>],
        literal: Lit,
    ) -> Vec<ClauseRef> {
        occurrences[literal.index()]
            .iter()
            .copied()
            .filter(|&reference| !self.clause_deleted(reference) && !self.clause_learned(reference))
            .collect()
    }

    fn elimination_resolvent(
        &self,
        positive: ClauseRef,
        negative: ClauseRef,
        variable: Var,
    ) -> Option<Vec<Lit>> {
        let mut resolvent =
            Vec::with_capacity(self.clause_len(positive) + self.clause_len(negative) - 2);
        for reference in [positive, negative] {
            for &literal in self.clause_literals(reference) {
                if literal.var() == variable {
                    continue;
                }
                match self.literal_value(literal) {
                    TRUE => return None,
                    FALSE => {}
                    UNASSIGNED => resolvent.push(literal),
                    _ => unreachable!("assignments only contain -1, 0, or 1"),
                }
            }
        }

        resolvent.sort_unstable_by_key(|literal| literal.index());
        let mut write = 0;
        for read in 0..resolvent.len() {
            if write > 0 {
                let previous = resolvent[write - 1];
                let current = resolvent[read];
                if previous == current {
                    continue;
                }
                if previous.var() == current.var() {
                    return None;
                }
            }
            resolvent[write] = resolvent[read];
            write += 1;
        }
        resolvent.truncate(write);
        Some(resolvent)
    }

    fn eliminate_variables(&mut self) -> bool {
        debug_assert_eq!(self.decision_level(), 0);
        debug_assert_eq!(self.propagation_head, self.trail.len());

        let mut occurrences = vec![Vec::<ClauseRef>::new(); self.watches.len()];
        for reference in self.clause_references() {
            if self.clause_deleted(reference) || self.clause_learned(reference) {
                continue;
            }
            for &literal in self.clause_literals(reference) {
                occurrences[literal.index()].push(reference);
            }
        }

        let mut schedule = (0..self.assignments.len())
            .filter(|&index| self.assignments[index] == UNASSIGNED)
            .filter_map(|index| {
                let occurrences = occurrences[2 * index].len() + occurrences[2 * index + 1].len();
                (occurrences > 0).then_some((occurrences, index))
            })
            .collect::<Vec<_>>();
        schedule.sort_unstable();

        let budget = self.elimination_literal_touch_budget();
        for (_, index) in schedule {
            if self.stats.elimination_literal_touches >= budget {
                break;
            }
            if self.assignments[index] != UNASSIGNED {
                continue;
            }
            let variable =
                Var::new(u32::try_from(index).expect("variable count checked when reserved"));
            let positive_literal = Lit::positive(variable);
            let negative_literal = !positive_literal;
            let positive = self.active_elimination_occurrences(&occurrences, positive_literal);
            let negative = self.active_elimination_occurrences(&occurrences, negative_literal);
            let removed_count = positive.len() + negative.len();
            if removed_count == 0 {
                continue;
            }
            if !positive.is_empty()
                && !negative.is_empty()
                && removed_count > Self::ELIMINATION_OCCURRENCE_LIMIT
            {
                self.stats.elimination_rejections =
                    self.stats.elimination_rejections.saturating_add(1);
                continue;
            }

            let mut resolvents = Vec::<Vec<Lit>>::new();
            let mut rejected = false;
            let mut exhausted = false;
            'pairs: for &positive_clause in &positive {
                for &negative_clause in &negative {
                    let touches = u64::try_from(
                        self.clause_len(positive_clause)
                            .saturating_add(self.clause_len(negative_clause)),
                    )
                    .unwrap_or(u64::MAX);
                    if self
                        .stats
                        .elimination_literal_touches
                        .saturating_add(touches)
                        > budget
                    {
                        exhausted = true;
                        break 'pairs;
                    }
                    self.stats.elimination_literal_touches = self
                        .stats
                        .elimination_literal_touches
                        .saturating_add(touches);
                    self.stats.elimination_pairs = self.stats.elimination_pairs.saturating_add(1);

                    let Some(resolvent) =
                        self.elimination_resolvent(positive_clause, negative_clause, variable)
                    else {
                        continue;
                    };
                    if resolvent.len() > Self::ELIMINATION_RESOLVENT_LENGTH_LIMIT {
                        rejected = true;
                        break 'pairs;
                    }
                    resolvents.push(resolvent);
                    if resolvents.len() > removed_count {
                        rejected = true;
                        break 'pairs;
                    }
                }
            }
            if exhausted {
                self.stats.elimination_rejections =
                    self.stats.elimination_rejections.saturating_add(1);
                break;
            }
            if rejected {
                self.stats.elimination_rejections =
                    self.stats.elimination_rejections.saturating_add(1);
                continue;
            }

            let removed = positive
                .iter()
                .chain(&negative)
                .copied()
                .collect::<Vec<_>>();
            let extension_clauses = removed
                .iter()
                .map(|&reference| self.clause_literals(reference).to_vec())
                .collect::<Vec<_>>();
            let extension_literals = extension_clauses
                .iter()
                .fold(0_usize, |total, clause| total.saturating_add(clause.len()));

            let mut units = Vec::new();
            let mut empty = false;
            for resolvent in resolvents {
                self.proof.add_clause(&resolvent);
                self.stats.elimination_resolvents =
                    self.stats.elimination_resolvents.saturating_add(1);
                match resolvent.len() {
                    0 => empty = true,
                    1 => {
                        units.push(resolvent[0]);
                        self.stats.elimination_units =
                            self.stats.elimination_units.saturating_add(1);
                    }
                    _ => {
                        let clause = self.allocate_clause(resolvent, 0, false);
                        self.attach_clause(clause);
                        for &literal in self.clause_literals(clause) {
                            occurrences[literal.index()].push(clause);
                        }
                    }
                }
            }

            for &reference in &removed {
                self.mark_clause_deleted(reference);
            }
            self.stats.elimination_removed_clauses = self
                .stats
                .elimination_removed_clauses
                .saturating_add(u64::try_from(removed.len()).unwrap_or(u64::MAX));
            self.stats.elimination_extension_clauses = self
                .stats
                .elimination_extension_clauses
                .saturating_add(u64::try_from(extension_clauses.len()).unwrap_or(u64::MAX));
            self.stats.elimination_extension_literals = self
                .stats
                .elimination_extension_literals
                .saturating_add(u64::try_from(extension_literals).unwrap_or(u64::MAX));
            self.elimination_records.push(EliminationRecord {
                variable,
                clauses: extension_clauses,
            });
            self.assignments[index] = if self.phase[index] { TRUE } else { FALSE };
            self.levels[index] = 0;
            self.reasons[index] = None;
            self.stats.eliminated_variables = self.stats.eliminated_variables.saturating_add(1);

            if empty {
                return false;
            }
            for unit in units {
                if !self.enqueue(unit, None) {
                    return false;
                }
            }
            if self.propagate().is_some() {
                return false;
            }
        }
        true
    }

    fn extend_model(&self, values: &mut [bool]) {
        for record in self.elimination_records.iter().rev() {
            let mut required = None;
            for clause in &record.clauses {
                let mut pivot = None;
                let mut satisfied_without_pivot = false;
                for &literal in clause {
                    if literal.var() == record.variable {
                        pivot = Some(literal);
                    } else if values[literal.var().index()] == literal.is_positive() {
                        satisfied_without_pivot = true;
                    }
                }
                if satisfied_without_pivot {
                    continue;
                }
                let pivot = pivot.expect("elimination record must contain its pivot");
                let value = pivot.is_positive();
                if let Some(previous) = required {
                    assert_eq!(
                        previous, value,
                        "elimination resolvents must prevent opposite model requirements"
                    );
                } else {
                    required = Some(value);
                }
            }
            if let Some(value) = required {
                values[record.variable.index()] = value;
            }
        }
    }

    fn analyze(&mut self, conflict: ClauseRef) -> (Vec<Lit>, u32, u32, Option<DerivationAncestry>) {
        let current_level = self.decision_level();
        let mut learned = vec![Lit::positive(Var::new(0))];
        let mut touched = Vec::new();
        let focused = self.uses_vmtf_branching();
        let lrb = self.maintains_lrb_scores();
        let transfer = self.uses_transfer_branching();
        let chb = self.uses_chb_branching();
        let mut focused_bumped = Vec::new();
        let mut path_count = 0_u32;
        let mut trail_index = self.trail.len();
        let mut resolved_literal = None;
        let mut clause = conflict;
        let mut derivation_ancestry = self
            .config
            .nonregular_clause_retention
            .then(|| self.clause_derivation_ancestry(conflict));

        loop {
            self.bump_clause_activity(clause);
            let literal_count = self.clause_len(clause);
            for index in 0..literal_count {
                let literal = self.clause_literal(clause, index);
                if resolved_literal.is_some_and(|resolved: Lit| resolved.var() == literal.var()) {
                    continue;
                }
                let variable = literal.var();
                let variable_index = variable.index();
                if !self.seen[variable_index] && self.levels[variable_index] > 0 {
                    self.seen[variable_index] = true;
                    touched.push(variable);
                    if focused {
                        focused_bumped.push(variable);
                        if self.config.search_strategy == SearchStrategy::ProbeEvsids {
                            self.bump_variable_activity(variable);
                        }
                    } else if (!lrb || transfer) && !chb {
                        self.bump_variable_activity(variable);
                    }
                    if self.levels[variable_index] == current_level {
                        path_count += 1;
                    } else {
                        learned.push(literal);
                    }
                }
            }

            let pivot = loop {
                trail_index -= 1;
                let candidate = self.trail[trail_index];
                if self.seen[candidate.var().index()] {
                    break candidate;
                }
            };
            self.seen[pivot.var().index()] = false;
            path_count -= 1;
            if path_count == 0 {
                learned[0] = !pivot;
                break;
            }
            resolved_literal = Some(pivot);
            let reason = self.reasons[pivot.var().index()]
                .expect("a non-UIP current-level literal must have a reason");
            if let Some(ancestry) = &mut derivation_ancestry {
                let parent = self.clause_derivation_ancestry(reason);
                self.stats.regularity_resolution_pivots =
                    self.stats.regularity_resolution_pivots.saturating_add(1);
                if ancestry.resolve_with(pivot.var(), parent) {
                    self.stats.regularity_sampled_repeat_witnesses = self
                        .stats
                        .regularity_sampled_repeat_witnesses
                        .saturating_add(1);
                }
            }
            clause = reason;
        }

        if lrb {
            self.lrb_record_participation(&touched);
        }
        if chb {
            self.chb_record_conflict_history(&touched);
        }
        let unminimized_length = learned.len();
        if self.config.minimize_learned_clauses && learned.len() > 1 {
            self.minimize_learned_clause(&mut learned, &mut touched);
        }
        let recursively_minimized_length = learned.len();
        let mut lbd = self.literal_block_distance(&learned);
        if self.config.binary_resolution_minimization
            && Self::eligible_for_binary_minimization(learned.len(), lbd)
        {
            self.binary_resolution_minimize(&mut learned);
            if learned.len() != recursively_minimized_length {
                lbd = self.literal_block_distance(&learned);
            }
        }
        if lrb {
            self.lrb_record_reason_side(&learned);
            self.lrb_decrease_step_size();
        }
        self.stats.learned_literals = self
            .stats
            .learned_literals
            .saturating_add(u64::try_from(learned.len()).unwrap_or(u64::MAX));
        self.stats.minimized_literals = self.stats.minimized_literals.saturating_add(
            u64::try_from(unminimized_length - recursively_minimized_length).unwrap_or(u64::MAX),
        );

        for variable in touched {
            self.seen[variable.index()] = false;
        }

        let backtrack_level = if learned.len() == 1 {
            0
        } else {
            let mut highest = 1;
            for index in 2..learned.len() {
                if self.levels[learned[index].var().index()]
                    > self.levels[learned[highest].var().index()]
                {
                    highest = index;
                }
            }
            learned.swap(1, highest);
            self.levels[learned[1].var().index()]
        };
        if focused {
            self.vmtf
                .bump_analyzed(&mut focused_bumped, &self.assignments);
        }
        (learned, backtrack_level, lbd, derivation_ancestry)
    }

    fn next_lrb_mark_epoch(&mut self) -> u32 {
        self.lrb_mark_epoch = self.lrb_mark_epoch.wrapping_add(1);
        if self.lrb_mark_epoch == 0 {
            self.lrb_marks.fill(0);
            self.lrb_mark_epoch = 1;
        }
        self.lrb_mark_epoch
    }

    fn lrb_record_participation(&mut self, variables: &[Var]) {
        debug_assert!(self.maintains_lrb_scores());
        let epoch = self.next_lrb_mark_epoch();
        for &variable in variables {
            let index = variable.index();
            if self.lrb_marks[index] == epoch {
                continue;
            }
            self.lrb_marks[index] = epoch;
            self.lrb_participated[index] = self.lrb_participated[index].saturating_add(1);
        }
    }

    fn lrb_record_reason_side(&mut self, learned: &[Lit]) {
        debug_assert!(self.maintains_lrb_scores());
        let epoch = self.next_lrb_mark_epoch();
        for &literal in learned {
            self.lrb_marks[literal.var().index()] = epoch;
        }
        for &literal in learned {
            let Some(reason) = self.reasons[literal.var().index()] else {
                continue;
            };
            let literal_count = self.clause_len(reason);
            for index in 0..literal_count {
                let variable = self.clause_literal(reason, index).var();
                let variable_index = variable.index();
                if self.lrb_marks[variable_index] == epoch {
                    continue;
                }
                self.lrb_marks[variable_index] = epoch;
                self.lrb_reasoned[variable_index] =
                    self.lrb_reasoned[variable_index].saturating_add(1);
                self.stats.lrb_reason_side_rewards =
                    self.stats.lrb_reason_side_rewards.saturating_add(1);
            }
        }
    }

    fn lrb_decrease_step_size(&mut self) {
        debug_assert!(self.maintains_lrb_scores());
        self.lrb_step_size =
            (self.lrb_step_size - Self::LRB_STEP_SIZE_DECREMENT).max(Self::LRB_MINIMUM_STEP_SIZE);
    }

    fn chb_record_conflict_history(&mut self, variables: &[Var]) {
        debug_assert!(self.uses_chb_branching());
        for &variable in variables {
            self.chb_last_conflict[variable.index()] = self.stats.conflicts;
            self.stats.chb_conflict_history_updates =
                self.stats.chb_conflict_history_updates.saturating_add(1);
        }
    }

    fn minimize_learned_clause(&mut self, learned: &mut Vec<Lit>, touched: &mut Vec<Var>) {
        let mut abstract_levels = 0_u32;
        for &literal in &learned[1..] {
            abstract_levels |= abstract_level(self.levels[literal.var().index()]);
        }

        let mut write = 1;
        for read in 1..learned.len() {
            let literal = learned[read];
            let variable = literal.var();
            let redundant = self.reasons[variable.index()].is_some()
                && self.literal_redundant(literal, abstract_levels, touched);
            if !redundant {
                learned[write] = literal;
                write += 1;
            }
        }
        learned.truncate(write);
    }

    fn literal_redundant(
        &mut self,
        literal: Lit,
        abstract_levels: u32,
        touched: &mut Vec<Var>,
    ) -> bool {
        let touched_before = touched.len();
        let mut stack = vec![literal];

        while let Some(candidate) = stack.pop() {
            let variable = candidate.var();
            let reason = self.reasons[variable.index()]
                .expect("recursive minimization only visits propagated variables");

            let literal_count = self.clause_len(reason);
            for index in 0..literal_count {
                let antecedent = self.clause_literal(reason, index);
                let antecedent_variable = antecedent.var();
                if antecedent_variable == variable {
                    continue;
                }
                let variable_index = antecedent_variable.index();
                let level = self.levels[variable_index];
                if level == 0 || self.seen[variable_index] {
                    continue;
                }
                if self.reasons[variable_index].is_some()
                    && abstract_levels & abstract_level(level) != 0
                {
                    self.seen[variable_index] = true;
                    touched.push(antecedent_variable);
                    stack.push(antecedent);
                } else {
                    while touched.len() > touched_before {
                        let added = touched.pop().expect("length checked above");
                        self.seen[added.index()] = false;
                    }
                    return false;
                }
            }
        }
        true
    }

    fn eligible_for_binary_minimization(length: usize, lbd: u32) -> bool {
        (2..=Self::BINARY_MINIMIZATION_MAX_LENGTH).contains(&length)
            && lbd <= Self::BINARY_MINIMIZATION_MAX_LBD
    }

    fn next_binary_minimize_epoch(&mut self) -> u32 {
        self.binary_minimize_epoch = self.binary_minimize_epoch.wrapping_add(1);
        if self.binary_minimize_epoch == 0 {
            self.binary_minimize_marks.fill(0);
            self.binary_minimize_epoch = 1;
        }
        self.binary_minimize_epoch
    }

    fn binary_resolution_minimize(&mut self, learned: &mut Vec<Lit>) {
        debug_assert!((2..=Self::BINARY_MINIMIZATION_MAX_LENGTH).contains(&learned.len()));
        debug_assert_eq!(self.binary_minimize_marks.len(), self.assignments.len());

        self.stats.binary_minimization_clauses =
            self.stats.binary_minimization_clauses.saturating_add(1);
        let epoch = self.next_binary_minimize_epoch();
        for &literal in &learned[1..] {
            self.binary_minimize_marks[literal.var().index()] = epoch;
        }

        let asserting = learned[0];
        for watch in self.watches[asserting.index()].iter().copied() {
            self.stats.binary_minimization_watch_visits = self
                .stats
                .binary_minimization_watch_visits
                .saturating_add(1);
            if !watch.is_binary() || self.clause_deleted(watch.clause()) {
                continue;
            }
            let other = watch.blocker();
            let variable_index = other.var().index();
            if self.binary_minimize_marks[variable_index] == epoch
                && value_of(&self.assignments, other) == TRUE
            {
                self.binary_minimize_marks[variable_index] = 0;
            }
        }

        let before = learned.len();
        let mut write = 1;
        for read in 1..learned.len() {
            let literal = learned[read];
            if self.binary_minimize_marks[literal.var().index()] == epoch {
                learned[write] = literal;
                write += 1;
            }
        }
        learned.truncate(write);
        self.stats.binary_minimized_literals = self
            .stats
            .binary_minimized_literals
            .saturating_add(u64::try_from(before - learned.len()).unwrap_or(u64::MAX));
    }

    fn next_level_mark(&mut self) -> u32 {
        self.level_mark = self.level_mark.wrapping_add(1);
        if self.level_mark == 0 {
            self.level_marks.fill(0);
            self.level_mark = 1;
        }
        let required = self.trail_limits.len().saturating_add(1);
        if self.level_marks.len() < required {
            self.level_marks.resize(required, 0);
        }
        self.level_mark
    }

    fn literal_block_distance(&mut self, clause: &[Lit]) -> u32 {
        let mark = self.next_level_mark();
        let mut count = 0_u32;
        for &literal in clause {
            let level = self.levels[literal.var().index()] as usize;
            if self.level_marks[level] != mark {
                self.level_marks[level] = mark;
                count = count.saturating_add(1);
            }
        }
        count
    }

    fn clause_literal_block_distance(&mut self, clause: ClauseRef) -> u32 {
        let mark = self.next_level_mark();
        let literals = self.clause_literals(clause).to_vec();
        let levels = &self.levels;
        let level_marks = &mut self.level_marks;
        let mut count = 0_u32;
        for literal in literals {
            let level = levels[literal.var().index()] as usize;
            if level_marks[level] != mark {
                level_marks[level] = mark;
                count = count.saturating_add(1);
            }
        }
        count
    }

    fn cancel_until(&mut self, level: u32) {
        self.cancel_until_internal::<true>(level);
    }

    fn cancel_until_internal<const RECORD_BEST_PHASE: bool>(&mut self, level: u32) {
        if self.decision_level() <= level {
            return;
        }
        if RECORD_BEST_PHASE {
            self.record_best_phase();
        }
        let target = self.trail_limits[level as usize];
        for index in (target..self.trail.len()).rev() {
            let variable = self.trail[index].var();
            if self.maintains_lrb_scores() {
                self.lrb_on_unassign(variable);
            }
            self.assignments[variable.index()] = UNASSIGNED;
            self.reasons[variable.index()] = None;
            self.levels[variable.index()] = 0;
            self.order.insert(variable, &self.activity);
            if self.uses_transfer_branching() {
                self.transfer_lrb_order
                    .insert(variable, &self.transfer_lrb_activity);
            }
            self.vmtf.unassign(variable);
        }
        self.trail.truncate(target);
        self.trail_limits.truncate(level as usize);
        self.propagation_head = self.propagation_head.min(target);
    }

    fn lrb_on_unassign(&mut self, variable: Var) {
        debug_assert!(self.maintains_lrb_scores());
        let index = variable.index();
        let interval = self
            .stats
            .conflicts
            .saturating_sub(self.lrb_assigned_at[index]);
        if interval > 0 {
            let reward = self.lrb_participated[index].saturating_add(self.lrb_reasoned[index])
                as f64
                / interval as f64;
            if self.uses_transfer_branching() {
                let old_activity = self.transfer_lrb_activity[index];
                self.transfer_lrb_activity[index] =
                    (1.0 - self.lrb_step_size) * old_activity + self.lrb_step_size * reward;
                self.transfer_lrb_order
                    .update(variable, old_activity, &self.transfer_lrb_activity);
            } else {
                let old_activity = self.activity[index];
                self.activity[index] =
                    (1.0 - self.lrb_step_size) * old_activity + self.lrb_step_size * reward;
                self.order.update(variable, old_activity, &self.activity);
            }
            self.stats.lrb_unassign_updates = self.stats.lrb_unassign_updates.saturating_add(1);
        }
        self.lrb_canceled_at[index] = self.stats.conflicts;
    }

    fn record_best_phase(&mut self) {
        if !self.config.systematic_rephasing || self.trail.len() <= self.best_assigned {
            return;
        }
        self.best_assigned = self.trail.len();
        self.best_phase.clone_from(&self.phase);
        self.stats.best_phase_updates = self.stats.best_phase_updates.saturating_add(1);
    }

    fn pick_branch_literal(&mut self) -> Option<Lit> {
        if self.uses_vmtf_branching() {
            let variable = self.vmtf.pick(&self.assignments)?;
            return Some(Lit::new(variable, self.phase[variable.index()]));
        }
        if self.uses_lrb_branching() {
            loop {
                let variable = self.order.peek_max(&self.assignments, &self.activity)?;
                if self.lrb_decay_stale_score(variable) {
                    continue;
                }
                let selected = self
                    .order
                    .pop_max(&self.activity)
                    .expect("peeked LRB heap root must remain present");
                debug_assert_eq!(selected, variable);
                return Some(Lit::new(variable, self.phase[variable.index()]));
            }
        }
        if self.transfer_uses_lrb_for_decisions() {
            loop {
                let variable = self
                    .transfer_lrb_order
                    .peek_max(&self.assignments, &self.transfer_lrb_activity)?;
                if self.lrb_decay_stale_score(variable) {
                    continue;
                }
                let selected = self
                    .transfer_lrb_order
                    .pop_max(&self.transfer_lrb_activity)
                    .expect("peeked transfer LRB heap root must remain present");
                debug_assert_eq!(selected, variable);
                return Some(Lit::new(variable, self.phase[variable.index()]));
            }
        }
        while let Some(variable) = self.order.pop_max(&self.activity) {
            if self.assignments[variable.index()] == UNASSIGNED {
                return Some(Lit::new(variable, self.phase[variable.index()]));
            }
        }
        None
    }

    fn clause_deleted(&self, clause: ClauseRef) -> bool {
        if clause.is_binary() {
            self.binary_flags[clause.index()] & BINARY_DELETED != 0
        } else {
            self.clauses[clause.index()].deleted
        }
    }

    fn clause_learned(&self, clause: ClauseRef) -> bool {
        if clause.is_binary() {
            self.binary_flags[clause.index()] & BINARY_LEARNED != 0
        } else {
            self.clauses[clause.index()].learned
        }
    }

    fn clause_len(&self, clause: ClauseRef) -> usize {
        if clause.is_binary() {
            2
        } else {
            self.clauses[clause.index()].len()
        }
    }

    fn clause_literals(&self, clause: ClauseRef) -> &[Lit] {
        if clause.is_binary() {
            &self.binary_literals[clause.index()]
        } else {
            &self.clause_arena[self.clauses[clause.index()].range()]
        }
    }

    fn clause_literal(&self, clause: ClauseRef, index: usize) -> Lit {
        self.clause_literals(clause)[index]
    }

    fn long_clause_references(&self) -> impl Iterator<Item = ClauseRef> + '_ {
        (0..self.clauses.len()).map(ClauseRef::long)
    }

    fn binary_clause_references(&self) -> impl Iterator<Item = ClauseRef> + '_ {
        (0..self.binary_literals.len()).map(ClauseRef::binary)
    }

    fn clause_references(&self) -> impl Iterator<Item = ClauseRef> + '_ {
        self.long_clause_references()
            .chain(self.binary_clause_references())
    }

    fn clause_derivation_ancestry(&self, clause: ClauseRef) -> DerivationAncestry {
        debug_assert!(self.config.nonregular_clause_retention);
        if clause.is_binary() {
            DerivationAncestry::from_storage(
                self.regularity_binary_samples[clause.index()],
                self.regularity_binary_states[clause.index()],
            )
        } else {
            DerivationAncestry::from_storage(
                self.regularity_long_samples[clause.index()],
                self.regularity_long_states[clause.index()],
            )
        }
    }

    fn set_clause_derivation_ancestry(&mut self, clause: ClauseRef, ancestry: DerivationAncestry) {
        debug_assert!(self.config.nonregular_clause_retention);
        debug_assert!(self.clause_learned(clause));
        if clause.is_binary() {
            self.regularity_binary_samples[clause.index()] = ancestry.sample;
            self.regularity_binary_states[clause.index()] = ancestry.state;
        } else {
            self.regularity_long_samples[clause.index()] = ancestry.sample;
            self.regularity_long_states[clause.index()] = ancestry.state;
        }
    }

    fn clause_has_nonregular_derivation(&self, clause: ClauseRef) -> bool {
        debug_assert!(self.config.nonregular_clause_retention);
        self.clause_derivation_ancestry(clause).is_nonregular()
    }

    fn allocate_clause(&mut self, literals: Vec<Lit>, lbd: u32, learned: bool) -> ClauseRef {
        if literals.len() == 2 {
            let reference = ClauseRef::binary(self.binary_literals.len());
            self.binary_literals.push([literals[0], literals[1]]);
            let activity_index = if learned {
                let index = u32::try_from(self.learned_binary_activity.len())
                    .expect("learned binary activity index does not fit u32");
                self.learned_binary_activity.push(0.0);
                index
            } else {
                NO_BINARY_ACTIVITY
            };
            self.binary_activity_index.push(activity_index);
            self.binary_flags
                .push(if learned { BINARY_LEARNED } else { 0 });
            if self.config.nonregular_clause_retention {
                self.regularity_binary_samples
                    .push(DerivationAncestry::empty().sample);
                self.regularity_binary_states.push(0);
            }
            if self.uses_transfer_branching() {
                let metadata = if learned {
                    TransferClauseMetadata::learned(self.transfer.active)
                } else {
                    TransferClauseMetadata::original()
                };
                self.transfer_binary_clause_metadata.push(metadata);
            }
            return reference;
        }

        let start = self.clause_arena.len();
        let length =
            u32::try_from(literals.len()).expect("clause length exceeds packed arena metadata");
        self.clause_arena.extend(literals);
        if self.config.compact_clause_arena {
            let arena_literals = u64::try_from(self.clause_arena.len()).unwrap_or(u64::MAX);
            self.stats.arena_literals = arena_literals;
            self.stats.peak_arena_literals = self.stats.peak_arena_literals.max(arena_literals);
        }
        let clause = if learned {
            Clause::learned(start, length, lbd)
        } else {
            Clause::original(start, length)
        };
        let reference = ClauseRef::long(self.clauses.len());
        self.clauses.push(clause);
        if self.config.lbd_free_clause_management {
            self.clause_usage_scores.push(u32::from(learned));
        }
        if self.config.scan_debt_clause_management {
            self.clause_scan_debt.push(0);
        }
        if self.config.nonregular_clause_retention {
            self.regularity_long_samples
                .push(DerivationAncestry::empty().sample);
            self.regularity_long_states.push(0);
        }
        if self.config.shadow_clause_reactivation {
            self.shadow_clause_states.push(SHADOW_ACTIVE);
            self.shadow_clause_started_at.push(0);
        }
        if self.uses_transfer_branching() {
            let metadata = if learned {
                TransferClauseMetadata::learned(self.transfer.active)
            } else {
                TransferClauseMetadata::original()
            };
            self.transfer_long_clause_metadata.push(metadata);
        }
        reference
    }

    fn attach_clause(&mut self, clause: ClauseRef) {
        let literals = self.clause_literals(clause);
        let first = literals[0];
        let second = literals[1];
        self.watches[first.index()].push(Watch::new(clause, second));
        self.watches[second.index()].push(Watch::new(clause, first));
    }

    fn clause_is_shadow(&self, clause: ClauseRef) -> bool {
        self.config.shadow_clause_reactivation
            && !clause.is_binary()
            && self.shadow_clause_states[clause.index()] != SHADOW_ACTIVE
    }

    fn charge_shadow_literal_checks(&mut self, checks: usize) {
        self.stats.shadow_literal_checks = self
            .stats
            .shadow_literal_checks
            .saturating_add(u64::try_from(checks).unwrap_or(u64::MAX));
    }

    fn trigger_shadow_clause(&mut self, clause: ClauseRef, conflict: bool) {
        debug_assert!(self.config.shadow_clause_reactivation);
        debug_assert!(!clause.is_binary());
        let state = &mut self.shadow_clause_states[clause.index()];
        if *state != SHADOW_OBSERVING {
            return;
        }
        *state = SHADOW_TRIGGERED;
        if conflict {
            self.stats.shadow_conflict_triggers =
                self.stats.shadow_conflict_triggers.saturating_add(1);
        } else {
            self.stats.shadow_unit_triggers = self.stats.shadow_unit_triggers.saturating_add(1);
        }
    }

    fn begin_shadow_observation(&mut self, reference: usize) {
        debug_assert!(self.config.shadow_clause_reactivation);
        debug_assert!(!self.clauses[reference].deleted);
        debug_assert!(self.clauses[reference].learned);
        debug_assert_eq!(self.shadow_clause_states[reference], SHADOW_ACTIVE);
        debug_assert_eq!(self.clause_usage_scores[reference], 0);
        debug_assert!(self.shadow_clauses.len() < Self::SHADOW_CAPACITY);

        self.shadow_clause_states[reference] = SHADOW_OBSERVING;
        self.shadow_clause_started_at[reference] = self.stats.conflicts;
        self.shadow_clauses.push(reference);
        self.active_learned_clauses = self.active_learned_clauses.saturating_sub(1);
        self.stats.shadow_clauses_started = self.stats.shadow_clauses_started.saturating_add(1);
        self.stats.shadow_effective_removals =
            self.stats.shadow_effective_removals.saturating_add(1);
        self.stats.shadow_active_peak = self
            .stats
            .shadow_active_peak
            .max(u64::try_from(self.shadow_clauses.len()).unwrap_or(u64::MAX));
    }

    fn bump_variable_activity(&mut self, variable: Var) {
        self.activity[variable.index()] += self.variable_increment;
        if self.activity[variable.index()] > 1.0e100 {
            for activity in &mut self.activity {
                *activity *= 1.0e-100;
            }
            self.variable_increment *= 1.0e-100;
        }
        self.order.increase(variable, &self.activity);
    }

    fn bump_clause_activity(&mut self, clause: ClauseRef) {
        self.observe_transfer_clause_use(clause, TransferUse::Analysis);
        if self.config.lbd_free_clause_management {
            self.bump_clause_usage(clause, ClauseUsageUse::Analysis);
            return;
        }
        if !self.clause_learned(clause) {
            return;
        }
        if clause.is_binary() {
            let index = clause.index();
            let activity_index = self.binary_activity_index[index];
            debug_assert_ne!(activity_index, NO_BINARY_ACTIVITY);
            let activity_index = activity_index as usize;
            self.learned_binary_activity[activity_index] += self.clause_increment;
            if self.learned_binary_activity[activity_index] > 1.0e20 {
                for candidate in &mut self.clauses {
                    candidate.activity *= 1.0e-20;
                }
                for activity in &mut self.learned_binary_activity {
                    *activity *= 1.0e-20;
                }
                self.clause_increment *= 1.0e-20;
            }
            return;
        }

        let index = clause.index();
        if self.config.tiered_clause_management {
            self.clauses[index].used = MAX_CLAUSE_USAGE;
            let old_lbd = self.clauses[index].lbd;
            if self.config.promote_clause_lbd && old_lbd > TIER1_LBD {
                let new_lbd = self.clause_literal_block_distance(clause);
                if new_lbd < old_lbd {
                    self.clauses[index].lbd = new_lbd;
                    self.stats.promoted_clauses += 1;
                }
            }
        }
        self.clauses[index].activity += self.clause_increment;
        if self.clauses[index].activity > 1.0e20 {
            for candidate in &mut self.clauses {
                candidate.activity *= 1.0e-20;
            }
            for activity in &mut self.learned_binary_activity {
                *activity *= 1.0e-20;
            }
            self.clause_increment *= 1.0e-20;
        }
    }

    fn observe_transfer_clause_use(&mut self, clause: ClauseRef, use_kind: TransferUse) -> bool {
        if !self.uses_transfer_branching() {
            return false;
        }
        let active = self.transfer.active;
        let epoch = self.transfer.epoch;
        let metadata = if clause.is_binary() {
            self.transfer_binary_clause_metadata[clause.index()]
        } else {
            self.transfer_long_clause_metadata[clause.index()]
        };
        let Some(origin) = metadata.origin else {
            return false;
        };
        if origin == active || metadata.last_credited_epoch == epoch {
            return false;
        }

        if clause.is_binary() {
            self.transfer_binary_clause_metadata[clause.index()].last_credited_epoch = epoch;
        } else {
            self.transfer_long_clause_metadata[clause.index()].last_credited_epoch = epoch;
        }
        self.transfer.record_credit(origin);
        match origin {
            TransferRegime::Evsids => {
                self.stats.transfer_evsids_origin_credits =
                    self.stats.transfer_evsids_origin_credits.saturating_add(1);
            }
            TransferRegime::Lrb => {
                self.stats.transfer_lrb_origin_credits =
                    self.stats.transfer_lrb_origin_credits.saturating_add(1);
            }
        }
        match use_kind {
            TransferUse::Propagation => {
                self.stats.transfer_bcp_credits = self.stats.transfer_bcp_credits.saturating_add(1);
            }
            TransferUse::Analysis => {
                self.stats.transfer_analysis_credits =
                    self.stats.transfer_analysis_credits.saturating_add(1);
            }
        }
        true
    }

    fn bump_clause_usage(&mut self, clause: ClauseRef, use_kind: ClauseUsageUse) {
        if !self.config.lbd_free_clause_management
            || clause.is_binary()
            || !self.clause_learned(clause)
            || self.clause_deleted(clause)
        {
            return;
        }
        self.reset_clause_scan_debt(clause);
        let score = &mut self.clause_usage_scores[clause.index()];
        *score = score.saturating_add(1);
        match use_kind {
            ClauseUsageUse::Propagation => {
                self.stats.clause_usage_bcp_increments =
                    self.stats.clause_usage_bcp_increments.saturating_add(1);
            }
            ClauseUsageUse::Analysis => {
                self.stats.clause_usage_analysis_increments = self
                    .stats
                    .clause_usage_analysis_increments
                    .saturating_add(1);
            }
        }
    }

    fn charge_clause_scan_debt(&mut self, clause: ClauseRef, literal_checks: usize) {
        if !self.config.scan_debt_clause_management
            || literal_checks == 0
            || clause.is_binary()
            || !self.clause_learned(clause)
            || self.clause_deleted(clause)
        {
            return;
        }
        let amount = u64::try_from(literal_checks).unwrap_or(u64::MAX);
        let debt = &mut self.clause_scan_debt[clause.index()];
        *debt = debt.saturating_add(amount);
        self.stats.clause_scan_debt_literal_checks = self
            .stats
            .clause_scan_debt_literal_checks
            .saturating_add(amount);
        self.stats.clause_scan_debt_peak = self.stats.clause_scan_debt_peak.max(*debt);
    }

    fn reset_clause_scan_debt(&mut self, clause: ClauseRef) {
        if !self.config.scan_debt_clause_management
            || clause.is_binary()
            || !self.clause_learned(clause)
            || self.clause_deleted(clause)
        {
            return;
        }
        let debt = &mut self.clause_scan_debt[clause.index()];
        if *debt == 0 {
            return;
        }
        *debt = 0;
        self.stats.clause_scan_debt_nonzero_resets =
            self.stats.clause_scan_debt_nonzero_resets.saturating_add(1);
    }

    fn decay_clause_usage_scores(&mut self) {
        debug_assert!(self.config.lbd_free_clause_management);
        debug_assert_eq!(self.clause_usage_scores.len(), self.clauses.len());
        self.stats.clause_usage_decay_passes =
            self.stats.clause_usage_decay_passes.saturating_add(1);
        for (index, clause) in self.clauses.iter().enumerate() {
            if !clause.learned || clause.deleted || self.clause_is_shadow(ClauseRef::long(index)) {
                continue;
            }
            let score = &mut self.clause_usage_scores[index];
            if *score > 0 {
                *score -= 1;
                self.stats.clause_usage_scores_decayed =
                    self.stats.clause_usage_scores_decayed.saturating_add(1);
            }
        }
    }

    fn decay_activities(&mut self) {
        if (!self.uses_vmtf_branching() && !self.uses_lrb_branching() && !self.uses_chb_branching())
            || (self.config.search_strategy == SearchStrategy::ProbeEvsids && !self.probe_finished)
        {
            self.variable_increment /= self.variable_decay;
        }
        if !self.config.lbd_free_clause_management {
            self.clause_increment /= self.clause_decay;
        }
    }

    fn reduce_database(&mut self) {
        if self.config.lbd_free_clause_management {
            if self.config.scan_debt_clause_management {
                self.reduce_database_scan_debt();
            } else if self.config.nonregular_clause_retention {
                self.reduce_database_nonregular();
            } else if self.config.shadow_clause_reactivation {
                self.reduce_database_shadow_reactivation();
            } else if self.config.counterfactual_phase_voting {
                self.reduce_database_counterfactual_phase();
            } else {
                self.reduce_database_lbd_free();
            }
            return;
        }

        let mut locked = vec![false; self.clauses.len()];
        for &reason in &self.reasons {
            if let Some(clause) = reason {
                if !clause.is_binary() {
                    locked[clause.index()] = true;
                }
            }
        }

        let mut candidates = Vec::new();
        for (reference, clause) in self.clauses.iter_mut().enumerate() {
            if !clause.learned || clause.deleted || clause.len() <= 2 || locked[reference] {
                continue;
            }
            if self.config.tiered_clause_management {
                let used = clause.used;
                clause.used = used.saturating_sub(1);
                if clause.lbd <= TIER1_LBD && used > 0 {
                    self.stats.tier1_protections += 1;
                    continue;
                }
                if clause.lbd <= TIER2_LBD && used >= MAX_CLAUSE_USAGE - 1 {
                    self.stats.tier2_protections += 1;
                    continue;
                }
            }
            candidates.push(reference);
        }
        candidates.sort_unstable_by(|&left, &right| {
            let left = &self.clauses[left];
            let right = &self.clauses[right];
            left.lbd
                .cmp(&right.lbd)
                .then_with(|| right.activity.total_cmp(&left.activity))
        });

        let retained = candidates.len() / 2;
        for clause in candidates.into_iter().skip(retained) {
            self.mark_clause_deleted(ClauseRef::long(clause));
            self.stats.deleted_clauses += 1;
            self.active_learned_clauses = self.active_learned_clauses.saturating_sub(1);
        }
        self.stats.reductions += 1;
        if self.config.compact_clause_arena {
            self.compact_clause_arena();
        }
    }

    fn reduce_database_scan_debt(&mut self) {
        debug_assert!(self.config.lbd_free_clause_management);
        debug_assert!(self.config.scan_debt_clause_management);
        debug_assert_eq!(self.clause_usage_scores.len(), self.clauses.len());
        debug_assert_eq!(self.clause_scan_debt.len(), self.clauses.len());

        let mut locked = vec![false; self.clauses.len()];
        for &reason in &self.reasons {
            if let Some(clause) = reason {
                if !clause.is_binary() {
                    locked[clause.index()] = true;
                }
            }
        }

        let mut candidates = Vec::new();
        let mut zero_candidates = Vec::new();
        let mut positive_candidates = 0_u64;
        for (reference, clause) in self.clauses.iter().enumerate() {
            if !clause.learned || clause.deleted || locked[reference] {
                continue;
            }
            candidates.push(reference);
            if self.clause_usage_scores[reference] == 0 {
                zero_candidates.push(reference);
            } else {
                positive_candidates = positive_candidates.saturating_add(1);
            }
        }
        self.stats.clause_usage_zero_candidates = self
            .stats
            .clause_usage_zero_candidates
            .saturating_add(u64::try_from(zero_candidates.len()).unwrap_or(u64::MAX));

        let reduction = self.stats.reductions.saturating_add(1);
        let deletion_count = (Self::lbd_free_deletion_fraction(reduction)
            * zero_candidates.len() as f64)
            .floor() as usize;

        zero_candidates.sort_unstable_by(|&left, &right| {
            self.clauses[right]
                .len()
                .cmp(&self.clauses[left].len())
                .then_with(|| left.cmp(&right))
        });
        let mut baseline_deleted = vec![false; self.clauses.len()];
        for &reference in zero_candidates.iter().take(deletion_count) {
            baseline_deleted[reference] = true;
        }

        candidates.sort_unstable_by(|&left, &right| {
            self.clause_scan_debt[right]
                .cmp(&self.clause_scan_debt[left])
                .then_with(|| self.clause_usage_scores[left].cmp(&self.clause_usage_scores[right]))
                .then_with(|| self.clauses[right].len().cmp(&self.clauses[left].len()))
                .then_with(|| left.cmp(&right))
        });

        let mut displacements = 0_u64;
        let mut positive_deletions = 0_u64;
        for clause in candidates.into_iter().take(deletion_count) {
            if !baseline_deleted[clause] {
                displacements = displacements.saturating_add(1);
            }
            if self.clause_usage_scores[clause] > 0 {
                positive_deletions = positive_deletions.saturating_add(1);
            }
            self.mark_clause_deleted(ClauseRef::long(clause));
            self.stats.deleted_clauses = self.stats.deleted_clauses.saturating_add(1);
            self.active_learned_clauses = self.active_learned_clauses.saturating_sub(1);
        }
        self.stats.clause_scan_debt_selection_displacements = self
            .stats
            .clause_scan_debt_selection_displacements
            .saturating_add(displacements);
        self.stats.clause_scan_debt_positive_deletions = self
            .stats
            .clause_scan_debt_positive_deletions
            .saturating_add(positive_deletions);
        self.stats.clause_scan_debt_zero_rescues = self
            .stats
            .clause_scan_debt_zero_rescues
            .saturating_add(displacements);
        self.stats.clause_usage_positive_protections = self
            .stats
            .clause_usage_positive_protections
            .saturating_add(positive_candidates.saturating_sub(positive_deletions));
        self.stats.reductions = reduction;
        if self.config.compact_clause_arena {
            self.compact_clause_arena();
        }
    }

    fn reduce_database_nonregular(&mut self) {
        debug_assert!(self.config.lbd_free_clause_management);
        debug_assert!(self.config.nonregular_clause_retention);
        debug_assert_eq!(self.clause_usage_scores.len(), self.clauses.len());
        debug_assert_eq!(self.regularity_long_samples.len(), self.clauses.len());
        debug_assert_eq!(self.regularity_long_states.len(), self.clauses.len());

        let mut locked = vec![false; self.clauses.len()];
        for &reason in &self.reasons {
            if let Some(clause) = reason {
                if !clause.is_binary() {
                    locked[clause.index()] = true;
                }
            }
        }

        let mut candidates = Vec::new();
        let mut nonregular_candidates = 0_u64;
        for (reference, clause) in self.clauses.iter().enumerate() {
            if !clause.learned || clause.deleted || locked[reference] {
                continue;
            }
            if self.clause_usage_scores[reference] > 0 {
                self.stats.clause_usage_positive_protections = self
                    .stats
                    .clause_usage_positive_protections
                    .saturating_add(1);
                continue;
            }
            let clause_ref = ClauseRef::long(reference);
            if self.clause_has_nonregular_derivation(clause_ref) {
                nonregular_candidates = nonregular_candidates.saturating_add(1);
            }
            candidates.push(reference);
        }
        self.stats.clause_usage_zero_candidates = self
            .stats
            .clause_usage_zero_candidates
            .saturating_add(u64::try_from(candidates.len()).unwrap_or(u64::MAX));
        self.stats.regularity_nonregular_zero_candidates = self
            .stats
            .regularity_nonregular_zero_candidates
            .saturating_add(nonregular_candidates);

        let reduction = self.stats.reductions.saturating_add(1);
        let deletion_count = (Self::lbd_free_deletion_fraction(reduction) * candidates.len() as f64)
            .floor() as usize;

        let mut baseline_order = candidates.clone();
        baseline_order.sort_unstable_by(|&left, &right| {
            self.clauses[right]
                .len()
                .cmp(&self.clauses[left].len())
                .then_with(|| left.cmp(&right))
        });
        let mut baseline_deleted = vec![false; self.clauses.len()];
        for &reference in baseline_order.iter().take(deletion_count) {
            baseline_deleted[reference] = true;
        }

        candidates.sort_unstable_by(|&left, &right| {
            self.clause_has_nonregular_derivation(ClauseRef::long(left))
                .cmp(&self.clause_has_nonregular_derivation(ClauseRef::long(right)))
                .then_with(|| self.clauses[right].len().cmp(&self.clauses[left].len()))
                .then_with(|| left.cmp(&right))
        });

        let mut treatment_deleted = vec![false; self.clauses.len()];
        let mut displacements = 0_u64;
        let mut nonregular_deletions = 0_u64;
        for clause in candidates.into_iter().take(deletion_count) {
            treatment_deleted[clause] = true;
            if !baseline_deleted[clause] {
                displacements = displacements.saturating_add(1);
            }
            if self.clause_has_nonregular_derivation(ClauseRef::long(clause)) {
                nonregular_deletions = nonregular_deletions.saturating_add(1);
            }
            self.mark_clause_deleted(ClauseRef::long(clause));
            self.stats.deleted_clauses = self.stats.deleted_clauses.saturating_add(1);
            self.active_learned_clauses = self.active_learned_clauses.saturating_sub(1);
        }

        let nonregular_rescues = baseline_order
            .into_iter()
            .take(deletion_count)
            .filter(|&reference| {
                !treatment_deleted[reference]
                    && self.clause_has_nonregular_derivation(ClauseRef::long(reference))
            })
            .count();
        self.stats.regularity_selection_displacements = self
            .stats
            .regularity_selection_displacements
            .saturating_add(displacements);
        self.stats.regularity_nonregular_rescues = self
            .stats
            .regularity_nonregular_rescues
            .saturating_add(u64::try_from(nonregular_rescues).unwrap_or(u64::MAX));
        self.stats.regularity_nonregular_deletions = self
            .stats
            .regularity_nonregular_deletions
            .saturating_add(nonregular_deletions);
        self.stats.reductions = reduction;
        if self.config.compact_clause_arena {
            self.compact_clause_arena();
        }
    }

    fn reduce_database_shadow_reactivation(&mut self) {
        debug_assert!(self.config.lbd_free_clause_management);
        debug_assert!(self.config.shadow_clause_reactivation);
        debug_assert!(!self.config.compact_clause_arena);
        debug_assert_eq!(self.clause_usage_scores.len(), self.clauses.len());
        debug_assert_eq!(self.shadow_clause_states.len(), self.clauses.len());
        debug_assert_eq!(self.shadow_clause_started_at.len(), self.clauses.len());

        let mut locked = vec![false; self.clauses.len()];
        for &reason in &self.reasons {
            if let Some(clause) = reason {
                if !clause.is_binary() {
                    debug_assert!(
                        !self.clause_is_shadow(clause),
                        "a shadow clause must never become a reason"
                    );
                    locked[clause.index()] = true;
                }
            }
        }

        let mut candidates = Vec::new();
        for (reference, clause) in self.clauses.iter().enumerate() {
            if !clause.learned
                || clause.deleted
                || locked[reference]
                || self.shadow_clause_states[reference] != SHADOW_ACTIVE
            {
                continue;
            }
            if self.clause_usage_scores[reference] > 0 {
                self.stats.clause_usage_positive_protections = self
                    .stats
                    .clause_usage_positive_protections
                    .saturating_add(1);
                continue;
            }
            candidates.push(reference);
        }
        self.stats.clause_usage_zero_candidates = self
            .stats
            .clause_usage_zero_candidates
            .saturating_add(u64::try_from(candidates.len()).unwrap_or(u64::MAX));
        candidates.sort_unstable_by(|&left, &right| {
            self.clauses[right]
                .len()
                .cmp(&self.clauses[left].len())
                .then_with(|| left.cmp(&right))
        });

        let reduction = self.stats.reductions.saturating_add(1);
        let deletion_count = (Self::lbd_free_deletion_fraction(reduction) * candidates.len() as f64)
            .floor() as usize;
        let deletions = &candidates[..deletion_count];
        let available = Self::SHADOW_CAPACITY.saturating_sub(self.shadow_clauses.len());
        let shadow_count = available.min(deletions.len());
        let mut ranked = deletions.to_vec();
        ranked.sort_unstable_by(|&left, &right| {
            shadow_clause_rank(left, reduction)
                .cmp(&shadow_clause_rank(right, reduction))
                .then_with(|| left.cmp(&right))
        });
        let mut selected = vec![false; self.clauses.len()];
        for &reference in ranked.iter().take(shadow_count) {
            selected[reference] = true;
        }

        for &reference in deletions {
            if selected[reference] {
                self.begin_shadow_observation(reference);
            } else {
                self.mark_clause_deleted(ClauseRef::long(reference));
                self.stats.deleted_clauses = self.stats.deleted_clauses.saturating_add(1);
                self.active_learned_clauses = self.active_learned_clauses.saturating_sub(1);
                self.stats.shadow_effective_removals =
                    self.stats.shadow_effective_removals.saturating_add(1);
            }
        }
        self.stats.shadow_capacity_skips = self.stats.shadow_capacity_skips.saturating_add(
            u64::try_from(deletions.len().saturating_sub(shadow_count)).unwrap_or(u64::MAX),
        );
        self.stats.reductions = reduction;
    }

    fn offer_counterfactual_phase_sample(&mut self, clause: ClauseRef, reduction: u64) {
        debug_assert!(self.config.counterfactual_phase_voting);
        debug_assert!(!clause.is_binary());
        debug_assert!(self.clause_learned(clause));
        debug_assert!(self.clause_deleted(clause));

        self.stats.counterfactual_phase_deletion_offers = self
            .stats
            .counterfactual_phase_deletion_offers
            .saturating_add(1);
        let sample = CounterfactualPhaseSample {
            rank: shadow_clause_rank(clause.index(), reduction),
            reduction,
            clause,
        };
        if self.counterfactual_phase_samples.len() < Self::COUNTERFACTUAL_PHASE_CAPACITY {
            self.counterfactual_phase_samples.push(sample);
            self.stats.counterfactual_phase_sample_insertions = self
                .stats
                .counterfactual_phase_sample_insertions
                .saturating_add(1);
        } else {
            let (worst_index, worst) = self
                .counterfactual_phase_samples
                .iter()
                .enumerate()
                .max_by_key(|(_, current)| **current)
                .expect("full counterfactual sample must have a maximum");
            if sample < *worst {
                self.counterfactual_phase_samples[worst_index] = sample;
                self.stats.counterfactual_phase_sample_insertions = self
                    .stats
                    .counterfactual_phase_sample_insertions
                    .saturating_add(1);
                self.stats.counterfactual_phase_sample_replacements = self
                    .stats
                    .counterfactual_phase_sample_replacements
                    .saturating_add(1);
            }
        }
        self.stats.counterfactual_phase_sample_peak = self
            .stats
            .counterfactual_phase_sample_peak
            .max(u64::try_from(self.counterfactual_phase_samples.len()).unwrap_or(u64::MAX));
    }

    fn reduce_database_counterfactual_phase(&mut self) {
        debug_assert!(self.config.lbd_free_clause_management);
        debug_assert!(self.config.counterfactual_phase_voting);
        debug_assert!(!self.config.compact_clause_arena);
        debug_assert_eq!(self.clause_usage_scores.len(), self.clauses.len());

        let mut locked = vec![false; self.clauses.len()];
        for &reason in &self.reasons {
            if let Some(clause) = reason {
                if !clause.is_binary() {
                    locked[clause.index()] = true;
                }
            }
        }

        let mut candidates = Vec::new();
        for (reference, clause) in self.clauses.iter().enumerate() {
            if !clause.learned || clause.deleted || locked[reference] {
                continue;
            }
            if self.clause_usage_scores[reference] > 0 {
                self.stats.clause_usage_positive_protections = self
                    .stats
                    .clause_usage_positive_protections
                    .saturating_add(1);
                continue;
            }
            candidates.push(reference);
        }
        self.stats.clause_usage_zero_candidates = self
            .stats
            .clause_usage_zero_candidates
            .saturating_add(u64::try_from(candidates.len()).unwrap_or(u64::MAX));
        candidates.sort_unstable_by(|&left, &right| {
            self.clauses[right]
                .len()
                .cmp(&self.clauses[left].len())
                .then_with(|| left.cmp(&right))
        });

        let reduction = self.stats.reductions.saturating_add(1);
        let deletion_count = (Self::lbd_free_deletion_fraction(reduction) * candidates.len() as f64)
            .floor() as usize;
        for reference in candidates.into_iter().take(deletion_count) {
            let clause = ClauseRef::long(reference);
            self.mark_clause_deleted(clause);
            self.stats.deleted_clauses = self.stats.deleted_clauses.saturating_add(1);
            self.active_learned_clauses = self.active_learned_clauses.saturating_sub(1);
            self.offer_counterfactual_phase_sample(clause, reduction);
        }
        self.stats.reductions = reduction;
    }

    fn reduce_database_lbd_free(&mut self) {
        debug_assert!(self.config.lbd_free_clause_management);
        debug_assert_eq!(self.clause_usage_scores.len(), self.clauses.len());
        let mut locked = vec![false; self.clauses.len()];
        for &reason in &self.reasons {
            if let Some(clause) = reason {
                if !clause.is_binary() {
                    locked[clause.index()] = true;
                }
            }
        }

        let mut candidates = Vec::new();
        for (reference, clause) in self.clauses.iter().enumerate() {
            if !clause.learned || clause.deleted || locked[reference] {
                continue;
            }
            if self.clause_usage_scores[reference] > 0 {
                self.stats.clause_usage_positive_protections = self
                    .stats
                    .clause_usage_positive_protections
                    .saturating_add(1);
                continue;
            }
            candidates.push(reference);
        }
        self.stats.clause_usage_zero_candidates = self
            .stats
            .clause_usage_zero_candidates
            .saturating_add(u64::try_from(candidates.len()).unwrap_or(u64::MAX));
        candidates.sort_unstable_by(|&left, &right| {
            self.clauses[right]
                .len()
                .cmp(&self.clauses[left].len())
                .then_with(|| left.cmp(&right))
        });

        let reduction = self.stats.reductions.saturating_add(1);
        let deletion_count = (Self::lbd_free_deletion_fraction(reduction) * candidates.len() as f64)
            .floor() as usize;
        for clause in candidates.into_iter().take(deletion_count) {
            self.mark_clause_deleted(ClauseRef::long(clause));
            self.stats.deleted_clauses = self.stats.deleted_clauses.saturating_add(1);
            self.active_learned_clauses = self.active_learned_clauses.saturating_sub(1);
        }
        self.stats.reductions = reduction;
        if self.config.compact_clause_arena {
            self.compact_clause_arena();
        }
    }

    fn lbd_free_deletion_fraction(reduction: u64) -> f64 {
        debug_assert!(reduction > 0);
        0.90 - 0.40 / (reduction.saturating_add(9) as f64).log10()
    }

    fn lbd_free_reduction_interval(reduction: u64) -> u64 {
        debug_assert!(reduction > 0);
        (Self::LBD_FREE_REDUCTION_BASE as f64 * (reduction as f64).sqrt()).floor() as u64
    }

    fn should_decay_clause_usage(conflicts: u64) -> bool {
        conflicts > 0 && conflicts % Self::LBD_FREE_DECAY_INTERVAL == 0
    }

    fn mark_clause_deleted(&mut self, clause: ClauseRef) {
        debug_assert!(!self.clause_deleted(clause));
        if clause.is_binary() {
            self.proof
                .delete_clause(&self.binary_literals[clause.index()]);
            self.binary_flags[clause.index()] |= BINARY_DELETED;
            return;
        }

        let index = clause.index();
        let range = self.clauses[index].range();
        self.proof.delete_clause(&self.clause_arena[range]);
        if self.config.compact_clause_arena {
            let metadata = &self.clauses[index];
            self.arena_garbage_literals =
                self.arena_garbage_literals.saturating_add(metadata.len());
            self.arena_garbage_clause = self.arena_garbage_clause.min(index);
            self.arena_garbage_start = self.arena_garbage_start.min(metadata.start);
            self.stats.arena_garbage_literals =
                u64::try_from(self.arena_garbage_literals).unwrap_or(u64::MAX);
        }
        self.clauses[index].deleted = true;
    }

    fn compact_clause_arena(&mut self) {
        if self.arena_garbage_literals == 0 {
            return;
        }

        debug_assert_ne!(self.arena_garbage_clause, usize::MAX);
        debug_assert_ne!(self.arena_garbage_start, usize::MAX);
        let old_length = self.clause_arena.len();
        let mut write = self.arena_garbage_start;
        let mut moved = 0_usize;

        for clause in self.arena_garbage_clause..self.clauses.len() {
            if self.clauses[clause].deleted {
                continue;
            }
            let old_start = self.clauses[clause].start;
            let length = self.clauses[clause].len();
            debug_assert!(old_start >= write);
            if old_start != write {
                self.clause_arena
                    .copy_within(old_start..old_start + length, write);
                moved = moved.saturating_add(length);
            }
            self.clauses[clause].start = write;
            write += length;
        }

        let reclaimed = old_length - write;
        debug_assert_eq!(reclaimed, self.arena_garbage_literals);
        self.clause_arena.truncate(write);
        self.stats.arena_compactions = self.stats.arena_compactions.saturating_add(1);
        self.stats.arena_moved_literals = self
            .stats
            .arena_moved_literals
            .saturating_add(u64::try_from(moved).unwrap_or(u64::MAX));
        self.stats.arena_reclaimed_literals = self
            .stats
            .arena_reclaimed_literals
            .saturating_add(u64::try_from(reclaimed).unwrap_or(u64::MAX));
        self.stats.arena_literals = u64::try_from(write).unwrap_or(u64::MAX);
        self.stats.arena_garbage_literals = 0;
        self.arena_garbage_literals = 0;
        self.arena_garbage_clause = usize::MAX;
        self.arena_garbage_start = usize::MAX;
    }
}

fn value_of(assignments: &[i8], literal: Lit) -> i8 {
    let value = assignments[literal.var().index()];
    if literal.is_positive() { value } else { -value }
}

fn abstract_level(level: u32) -> u32 {
    1_u32 << (level & 31)
}

fn luby(index: u32) -> u64 {
    let mut size = 1_u64;
    let mut sequence = 0_u32;
    let mut index = u64::from(index);
    while size < index + 1 {
        size = size.saturating_mul(2).saturating_add(1);
        sequence += 1;
    }
    while size.saturating_sub(1) != index {
        size = (size - 1) / 2;
        sequence -= 1;
        index %= size;
    }
    1_u64 << sequence
}

fn try_reserve_len<T>(values: &mut Vec<T>, length: usize) -> Result<(), IncrementalError> {
    if values.capacity() >= length {
        return Ok(());
    }
    values
        .try_reserve(length.saturating_sub(values.len()))
        .map_err(|_| IncrementalError::ResourceExhausted)
}

#[derive(Debug, Default)]
struct VarOrder {
    heap: Vec<Var>,
    positions: Vec<usize>,
}

impl VarOrder {
    fn try_reserve(&mut self, variable_count: usize) -> Result<(), IncrementalError> {
        try_reserve_len(&mut self.heap, variable_count)?;
        try_reserve_len(&mut self.positions, variable_count)
    }

    fn grow(&mut self, old_count: usize, new_count: usize, activity: &[f64]) {
        self.positions.resize(new_count, NO_POSITION);
        for index in old_count..new_count {
            let variable =
                Var::new(u32::try_from(index).expect("variable count checked by caller"));
            self.insert(variable, activity);
        }
    }

    fn insert(&mut self, variable: Var, activity: &[f64]) {
        if self.positions[variable.index()] != NO_POSITION {
            return;
        }
        let position = self.heap.len();
        self.positions[variable.index()] = position;
        self.heap.push(variable);
        self.sift_up(position, activity);
    }

    fn increase(&mut self, variable: Var, activity: &[f64]) {
        let position = self.positions[variable.index()];
        if position != NO_POSITION {
            self.sift_up(position, activity);
        }
    }

    fn update(&mut self, variable: Var, old_activity: f64, activity: &[f64]) {
        let position = self.positions[variable.index()];
        if position == NO_POSITION {
            return;
        }
        match activity[variable.index()].total_cmp(&old_activity) {
            Ordering::Greater => self.sift_up(position, activity),
            Ordering::Less => self.sift_down(position, activity),
            Ordering::Equal => {}
        }
    }

    fn pop_max(&mut self, activity: &[f64]) -> Option<Var> {
        let maximum = *self.heap.first()?;
        let last = self.heap.pop().expect("heap is nonempty");
        self.positions[maximum.index()] = NO_POSITION;
        if !self.heap.is_empty() {
            self.heap[0] = last;
            self.positions[last.index()] = 0;
            self.sift_down(0, activity);
        }
        Some(maximum)
    }

    fn peek_max(&mut self, assignments: &[i8], activity: &[f64]) -> Option<Var> {
        loop {
            let maximum = *self.heap.first()?;
            if assignments[maximum.index()] == UNASSIGNED {
                return Some(maximum);
            }
            self.pop_max(activity);
        }
    }

    fn sift_up(&mut self, mut position: usize, activity: &[f64]) {
        while position > 0 {
            let parent = (position - 1) / 2;
            if !higher_priority(self.heap[position], self.heap[parent], activity) {
                break;
            }
            self.heap.swap(position, parent);
            self.positions[self.heap[position].index()] = position;
            self.positions[self.heap[parent].index()] = parent;
            position = parent;
        }
    }

    fn sift_down(&mut self, mut position: usize, activity: &[f64]) {
        loop {
            let left = position * 2 + 1;
            if left >= self.heap.len() {
                break;
            }
            let right = left + 1;
            let child = if right < self.heap.len()
                && higher_priority(self.heap[right], self.heap[left], activity)
            {
                right
            } else {
                left
            };
            if !higher_priority(self.heap[child], self.heap[position], activity) {
                break;
            }
            self.heap.swap(position, child);
            self.positions[self.heap[position].index()] = position;
            self.positions[self.heap[child].index()] = child;
            position = child;
        }
    }
}

const DISCONNECTED: usize = usize::MAX;

#[derive(Debug)]
struct VmtfLink {
    previous: usize,
    next: usize,
    stamp: u64,
}

#[derive(Debug)]
struct VmtfOrder {
    links: Vec<VmtfLink>,
    first: usize,
    last: usize,
    search: usize,
    stamp: u64,
}

impl Default for VmtfOrder {
    fn default() -> Self {
        Self {
            links: Vec::new(),
            first: DISCONNECTED,
            last: DISCONNECTED,
            search: DISCONNECTED,
            stamp: 0,
        }
    }
}

impl VmtfOrder {
    fn try_reserve(&mut self, variable_count: usize) -> Result<(), IncrementalError> {
        try_reserve_len(&mut self.links, variable_count)
    }

    fn grow(&mut self, old_count: usize, new_count: usize) {
        debug_assert_eq!(old_count, self.links.len());
        for index in old_count..new_count {
            self.advance_stamp();
            let previous = self.last;
            self.links.push(VmtfLink {
                previous,
                next: DISCONNECTED,
                stamp: self.stamp,
            });
            if previous == DISCONNECTED {
                self.first = index;
            } else {
                self.links[previous].next = index;
            }
            self.last = index;
            self.search = index;
        }
    }

    fn bump_analyzed(&mut self, variables: &mut [Var], assignments: &[i8]) {
        variables.sort_unstable_by_key(|variable| self.links[variable.index()].stamp);
        for &variable in variables.iter() {
            self.move_to_front(variable, assignments);
        }
    }

    fn move_to_front(&mut self, variable: Var, assignments: &[i8]) {
        let index = variable.index();
        if index == self.last {
            if assignments[index] == UNASSIGNED {
                self.search = index;
            }
            return;
        }

        let previous = self.links[index].previous;
        let next = self.links[index].next;
        if self.search == index && assignments[index] != UNASSIGNED {
            self.search = if previous != DISCONNECTED {
                previous
            } else {
                next
            };
        }
        if previous == DISCONNECTED {
            self.first = next;
        } else {
            self.links[previous].next = next;
        }
        if next != DISCONNECTED {
            self.links[next].previous = previous;
        }

        self.advance_stamp();
        self.links[index].previous = self.last;
        self.links[index].next = DISCONNECTED;
        self.links[index].stamp = self.stamp;
        self.links[self.last].next = index;
        self.last = index;
        if assignments[index] == UNASSIGNED {
            self.search = index;
        }
    }

    fn unassign(&mut self, variable: Var) {
        let index = variable.index();
        if self.search == DISCONNECTED || self.links[index].stamp > self.links[self.search].stamp {
            self.search = index;
        }
    }

    fn reset_search(&mut self, assignments: &[i8]) {
        self.search = self.last;
        while self.search != DISCONNECTED && assignments[self.search] != UNASSIGNED {
            self.search = self.links[self.search].previous;
        }
    }

    fn pick(&mut self, assignments: &[i8]) -> Option<Var> {
        while self.search != DISCONNECTED {
            let index = self.search;
            if assignments[index] == UNASSIGNED {
                return Some(Var::new(
                    u32::try_from(index).expect("variable count is bounded by u32"),
                ));
            }
            self.search = self.links[index].previous;
        }
        None
    }

    fn advance_stamp(&mut self) {
        if self.stamp == u64::MAX {
            self.stamp = 0;
            let mut current = self.first;
            while current != DISCONNECTED {
                self.stamp += 1;
                self.links[current].stamp = self.stamp;
                current = self.links[current].next;
            }
        }
        self.stamp += 1;
    }
}

fn higher_priority(left: Var, right: Var, activity: &[f64]) -> bool {
    match activity[left.index()].total_cmp(&activity[right.index()]) {
        Ordering::Greater => true,
        Ordering::Less => false,
        Ordering::Equal => left < right,
    }
}

#[cfg(test)]
mod tests {
    use super::{
        AdaptiveReuseChoice, AdaptiveTrailReuseState, ClauseRef, ClauseUsageUse,
        DerivationAncestry, EliminationRecord, ExponentialMovingAverage, FALSE, LBD_RESTART_WINDOW,
        LbdRestartState, Model, NO_BINARY_ACTIVITY, NONREGULAR_DERIVATION_BIT, ReluctantRestart,
        RestartAction, RestartEpochQuality, RestartTrailReuse, SHADOW_ACTIVE, SHADOW_OBSERVING,
        SHADOW_TRIGGERED, SearchStrategy, SolveResult, Solver, SolverConfig, TRUE,
        TrailRestartState, TransferRegime, TransferSearchState, TransferUse, UNASSIGNED, VarOrder,
        VmtfOrder, Watch, luby, pivot_rank, shadow_clause_rank,
    };
    use crate::{Lit, Var};

    #[test]
    fn luby_sequence_matches_the_standard_schedule() {
        let values = (0..15).map(luby).collect::<Vec<_>>();
        assert_eq!(values, [1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8]);
    }

    #[test]
    fn pivot_sample_uses_frozen_splitmix_rank_and_keeps_exact_bottom_four() {
        assert_eq!(pivot_rank(0), 0xe220_a839_7b1d_cdaf);
        assert_eq!(pivot_rank(1), 0x910a_2dec_8902_5cc1);
        assert_eq!(pivot_rank(3), 0x1d0b_14e4_db01_8fed);

        let mut ancestry = DerivationAncestry::empty();
        for variable in 0..8 {
            ancestry.insert(Var::new(variable));
        }

        assert_eq!(ancestry.sample_len(), 4);
        assert_eq!(ancestry.sample, [3, 5, 7, 4]);
        assert!(ancestry.contains(Var::new(3)));
        assert!(!ancestry.contains(Var::new(1)));
        ancestry.insert(Var::new(3));
        assert_eq!(ancestry.sample, [3, 5, 7, 4]);
    }

    #[test]
    fn derivation_ancestry_reports_only_sampled_repeats_and_inherits_witnesses() {
        let mut current = DerivationAncestry::empty();
        current.insert(Var::new(3));
        current.insert(Var::new(5));

        let mut parent = DerivationAncestry::empty();
        parent.insert(Var::new(7));
        parent.insert(Var::new(11));
        assert!(!current.resolve_with(Var::new(13), parent));
        assert!(!current.is_nonregular());
        assert!(current.resolve_with(Var::new(7), parent));
        assert!(current.is_nonregular());

        let mut inherited = DerivationAncestry::empty();
        let mut witnessed_parent = DerivationAncestry::empty();
        witnessed_parent.state |= NONREGULAR_DERIVATION_BIT;
        assert!(!inherited.resolve_with(Var::new(17), witnessed_parent));
        assert!(inherited.is_nonregular());
    }

    #[test]
    fn lbd_restart_detects_recent_quality_degradation() {
        let mut state = LbdRestartState::default();
        for _ in 0..100 {
            state.observe(2);
        }
        assert!(!state.should_restart());

        for _ in 0..LBD_RESTART_WINDOW {
            state.observe(10);
        }
        assert!(state.should_restart());
        state.clear_recent();
        assert!(!state.should_restart());
        assert_eq!(state.global_sum, 700);
        assert_eq!(state.conflicts, 150);
    }

    #[test]
    fn trail_restart_state_blocks_only_unusually_deep_trails() {
        let mut state = TrailRestartState::default();
        for _ in 0..100 {
            state.observe(100);
        }
        assert!(!state.unusually_deep(140));
        assert!(state.unusually_deep(141));
    }

    #[test]
    fn restart_epoch_quality_rewards_conflicts_with_less_bcp_and_lower_lbd() {
        let baseline = RestartEpochQuality {
            conflicts: 10,
            propagations: 200,
            lbd_sum: 40,
        };
        let less_bcp = RestartEpochQuality {
            conflicts: 10,
            propagations: 100,
            lbd_sum: 40,
        };
        let lower_lbd = RestartEpochQuality {
            conflicts: 10,
            propagations: 200,
            lbd_sum: 20,
        };
        assert!(less_bcp.at_least(baseline));
        assert!(lower_lbd.at_least(baseline));
        assert!(!baseline.at_least(less_bcp));
        assert!(!baseline.at_least(lower_lbd));

        let saturated = RestartEpochQuality {
            conflicts: u64::MAX,
            propagations: u64::MAX,
            lbd_sum: u64::MAX,
        };
        assert!(saturated.at_least(saturated));
    }

    #[test]
    fn adaptive_reuse_uses_latest_action_epochs_and_logarithmic_probes() {
        let mut state = AdaptiveTrailReuseState::default();
        let mut stats = super::SolverStats {
            conflicts: 10,
            propagations: 200,
            ..super::SolverStats::default()
        };
        for _ in 0..10 {
            state.observe_lbd(4);
        }
        state.finish_epoch(&mut stats);
        assert_eq!(
            state.root_quality,
            Some(RestartEpochQuality {
                conflicts: 10,
                propagations: 200,
                lbd_sum: 40,
            })
        );
        assert_eq!(stats.adaptive_root_epochs, 1);
        assert_eq!(state.choose(), AdaptiveReuseChoice::Probe); // event 1

        state.begin_epoch(RestartAction::Reuse, stats);
        stats.conflicts += 10;
        stats.propagations += 100;
        for _ in 0..10 {
            state.observe_lbd(2);
        }
        state.finish_epoch(&mut stats);
        assert_eq!(stats.adaptive_reuse_epochs, 1);
        assert_eq!(state.choose(), AdaptiveReuseChoice::Probe); // event 2
        assert_eq!(state.choose(), AdaptiveReuseChoice::QualityAccept); // event 3
        assert_eq!(state.choose(), AdaptiveReuseChoice::Probe); // event 4

        state.reuse_quality = Some(RestartEpochQuality {
            conflicts: 10,
            propagations: 400,
            lbd_sum: 80,
        });
        assert_eq!(state.choose(), AdaptiveReuseChoice::QualityReject); // event 5
    }

    #[test]
    fn exponential_average_is_bias_corrected() {
        let mut average = ExponentialMovingAverage::new(33);
        for _ in 0..100 {
            average.update(7);
            assert!((average.value - 7.0).abs() < 1.0e-12);
        }
    }

    #[test]
    fn reluctant_restart_starts_with_one_one_two_intervals() {
        let mut state = ReluctantRestart {
            period: 1,
            limit: 100,
            wait: 1,
            u: 1,
            v: 1,
            triggered: false,
        };
        state.tick();
        assert!(state.take_trigger());
        state.tick();
        assert!(state.take_trigger());
        state.tick();
        assert!(!state.triggered);
        state.tick();
        assert!(state.take_trigger());
    }

    #[test]
    fn vmtf_prefers_recently_bumped_unassigned_variables() {
        let mut order = VmtfOrder::default();
        order.grow(0, 4);
        let mut assignments = vec![UNASSIGNED; 4];
        assert_eq!(order.pick(&assignments), Some(Var::new(3)));
        assignments[3] = TRUE;
        assert_eq!(order.pick(&assignments), Some(Var::new(2)));

        order.bump_analyzed(&mut [Var::new(0), Var::new(1)], &assignments);
        assert_eq!(order.pick(&assignments), Some(Var::new(1)));
        assignments[1] = TRUE;
        assert_eq!(order.pick(&assignments), Some(Var::new(0)));

        assignments[3] = UNASSIGNED;
        order.unassign(Var::new(3));
        assert_eq!(order.pick(&assignments), Some(Var::new(0)));
    }

    #[test]
    fn variable_heap_tracks_activity_and_ties() {
        let mut order = VarOrder::default();
        let mut activity = vec![0.0; 4];
        order.grow(0, 4, &activity);
        assert_eq!(order.pop_max(&activity), Some(Var::new(0)));
        activity[3] = 10.0;
        order.increase(Var::new(3), &activity);
        assert_eq!(order.pop_max(&activity), Some(Var::new(3)));
    }

    #[test]
    fn variable_heap_repairs_score_increases_and_decreases() {
        let mut order = VarOrder::default();
        let mut activity = vec![0.0; 3];
        order.grow(0, 3, &activity);
        for (index, score) in [3.0, 2.0, 1.0].into_iter().enumerate() {
            let variable = Var::new(index as u32);
            let old_activity = activity[index];
            activity[index] = score;
            order.update(variable, old_activity, &activity);
        }
        activity[0] = 0.5;
        order.update(Var::new(0), 3.0, &activity);
        assert_eq!(order.pop_max(&activity), Some(Var::new(1)));
    }

    #[test]
    fn lrb_updates_interval_rewards_and_clamps_step_size() {
        let mut solver = Solver::with_config(SolverConfig {
            search_strategy: SearchStrategy::Lrb,
            ..SolverConfig::default()
        });
        solver.reserve_variables(1);
        let variable = Var::new(0);
        solver.activity[0] = 0.8;
        solver.stats.conflicts = 10;
        solver.lrb_canceled_at[0] = 8;

        solver.lrb_on_assign(variable);
        let decayed = 0.8 * Solver::LRB_ANTI_EXPLORATION_DECAY.powi(2);
        assert!((solver.activity[0] - decayed).abs() < 1.0e-12);
        assert_eq!(solver.lrb_assigned_at[0], 10);
        assert_eq!(solver.stats.lrb_anti_exploration_decays, 1);

        solver.stats.conflicts = 15;
        solver.lrb_participated[0] = 2;
        solver.lrb_reasoned[0] = 1;
        solver.lrb_on_unassign(variable);
        let expected = 0.6 * decayed + 0.4 * (3.0 / 5.0);
        assert!((solver.activity[0] - expected).abs() < 1.0e-12);
        assert_eq!(solver.lrb_canceled_at[0], 15);
        assert_eq!(solver.stats.lrb_unassign_updates, 1);

        solver.lrb_step_size = Solver::LRB_MINIMUM_STEP_SIZE + 0.5e-6;
        solver.lrb_decrease_step_size();
        assert_eq!(solver.lrb_step_size, Solver::LRB_MINIMUM_STEP_SIZE);
    }

    #[test]
    fn lrb_counts_distinct_participants_and_reason_side_union() {
        let mut solver = Solver::with_config(SolverConfig {
            search_strategy: SearchStrategy::Lrb,
            ..SolverConfig::default()
        });
        solver.reserve_variables(4);
        let a = Lit::positive(Var::new(0));
        let b = Lit::positive(Var::new(1));
        let c = Lit::positive(Var::new(2));
        let d = Lit::positive(Var::new(3));

        solver.lrb_record_participation(&[a.var(), b.var(), a.var()]);
        assert_eq!(solver.lrb_participated, [1, 1, 0, 0]);

        let reason_a = solver.allocate_clause(vec![a, c, d], 0, false);
        let reason_b = solver.allocate_clause(vec![b, c], 0, false);
        solver.reasons[a.var().index()] = Some(reason_a);
        solver.reasons[b.var().index()] = Some(reason_b);
        solver.lrb_record_reason_side(&[!a, !b]);

        assert_eq!(solver.lrb_reasoned, [0, 0, 1, 1]);
        assert_eq!(solver.stats.lrb_reason_side_rewards, 2);
    }

    #[test]
    fn lrb_lazily_decays_stale_heap_roots_before_branching() {
        let mut solver = Solver::with_config(SolverConfig {
            search_strategy: SearchStrategy::Lrb,
            ..SolverConfig::default()
        });
        solver.reserve_variables(3);
        for (index, score) in [1.0, 0.9, 0.8].into_iter().enumerate() {
            let variable = Var::new(index as u32);
            let old_activity = solver.activity[index];
            solver.activity[index] = score;
            solver
                .order
                .update(variable, old_activity, &solver.activity);
        }
        solver.stats.conflicts = 10;
        solver.lrb_canceled_at = vec![0, 10, 10];

        let decision = solver.pick_branch_literal().expect("LRB decision");
        assert_eq!(decision.var(), Var::new(1));
        assert!(solver.activity[0] < solver.activity[1]);
        assert_eq!(solver.stats.lrb_anti_exploration_decays, 1);
    }

    #[test]
    fn transfer_schedule_bootstraps_then_probes_and_exploits() {
        let mut state = TransferSearchState::default();
        state.record_credit(TransferRegime::Lrb);
        assert_eq!(
            state.finish_epoch(100),
            (TransferRegime::Evsids, TransferRegime::Lrb)
        );
        assert_eq!(state.observations, [0, 0]);

        let mut conflicts = 100;
        for epoch in 2..=9 {
            let active = if epoch % 2 == 0 {
                TransferRegime::Lrb
            } else {
                TransferRegime::Evsids
            };
            assert_eq!(state.active, active);
            let producer = active.opposite();
            let credits = if producer == TransferRegime::Evsids {
                10
            } else {
                5
            };
            for _ in 0..credits {
                state.record_credit(producer);
            }
            conflicts += 100;
            state.finish_epoch(conflicts);
        }
        assert_eq!(state.observations, [4, 4]);
        assert_eq!(state.estimates, [100.0, 50.0]);
        assert_eq!(state.epoch, 10);
        assert_eq!(state.active, TransferRegime::Evsids);

        for _ in 0..20 {
            state.record_credit(TransferRegime::Lrb);
        }
        conflicts += 100;
        state.finish_epoch(conflicts);
        assert_eq!(state.active, TransferRegime::Lrb);

        state.record_credit(TransferRegime::Evsids);
        conflicts += 100;
        state.finish_epoch(conflicts);
        assert_eq!(state.winner, TransferRegime::Lrb);
        assert_eq!(state.active, TransferRegime::Lrb);
        for _ in 0..7 {
            conflicts += 100;
            state.finish_epoch(conflicts);
            assert_eq!(state.active, TransferRegime::Lrb);
        }
        conflicts += 100;
        state.finish_epoch(conflicts);
        assert_eq!(state.epoch, 20);
        assert_eq!(state.active, TransferRegime::Evsids);
    }

    #[test]
    fn transfer_selector_breaks_exact_estimate_ties_for_evsids() {
        let mut state = TransferSearchState {
            active: TransferRegime::Lrb,
            epoch: 11,
            epoch_start_conflicts: 1_000,
            estimates: [0.0, 0.0],
            observations: [4, 5],
            ..TransferSearchState::default()
        };
        state.finish_epoch(1_100);
        assert_eq!(state.winner, TransferRegime::Evsids);
        assert_eq!(state.active, TransferRegime::Evsids);
    }

    #[test]
    fn transfer_clause_credit_is_directional_and_once_per_epoch() {
        let mut solver = Solver::with_config(SolverConfig {
            search_strategy: SearchStrategy::Transfer,
            ..SolverConfig::default()
        });
        solver.reserve_variables(3);
        let a = Lit::positive(Var::new(0));
        let b = Lit::positive(Var::new(1));
        let c = Lit::positive(Var::new(2));
        let original = solver.allocate_clause(vec![a, b], 0, false);
        let binary = solver.allocate_clause(vec![a, !b], 2, true);
        let long = solver.allocate_clause(vec![a, b, c], 3, true);

        assert_eq!(solver.transfer_binary_clause_metadata.len(), 2);
        assert_eq!(solver.transfer_long_clause_metadata.len(), 1);
        assert_eq!(
            solver.transfer_binary_clause_metadata[original.index()].origin,
            None
        );
        assert_eq!(
            solver.transfer_binary_clause_metadata[binary.index()].origin,
            Some(TransferRegime::Evsids)
        );
        assert_eq!(
            solver.transfer_long_clause_metadata[long.index()].origin,
            Some(TransferRegime::Evsids)
        );
        assert!(!solver.observe_transfer_clause_use(binary, TransferUse::Propagation));

        solver.transfer.active = TransferRegime::Lrb;
        assert!(solver.observe_transfer_clause_use(binary, TransferUse::Propagation));
        assert!(!solver.observe_transfer_clause_use(binary, TransferUse::Analysis));
        assert!(solver.observe_transfer_clause_use(long, TransferUse::Analysis));
        assert!(!solver.observe_transfer_clause_use(original, TransferUse::Propagation));
        assert_eq!(solver.stats.transfer_evsids_origin_credits, 2);
        assert_eq!(solver.stats.transfer_lrb_origin_credits, 0);
        assert_eq!(solver.stats.transfer_bcp_credits, 1);
        assert_eq!(solver.stats.transfer_analysis_credits, 1);

        solver.transfer.epoch += 1;
        assert!(solver.observe_transfer_clause_use(binary, TransferUse::Analysis));
        assert_eq!(solver.stats.transfer_evsids_origin_credits, 3);

        let lrb_long = solver.allocate_clause(vec![!a, b, c], 3, true);
        solver.transfer.active = TransferRegime::Evsids;
        assert!(solver.observe_transfer_clause_use(lrb_long, TransferUse::Propagation));
        assert_eq!(solver.stats.transfer_lrb_origin_credits, 1);
        solver.mark_clause_deleted(long);
        assert_eq!(
            solver.transfer_long_clause_metadata[long.index()].origin,
            Some(TransferRegime::Evsids)
        );
    }

    #[test]
    fn transfer_keeps_independent_evsids_and_lrb_heaps() {
        let mut solver = Solver::with_config(SolverConfig {
            search_strategy: SearchStrategy::Transfer,
            ..SolverConfig::default()
        });
        solver.reserve_variables(3);
        solver.activity[1] = 10.0;
        solver.order.increase(Var::new(1), &solver.activity);
        solver.transfer_lrb_activity[0] = 10.0;
        solver
            .transfer_lrb_order
            .increase(Var::new(0), &solver.transfer_lrb_activity);

        assert_eq!(
            solver.pick_branch_literal().map(Lit::var),
            Some(Var::new(1))
        );
        solver.transfer.active = TransferRegime::Lrb;
        assert_eq!(
            solver.pick_branch_literal().map(Lit::var),
            Some(Var::new(0))
        );

        solver.activity[2] = 7.0;
        solver.transfer_lrb_activity[2] = 0.8;
        solver.stats.conflicts = 10;
        solver.lrb_canceled_at[2] = 8;
        solver.lrb_on_assign(Var::new(2));
        let decayed = 0.8 * Solver::LRB_ANTI_EXPLORATION_DECAY.powi(2);
        assert_eq!(solver.activity[2], 7.0);
        assert!((solver.transfer_lrb_activity[2] - decayed).abs() < 1.0e-12);
    }

    #[test]
    fn transfer_metadata_is_not_allocated_in_pure_modes() {
        for strategy in [
            SearchStrategy::Evsids,
            SearchStrategy::Lrb,
            SearchStrategy::Chb,
        ] {
            let mut solver = Solver::with_config(SolverConfig {
                search_strategy: strategy,
                ..SolverConfig::default()
            });
            solver.reserve_variables(3);
            let a = Lit::positive(Var::new(0));
            let b = Lit::positive(Var::new(1));
            let c = Lit::positive(Var::new(2));
            solver.allocate_clause(vec![a, b], 2, true);
            solver.allocate_clause(vec![a, b, c], 3, true);
            assert!(solver.transfer_binary_clause_metadata.is_empty());
            assert!(solver.transfer_long_clause_metadata.is_empty());
            assert!(solver.transfer_lrb_activity.is_empty());
            assert!(solver.transfer_lrb_order.heap.is_empty());
        }
    }

    #[test]
    fn chb_updates_propagation_round_rewards_before_the_current_conflict() {
        let mut solver = Solver::with_config(SolverConfig {
            search_strategy: SearchStrategy::Chb,
            ..SolverConfig::default()
        });
        solver.reserve_variables(3);
        solver.activity[0] = 0.5;
        solver.stats.conflicts = 10;
        solver.chb_last_conflict = vec![8, 10, 5];
        solver.chb_plays.extend([Var::new(0), Var::new(1)]);

        solver.chb_finish_propagation(false);
        let expected_zero = 0.6 * 0.5 + 0.4 * (0.9 / 3.0);
        let expected_one = 0.4 * 0.9;
        assert!((solver.activity[0] - expected_zero).abs() < 1.0e-12);
        assert!((solver.activity[1] - expected_one).abs() < 1.0e-12);
        assert!(solver.chb_plays.is_empty());
        assert_eq!(solver.stats.chb_score_updates, 2);
        assert_eq!(solver.stats.chb_conflict_score_updates, 0);

        solver.chb_plays.push(Var::new(2));
        solver.chb_finish_propagation(true);
        assert!((solver.activity[2] - 0.4 * (1.0 / 6.0)).abs() < 1.0e-12);
        assert_eq!(solver.stats.chb_score_updates, 3);
        assert_eq!(solver.stats.chb_conflict_score_updates, 1);
    }

    #[test]
    fn chb_records_conflict_history_and_clamps_step_size() {
        let mut solver = Solver::with_config(SolverConfig {
            search_strategy: SearchStrategy::Chb,
            ..SolverConfig::default()
        });
        solver.reserve_variables(3);
        solver.stats.conflicts = 17;
        solver.chb_record_conflict_history(&[Var::new(0), Var::new(2)]);
        assert_eq!(solver.chb_last_conflict, [17, 0, 17]);
        assert_eq!(solver.stats.chb_conflict_history_updates, 2);

        solver.chb_step_size = Solver::CHB_MINIMUM_STEP_SIZE + 0.5e-6;
        solver.chb_decrease_step_size();
        assert_eq!(solver.chb_step_size, Solver::CHB_MINIMUM_STEP_SIZE);
    }

    #[test]
    fn chb_repairs_the_heap_when_an_erwa_update_decreases_a_score() {
        let mut solver = Solver::with_config(SolverConfig {
            search_strategy: SearchStrategy::Chb,
            ..SolverConfig::default()
        });
        solver.reserve_variables(2);
        solver.activity = vec![1.0, 0.7];
        solver.order.increase(Var::new(0), &solver.activity);
        solver.order.increase(Var::new(1), &solver.activity);
        solver.stats.conflicts = 99;
        solver.chb_plays.push(Var::new(0));

        solver.chb_finish_propagation(false);
        assert!(solver.activity[0] < solver.activity[1]);
        assert_eq!(
            solver.pick_branch_literal().map(Lit::var),
            Some(Var::new(1))
        );
    }

    #[test]
    fn restart_trail_reuse_keeps_only_decisions_ahead_of_the_frontier() {
        let mut solver = Solver::with_config(SolverConfig {
            restart_trail_reuse: RestartTrailReuse::Always,
            ..SolverConfig::default()
        });
        solver.reserve_variables(4);
        solver.activity = vec![10.0, 8.0, 5.0, 1.0];
        for index in 0..4 {
            solver.order.increase(Var::new(index), &solver.activity);
        }

        for expected in [Var::new(0), Var::new(1)] {
            let decision = solver.pick_branch_literal().expect("decision");
            assert_eq!(decision.var(), expected);
            solver.trail_limits.push(solver.trail.len());
            assert!(solver.enqueue(decision, None));
        }
        assert_eq!(solver.restart_reuse_level(), 2);

        solver.activity[2] = 9.0;
        solver.order.increase(Var::new(2), &solver.activity);
        assert_eq!(solver.restart_reuse_level(), 1);

        solver.activity[2] = 11.0;
        solver.order.increase(Var::new(2), &solver.activity);
        assert_eq!(solver.restart_reuse_level(), 0);
    }

    #[test]
    fn packed_watch_round_trips_all_fields_in_eight_bytes() {
        assert_eq!(std::mem::size_of::<Watch>(), 8);
        assert_eq!(std::mem::size_of::<Option<ClauseRef>>(), 4);
        let blocker = Lit::negative(Var::new(u32::MAX >> 1));
        let binary = ClauseRef::binary((ClauseRef::INDEX_MASK - 1) as usize);
        let watch = Watch::new(binary, blocker);
        assert_eq!(watch.clause(), binary);
        assert_eq!(watch.blocker(), blocker);
        assert!(watch.is_binary());

        let long = ClauseRef::long(17);
        let nonbinary = Watch::new(long, Lit::positive(Var::new(3)));
        assert_eq!(nonbinary.clause(), long);
        assert_eq!(nonbinary.blocker(), Lit::positive(Var::new(3)));
        assert!(!nonbinary.is_binary());
    }

    #[test]
    fn binary_clauses_use_parallel_storage_outside_the_long_arena() {
        let a = Lit::positive(Var::new(0));
        let b = Lit::negative(Var::new(1));
        let c = Lit::positive(Var::new(2));
        let mut solver = Solver::new();
        solver.reserve_variables(3);

        let binary = solver.allocate_clause(vec![a, b], 0, false);
        let long = solver.allocate_clause(vec![a, b, c], 0, false);

        assert!(binary.is_binary());
        assert!(!long.is_binary());
        assert_eq!(solver.binary_literals, [[a, b]]);
        assert_eq!(solver.binary_activity_index, [NO_BINARY_ACTIVITY]);
        assert!(solver.learned_binary_activity.is_empty());
        assert_eq!(solver.binary_flags, [0]);
        assert_eq!(solver.clause_arena, [a, b, c]);
        assert_eq!(solver.clauses.len(), 1);
        assert_eq!(solver.clause_literals(binary), [a, b]);
        assert_eq!(solver.clause_literals(long), [a, b, c]);

        let stats = solver.stats();
        assert_eq!(stats.stored_binary_clauses, 1);
        assert_eq!(stats.stored_long_clauses, 1);
        assert_eq!(stats.binary_storage_bytes, 13);
        assert_eq!(stats.long_storage_bytes, 48);
        assert_eq!(stats.reason_storage_bytes, 12);
        assert_eq!(stats.legacy_equivalent_storage_bytes, 132);
    }

    #[test]
    fn learned_binary_activities_are_dense_and_rescale_exact_values() {
        let a = Lit::positive(Var::new(0));
        let b = Lit::negative(Var::new(1));
        let c = Lit::positive(Var::new(2));
        let mut solver = Solver::with_config(SolverConfig {
            lbd_free_clause_management: false,
            ..SolverConfig::default()
        });
        solver.reserve_variables(3);

        solver.allocate_clause(vec![a, b], 0, false);
        let first = solver.allocate_clause(vec![a, c], 2, true);
        let second = solver.allocate_clause(vec![b, c], 2, true);
        let long = solver.allocate_clause(vec![a, b, c], 3, true);

        assert_eq!(solver.binary_activity_index, [NO_BINARY_ACTIVITY, 0, 1]);
        assert_eq!(solver.learned_binary_activity, [0.0, 0.0]);
        solver.learned_binary_activity = vec![20.0, 1.1e20];
        solver.clauses[long.index()].activity = 10.0;
        solver.clause_increment = 1.0;

        solver.bump_clause_activity(second);

        assert_eq!(solver.binary_activity_index[first.index()], 0);
        assert_eq!(
            solver.learned_binary_activity,
            [20.0 * 1.0e-20, 1.1e20 * 1.0e-20]
        );
        assert_eq!(solver.clauses[long.index()].activity, 1.0e-19);
        assert_eq!(solver.clause_increment, 1.0e-20);
    }

    #[test]
    fn binary_resolution_minimization_removes_matching_complements_once() {
        let a = Lit::positive(Var::new(0));
        let b = Lit::positive(Var::new(1));
        let c = Lit::positive(Var::new(2));
        let d = Lit::positive(Var::new(3));
        let e = Lit::positive(Var::new(4));
        let mut solver = Solver::with_config(SolverConfig {
            binary_resolution_minimization: true,
            ..SolverConfig::default()
        });
        solver.add_clause(&[a, b]);
        solver.add_clause(&[a, c]);
        solver.add_clause(&[a, b]);
        solver.add_clause(&[a, !d]);
        solver.add_clause(&[a, d, e]);
        solver.add_clause(&[a, e]);
        solver.mark_clause_deleted(ClauseRef::binary(4));
        solver.assignments = vec![FALSE, TRUE, TRUE, TRUE, TRUE];
        solver.levels.fill(1);

        let mut learned = vec![a, !b, !c, !d, !e];
        solver.binary_resolution_minimize(&mut learned);

        assert_eq!(learned, [a, !d, !e]);
        assert_eq!(solver.stats.binary_minimization_clauses, 1);
        assert_eq!(solver.stats.binary_minimized_literals, 2);
        assert_eq!(solver.stats.binary_minimization_watch_visits, 6);
    }

    #[test]
    fn binary_resolution_minimization_handles_negative_polarity_and_units() {
        let a = Lit::positive(Var::new(0));
        let b = Lit::positive(Var::new(1));
        let mut solver = Solver::with_config(SolverConfig {
            binary_resolution_minimization: true,
            ..SolverConfig::default()
        });
        solver.add_clause(&[!a, !b]);
        solver.assignments = vec![TRUE, FALSE];
        solver.levels.fill(1);

        let mut learned = vec![!a, b];
        solver.binary_resolution_minimize(&mut learned);

        assert_eq!(learned, [!a]);
        assert_eq!(solver.stats.binary_minimized_literals, 1);
    }

    #[test]
    fn binary_resolution_minimization_eligibility_is_bounded() {
        assert!(!Solver::eligible_for_binary_minimization(1, 1));
        assert!(Solver::eligible_for_binary_minimization(2, 6));
        assert!(Solver::eligible_for_binary_minimization(30, 6));
        assert!(!Solver::eligible_for_binary_minimization(31, 6));
        assert!(!Solver::eligible_for_binary_minimization(30, 7));
    }

    #[test]
    fn failed_literal_probing_derives_a_root_unit_from_either_polarity() {
        let x = Lit::positive(Var::new(0));
        let y = Lit::positive(Var::new(1));

        let mut positive = Solver::with_config(SolverConfig {
            failed_literal_probing: true,
            ..SolverConfig::default()
        });
        positive.add_clause(&[x, y]);
        positive.add_clause(&[x, !y]);
        let SolveResult::Sat(model) = positive.solve() else {
            panic!("formula implying x should be satisfiable");
        };
        assert!(model.literal_value(x));
        assert_eq!(positive.stats.failed_literal_units, 1);
        assert!(positive.stats.failed_literal_probes >= 2);

        let mut negative = Solver::with_config(SolverConfig {
            failed_literal_probing: true,
            ..SolverConfig::default()
        });
        negative.add_clause(&[!x, y]);
        negative.add_clause(&[!x, !y]);
        let SolveResult::Sat(model) = negative.solve() else {
            panic!("formula implying not-x should be satisfiable");
        };
        assert!(model.literal_value(!x));
        assert_eq!(negative.stats.failed_literal_units, 1);
        assert!(negative.stats.failed_literal_probes >= 1);
    }

    #[test]
    fn failed_literal_unit_can_expose_a_root_contradiction() {
        let x = Lit::positive(Var::new(0));
        let y = Lit::positive(Var::new(1));
        let z = Lit::positive(Var::new(2));
        let mut solver = Solver::with_config(SolverConfig {
            failed_literal_probing: true,
            ..SolverConfig::default()
        });
        for clause in [[x, y], [x, !y], [!x, z], [!x, !z]] {
            solver.add_clause(&clause);
        }

        assert_eq!(solver.solve(), SolveResult::Unsat);
        assert_eq!(solver.stats.failed_literal_units, 1);
        assert_eq!(solver.stats.conflicts, 0);
        assert!(solver.stats.probing_propagations > 0);
    }

    #[test]
    fn successful_probes_do_not_change_saved_phases_or_best_phase() {
        let x = Lit::positive(Var::new(0));
        let y = Lit::positive(Var::new(1));
        let mut solver = Solver::with_config(SolverConfig {
            failed_literal_probing: true,
            systematic_rephasing: true,
            ..SolverConfig::default()
        });
        solver.add_clause(&[x, y]);
        solver.phase = vec![false, true];
        solver.best_phase = vec![true, false];
        let saved_phase = solver.phase.clone();
        let best_phase = solver.best_phase.clone();

        assert!(solver.propagate().is_none());
        assert!(solver.probe_failed_literals());
        assert_eq!(solver.phase, saved_phase);
        assert_eq!(solver.best_phase, best_phase);
        assert_eq!(solver.stats.failed_literal_units, 0);
        assert_eq!(solver.stats.failed_literal_probes, 3);
        assert_eq!(solver.stats.probing_propagations, 4);
    }

    #[test]
    fn failed_literal_probe_budget_scales_and_caps() {
        let mut small = Solver::new();
        small.reserve_variables(3);
        assert_eq!(small.failed_literal_probe_budget(), 6);

        let mut capped = Solver::new();
        capped.reserve_variables(50_001);
        assert_eq!(
            capped.failed_literal_probe_budget(),
            Solver::FAILED_LITERAL_PROBE_PROPAGATION_CAP
        );
    }

    #[test]
    fn root_vivification_installs_a_conflicting_prefix_clause() {
        let a = Lit::positive(Var::new(0));
        let b = Lit::positive(Var::new(1));
        let c = Lit::positive(Var::new(2));
        let d = Lit::positive(Var::new(3));
        let mut solver = Solver::with_config(SolverConfig {
            clause_vivification: true,
            ..SolverConfig::default()
        });
        solver.add_clause(&[a, b, c]);
        solver.add_clause(&[a, b, d]);
        solver.add_clause(&[a, b, !d]);

        let SolveResult::Sat(model) = solver.solve() else {
            panic!("vivification example should be satisfiable");
        };
        assert!(model.literal_value(a) || model.literal_value(b) || model.literal_value(c));
        assert!(model.literal_value(a) || model.literal_value(b) || model.literal_value(d));
        assert!(model.literal_value(a) || model.literal_value(b) || model.literal_value(!d));
        assert!(solver.stats.vivified_clauses >= 1);
        assert!(solver.stats.vivified_literals >= 1);
        assert!(solver.clauses[0].deleted);
        assert!(solver.binary_clause_references().any(|clause| {
            !solver.clause_deleted(clause) && solver.clause_literals(clause) == [a, b]
        }));
    }

    #[test]
    fn root_vivification_uses_an_already_implied_prefix_literal() {
        let a = Lit::positive(Var::new(0));
        let b = Lit::positive(Var::new(1));
        let c = Lit::positive(Var::new(2));
        let mut solver = Solver::with_config(SolverConfig {
            clause_vivification: true,
            ..SolverConfig::default()
        });
        solver.add_clause(&[a, b, c]);
        solver.add_clause(&[a, b]);

        assert!(solver.solve().is_sat());
        assert_eq!(solver.stats.vivified_clauses, 1);
        assert_eq!(solver.stats.vivified_literals, 1);
        assert!(solver.clauses[0].deleted);
    }

    #[test]
    fn root_vivification_removes_root_false_literals() {
        let a = Lit::positive(Var::new(0));
        let b = Lit::positive(Var::new(1));
        let c = Lit::positive(Var::new(2));
        let mut solver = Solver::with_config(SolverConfig {
            clause_vivification: true,
            ..SolverConfig::default()
        });
        solver.add_clause(&[a, b, c]);
        solver.add_clause(&[!c]);

        let SolveResult::Sat(model) = solver.solve() else {
            panic!("root-simplified clause should remain satisfiable");
        };
        assert!(model.literal_value(a) || model.literal_value(b));
        assert_eq!(solver.stats.vivified_clauses, 1);
        assert_eq!(solver.stats.vivified_literals, 1);
    }

    #[test]
    fn root_vivification_drops_literals_falsified_by_earlier_assumptions() {
        let a = Lit::positive(Var::new(0));
        let b = Lit::positive(Var::new(1));
        let c = Lit::positive(Var::new(2));
        let mut solver = Solver::with_config(SolverConfig {
            clause_vivification: true,
            ..SolverConfig::default()
        });
        solver.add_clause(&[a, b, c]);
        solver.add_clause(&[a, !b]);

        let SolveResult::Sat(model) = solver.solve() else {
            panic!("vivification drop example should be satisfiable");
        };
        assert!(model.literal_value(a) || model.literal_value(c));
        assert_eq!(solver.stats.vivified_clauses, 1);
        assert_eq!(solver.stats.vivified_literals, 1);
        assert!(solver.clauses[0].deleted);
        assert!(solver.binary_clause_references().any(|clause| {
            !solver.clause_deleted(clause) && solver.clause_literals(clause) == [a, c]
        }));
    }

    #[test]
    fn root_vivification_can_derive_and_propagate_a_unit() {
        let a = Lit::positive(Var::new(0));
        let b = Lit::positive(Var::new(1));
        let c = Lit::positive(Var::new(2));
        let d = Lit::positive(Var::new(3));
        let mut solver = Solver::with_config(SolverConfig {
            clause_vivification: true,
            ..SolverConfig::default()
        });
        solver.add_clause(&[a, b, c]);
        solver.add_clause(&[a, d]);
        solver.add_clause(&[a, !d]);

        let SolveResult::Sat(model) = solver.solve() else {
            panic!("formula implying a should be satisfiable");
        };
        assert!(model.literal_value(a));
        assert_eq!(solver.stats.vivified_units, 1);
        assert_eq!(solver.stats.vivified_literals, 2);
    }

    #[test]
    fn unsuccessful_vivification_ignores_its_candidate_and_preserves_phases() {
        let a = Lit::positive(Var::new(0));
        let b = Lit::positive(Var::new(1));
        let c = Lit::positive(Var::new(2));
        let mut solver = Solver::with_config(SolverConfig {
            clause_vivification: true,
            systematic_rephasing: true,
            ..SolverConfig::default()
        });
        solver.add_clause(&[a, b, c]);
        solver.phase = vec![false, true, false];
        solver.best_phase = vec![true, false, true];
        let saved_phase = solver.phase.clone();
        let best_phase = solver.best_phase.clone();

        assert!(solver.propagate().is_none());
        assert!(solver.vivify_original_clauses());
        assert_eq!(solver.stats.vivification_checks, 1);
        assert_eq!(solver.stats.vivified_clauses, 0);
        assert_eq!(solver.phase, saved_phase);
        assert_eq!(solver.best_phase, best_phase);
        assert!(!solver.clauses[0].deleted);
    }

    #[test]
    fn root_vivification_schedule_and_effort_are_capped() {
        let a = Lit::positive(Var::new(0));
        let b = Lit::positive(Var::new(1));
        let c = Lit::positive(Var::new(2));
        let mut solver = Solver::new();
        for _ in 0..Solver::VIVIFICATION_SCHEDULE_CAP + 1 {
            solver.add_clause(&[a, b, c]);
        }
        assert_eq!(
            solver.vivification_schedule().len(),
            Solver::VIVIFICATION_SCHEDULE_CAP
        );

        solver.clause_arena.resize(
            usize::try_from(Solver::VIVIFICATION_PROPAGATION_CAP).unwrap() + 1,
            a,
        );
        assert_eq!(
            solver.vivification_budget(),
            Solver::VIVIFICATION_PROPAGATION_CAP
        );
    }

    #[test]
    fn short_clause_subsumption_removes_strict_supersets_and_duplicates_once() {
        let a = Lit::positive(Var::new(0));
        let b = Lit::positive(Var::new(1));
        let c = Lit::positive(Var::new(2));
        let mut solver = Solver::with_config(SolverConfig {
            clause_subsumption: true,
            ..SolverConfig::default()
        });
        solver.add_clause(&[a, b]);
        solver.add_clause(&[a, b, c]);
        solver.add_clause(&[a, b]);

        assert!(solver.solve().is_sat());
        assert_eq!(solver.stats.subsumed_clauses, 2);
        assert_eq!(solver.stats.subsumption_checks, 2);
        assert!(!solver.clause_deleted(ClauseRef::binary(0)));
        assert!(solver.clause_deleted(ClauseRef::long(0)));
        assert!(solver.clause_deleted(ClauseRef::binary(1)));
    }

    #[test]
    fn self_subsuming_resolution_handles_both_pivot_signs() {
        let a = Lit::positive(Var::new(0));
        let b = Lit::positive(Var::new(1));
        let c = Lit::positive(Var::new(2));
        let d = Lit::positive(Var::new(3));
        let e = Lit::positive(Var::new(4));
        let f = Lit::positive(Var::new(5));
        let mut solver = Solver::with_config(SolverConfig {
            clause_subsumption: true,
            ..SolverConfig::default()
        });
        solver.add_clause(&[a, b]);
        solver.add_clause(&[!a, b, c]);
        solver.add_clause(&[!d, e]);
        solver.add_clause(&[d, e, f]);

        let SolveResult::Sat(model) = solver.solve() else {
            panic!("SSR examples should be satisfiable");
        };
        assert!(model.literal_value(a) || model.literal_value(b));
        assert!(model.literal_value(!a) || model.literal_value(b) || model.literal_value(c));
        assert!(model.literal_value(!d) || model.literal_value(e));
        assert!(model.literal_value(d) || model.literal_value(e) || model.literal_value(f));
        assert_eq!(solver.stats.self_subsumed_clauses, 2);
        assert_eq!(solver.stats.self_subsumed_literals, 2);
        assert!(solver.clause_deleted(ClauseRef::long(0)));
        assert!(solver.clause_deleted(ClauseRef::long(1)));
        assert!(solver.binary_clause_references().any(|clause| {
            !solver.clause_deleted(clause) && solver.clause_literals(clause) == [b, c]
        }));
        assert!(solver.binary_clause_references().any(|clause| {
            !solver.clause_deleted(clause) && solver.clause_literals(clause) == [e, f]
        }));
    }

    #[test]
    fn self_subsuming_resolution_can_derive_and_propagate_a_unit() {
        let a = Lit::positive(Var::new(0));
        let b = Lit::positive(Var::new(1));
        let mut solver = Solver::with_config(SolverConfig {
            clause_subsumption: true,
            ..SolverConfig::default()
        });
        solver.add_clause(&[a, b]);
        solver.add_clause(&[!a, b]);

        let SolveResult::Sat(model) = solver.solve() else {
            panic!("SSR unit example should be satisfiable");
        };
        assert!(model.literal_value(b));
        assert_eq!(solver.stats.self_subsumed_clauses, 1);
        assert_eq!(solver.stats.self_subsumed_units, 1);
        assert!(solver.clause_deleted(ClauseRef::binary(1)));
    }

    #[test]
    fn subsumption_ignores_pairs_with_two_missing_literals_or_no_complement() {
        let a = Lit::positive(Var::new(0));
        let b = Lit::positive(Var::new(1));
        let c = Lit::positive(Var::new(2));
        let d = Lit::positive(Var::new(3));
        let e = Lit::positive(Var::new(4));
        let f = Lit::positive(Var::new(5));
        let g = Lit::positive(Var::new(6));
        let h = Lit::positive(Var::new(7));
        let i = Lit::positive(Var::new(8));
        let j = Lit::positive(Var::new(9));
        let k = Lit::positive(Var::new(10));
        let mut solver = Solver::with_config(SolverConfig {
            clause_subsumption: true,
            ..SolverConfig::default()
        });
        solver.add_clause(&[a, b, c]);
        solver.add_clause(&[a, b, d, e, f, g, h, i, j]);
        solver.add_clause(&[a, d, e, f, g, h, i, j, k]);

        assert!(solver.solve().is_sat());
        assert_eq!(solver.stats.subsumed_clauses, 0);
        assert_eq!(solver.stats.self_subsumed_clauses, 0);
        assert!(solver.clauses.iter().all(|clause| !clause.deleted));
    }

    #[test]
    fn sparse_subsumption_index_deduplicates_targets_and_skips_long_clauses() {
        let a = Lit::positive(Var::new(0));
        let b = Lit::positive(Var::new(1));
        let c = Lit::positive(Var::new(2));
        let mut solver = Solver::with_config(SolverConfig {
            clause_subsumption: true,
            ..SolverConfig::default()
        });
        solver.add_clause(&[a, b]);
        solver.add_clause(&[a, b, c]);
        let long = (0..=Solver::SUBSUMPTION_TARGET_MAX_LENGTH)
            .map(|index| Lit::positive(Var::new(index as u32)))
            .collect::<Vec<_>>();
        solver.add_clause(&long);

        assert!(solver.solve().is_sat());
        assert_eq!(solver.stats.subsumption_checks, 1);
        assert_eq!(solver.stats.subsumed_clauses, 1);
        assert!(solver.clause_deleted(ClauseRef::long(0)));
        assert!(!solver.clause_deleted(ClauseRef::long(1)));
    }

    #[test]
    fn short_subsumption_schedule_and_effort_are_capped() {
        let a = Lit::positive(Var::new(0));
        let b = Lit::positive(Var::new(1));
        let mut solver = Solver::new();
        for _ in 0..Solver::SUBSUMPTION_SCHEDULE_CAP + 1 {
            solver.add_clause(&[a, b]);
        }
        assert_eq!(
            solver
                .subsumption_schedule(solver.clauses.len(), solver.binary_literals.len())
                .len(),
            Solver::SUBSUMPTION_SCHEDULE_CAP
        );
        assert_eq!(
            Solver::bounded_subsumption_literal_touch_budget(u64::MAX),
            Solver::SUBSUMPTION_LITERAL_TOUCH_CAP
        );
        assert_eq!(Solver::bounded_subsumption_literal_touch_budget(17), 17);
    }

    #[test]
    fn elimination_resolvent_simplifies_root_values_and_tautologies() {
        let x = Lit::positive(Var::new(0));
        let a = Lit::positive(Var::new(1));
        let b = Lit::positive(Var::new(2));
        let c = Lit::positive(Var::new(3));
        let mut solver = Solver::new();
        solver.reserve_variables(4);
        solver.assignments[a.var().index()] = FALSE;
        let positive = solver.allocate_clause(vec![x, a, b], 0, false);
        let negative = solver.allocate_clause(vec![!x, b, c], 0, false);
        assert_eq!(
            solver.elimination_resolvent(positive, negative, x.var()),
            Some(vec![b, c])
        );

        let tautological = solver.allocate_clause(vec![!x, !b, c], 0, false);
        assert_eq!(
            solver.elimination_resolvent(positive, tautological, x.var()),
            None
        );

        solver.assignments[c.var().index()] = TRUE;
        assert_eq!(
            solver.elimination_resolvent(positive, negative, x.var()),
            None
        );
    }

    #[test]
    fn pure_elimination_reconstructs_both_pivot_polarities() {
        let x = Lit::positive(Var::new(0));
        let y = Lit::positive(Var::new(1));
        for (clauses, expected) in [
            (vec![vec![x, y], vec![x, !y]], true),
            (vec![vec![!x, y], vec![!x, !y]], false),
        ] {
            let mut solver = Solver::with_config(SolverConfig {
                bounded_variable_elimination: true,
                ..SolverConfig::default()
            });
            for clause in &clauses {
                solver.add_clause(clause);
            }
            let SolveResult::Sat(model) = solver.solve() else {
                panic!("pure-elimination example should be satisfiable");
            };
            assert_eq!(model.value(x.var()), expected);
            assert!(
                clauses
                    .iter()
                    .all(|clause| clause.iter().any(|&literal| model.literal_value(literal)))
            );
            assert_eq!(solver.stats.eliminated_variables, 1);
            assert_eq!(solver.stats.elimination_removed_clauses, 2);
            assert_eq!(solver.stats.elimination_resolvents, 0);
            assert_eq!(solver.stats.elimination_extension_clauses, 2);
        }
    }

    #[test]
    fn mixed_elimination_installs_a_unit_resolvent() {
        let x = Lit::positive(Var::new(0));
        let a = Lit::positive(Var::new(1));
        let mut solver = Solver::with_config(SolverConfig {
            bounded_variable_elimination: true,
            ..SolverConfig::default()
        });
        solver.add_clause(&[x, a]);
        solver.add_clause(&[!x, a]);

        let SolveResult::Sat(model) = solver.solve() else {
            panic!("unit-resolvent example should be satisfiable");
        };
        assert!(model.literal_value(a));
        assert_eq!(solver.stats.eliminated_variables, 1);
        assert_eq!(solver.stats.elimination_pairs, 1);
        assert_eq!(solver.stats.elimination_resolvents, 1);
        assert_eq!(solver.stats.elimination_units, 1);
    }

    #[test]
    fn mixed_elimination_resolvent_can_expose_unsatisfiability() {
        let x = Lit::positive(Var::new(0));
        let a = Lit::positive(Var::new(1));
        let b = Lit::positive(Var::new(2));
        let mut solver = Solver::with_config(SolverConfig {
            bounded_variable_elimination: true,
            ..SolverConfig::default()
        });
        for clause in [[x, a], [!x, b], [a, !b], [!a, b], [!a, !b]] {
            solver.add_clause(&clause);
        }

        assert!(solver.solve().is_unsat());
        assert!(solver.stats.eliminated_variables >= 1);
        assert!(solver.stats.elimination_resolvents >= 1);
        assert_eq!(
            solver.elimination_records[0].variable,
            x.var(),
            "the low-occurrence pivot should be eliminated first"
        );
    }

    #[test]
    fn elimination_rejects_growth_and_effort_overruns_without_mutation() {
        let x = Lit::positive(Var::new(0));
        let mut growth = Solver::with_config(SolverConfig {
            bounded_variable_elimination: true,
            ..SolverConfig::default()
        });
        growth.reserve_variables(9);
        for index in 1_usize..=3 {
            let tail = Lit::positive(Var::new(index as u32));
            growth.assignments[index] = FALSE;
            growth.add_clause(&[x, tail]);
        }
        for index in 4_usize..=6 {
            let tail = Lit::positive(Var::new(index as u32));
            growth.assignments[index] = FALSE;
            growth.add_clause(&[!x, tail]);
        }
        let filler_left = Lit::positive(Var::new(7));
        let filler_right = Lit::positive(Var::new(8));
        growth.assignments[7] = TRUE;
        growth.assignments[8] = TRUE;
        for _ in 0..20 {
            growth.add_clause(&[filler_left, filler_right]);
        }
        assert!(growth.eliminate_variables());
        assert_eq!(growth.stats.eliminated_variables, 0);
        assert_eq!(growth.stats.elimination_rejections, 1);
        assert_eq!(growth.stats.elimination_pairs, 7);
        assert!(growth.clauses.iter().all(|clause| !clause.deleted));

        let a = Lit::positive(Var::new(1));
        let b = Lit::positive(Var::new(2));
        let mut effort = Solver::with_config(SolverConfig {
            bounded_variable_elimination: true,
            ..SolverConfig::default()
        });
        effort.add_clause(&[x, a]);
        effort.add_clause(&[!x, b]);
        effort.assignments[a.var().index()] = FALSE;
        effort.assignments[b.var().index()] = FALSE;
        effort.stats.elimination_literal_touches = 3;
        assert!(effort.eliminate_variables());
        assert_eq!(effort.stats.eliminated_variables, 0);
        assert_eq!(effort.stats.elimination_rejections, 1);
        assert!(effort.clauses.iter().all(|clause| !clause.deleted));
    }

    #[test]
    fn exact_neighborhood_factorization_replaces_a_complete_binary_product() {
        let factors = (0..3)
            .map(|index| Lit::positive(Var::new(index)))
            .collect::<Vec<_>>();
        let quotients = (3..6)
            .map(|index| Lit::positive(Var::new(index)))
            .collect::<Vec<_>>();
        let matrix = factors
            .iter()
            .flat_map(|&factor| {
                quotients
                    .iter()
                    .map(move |&quotient| vec![factor, quotient])
            })
            .collect::<Vec<_>>();
        let mut solver = Solver::with_config(SolverConfig {
            bounded_variable_addition: true,
            ..SolverConfig::default()
        });
        solver.reserve_variables(6);
        for clause in &matrix {
            solver.add_clause(clause);
        }

        let SolveResult::Sat(model) = solver.solve() else {
            panic!("the complete clause product should be satisfiable");
        };

        assert_eq!(solver.variable_count(), 6);
        assert_eq!(solver.assignments.len(), 7);
        assert_eq!(model.len(), 6);
        assert!(
            matrix
                .iter()
                .all(|clause| clause.iter().any(|&literal| model.literal_value(literal)))
        );
        assert_eq!(solver.stats.factored_variables, 1);
        assert_eq!(solver.stats.factorization_clauses_removed, 9);
        assert_eq!(solver.stats.factorization_clauses_added, 6);
        assert_eq!(solver.stats.factorization_clause_reduction, 3);
        assert_eq!(solver.stats.factorization_peak_factors, 3);
        assert_eq!(solver.stats.factorization_peak_quotients, 3);
    }

    #[test]
    fn exact_neighborhood_factorization_supports_multi_literal_quotients() {
        let factors = (0..3)
            .map(|index| Lit::positive(Var::new(index)))
            .collect::<Vec<_>>();
        let quotients = [
            vec![Lit::positive(Var::new(3)), Lit::negative(Var::new(4))],
            vec![Lit::positive(Var::new(5)), Lit::negative(Var::new(6))],
            vec![Lit::positive(Var::new(7)), Lit::negative(Var::new(8))],
        ];
        let matrix = factors
            .iter()
            .flat_map(|&factor| {
                quotients.iter().map(move |quotient| {
                    let mut clause = vec![factor];
                    clause.extend_from_slice(quotient);
                    clause
                })
            })
            .collect::<Vec<_>>();
        let mut solver = Solver::with_config(SolverConfig {
            bounded_variable_addition: true,
            ..SolverConfig::default()
        });
        solver.reserve_variables(9);
        for clause in &matrix {
            solver.add_clause(clause);
        }

        let SolveResult::Sat(model) = solver.solve() else {
            panic!("the ternary complete product should be satisfiable");
        };
        assert_eq!(model.len(), 9);
        assert!(
            matrix
                .iter()
                .all(|clause| clause.iter().any(|&literal| model.literal_value(literal)))
        );
        assert_eq!(solver.stats.factored_variables, 1);
        assert_eq!(solver.stats.factorization_clauses_removed, 9);
        assert_eq!(solver.stats.factorization_clauses_added, 6);
    }

    #[test]
    fn exact_neighborhood_factorization_rejects_an_incomplete_product() {
        let factors = (0..3)
            .map(|index| Lit::positive(Var::new(index)))
            .collect::<Vec<_>>();
        let quotients = (3..6)
            .map(|index| Lit::positive(Var::new(index)))
            .collect::<Vec<_>>();
        let incidence = [[0, 1, 2], [0, 1, usize::MAX], [0, 2, usize::MAX]];
        let mut solver = Solver::with_config(SolverConfig {
            bounded_variable_addition: true,
            ..SolverConfig::default()
        });
        solver.reserve_variables(6);
        for (factor, neighbors) in factors.iter().zip(incidence) {
            for quotient in neighbors.into_iter().filter(|&index| index != usize::MAX) {
                solver.add_clause(&[*factor, quotients[quotient]]);
            }
        }

        assert!(solver.solve().is_sat());
        assert_eq!(solver.stats.factored_variables, 0);
        assert_eq!(solver.stats.factorization_clauses_removed, 0);
        assert_eq!(solver.stats.factorization_clauses_added, 0);
    }

    #[test]
    fn macro_factorization_density_gate_has_an_exact_sixteen_to_one_boundary() {
        let mut solver = Solver::with_config(SolverConfig {
            bounded_variable_addition: true,
            macro_bounded_variable_addition: true,
            ..SolverConfig::default()
        });
        solver.reserve_variables(2);
        solver.stats.factorization_input_short_clauses = 31;
        assert!(!solver.factorization_density_eligible());
        solver.stats.factorization_input_short_clauses = 32;
        assert!(solver.factorization_density_eligible());
        assert_eq!(solver.stats.factorization_density_checks, 2);
        assert_eq!(solver.stats.factorization_density_skips, 1);

        let empty = Lit::positive(Var::new(0));
        let mut no_variables = Solver::with_config(SolverConfig {
            bounded_variable_addition: true,
            macro_bounded_variable_addition: true,
            ..SolverConfig::default()
        });
        no_variables.stats.factorization_input_short_clauses = u64::MAX;
        assert!(!no_variables.factorization_density_eligible());
        assert_eq!(no_variables.stats.factorization_density_skips, 1);
        assert_eq!(empty.var(), Var::new(0));
    }

    #[test]
    fn macro_factorization_counts_only_normalized_short_input_clauses() {
        let a = Lit::positive(Var::new(0));
        let b = Lit::positive(Var::new(1));
        let c = Lit::positive(Var::new(2));
        let d = Lit::positive(Var::new(3));
        let e = Lit::positive(Var::new(4));
        let f = Lit::positive(Var::new(5));
        let mut solver = Solver::with_config(SolverConfig {
            bounded_variable_addition: true,
            macro_bounded_variable_addition: true,
            ..SolverConfig::default()
        });
        solver.add_clause(&[a]);
        solver.add_clause(&[a, b, a]);
        solver.add_clause(&[a, !a, b]);
        solver.add_clause(&[a, b, c, d, e]);
        solver.add_clause(&[a, b, c, d, e, f]);

        assert_eq!(solver.stats.factorization_input_short_clauses, 2);
    }

    #[test]
    fn macro_factorization_requires_at_least_half_matrix_reduction() {
        fn plans(factor_count: u32, quotient_count: u32) -> (Vec<super::FactorPlan>, u64) {
            let mut solver = Solver::with_config(SolverConfig {
                bounded_variable_addition: true,
                macro_bounded_variable_addition: true,
                ..SolverConfig::default()
            });
            let quotients = (factor_count..factor_count + quotient_count)
                .map(|index| Lit::positive(Var::new(index)))
                .collect::<Vec<_>>();
            for factor_index in 0..factor_count {
                let factor = Lit::positive(Var::new(factor_index));
                for &quotient in &quotients {
                    solver.add_clause(&[factor, quotient]);
                }
            }
            let snapshot = solver.factor_snapshot();
            let plans = solver
                .exact_factor_plans(&snapshot, u64::MAX)
                .expect("the small snapshot stays within budget");
            (plans, solver.stats.factorization_macro_rejections)
        }

        let (below_half, rejections) = plans(3, 5);
        assert!(below_half.is_empty());
        assert!(rejections > 0);

        let (at_half, _) = plans(3, 6);
        assert!(!at_half.is_empty());
        assert!(at_half.iter().all(|plan| {
            plan.matrix.len() >= 2_usize.saturating_mul(plan.factors.len() + plan.quotients.len())
        }));
    }

    #[test]
    fn macro_factorization_skips_snapshot_work_on_sparse_input() {
        let factors = (0..3)
            .map(|index| Lit::positive(Var::new(index)))
            .collect::<Vec<_>>();
        let quotients = (3..6)
            .map(|index| Lit::positive(Var::new(index)))
            .collect::<Vec<_>>();
        let mut solver = Solver::with_config(SolverConfig {
            bounded_variable_addition: true,
            macro_bounded_variable_addition: true,
            ..SolverConfig::default()
        });
        solver.reserve_variables(6);
        for &factor in &factors {
            for &quotient in &quotients {
                solver.add_clause(&[factor, quotient]);
            }
        }

        assert!(solver.solve().is_sat());
        assert_eq!(solver.stats.factorization_input_short_clauses, 9);
        assert_eq!(solver.stats.factorization_density_checks, 1);
        assert_eq!(solver.stats.factorization_density_skips, 1);
        assert_eq!(solver.stats.factorization_rounds, 0);
        assert_eq!(solver.stats.factored_variables, 0);
    }

    #[test]
    fn reverse_extension_honors_dependencies_between_eliminated_variables() {
        let x = Lit::positive(Var::new(0));
        let y = Lit::positive(Var::new(1));
        let z = Lit::positive(Var::new(2));
        let mut solver = Solver::new();
        solver.elimination_records.push(EliminationRecord {
            variable: x.var(),
            clauses: vec![vec![x, y]],
        });
        solver.elimination_records.push(EliminationRecord {
            variable: y.var(),
            clauses: vec![vec![!y, z]],
        });
        let mut values = vec![false, true, false];

        solver.extend_model(&mut values);

        assert_eq!(values, [true, false, false]);
    }

    #[test]
    fn lbd_free_scores_initialize_and_saturate_on_bcp_and_analysis_use() {
        let mut solver = Solver::with_config(SolverConfig {
            lbd_free_clause_management: true,
            ..SolverConfig::default()
        });
        solver.reserve_variables(8);
        let a = Lit::positive(Var::new(0));
        let b = Lit::positive(Var::new(1));
        let c = Lit::positive(Var::new(2));
        let original = solver.allocate_clause(
            vec![
                Lit::positive(Var::new(3)),
                Lit::positive(Var::new(4)),
                Lit::positive(Var::new(5)),
            ],
            0,
            false,
        );
        let learned = solver.allocate_clause(vec![a, b, c], 7, true);
        let learned_binary = solver.allocate_clause(
            vec![Lit::positive(Var::new(6)), Lit::positive(Var::new(7))],
            2,
            true,
        );
        solver.attach_clause(learned);

        assert_eq!(solver.clause_usage_scores, [0, 1]);
        assert_eq!(solver.clause_usage_scores.len(), solver.clauses.len());
        assert!(learned_binary.is_binary());

        assert!(solver.enqueue(!b, None));
        assert_eq!(solver.propagate(), None);
        assert!(solver.enqueue(!c, None));
        assert_eq!(solver.propagate(), None);
        assert_eq!(solver.assignments[a.var().index()], TRUE);
        assert_eq!(solver.clause_usage_scores[learned.index()], 2);
        assert_eq!(solver.stats.clause_usage_bcp_increments, 1);

        solver.bump_clause_activity(learned);
        assert_eq!(solver.clause_usage_scores[learned.index()], 3);
        assert_eq!(solver.stats.clause_usage_analysis_increments, 1);
        assert_eq!(solver.clauses[learned.index()].activity, 0.0);

        solver.bump_clause_activity(original);
        solver.bump_clause_activity(learned_binary);
        assert_eq!(solver.stats.clause_usage_analysis_increments, 1);
        assert_eq!(solver.learned_binary_activity, [0.0]);

        solver.clause_usage_scores[learned.index()] = u32::MAX;
        solver.bump_clause_usage(learned, ClauseUsageUse::Propagation);
        assert_eq!(solver.clause_usage_scores[learned.index()], u32::MAX);
        assert_eq!(solver.stats.clause_usage_bcp_increments, 2);
    }

    #[test]
    fn lbd_free_decay_uses_exact_interval_and_skips_original_and_deleted_clauses() {
        assert!(!Solver::should_decay_clause_usage(0));
        assert!(!Solver::should_decay_clause_usage(2_047));
        assert!(Solver::should_decay_clause_usage(2_048));
        assert!(!Solver::should_decay_clause_usage(2_049));
        assert!(Solver::should_decay_clause_usage(4_096));

        let mut solver = Solver::with_config(SolverConfig {
            lbd_free_clause_management: true,
            ..SolverConfig::default()
        });
        solver.reserve_variables(4);
        let literals = vec![
            Lit::positive(Var::new(0)),
            Lit::positive(Var::new(1)),
            Lit::positive(Var::new(2)),
        ];
        let original = solver.allocate_clause(literals.clone(), 0, false);
        let live = solver.allocate_clause(literals.clone(), 5, true);
        let deleted = solver.allocate_clause(literals.clone(), 6, true);
        let zero = solver.allocate_clause(literals, 7, true);
        solver.clause_usage_scores[original.index()] = 9;
        solver.clause_usage_scores[live.index()] = 3;
        solver.clause_usage_scores[deleted.index()] = 7;
        solver.clause_usage_scores[zero.index()] = 0;
        solver.mark_clause_deleted(deleted);

        solver.decay_clause_usage_scores();

        assert_eq!(solver.clause_usage_scores[original.index()], 9);
        assert_eq!(solver.clause_usage_scores[live.index()], 2);
        assert_eq!(solver.clause_usage_scores[deleted.index()], 7);
        assert_eq!(solver.clause_usage_scores[zero.index()], 0);
        assert_eq!(solver.stats.clause_usage_decay_passes, 1);
        assert_eq!(solver.stats.clause_usage_scores_decayed, 1);
    }

    #[test]
    fn lbd_free_reduction_protects_use_and_locks_then_deletes_longest_zero_scores() {
        let mut solver = Solver::with_config(SolverConfig {
            lbd_free_clause_management: true,
            ..SolverConfig::default()
        });
        solver.reserve_variables(12);
        let literals = (0..12)
            .map(|index| Lit::positive(Var::new(index)))
            .collect::<Vec<_>>();
        let positive = solver.allocate_clause(literals[..12].to_vec(), 20, true);
        let locked = solver.allocate_clause(literals[..11].to_vec(), 19, true);
        let longest = solver.allocate_clause(literals[..10].to_vec(), 2, true);
        let tied_earlier = solver.allocate_clause(literals[..8].to_vec(), 2, true);
        let tied_later = solver.allocate_clause(literals[..8].to_vec(), 20, true);
        let medium = solver.allocate_clause(literals[..6].to_vec(), 20, true);
        let short = solver.allocate_clause(literals[..4].to_vec(), 20, true);
        solver.clause_usage_scores.fill(0);
        solver.clause_usage_scores[positive.index()] = 4;
        solver.reasons[0] = Some(locked);
        solver.clauses[longest.index()].activity = 1.0e10;
        solver.clauses[tied_earlier.index()].activity = 1.0e10;

        solver.reduce_database();

        assert!(!solver.clause_deleted(positive));
        assert!(!solver.clause_deleted(locked));
        assert!(solver.clause_deleted(longest));
        assert!(solver.clause_deleted(tied_earlier));
        assert!(!solver.clause_deleted(tied_later));
        assert!(!solver.clause_deleted(medium));
        assert!(!solver.clause_deleted(short));
        assert_eq!(solver.stats.reductions, 1);
        assert_eq!(solver.stats.deleted_clauses, 2);
        assert_eq!(solver.stats.clause_usage_positive_protections, 1);
        assert_eq!(solver.stats.clause_usage_zero_candidates, 5);
    }

    #[test]
    fn lbd_free_fraction_and_square_root_schedule_match_the_frozen_policy() {
        assert!((Solver::lbd_free_deletion_fraction(1) - 0.5).abs() < f64::EPSILON);
        assert!(
            (Solver::lbd_free_deletion_fraction(10) - (0.90 - 0.40 / 19_f64.log10())).abs()
                < f64::EPSILON
        );
        assert!(Solver::lbd_free_deletion_fraction(1_000_000) < 0.90);
        assert_eq!(Solver::lbd_free_reduction_interval(1), 1_000);
        assert_eq!(Solver::lbd_free_reduction_interval(2), 1_414);
        assert_eq!(Solver::lbd_free_reduction_interval(9), 3_000);

        let treatment = Solver::with_config(SolverConfig {
            lbd_free_clause_management: true,
            ..SolverConfig::default()
        });
        let control = Solver::with_config(SolverConfig {
            lbd_free_clause_management: false,
            ..SolverConfig::default()
        });
        assert_eq!(treatment.next_reduction, 1_000);
        assert_eq!(control.next_reduction, 2_000);
    }

    #[test]
    fn lbd_free_score_metadata_is_optional_and_stable_across_compaction() {
        let literals = vec![
            Lit::positive(Var::new(0)),
            Lit::positive(Var::new(1)),
            Lit::positive(Var::new(2)),
        ];
        let mut control = Solver::with_config(SolverConfig {
            lbd_free_clause_management: false,
            ..SolverConfig::default()
        });
        control.reserve_variables(5);
        control.allocate_clause(literals.clone(), 0, false);
        control.allocate_clause(literals.clone(), 4, true);
        assert!(control.clause_usage_scores.is_empty());

        let mut treatment = Solver::with_config(SolverConfig {
            lbd_free_clause_management: true,
            compact_clause_arena: true,
            ..SolverConfig::default()
        });
        treatment.reserve_variables(5);
        let prefix = treatment.allocate_clause(literals, 0, false);
        let deleted = treatment.allocate_clause(
            vec![
                Lit::positive(Var::new(1)),
                Lit::positive(Var::new(2)),
                Lit::positive(Var::new(3)),
                Lit::positive(Var::new(4)),
            ],
            8,
            true,
        );
        let live = treatment.allocate_clause(
            vec![
                Lit::positive(Var::new(0)),
                Lit::positive(Var::new(3)),
                Lit::positive(Var::new(4)),
            ],
            3,
            true,
        );
        treatment.clause_usage_scores[deleted.index()] = 5;
        treatment.clause_usage_scores[live.index()] = 7;
        treatment.mark_clause_deleted(deleted);
        treatment.compact_clause_arena();

        assert_eq!(treatment.clause_usage_scores, [0, 5, 7]);
        assert_eq!(treatment.clause_usage_scores.len(), treatment.clauses.len());
        assert_eq!(treatment.clause_literals(prefix).len(), 3);
        assert_eq!(treatment.clause_literals(live).len(), 3);
        assert_eq!(treatment.clause_arena.len(), 6);
    }

    #[test]
    fn scan_debt_charges_exact_watch_work_and_resets_only_on_beneficial_use() {
        let mut solver = Solver::with_config(SolverConfig {
            scan_debt_clause_management: true,
            ..SolverConfig::default()
        });
        solver.reserve_variables(6);
        let a = Lit::positive(Var::new(0));
        let b = Lit::positive(Var::new(1));
        let c = Lit::positive(Var::new(2));
        let d = Lit::positive(Var::new(3));
        let learned = solver.allocate_clause(vec![a, b, c, d], 4, true);
        let original = solver.allocate_clause(
            vec![
                Lit::positive(Var::new(3)),
                Lit::positive(Var::new(4)),
                Lit::positive(Var::new(5)),
            ],
            0,
            false,
        );
        let binary = solver.allocate_clause(
            vec![Lit::positive(Var::new(4)), Lit::positive(Var::new(5))],
            2,
            true,
        );
        solver.attach_clause(learned);

        assert!(solver.enqueue(!a, None));
        assert_eq!(solver.propagate(), None);
        assert_eq!(solver.clause_scan_debt[learned.index()], 3);

        assert!(solver.enqueue(!c, None));
        assert_eq!(solver.propagate(), None);
        assert_eq!(solver.clause_scan_debt[learned.index()], 7);

        assert!(solver.enqueue(!d, None));
        assert_eq!(solver.propagate(), None);
        assert_eq!(solver.assignments[b.var().index()], TRUE);
        assert_eq!(solver.clause_scan_debt[learned.index()], 0);
        assert_eq!(solver.stats.clause_scan_debt_literal_checks, 11);
        assert_eq!(solver.stats.clause_scan_debt_nonzero_resets, 1);
        assert_eq!(solver.stats.clause_scan_debt_peak, 11);

        solver.charge_clause_scan_debt(learned, 5);
        solver.bump_clause_activity(learned);
        assert_eq!(solver.clause_scan_debt[learned.index()], 0);
        assert_eq!(solver.stats.clause_scan_debt_nonzero_resets, 2);

        let charged_before = solver.stats.clause_scan_debt_literal_checks;
        solver.charge_clause_scan_debt(original, 9);
        solver.charge_clause_scan_debt(binary, 9);
        assert_eq!(solver.stats.clause_scan_debt_literal_checks, charged_before);

        solver.clause_scan_debt[learned.index()] = u64::MAX;
        solver.charge_clause_scan_debt(learned, 1);
        assert_eq!(solver.clause_scan_debt[learned.index()], u64::MAX);
        assert_eq!(solver.stats.clause_scan_debt_peak, u64::MAX);
    }

    #[test]
    fn scan_debt_excludes_probe_and_vivification_propagation() {
        for vivification in [false, true] {
            let mut solver = Solver::with_config(SolverConfig {
                scan_debt_clause_management: true,
                ..SolverConfig::default()
            });
            solver.reserve_variables(3);
            let a = Lit::positive(Var::new(0));
            let b = Lit::positive(Var::new(1));
            let c = Lit::positive(Var::new(2));
            let learned = solver.allocate_clause(vec![a, b, c], 3, true);
            solver.attach_clause(learned);
            assert!(solver.enqueue_internal::<false>(!a, None));

            let conflict = if vivification {
                solver.propagate_vivification::<false>(None)
            } else {
                solver.propagate_probe::<false>()
            };

            assert_eq!(conflict, None);
            assert_eq!(solver.clause_scan_debt[learned.index()], 0);
            assert_eq!(solver.stats.clause_scan_debt_literal_checks, 0);
            assert_eq!(solver.stats.clause_scan_debt_nonzero_resets, 0);
        }
    }

    #[test]
    fn scan_debt_zero_state_reproduces_promoted_reduction_exactly() {
        let mut solver = Solver::with_config(SolverConfig {
            scan_debt_clause_management: true,
            ..SolverConfig::default()
        });
        solver.reserve_variables(12);
        let literals = (0..12)
            .map(|index| Lit::positive(Var::new(index)))
            .collect::<Vec<_>>();
        let positive = solver.allocate_clause(literals[..12].to_vec(), 20, true);
        let locked = solver.allocate_clause(literals[..11].to_vec(), 19, true);
        let longest = solver.allocate_clause(literals[..10].to_vec(), 2, true);
        let tied_earlier = solver.allocate_clause(literals[..8].to_vec(), 2, true);
        let tied_later = solver.allocate_clause(literals[..8].to_vec(), 20, true);
        let medium = solver.allocate_clause(literals[..6].to_vec(), 20, true);
        let short = solver.allocate_clause(literals[..4].to_vec(), 20, true);
        solver.clause_usage_scores.fill(0);
        solver.clause_usage_scores[positive.index()] = 4;
        solver.reasons[0] = Some(locked);

        solver.reduce_database();

        assert!(!solver.clause_deleted(positive));
        assert!(!solver.clause_deleted(locked));
        assert!(solver.clause_deleted(longest));
        assert!(solver.clause_deleted(tied_earlier));
        assert!(!solver.clause_deleted(tied_later));
        assert!(!solver.clause_deleted(medium));
        assert!(!solver.clause_deleted(short));
        assert_eq!(solver.stats.deleted_clauses, 2);
        assert_eq!(solver.stats.clause_usage_zero_candidates, 5);
        assert_eq!(solver.stats.clause_usage_positive_protections, 1);
        assert_eq!(solver.stats.clause_scan_debt_selection_displacements, 0);
        assert_eq!(solver.stats.clause_scan_debt_positive_deletions, 0);
        assert_eq!(solver.stats.clause_scan_debt_zero_rescues, 0);
    }

    #[test]
    fn scan_debt_displaces_baseline_deletions_without_changing_the_quota() {
        let mut solver = Solver::with_config(SolverConfig {
            scan_debt_clause_management: true,
            ..SolverConfig::default()
        });
        solver.reserve_variables(12);
        let literals = (0..12)
            .map(|index| Lit::positive(Var::new(index)))
            .collect::<Vec<_>>();
        let zero_long = solver.allocate_clause(literals[..10].to_vec(), 10, true);
        let zero_medium = solver.allocate_clause(literals[..8].to_vec(), 10, true);
        let zero_debt = solver.allocate_clause(literals[..6].to_vec(), 10, true);
        let zero_short = solver.allocate_clause(literals[..4].to_vec(), 10, true);
        let positive_debt = solver.allocate_clause(literals[..5].to_vec(), 10, true);
        let positive_clean = solver.allocate_clause(literals[..3].to_vec(), 10, true);
        let locked = solver.allocate_clause(literals[..12].to_vec(), 10, true);
        solver.clause_usage_scores.fill(0);
        solver.clause_usage_scores[positive_debt.index()] = 1;
        solver.clause_usage_scores[positive_clean.index()] = 7;
        solver.clause_scan_debt[positive_debt.index()] = 100;
        solver.clause_scan_debt[zero_debt.index()] = 50;
        solver.clause_scan_debt[locked.index()] = u64::MAX;
        solver.reasons[0] = Some(locked);

        solver.reduce_database();

        assert_eq!(solver.stats.deleted_clauses, 2);
        assert!(solver.clause_deleted(positive_debt));
        assert!(solver.clause_deleted(zero_debt));
        assert!(!solver.clause_deleted(zero_long));
        assert!(!solver.clause_deleted(zero_medium));
        assert!(!solver.clause_deleted(zero_short));
        assert!(!solver.clause_deleted(positive_clean));
        assert!(!solver.clause_deleted(locked));
        assert_eq!(solver.stats.clause_usage_zero_candidates, 4);
        assert_eq!(solver.stats.clause_usage_positive_protections, 1);
        assert_eq!(solver.stats.clause_scan_debt_selection_displacements, 2);
        assert_eq!(solver.stats.clause_scan_debt_positive_deletions, 1);
        assert_eq!(solver.stats.clause_scan_debt_zero_rescues, 2);
    }

    #[test]
    fn scan_debt_metadata_is_optional_and_stays_aligned_across_compaction() {
        let literals = vec![
            Lit::positive(Var::new(0)),
            Lit::positive(Var::new(1)),
            Lit::positive(Var::new(2)),
        ];
        let mut control = Solver::new();
        control.reserve_variables(4);
        control.allocate_clause(literals.clone(), 0, false);
        control.allocate_clause(literals.clone(), 4, true);
        assert!(control.clause_scan_debt.is_empty());

        let mut treatment = Solver::with_config(SolverConfig {
            scan_debt_clause_management: true,
            compact_clause_arena: true,
            ..SolverConfig::default()
        });
        treatment.reserve_variables(4);
        treatment.allocate_clause(literals.clone(), 0, false);
        let deleted = treatment.allocate_clause(literals.clone(), 4, true);
        let live = treatment.allocate_clause(literals, 4, true);
        treatment.clause_scan_debt[deleted.index()] = 13;
        treatment.clause_scan_debt[live.index()] = 21;
        treatment.mark_clause_deleted(deleted);
        treatment.compact_clause_arena();

        assert_eq!(treatment.clause_scan_debt, [0, 13, 21]);
        assert_eq!(treatment.clause_scan_debt.len(), treatment.clauses.len());
        assert_eq!(treatment.clause_literals(live).len(), 3);
    }

    #[test]
    #[should_panic(expected = "scan-debt clause management requires LBD-free clause management")]
    fn scan_debt_rejects_the_legacy_reducer() {
        let _solver = Solver::with_config(SolverConfig {
            lbd_free_clause_management: false,
            scan_debt_clause_management: true,
            ..SolverConfig::default()
        });
    }

    #[test]
    fn regularity_metadata_is_optional_aligned_for_both_stores_and_compaction_stable() {
        let long_literals = vec![
            Lit::positive(Var::new(0)),
            Lit::positive(Var::new(1)),
            Lit::positive(Var::new(2)),
        ];
        let binary_literals = vec![Lit::positive(Var::new(3)), Lit::positive(Var::new(4))];

        let mut control = Solver::new();
        control.reserve_variables(6);
        control.allocate_clause(long_literals.clone(), 0, false);
        control.allocate_clause(binary_literals.clone(), 0, false);
        assert!(control.regularity_long_samples.is_empty());
        assert!(control.regularity_long_states.is_empty());
        assert!(control.regularity_binary_samples.is_empty());
        assert!(control.regularity_binary_states.is_empty());
        assert_eq!(control.stats().regularity_metadata_bytes, 0);

        let mut treatment = Solver::with_config(SolverConfig {
            nonregular_clause_retention: true,
            compact_clause_arena: true,
            ..SolverConfig::default()
        });
        treatment.reserve_variables(6);
        treatment.allocate_clause(long_literals.clone(), 0, false);
        let deleted = treatment.allocate_clause(long_literals.clone(), 4, true);
        let live = treatment.allocate_clause(long_literals, 5, true);
        treatment.allocate_clause(binary_literals.clone(), 0, false);
        let binary = treatment.allocate_clause(binary_literals, 2, true);

        let mut deleted_ancestry = DerivationAncestry::empty();
        deleted_ancestry.insert(Var::new(1));
        treatment.set_clause_derivation_ancestry(deleted, deleted_ancestry);
        let mut live_ancestry = DerivationAncestry::empty();
        live_ancestry.insert(Var::new(2));
        live_ancestry.set_nonregular();
        treatment.set_clause_derivation_ancestry(live, live_ancestry);
        let mut binary_ancestry = DerivationAncestry::empty();
        binary_ancestry.insert(Var::new(4));
        binary_ancestry.set_nonregular();
        treatment.set_clause_derivation_ancestry(binary, binary_ancestry);

        treatment.mark_clause_deleted(deleted);
        treatment.compact_clause_arena();

        assert_eq!(
            treatment.regularity_long_samples.len(),
            treatment.clauses.len()
        );
        assert_eq!(
            treatment.regularity_long_states.len(),
            treatment.clauses.len()
        );
        assert_eq!(
            treatment.regularity_binary_samples.len(),
            treatment.binary_literals.len()
        );
        assert_eq!(
            treatment.regularity_binary_states.len(),
            treatment.binary_literals.len()
        );
        assert_eq!(
            treatment.clause_derivation_ancestry(deleted),
            deleted_ancestry
        );
        assert_eq!(treatment.clause_derivation_ancestry(live), live_ancestry);
        assert_eq!(
            treatment.clause_derivation_ancestry(binary),
            binary_ancestry
        );
        let clause_count = treatment
            .clauses
            .len()
            .saturating_add(treatment.binary_literals.len());
        assert_eq!(
            treatment.stats().regularity_metadata_bytes,
            u64::try_from(clause_count * 17).unwrap()
        );
    }

    #[test]
    fn all_regular_retention_reproduces_promoted_reduction_exactly() {
        let mut control = Solver::new();
        let mut treatment = Solver::with_config(SolverConfig {
            nonregular_clause_retention: true,
            ..SolverConfig::default()
        });
        for solver in [&mut control, &mut treatment] {
            solver.reserve_variables(12);
            let literals = (0..12)
                .map(|index| Lit::positive(Var::new(index)))
                .collect::<Vec<_>>();
            for length in [12, 11, 10, 8, 8, 6, 4] {
                solver.allocate_clause(literals[..length].to_vec(), 20, true);
            }
            solver.clause_usage_scores.fill(0);
            solver.clause_usage_scores[0] = 3;
            solver.reasons[0] = Some(ClauseRef::long(1));
            solver.reduce_database();
        }

        assert_eq!(
            control
                .clauses
                .iter()
                .map(|clause| clause.deleted)
                .collect::<Vec<_>>(),
            treatment
                .clauses
                .iter()
                .map(|clause| clause.deleted)
                .collect::<Vec<_>>()
        );
        assert_eq!(
            control.stats.deleted_clauses,
            treatment.stats.deleted_clauses
        );
        assert_eq!(treatment.stats.regularity_selection_displacements, 0);
        assert_eq!(treatment.stats.regularity_nonregular_rescues, 0);
        assert_eq!(treatment.stats.regularity_nonregular_deletions, 0);
    }

    #[test]
    fn nonregular_retention_displaces_one_baseline_deletion_at_fixed_quota() {
        let mut solver = Solver::with_config(SolverConfig {
            nonregular_clause_retention: true,
            ..SolverConfig::default()
        });
        solver.reserve_variables(12);
        let literals = (0..12)
            .map(|index| Lit::positive(Var::new(index)))
            .collect::<Vec<_>>();
        let witnessed_long = solver.allocate_clause(literals[..12].to_vec(), 20, true);
        let regular_11 = solver.allocate_clause(literals[..11].to_vec(), 20, true);
        let regular_10 = solver.allocate_clause(literals[..10].to_vec(), 20, true);
        let regular_9 = solver.allocate_clause(literals[..9].to_vec(), 20, true);
        let witnessed_8 = solver.allocate_clause(literals[..8].to_vec(), 20, true);
        let regular_7 = solver.allocate_clause(literals[..7].to_vec(), 20, true);
        solver.clause_usage_scores.fill(0);
        let mut witness = DerivationAncestry::empty();
        witness.set_nonregular();
        solver.set_clause_derivation_ancestry(witnessed_long, witness);
        solver.set_clause_derivation_ancestry(witnessed_8, witness);

        solver.reduce_database();

        assert!(!solver.clause_deleted(witnessed_long));
        assert!(solver.clause_deleted(regular_11));
        assert!(solver.clause_deleted(regular_10));
        assert!(solver.clause_deleted(regular_9));
        assert!(!solver.clause_deleted(witnessed_8));
        assert!(!solver.clause_deleted(regular_7));
        assert_eq!(solver.stats.deleted_clauses, 3);
        assert_eq!(solver.stats.clause_usage_zero_candidates, 6);
        assert_eq!(solver.stats.regularity_nonregular_zero_candidates, 2);
        assert_eq!(solver.stats.regularity_selection_displacements, 1);
        assert_eq!(solver.stats.regularity_nonregular_rescues, 1);
        assert_eq!(solver.stats.regularity_nonregular_deletions, 0);
    }

    #[test]
    fn nonregular_retention_deletes_witnesses_when_regular_pool_is_exhausted() {
        let mut solver = Solver::with_config(SolverConfig {
            nonregular_clause_retention: true,
            ..SolverConfig::default()
        });
        solver.reserve_variables(12);
        let literals = (0..12)
            .map(|index| Lit::positive(Var::new(index)))
            .collect::<Vec<_>>();
        let witnessed_12 = solver.allocate_clause(literals[..12].to_vec(), 20, true);
        let witnessed_10 = solver.allocate_clause(literals[..10].to_vec(), 20, true);
        let witnessed_8 = solver.allocate_clause(literals[..8].to_vec(), 20, true);
        let regular_4 = solver.allocate_clause(literals[..4].to_vec(), 20, true);
        solver.clause_usage_scores.fill(0);
        let mut witness = DerivationAncestry::empty();
        witness.set_nonregular();
        for clause in [witnessed_12, witnessed_10, witnessed_8] {
            solver.set_clause_derivation_ancestry(clause, witness);
        }

        solver.reduce_database();

        assert!(solver.clause_deleted(regular_4));
        assert!(solver.clause_deleted(witnessed_12));
        assert!(!solver.clause_deleted(witnessed_10));
        assert!(!solver.clause_deleted(witnessed_8));
        assert_eq!(solver.stats.deleted_clauses, 2);
        assert_eq!(solver.stats.regularity_selection_displacements, 1);
        assert_eq!(solver.stats.regularity_nonregular_rescues, 1);
        assert_eq!(solver.stats.regularity_nonregular_deletions, 1);
    }

    #[test]
    #[should_panic(expected = "nonregular clause retention requires LBD-free clause management")]
    fn nonregular_retention_rejects_the_legacy_reducer() {
        let _solver = Solver::with_config(SolverConfig {
            lbd_free_clause_management: false,
            nonregular_clause_retention: true,
            ..SolverConfig::default()
        });
    }

    #[test]
    #[should_panic(
        expected = "nonregular clause retention is incompatible with scan-debt clause management"
    )]
    fn nonregular_retention_rejects_scan_debt_ranking() {
        let _solver = Solver::with_config(SolverConfig {
            scan_debt_clause_management: true,
            nonregular_clause_retention: true,
            ..SolverConfig::default()
        });
    }

    #[test]
    fn shadow_clause_rank_matches_the_frozen_splitmix_policy() {
        assert_eq!(shadow_clause_rank(0, 1), 14_135_772_400_868_000_056);
        assert_eq!(shadow_clause_rank(1, 1), 2_324_861_979_054_413_167);
        assert_eq!(shadow_clause_rank(63, 1), 8_180_459_214_492_928_684);
        assert_eq!(shadow_clause_rank(0, 2), 16_695_506_628_682_495_282);
        assert_eq!(shadow_clause_rank(123_456, 789), 17_590_868_661_875_658_749);
    }

    #[test]
    fn shadow_metadata_is_optional_and_aligned_only_with_long_clauses() {
        let long = vec![
            Lit::positive(Var::new(0)),
            Lit::positive(Var::new(1)),
            Lit::positive(Var::new(2)),
        ];
        let binary = vec![Lit::positive(Var::new(3)), Lit::positive(Var::new(4))];

        let mut control = Solver::new();
        control.reserve_variables(5);
        control.allocate_clause(long.clone(), 0, false);
        control.allocate_clause(long.clone(), 3, true);
        control.allocate_clause(binary.clone(), 2, true);
        assert!(control.shadow_clause_states.is_empty());
        assert!(control.shadow_clause_started_at.is_empty());
        assert!(control.shadow_clauses.is_empty());
        assert_eq!(control.stats().shadow_metadata_bytes, 0);

        let mut treatment = Solver::with_config(SolverConfig {
            shadow_clause_reactivation: true,
            ..SolverConfig::default()
        });
        treatment.reserve_variables(5);
        treatment.allocate_clause(long.clone(), 0, false);
        let learned = treatment.allocate_clause(long, 3, true);
        treatment.allocate_clause(binary, 2, true);
        assert_eq!(treatment.shadow_clause_states, [SHADOW_ACTIVE; 2]);
        assert_eq!(treatment.shadow_clause_started_at, [0; 2]);
        assert!(treatment.shadow_clauses.is_empty());
        assert_eq!(treatment.stats().shadow_metadata_bytes, 18);

        treatment.clause_usage_scores[learned.index()] = 0;
        treatment.active_learned_clauses = 1;
        treatment.begin_shadow_observation(learned.index());
        assert_eq!(treatment.stats().shadow_metadata_bytes, 26);
    }

    #[test]
    fn shadow_reduction_preserves_the_control_quota_and_frozen_capacity() {
        let mut solver = Solver::with_config(SolverConfig {
            shadow_clause_reactivation: true,
            ..SolverConfig::default()
        });
        solver.reserve_variables(3);
        let literals = vec![
            Lit::positive(Var::new(0)),
            Lit::positive(Var::new(1)),
            Lit::positive(Var::new(2)),
        ];
        for _ in 0..132 {
            let clause = solver.allocate_clause(literals.clone(), 8, true);
            solver.attach_clause(clause);
        }
        solver.clause_usage_scores.fill(0);
        solver.active_learned_clauses = 132;

        let mut ranked = (0..66).collect::<Vec<_>>();
        ranked.sort_unstable_by(|&left, &right| {
            shadow_clause_rank(left, 1)
                .cmp(&shadow_clause_rank(right, 1))
                .then_with(|| left.cmp(&right))
        });
        let selected = ranked[..Solver::SHADOW_CAPACITY].to_vec();
        let permanently_deleted = ranked[Solver::SHADOW_CAPACITY..].to_vec();

        solver.reduce_database();

        assert_eq!(solver.stats.reductions, 1);
        assert_eq!(solver.stats.clause_usage_zero_candidates, 132);
        assert_eq!(solver.shadow_clauses.len(), Solver::SHADOW_CAPACITY);
        assert_eq!(solver.stats.shadow_clauses_started, 64);
        assert_eq!(solver.stats.shadow_active_peak, 64);
        assert_eq!(solver.stats.shadow_capacity_skips, 2);
        assert_eq!(solver.stats.shadow_effective_removals, 66);
        assert_eq!(solver.stats.deleted_clauses, 2);
        assert_eq!(solver.active_learned_clauses, 66);
        for reference in selected {
            assert_eq!(
                solver.shadow_clause_states[reference], SHADOW_OBSERVING,
                "selected reference {reference} must remain as a shadow"
            );
            assert!(!solver.clauses[reference].deleted);
        }
        for reference in permanently_deleted {
            assert!(solver.clauses[reference].deleted);
            assert_eq!(solver.shadow_clause_states[reference], SHADOW_ACTIVE);
        }
        for reference in 66..132 {
            assert!(!solver.clauses[reference].deleted);
            assert_eq!(solver.shadow_clause_states[reference], SHADOW_ACTIVE);
        }

        let second_candidates = 66_usize;
        let second_deletions =
            (Solver::lbd_free_deletion_fraction(2) * second_candidates as f64).floor() as usize;
        solver.reduce_database();
        assert_eq!(solver.stats.reductions, 2);
        assert_eq!(solver.shadow_clauses.len(), Solver::SHADOW_CAPACITY);
        assert_eq!(
            solver.stats.shadow_capacity_skips,
            u64::try_from(2 + second_deletions).unwrap()
        );
        assert_eq!(
            solver.stats.shadow_effective_removals,
            u64::try_from(66 + second_deletions).unwrap()
        );
        assert_eq!(
            solver.active_learned_clauses,
            u64::try_from(second_candidates - second_deletions).unwrap()
        );
    }

    #[test]
    fn shadow_reduction_excludes_positive_locked_binary_and_existing_shadows() {
        let mut solver = Solver::with_config(SolverConfig {
            shadow_clause_reactivation: true,
            ..SolverConfig::default()
        });
        solver.reserve_variables(8);
        let literals = (0..8)
            .map(|index| Lit::positive(Var::new(index)))
            .collect::<Vec<_>>();
        let positive = solver.allocate_clause(literals[..8].to_vec(), 9, true);
        let locked = solver.allocate_clause(literals[..7].to_vec(), 9, true);
        let existing_shadow = solver.allocate_clause(literals[..6].to_vec(), 9, true);
        let longest = solver.allocate_clause(literals[..5].to_vec(), 9, true);
        let medium = solver.allocate_clause(literals[..4].to_vec(), 9, true);
        let short = solver.allocate_clause(literals[..3].to_vec(), 9, true);
        let binary = solver.allocate_clause(literals[..2].to_vec(), 2, true);
        solver.clause_usage_scores.fill(0);
        solver.clause_usage_scores[positive.index()] = 4;
        solver.reasons[0] = Some(locked);
        solver.active_learned_clauses = 6;
        solver.begin_shadow_observation(existing_shadow.index());

        solver.reduce_database();

        assert!(binary.is_binary());
        assert_eq!(solver.stats.clause_usage_positive_protections, 1);
        assert_eq!(solver.stats.clause_usage_zero_candidates, 3);
        assert_eq!(solver.shadow_clauses.len(), 2);
        assert_eq!(
            solver.shadow_clause_states[existing_shadow.index()],
            SHADOW_OBSERVING
        );
        assert_eq!(
            solver.shadow_clause_states[longest.index()],
            SHADOW_OBSERVING
        );
        assert_eq!(solver.shadow_clause_states[medium.index()], SHADOW_ACTIVE);
        assert_eq!(solver.shadow_clause_states[short.index()], SHADOW_ACTIVE);
        assert_eq!(solver.shadow_clause_states[positive.index()], SHADOW_ACTIVE);
        assert_eq!(solver.shadow_clause_states[locked.index()], SHADOW_ACTIVE);
        assert_eq!(solver.stats.deleted_clauses, 0);
        assert_eq!(solver.stats.shadow_effective_removals, 2);
    }

    #[test]
    fn shadow_propagation_observes_units_without_changing_the_deleted_trajectory() {
        let config = SolverConfig {
            shadow_clause_reactivation: true,
            ..SolverConfig::default()
        };
        let mut shadow = Solver::with_config(config);
        let mut deleted = Solver::with_config(config);
        for solver in [&mut shadow, &mut deleted] {
            solver.reserve_variables(4);
            let clause = solver.allocate_clause(
                (0..4).map(|index| Lit::positive(Var::new(index))).collect(),
                4,
                true,
            );
            solver.attach_clause(clause);
            solver.clause_usage_scores[clause.index()] = 0;
            solver.active_learned_clauses = 1;
        }
        let shadow_clause = ClauseRef::long(0);
        shadow.begin_shadow_observation(shadow_clause.index());
        deleted.mark_clause_deleted(shadow_clause);
        deleted.active_learned_clauses = 0;

        for index in 0..4 {
            let literal = !Lit::positive(Var::new(index));
            assert!(shadow.enqueue(literal, None));
            assert!(deleted.enqueue(literal, None));
            assert_eq!(shadow.propagate(), None);
            assert_eq!(deleted.propagate(), None);
            assert_eq!(shadow.assignments, deleted.assignments);
            assert_eq!(shadow.levels, deleted.levels);
            assert_eq!(shadow.reasons, deleted.reasons);
            assert_eq!(shadow.trail, deleted.trail);
            assert_eq!(shadow.stats.decisions, deleted.stats.decisions);
            assert_eq!(shadow.stats.propagations, deleted.stats.propagations);
            assert_eq!(shadow.stats.conflicts, deleted.stats.conflicts);
            assert_eq!(shadow.stats.restarts, deleted.stats.restarts);
            assert_eq!(shadow.stats.reductions, deleted.stats.reductions);
        }

        assert_eq!(
            shadow.shadow_clause_states[shadow_clause.index()],
            SHADOW_TRIGGERED
        );
        assert_eq!(shadow.stats.shadow_unit_triggers, 1);
        assert_eq!(shadow.stats.shadow_conflict_triggers, 0);
        assert!(shadow.stats.shadow_watch_visits > 0);
        assert!(shadow.stats.shadow_literal_checks > 0);
        assert_eq!(shadow.clause_usage_scores[shadow_clause.index()], 0);
        assert_eq!(shadow.clauses[shadow_clause.index()].activity, 0.0);
    }

    #[test]
    fn shadow_propagation_observes_a_first_conflict_without_returning_it() {
        let mut solver = Solver::with_config(SolverConfig {
            shadow_clause_reactivation: true,
            ..SolverConfig::default()
        });
        solver.reserve_variables(3);
        let a = Lit::positive(Var::new(0));
        let b = Lit::positive(Var::new(1));
        let c = Lit::positive(Var::new(2));
        assert!(solver.enqueue(!b, None));
        assert!(solver.enqueue(!c, None));
        assert_eq!(solver.propagate(), None);
        let clause = solver.allocate_clause(vec![a, b, c], 3, true);
        solver.attach_clause(clause);
        solver.clause_usage_scores[clause.index()] = 0;
        solver.active_learned_clauses = 1;
        solver.begin_shadow_observation(clause.index());

        assert!(solver.enqueue(!a, None));
        assert_eq!(solver.propagate(), None);

        assert_eq!(
            solver.shadow_clause_states[clause.index()],
            SHADOW_TRIGGERED
        );
        assert_eq!(solver.stats.shadow_unit_triggers, 0);
        assert_eq!(solver.stats.shadow_conflict_triggers, 1);
        assert_eq!(solver.stats.conflicts, 0);
        assert!(solver.reasons.iter().all(Option::is_none));
    }

    #[test]
    fn shadow_finalization_honors_the_exact_horizon_and_state_transitions() {
        let literals = vec![
            Lit::positive(Var::new(0)),
            Lit::positive(Var::new(1)),
            Lit::positive(Var::new(2)),
        ];

        let mut expired = Solver::with_config(SolverConfig {
            shadow_clause_reactivation: true,
            ..SolverConfig::default()
        });
        expired.reserve_variables(3);
        let expired_clause = expired.allocate_clause(literals.clone(), 3, true);
        expired.attach_clause(expired_clause);
        expired.clause_usage_scores[expired_clause.index()] = 0;
        expired.active_learned_clauses = 1;
        expired.begin_shadow_observation(expired_clause.index());
        expired.stats.conflicts = 255;
        expired.finalize_shadow_clauses_at_root();
        assert_eq!(expired.shadow_clauses, [expired_clause.index()]);
        assert!(!expired.clause_deleted(expired_clause));
        assert_eq!(expired.stats.shadow_expired_clauses, 0);

        expired.stats.conflicts = 256;
        expired.finalize_shadow_clauses_at_root();
        assert!(expired.shadow_clauses.is_empty());
        assert!(expired.clause_deleted(expired_clause));
        assert_eq!(expired.stats.shadow_expired_clauses, 1);
        assert_eq!(expired.stats.deleted_clauses, 1);
        assert_eq!(expired.stats.shadow_observation_conflicts, 256);
        assert_eq!(expired.active_learned_clauses, 0);

        let mut reactivated = Solver::with_config(SolverConfig {
            shadow_clause_reactivation: true,
            ..SolverConfig::default()
        });
        reactivated.reserve_variables(3);
        let reactivated_clause = reactivated.allocate_clause(literals, 3, true);
        reactivated.attach_clause(reactivated_clause);
        reactivated.clause_usage_scores[reactivated_clause.index()] = 0;
        reactivated.active_learned_clauses = 1;
        reactivated.begin_shadow_observation(reactivated_clause.index());
        reactivated.trigger_shadow_clause(reactivated_clause, false);
        reactivated.stats.conflicts = 256;
        reactivated.finalize_shadow_clauses_at_root();

        assert!(reactivated.shadow_clauses.is_empty());
        assert_eq!(
            reactivated.shadow_clause_states[reactivated_clause.index()],
            SHADOW_ACTIVE
        );
        assert!(!reactivated.clause_deleted(reactivated_clause));
        assert_eq!(
            reactivated.clause_usage_scores[reactivated_clause.index()],
            1
        );
        assert_eq!(reactivated.stats.shadow_reactivated_clauses, 1);
        assert_eq!(reactivated.stats.shadow_expired_clauses, 0);
        assert_eq!(reactivated.active_learned_clauses, 1);
    }

    #[test]
    fn shadow_reactivation_installs_root_units_and_defers_root_conflicts() {
        let a = Lit::positive(Var::new(0));
        let b = Lit::positive(Var::new(1));
        let c = Lit::positive(Var::new(2));
        let mut unit = Solver::with_config(SolverConfig {
            shadow_clause_reactivation: true,
            ..SolverConfig::default()
        });
        unit.reserve_variables(3);
        let unit_clause = unit.allocate_clause(vec![a, b, c], 3, true);
        unit.attach_clause(unit_clause);
        unit.clause_usage_scores[unit_clause.index()] = 0;
        unit.active_learned_clauses = 1;
        unit.begin_shadow_observation(unit_clause.index());
        unit.trigger_shadow_clause(unit_clause, false);
        assert!(unit.enqueue(!a, None));
        assert!(unit.enqueue(!b, None));
        unit.stats.conflicts = 256;

        unit.finalize_shadow_clauses_at_root();

        assert_eq!(unit.assignments[c.var().index()], TRUE);
        assert_eq!(unit.reasons[c.var().index()], Some(unit_clause));
        assert_eq!(unit.stats.shadow_root_units, 1);
        assert_eq!(unit.stats.shadow_root_conflicts, 0);
        assert_eq!(unit.propagate(), None);

        let mut conflict = Solver::with_config(SolverConfig {
            shadow_clause_reactivation: true,
            ..SolverConfig::default()
        });
        conflict.reserve_variables(3);
        let conflict_clause = conflict.allocate_clause(vec![a, b, c], 3, true);
        conflict.attach_clause(conflict_clause);
        conflict.clause_usage_scores[conflict_clause.index()] = 0;
        conflict.active_learned_clauses = 1;
        conflict.begin_shadow_observation(conflict_clause.index());
        conflict.trigger_shadow_clause(conflict_clause, true);
        for literal in [!a, !b, !c] {
            assert!(conflict.enqueue(literal, None));
        }
        conflict.stats.conflicts = 256;

        conflict.finalize_shadow_clauses_at_root();

        assert_eq!(conflict.stats.shadow_root_units, 0);
        assert_eq!(conflict.stats.shadow_root_conflicts, 1);
        assert_eq!(conflict.propagate(), Some(conflict_clause));
        assert!(conflict.shadow_deferred_root_conflict.is_none());
    }

    #[test]
    fn shadow_reactivation_rejects_every_incompatible_configuration() {
        let incompatible = [
            SolverConfig {
                shadow_clause_reactivation: true,
                lbd_free_clause_management: false,
                ..SolverConfig::default()
            },
            SolverConfig {
                shadow_clause_reactivation: true,
                scan_debt_clause_management: true,
                ..SolverConfig::default()
            },
            SolverConfig {
                shadow_clause_reactivation: true,
                nonregular_clause_retention: true,
                ..SolverConfig::default()
            },
            SolverConfig {
                shadow_clause_reactivation: true,
                restart_trail_reuse: RestartTrailReuse::Always,
                ..SolverConfig::default()
            },
            SolverConfig {
                shadow_clause_reactivation: true,
                compact_clause_arena: true,
                ..SolverConfig::default()
            },
        ];

        for config in incompatible {
            assert!(std::panic::catch_unwind(|| Solver::with_config(config)).is_err());
        }
    }

    #[test]
    fn counterfactual_phase_sample_is_optional_and_holds_only_deleted_references() {
        let control = Solver::new();
        assert!(control.counterfactual_phase_samples.is_empty());
        assert_eq!(control.stats().counterfactual_phase_metadata_bytes, 0);

        let mut treatment = Solver::with_config(SolverConfig {
            counterfactual_phase_voting: true,
            ..SolverConfig::default()
        });
        treatment.reserve_variables(3);
        let clause = treatment.allocate_clause(
            vec![
                Lit::positive(Var::new(0)),
                Lit::positive(Var::new(1)),
                Lit::positive(Var::new(2)),
            ],
            3,
            true,
        );
        treatment.mark_clause_deleted(clause);
        treatment.offer_counterfactual_phase_sample(clause, 1);

        assert_eq!(treatment.counterfactual_phase_samples.len(), 1);
        assert_eq!(treatment.counterfactual_phase_samples[0].clause, clause);
        assert!(treatment.clause_deleted(clause));
        assert!(treatment.clause_learned(clause));
        assert_eq!(treatment.stats().counterfactual_phase_live_samples, 1);
        assert_eq!(
            treatment.stats().counterfactual_phase_metadata_bytes,
            u64::try_from(std::mem::size_of::<super::CounterfactualPhaseSample>()).unwrap()
        );
    }

    #[test]
    fn counterfactual_phase_priority_reservoir_keeps_the_lowest_frozen_ranks() {
        let mut solver = Solver::with_config(SolverConfig {
            counterfactual_phase_voting: true,
            ..SolverConfig::default()
        });
        solver.reserve_variables(3);
        let literals = vec![
            Lit::positive(Var::new(0)),
            Lit::positive(Var::new(1)),
            Lit::positive(Var::new(2)),
        ];
        let mut all = Vec::new();
        for index in 0..96 {
            let clause = solver.allocate_clause(literals.clone(), 4, true);
            solver.mark_clause_deleted(clause);
            let reduction = 1 + u64::try_from(index / 24).unwrap();
            solver.offer_counterfactual_phase_sample(clause, reduction);
            all.push(super::CounterfactualPhaseSample {
                rank: shadow_clause_rank(clause.index(), reduction),
                reduction,
                clause,
            });
        }
        all.sort_unstable();
        let expected = all[..Solver::COUNTERFACTUAL_PHASE_CAPACITY].to_vec();
        let mut actual = solver.counterfactual_phase_samples.clone();
        actual.sort_unstable();

        assert_eq!(actual, expected);
        assert_eq!(
            solver.counterfactual_phase_samples.len(),
            Solver::COUNTERFACTUAL_PHASE_CAPACITY
        );
        assert_eq!(solver.stats.counterfactual_phase_deletion_offers, 96);
        assert!(
            solver.stats.counterfactual_phase_sample_insertions
                >= u64::try_from(Solver::COUNTERFACTUAL_PHASE_CAPACITY).unwrap()
        );
        assert_eq!(
            solver.stats.counterfactual_phase_sample_replacements,
            solver
                .stats
                .counterfactual_phase_sample_insertions
                .saturating_sub(u64::try_from(Solver::COUNTERFACTUAL_PHASE_CAPACITY).unwrap())
        );
        assert_eq!(solver.stats.counterfactual_phase_sample_peak, 64);
    }

    #[test]
    fn counterfactual_phase_reduction_exactly_matches_control_deletions() {
        let mut control = Solver::new();
        let mut treatment = Solver::with_config(SolverConfig {
            counterfactual_phase_voting: true,
            ..SolverConfig::default()
        });
        for solver in [&mut control, &mut treatment] {
            solver.reserve_variables(8);
            let literals = (0..8)
                .map(|index| Lit::positive(Var::new(index)))
                .collect::<Vec<_>>();
            for length in [8, 8, 7, 6, 5, 4, 3, 3] {
                let clause = solver.allocate_clause(literals[..length].to_vec(), 10, true);
                solver.attach_clause(clause);
            }
            solver.clause_usage_scores.fill(0);
            solver.clause_usage_scores[0] = 3;
            solver.reasons[0] = Some(ClauseRef::long(1));
            solver.active_learned_clauses = 8;
            solver.reduce_database();
        }

        assert_eq!(
            control
                .clauses
                .iter()
                .map(|clause| clause.deleted)
                .collect::<Vec<_>>(),
            treatment
                .clauses
                .iter()
                .map(|clause| clause.deleted)
                .collect::<Vec<_>>()
        );
        assert_eq!(
            control.stats.deleted_clauses,
            treatment.stats.deleted_clauses
        );
        assert_eq!(
            control.stats.clause_usage_zero_candidates,
            treatment.stats.clause_usage_zero_candidates
        );
        assert_eq!(
            control.stats.clause_usage_positive_protections,
            treatment.stats.clause_usage_positive_protections
        );
        assert_eq!(control.stats.reductions, treatment.stats.reductions);
        assert_eq!(
            control.active_learned_clauses,
            treatment.active_learned_clauses
        );
        assert_eq!(
            treatment.stats.counterfactual_phase_deletion_offers,
            treatment.stats.deleted_clauses
        );
        assert!(treatment.counterfactual_phase_samples.iter().all(|sample| {
            treatment.clause_deleted(sample.clause) && treatment.clause_learned(sample.clause)
        }));
    }

    #[test]
    fn counterfactual_phase_snapshot_classifies_and_aggregates_without_propagating() {
        let mut solver = Solver::with_config(SolverConfig {
            counterfactual_phase_voting: true,
            ..SolverConfig::default()
        });
        solver.reserve_variables(8);
        let literals = (0..8)
            .map(|index| Lit::positive(Var::new(index)))
            .collect::<Vec<_>>();
        let [a, b, c, x, y, d, e, f] = literals.as_slice() else {
            unreachable!("fixed literal fixture")
        };
        solver.trail_limits.push(0);
        for literal in [*a, *b, *c] {
            assert!(solver.enqueue(literal, None));
        }

        let clauses = [
            vec![*a, *d, *e],
            vec![*d, *e, *f],
            vec![*x, !*a, !*b],
            vec![*x, !*b, !*c],
            vec![*y, !*a, !*b],
            vec![!*y, !*b, !*c],
            vec![!*a, !*b, !*c],
        ];
        for literals in clauses {
            let clause = solver.allocate_clause(literals, 4, true);
            solver.mark_clause_deleted(clause);
            solver.offer_counterfactual_phase_sample(clause, 1);
        }
        let assignments_before = solver.assignments.clone();
        let reasons_before = solver.reasons.clone();
        let trail_before = solver.trail.clone();
        solver.phase[x.var().index()] = false;

        let votes = solver.observe_counterfactual_phases_before_root_restart();

        assert_eq!(votes, [(x.var(), true)]);
        assert_eq!(solver.assignments, assignments_before);
        assert_eq!(solver.reasons, reasons_before);
        assert_eq!(solver.trail, trail_before);
        assert_eq!(solver.stats.counterfactual_phase_snapshots, 1);
        assert_eq!(solver.stats.counterfactual_phase_clauses_scanned, 7);
        assert_eq!(solver.stats.counterfactual_phase_satisfied_clauses, 1);
        assert_eq!(solver.stats.counterfactual_phase_open_clauses, 1);
        assert_eq!(solver.stats.counterfactual_phase_unit_clauses, 4);
        assert_eq!(solver.stats.counterfactual_phase_conflict_clauses, 1);
        assert_eq!(solver.stats.counterfactual_phase_unit_votes, 4);
        assert_eq!(solver.stats.counterfactual_phase_unanimous_variables, 1);
        assert_eq!(solver.stats.counterfactual_phase_disagreeing_variables, 1);
        assert!(solver.counterfactual_phase_samples.is_empty());

        solver.cancel_until(0);
        solver.apply_counterfactual_phase_votes_at_root(&votes);
        assert!(solver.phase[x.var().index()]);
        assert_eq!(solver.stats.counterfactual_phase_writes, 1);
        assert_eq!(solver.stats.counterfactual_phase_changes, 1);
        assert_eq!(solver.stats.counterfactual_phase_root_assigned_skips, 0);
    }

    #[test]
    fn counterfactual_phase_application_skips_root_assignments_and_is_one_shot() {
        let mut solver = Solver::with_config(SolverConfig {
            counterfactual_phase_voting: true,
            ..SolverConfig::default()
        });
        solver.reserve_variables(2);
        let a = Var::new(0);
        let b = Var::new(1);
        assert!(solver.enqueue(Lit::positive(a), None));
        solver.phase.fill(true);

        solver.apply_counterfactual_phase_votes_at_root(&[(a, false), (b, false)]);

        assert!(solver.phase[a.index()]);
        assert!(!solver.phase[b.index()]);
        assert_eq!(solver.stats.counterfactual_phase_root_assigned_skips, 1);
        assert_eq!(solver.stats.counterfactual_phase_writes, 1);
        assert_eq!(solver.stats.counterfactual_phase_changes, 1);
        assert!(solver.counterfactual_phase_samples.is_empty());
    }

    #[test]
    fn counterfactual_phase_rejects_every_incompatible_configuration() {
        let incompatible = [
            SolverConfig {
                counterfactual_phase_voting: true,
                lbd_free_clause_management: false,
                ..SolverConfig::default()
            },
            SolverConfig {
                counterfactual_phase_voting: true,
                scan_debt_clause_management: true,
                ..SolverConfig::default()
            },
            SolverConfig {
                counterfactual_phase_voting: true,
                nonregular_clause_retention: true,
                ..SolverConfig::default()
            },
            SolverConfig {
                counterfactual_phase_voting: true,
                shadow_clause_reactivation: true,
                ..SolverConfig::default()
            },
            SolverConfig {
                counterfactual_phase_voting: true,
                restart_trail_reuse: RestartTrailReuse::Always,
                ..SolverConfig::default()
            },
            SolverConfig {
                counterfactual_phase_voting: true,
                compact_clause_arena: true,
                ..SolverConfig::default()
            },
            SolverConfig {
                counterfactual_phase_voting: true,
                systematic_rephasing: true,
                ..SolverConfig::default()
            },
        ];

        for config in incompatible {
            assert!(std::panic::catch_unwind(|| Solver::with_config(config)).is_err());
        }
    }

    #[test]
    fn tiered_reduction_ages_strong_and_middle_tiers_at_different_rates() {
        let mut solver = Solver::with_config(SolverConfig {
            tiered_clause_management: true,
            lbd_free_clause_management: false,
            ..SolverConfig::default()
        });
        solver.reserve_variables(3);
        let literals = vec![
            Lit::positive(Var::new(0)),
            Lit::positive(Var::new(1)),
            Lit::positive(Var::new(2)),
        ];
        let glue = solver.allocate_clause(literals.clone(), 2, true);
        let middle = solver.allocate_clause(literals.clone(), 4, true);
        let local = solver.allocate_clause(literals.clone(), 8, true);
        let worst = solver.allocate_clause(literals, 10, true);

        solver.reduce_database();
        assert!(!solver.clauses[glue.index()].deleted);
        assert!(!solver.clauses[middle.index()].deleted);
        assert!(!solver.clauses[local.index()].deleted);
        assert!(solver.clauses[worst.index()].deleted);

        solver.reduce_database();
        assert!(!solver.clauses[glue.index()].deleted);
        assert!(!solver.clauses[middle.index()].deleted);
        assert!(solver.clauses[local.index()].deleted);

        solver.reduce_database();
        assert!(!solver.clauses[glue.index()].deleted);
        assert!(solver.clauses[middle.index()].deleted);

        solver.reduce_database();
        assert!(solver.clauses[glue.index()].deleted);
        assert_eq!(solver.stats.tier1_protections, 3);
        assert_eq!(solver.stats.tier2_protections, 2);
    }

    #[test]
    fn untiered_reduction_reproduces_unprotected_policy() {
        let mut solver = Solver::with_config(SolverConfig {
            tiered_clause_management: false,
            lbd_free_clause_management: false,
            ..SolverConfig::default()
        });
        solver.reserve_variables(3);
        let clause = solver.allocate_clause(
            vec![
                Lit::positive(Var::new(0)),
                Lit::positive(Var::new(1)),
                Lit::positive(Var::new(2)),
            ],
            2,
            true,
        );
        solver.reduce_database();
        assert!(solver.clauses[clause.index()].deleted);
        assert_eq!(solver.stats.tier1_protections, 0);
        assert_eq!(solver.stats.tier2_protections, 0);
    }

    #[test]
    fn clause_arena_compaction_preserves_references_and_live_payloads() {
        let a = Lit::positive(Var::new(0));
        let b = Lit::negative(Var::new(1));
        let c = Lit::positive(Var::new(2));
        let d = Lit::negative(Var::new(3));
        let e = Lit::positive(Var::new(4));
        let f = Lit::negative(Var::new(5));
        let mut solver = Solver::with_config(SolverConfig {
            compact_clause_arena: true,
            lbd_free_clause_management: false,
            ..SolverConfig::default()
        });
        solver.reserve_variables(6);

        let prefix = solver.allocate_clause(vec![a, b, c], 0, false);
        let deleted_first = solver.allocate_clause(vec![b, c, d], 8, true);
        let live_first = solver.allocate_clause(vec![c, d, e], 4, true);
        let deleted_second = solver.allocate_clause(vec![d, e, f], 9, true);
        let live_second = solver.allocate_clause(vec![e, f, a], 3, true);
        for clause in [
            prefix,
            deleted_first,
            live_first,
            deleted_second,
            live_second,
        ] {
            solver.attach_clause(clause);
        }
        solver.reasons[e.var().index()] = Some(live_first);
        let old_capacity = solver.clause_arena.capacity();

        solver.mark_clause_deleted(deleted_first);
        solver.mark_clause_deleted(deleted_second);
        assert_eq!(solver.stats.arena_garbage_literals, 6);
        solver.compact_clause_arena();

        assert_eq!(solver.clause_arena, [a, b, c, c, d, e, e, f, a]);
        assert_eq!(solver.clauses[prefix.index()].start, 0);
        assert_eq!(solver.clauses[live_first.index()].start, 3);
        assert_eq!(solver.clauses[live_second.index()].start, 6);
        assert_eq!(solver.reasons[e.var().index()], Some(live_first));
        assert!(
            solver.watches[c.index()]
                .iter()
                .any(|watch| watch.clause() == live_first)
        );
        assert!(
            solver.watches[e.index()]
                .iter()
                .any(|watch| watch.clause() == live_second)
        );
        assert_eq!(solver.clause_arena.capacity(), old_capacity);
        assert_eq!(solver.stats.arena_compactions, 1);
        assert_eq!(solver.stats.arena_moved_literals, 6);
        assert_eq!(solver.stats.arena_reclaimed_literals, 6);
        assert_eq!(solver.stats.peak_arena_literals, 15);
        assert_eq!(solver.stats.arena_literals, 9);
        assert_eq!(solver.stats.arena_garbage_literals, 0);

        solver.compact_clause_arena();
        assert_eq!(solver.stats.arena_compactions, 1);
        assert_eq!(solver.clause_arena, [a, b, c, c, d, e, e, f, a]);
    }

    #[test]
    fn productive_database_reduction_triggers_arena_compaction() {
        let mut solver = Solver::with_config(SolverConfig {
            compact_clause_arena: true,
            lbd_free_clause_management: false,
            ..SolverConfig::default()
        });
        solver.reserve_variables(3);
        let literals = vec![
            Lit::positive(Var::new(0)),
            Lit::positive(Var::new(1)),
            Lit::positive(Var::new(2)),
        ];
        solver.allocate_clause(literals.clone(), 4, true);
        solver.allocate_clause(literals, 8, true);

        solver.reduce_database();

        assert_eq!(solver.stats.deleted_clauses, 1);
        assert_eq!(solver.stats.arena_compactions, 1);
        assert_eq!(solver.stats.arena_reclaimed_literals, 3);
        assert_eq!(solver.stats.arena_literals, 3);
        assert_eq!(solver.stats.arena_garbage_literals, 0);
    }

    #[test]
    fn learned_binary_clauses_are_permanent() {
        let mut solver = Solver::new();
        solver.reserve_variables(2);
        let clause = solver.allocate_clause(
            vec![Lit::positive(Var::new(0)), Lit::negative(Var::new(1))],
            2,
            true,
        );
        solver.reduce_database();
        assert!(!solver.clause_deleted(clause));
    }

    #[test]
    fn chronological_backtracking_uses_a_strict_hundred_level_cutoff() {
        let mut solver = Solver::with_config(SolverConfig {
            chronological_backtracking: true,
            ..SolverConfig::default()
        });
        solver.trail_limits = vec![0; 150];

        assert_eq!(solver.determine_backtrack_level(49, 2), 49);
        assert_eq!(solver.determine_backtrack_level(48, 2), 149);
        assert_eq!(solver.determine_backtrack_level(0, 1), 0);
        assert_eq!(solver.stats.chronological_backtracks, 1);
        assert_eq!(solver.stats.chronological_levels_preserved, 101);
    }

    #[test]
    fn systematic_rephase_schedule_cycles_best_inverted_best_original() {
        let mut solver = Solver::with_config(SolverConfig {
            systematic_rephasing: true,
            ..SolverConfig::default()
        });
        solver.reserve_variables(3);
        solver.best_phase = vec![true, false, true];

        solver.rephase();
        assert_eq!(solver.phase, [true, false, true]);
        solver.rephase();
        assert_eq!(solver.phase, [false, false, false]);
        solver.rephase();
        assert_eq!(solver.phase, [true, false, true]);
        solver.rephase();
        assert_eq!(solver.phase, [true, true, true]);

        assert_eq!(solver.stats.rephases, 4);
        assert_eq!(solver.stats.best_rephases, 2);
        assert_eq!(solver.stats.inverted_rephases, 1);
        assert_eq!(solver.stats.original_rephases, 1);
        assert_eq!(Solver::rephase_interval(1), 1_000);
        assert!(Solver::rephase_interval(2) > Solver::rephase_interval(1));
    }

    #[test]
    fn systematic_rephasing_runs_during_search() {
        let gate = Lit::positive(Var::new(0));
        let left = Lit::positive(Var::new(1));
        let right = Lit::positive(Var::new(2));
        let mut solver = Solver::with_config(SolverConfig {
            systematic_rephasing: true,
            ..SolverConfig::default()
        });
        for clause in [
            vec![!gate, left, right],
            vec![!gate, left, !right],
            vec![!gate, !left, right],
            vec![!gate, !left, !right],
        ] {
            solver.add_clause(&clause);
        }
        solver.next_rephase = 1;
        let SolveResult::Sat(model) = solver.solve() else {
            panic!("the gated contradiction should be satisfiable");
        };
        assert!(!model.literal_value(gate));
        assert!(solver.stats.rephases > 0);
        assert!(solver.stats.best_phase_updates > 0);
    }

    #[test]
    fn contradictory_units_are_unsatisfiable() {
        let x = Lit::positive(Var::new(0));
        let mut solver = Solver::new();
        assert!(solver.add_clause(&[x]));
        assert!(!solver.add_clause(&[!x]));
        assert_eq!(solver.solve(), SolveResult::Unsat);
    }

    #[test]
    fn empty_formula_has_a_complete_model() {
        let mut solver = Solver::new();
        solver.reserve_variables(3);
        let SolveResult::Sat(model) = solver.solve() else {
            panic!("empty formula should be satisfiable");
        };
        assert_eq!(model.len(), 3);
    }

    #[test]
    fn tautologies_and_duplicates_are_normalized() {
        let x = Lit::positive(Var::new(0));
        let y = Lit::positive(Var::new(1));
        let mut solver = Solver::new();
        assert!(solver.add_clause(&[x, !x]));
        assert!(solver.add_clause(&[y, y]));
        let SolveResult::Sat(model) = solver.solve() else {
            panic!("formula should be satisfiable");
        };
        assert!(model.literal_value(y));
    }

    #[test]
    fn model_helpers_report_literal_values() {
        let model = Model {
            values: vec![true, false],
        };
        assert!(model.literal_value(Lit::positive(Var::new(0))));
        assert!(model.literal_value(Lit::negative(Var::new(1))));
        assert_eq!(model.iter().collect::<Vec<_>>(), [true, false]);
    }
}
