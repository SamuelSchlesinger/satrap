use std::ffi::OsString;
use std::fs::{self, File};
use std::io::{self, BufWriter, Read, Write};
use std::path::PathBuf;
use std::process::ExitCode;
use std::time::Instant;

use sat::{
    RestartPolicy, RestartTrailReuse, SearchStrategy, SolveResult, Solver, SolverConfig, dimacs,
};

const SAT_EXIT: u8 = 10;
const UNSAT_EXIT: u8 = 20;
const ERROR_EXIT: u8 = 1;

fn main() -> ExitCode {
    match run() {
        Ok(code) => ExitCode::from(code),
        Err(message) => {
            eprintln!("error: {message}");
            ExitCode::from(ERROR_EXIT)
        }
    }
}

fn run() -> Result<u8, String> {
    let action = parse_args(std::env::args_os().skip(1))?;
    let Action::Solve(options) = action else {
        match action {
            Action::Help => print_help(),
            Action::Version => println!("sat {}", env!("CARGO_PKG_VERSION")),
            Action::Solve(_) => unreachable!(),
        }
        return Ok(0);
    };

    let input = read_input(options.input.as_ref())?;
    let formula = dimacs::parse(&input).map_err(|error| error.to_string())?;
    let mut solver = Solver::with_config(SolverConfig {
        minimize_learned_clauses: options.minimize,
        binary_resolution_minimization: options.binary_resolution_minimization,
        compact_clause_arena: options.compact_clause_arena,
        bounded_variable_elimination: options.bounded_variable_elimination,
        bounded_variable_addition: options.bounded_variable_addition,
        macro_bounded_variable_addition: options.macro_bounded_variable_addition,
        failed_literal_probing: options.failed_literal_probing,
        clause_vivification: options.clause_vivification,
        clause_subsumption: options.clause_subsumption,
        binary_fast_path: options.binary_fast_path,
        restart_policy: options.restart_policy,
        block_lbd_restarts: options.block_lbd_restarts,
        search_strategy: options.search_strategy,
        tiered_clause_management: options.tiered_clause_management,
        lbd_free_clause_management: options.lbd_free_clause_management,
        scan_debt_clause_management: options.scan_debt_clause_management,
        nonregular_clause_retention: options.nonregular_clause_retention,
        shadow_clause_reactivation: options.shadow_clause_reactivation,
        counterfactual_phase_voting: options.counterfactual_phase_voting,
        promote_clause_lbd: options.promote_clause_lbd,
        chronological_backtracking: options.chronological_backtracking,
        systematic_rephasing: options.systematic_rephasing,
        restart_trail_reuse: options.restart_trail_reuse,
    });
    if let Some(path) = &options.proof {
        let file = File::create(path)
            .map_err(|error| format!("could not create proof `{}`: {error}", path.display()))?;
        solver.enable_drat_proof(BufWriter::with_capacity(1024 * 1024, file));
    }
    solver.reserve_variables(formula.variable_count);
    for clause in &formula.clauses {
        solver.add_clause(clause);
    }

    let started = Instant::now();
    let result = solver.solve();
    let elapsed = started.elapsed();
    if let Some(error) = solver.proof_error() {
        return Err(format!("could not finish DRAT proof: {error}"));
    }
    let stdout = io::stdout();
    let mut output = io::BufWriter::new(stdout.lock());

    if options.stats {
        let stats = solver.stats();
        writeln!(output, "c variables {}", solver.variable_count()).map_err(io_error)?;
        writeln!(output, "c clauses {}", solver.original_clause_count()).map_err(io_error)?;
        writeln!(output, "c decisions {}", stats.decisions).map_err(io_error)?;
        writeln!(output, "c propagations {}", stats.propagations).map_err(io_error)?;
        writeln!(output, "c conflicts {}", stats.conflicts).map_err(io_error)?;
        writeln!(output, "c restarts {}", stats.restarts).map_err(io_error)?;
        writeln!(
            output,
            "c trail_reuse_restarts {}",
            stats.trail_reuse_restarts
        )
        .map_err(io_error)?;
        writeln!(output, "c trail_reuse_levels {}", stats.trail_reuse_levels).map_err(io_error)?;
        writeln!(
            output,
            "c trail_reuse_eligible_restarts {}",
            stats.trail_reuse_eligible_restarts
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c adaptive_reuse_probes {}",
            stats.adaptive_reuse_probes
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c adaptive_reuse_quality_accepts {}",
            stats.adaptive_reuse_quality_accepts
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c adaptive_reuse_quality_rejects {}",
            stats.adaptive_reuse_quality_rejects
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c adaptive_root_epochs {}",
            stats.adaptive_root_epochs
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c adaptive_reuse_epochs {}",
            stats.adaptive_reuse_epochs
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c chronological_backtracks {}",
            stats.chronological_backtracks
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c chronological_levels_preserved {}",
            stats.chronological_levels_preserved
        )
        .map_err(io_error)?;
        writeln!(output, "c rephases {}", stats.rephases).map_err(io_error)?;
        writeln!(output, "c best_rephases {}", stats.best_rephases).map_err(io_error)?;
        writeln!(output, "c inverted_rephases {}", stats.inverted_rephases).map_err(io_error)?;
        writeln!(output, "c original_rephases {}", stats.original_rephases).map_err(io_error)?;
        writeln!(output, "c best_phase_updates {}", stats.best_phase_updates).map_err(io_error)?;
        writeln!(output, "c blocked_restarts {}", stats.blocked_restarts).map_err(io_error)?;
        writeln!(output, "c mode_switches {}", stats.mode_switches).map_err(io_error)?;
        writeln!(output, "c focused_conflicts {}", stats.focused_conflicts).map_err(io_error)?;
        writeln!(output, "c stable_conflicts {}", stats.stable_conflicts).map_err(io_error)?;
        writeln!(output, "c focused_decisions {}", stats.focused_decisions).map_err(io_error)?;
        writeln!(output, "c stable_decisions {}", stats.stable_decisions).map_err(io_error)?;
        writeln!(output, "c focused_restarts {}", stats.focused_restarts).map_err(io_error)?;
        writeln!(output, "c stable_restarts {}", stats.stable_restarts).map_err(io_error)?;
        writeln!(
            output,
            "c lrb_unassign_updates {}",
            stats.lrb_unassign_updates
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c lrb_reason_side_rewards {}",
            stats.lrb_reason_side_rewards
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c lrb_anti_exploration_decays {}",
            stats.lrb_anti_exploration_decays
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c transfer_evsids_epochs {}",
            stats.transfer_evsids_epochs
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c transfer_lrb_epochs {}",
            stats.transfer_lrb_epochs
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c transfer_mode_switches {}",
            stats.transfer_mode_switches
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c transfer_evsids_origin_credits {}",
            stats.transfer_evsids_origin_credits
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c transfer_lrb_origin_credits {}",
            stats.transfer_lrb_origin_credits
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c transfer_bcp_credits {}",
            stats.transfer_bcp_credits
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c transfer_analysis_credits {}",
            stats.transfer_analysis_credits
        )
        .map_err(io_error)?;
        writeln!(output, "c chb_score_updates {}", stats.chb_score_updates).map_err(io_error)?;
        writeln!(
            output,
            "c chb_conflict_score_updates {}",
            stats.chb_conflict_score_updates
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c chb_conflict_history_updates {}",
            stats.chb_conflict_history_updates
        )
        .map_err(io_error)?;
        writeln!(output, "c learned {}", stats.learned_clauses).map_err(io_error)?;
        writeln!(output, "c learned_literals {}", stats.learned_literals).map_err(io_error)?;
        writeln!(output, "c minimized_literals {}", stats.minimized_literals).map_err(io_error)?;
        writeln!(
            output,
            "c binary_minimization_clauses {}",
            stats.binary_minimization_clauses
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c binary_minimization_watch_visits {}",
            stats.binary_minimization_watch_visits
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c binary_minimized_literals {}",
            stats.binary_minimized_literals
        )
        .map_err(io_error)?;
        writeln!(output, "c arena_compactions {}", stats.arena_compactions).map_err(io_error)?;
        writeln!(
            output,
            "c arena_moved_literals {}",
            stats.arena_moved_literals
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c arena_reclaimed_literals {}",
            stats.arena_reclaimed_literals
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c peak_arena_literals {}",
            stats.peak_arena_literals
        )
        .map_err(io_error)?;
        writeln!(output, "c arena_literals {}", stats.arena_literals).map_err(io_error)?;
        writeln!(
            output,
            "c arena_garbage_literals {}",
            stats.arena_garbage_literals
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c eliminated_variables {}",
            stats.eliminated_variables
        )
        .map_err(io_error)?;
        writeln!(output, "c elimination_pairs {}", stats.elimination_pairs).map_err(io_error)?;
        writeln!(
            output,
            "c elimination_literal_touches {}",
            stats.elimination_literal_touches
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c elimination_removed_clauses {}",
            stats.elimination_removed_clauses
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c elimination_resolvents {}",
            stats.elimination_resolvents
        )
        .map_err(io_error)?;
        writeln!(output, "c elimination_units {}", stats.elimination_units).map_err(io_error)?;
        writeln!(
            output,
            "c elimination_rejections {}",
            stats.elimination_rejections
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c elimination_extension_clauses {}",
            stats.elimination_extension_clauses
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c elimination_extension_literals {}",
            stats.elimination_extension_literals
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c factorization_rounds {}",
            stats.factorization_rounds
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c factorization_candidate_clauses {}",
            stats.factorization_candidate_clauses
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c factorization_literal_touches {}",
            stats.factorization_literal_touches
        )
        .map_err(io_error)?;
        writeln!(output, "c factored_variables {}", stats.factored_variables).map_err(io_error)?;
        writeln!(
            output,
            "c factorization_clauses_removed {}",
            stats.factorization_clauses_removed
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c factorization_clauses_added {}",
            stats.factorization_clauses_added
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c factorization_clause_reduction {}",
            stats.factorization_clause_reduction
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c factorization_peak_factors {}",
            stats.factorization_peak_factors
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c factorization_peak_quotients {}",
            stats.factorization_peak_quotients
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c factorization_input_short_clauses {}",
            stats.factorization_input_short_clauses
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c factorization_density_checks {}",
            stats.factorization_density_checks
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c factorization_density_skips {}",
            stats.factorization_density_skips
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c factorization_macro_rejections {}",
            stats.factorization_macro_rejections
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c failed_literal_probes {}",
            stats.failed_literal_probes
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c failed_literal_units {}",
            stats.failed_literal_units
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c probing_propagations {}",
            stats.probing_propagations
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c vivification_checks {}",
            stats.vivification_checks
        )
        .map_err(io_error)?;
        writeln!(output, "c vivified_clauses {}", stats.vivified_clauses).map_err(io_error)?;
        writeln!(output, "c vivified_literals {}", stats.vivified_literals).map_err(io_error)?;
        writeln!(output, "c vivified_units {}", stats.vivified_units).map_err(io_error)?;
        writeln!(
            output,
            "c vivification_propagations {}",
            stats.vivification_propagations
        )
        .map_err(io_error)?;
        writeln!(output, "c subsumption_checks {}", stats.subsumption_checks).map_err(io_error)?;
        writeln!(
            output,
            "c subsumption_literal_touches {}",
            stats.subsumption_literal_touches
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c subsumption_occurrences {}",
            stats.subsumption_occurrences
        )
        .map_err(io_error)?;
        writeln!(output, "c subsumed_clauses {}", stats.subsumed_clauses).map_err(io_error)?;
        writeln!(
            output,
            "c self_subsumed_clauses {}",
            stats.self_subsumed_clauses
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c self_subsumed_literals {}",
            stats.self_subsumed_literals
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c self_subsumed_units {}",
            stats.self_subsumed_units
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c binary_watch_visits {}",
            stats.binary_watch_visits
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c stored_binary_clauses {}",
            stats.stored_binary_clauses
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c stored_long_clauses {}",
            stats.stored_long_clauses
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c binary_storage_bytes {}",
            stats.binary_storage_bytes
        )
        .map_err(io_error)?;
        writeln!(output, "c long_storage_bytes {}", stats.long_storage_bytes).map_err(io_error)?;
        writeln!(
            output,
            "c reason_storage_bytes {}",
            stats.reason_storage_bytes
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c legacy_equivalent_storage_bytes {}",
            stats.legacy_equivalent_storage_bytes
        )
        .map_err(io_error)?;
        writeln!(output, "c deleted {}", stats.deleted_clauses).map_err(io_error)?;
        writeln!(output, "c reductions {}", stats.reductions).map_err(io_error)?;
        writeln!(output, "c learned_tier1 {}", stats.learned_tier1_clauses).map_err(io_error)?;
        writeln!(output, "c learned_tier2 {}", stats.learned_tier2_clauses).map_err(io_error)?;
        writeln!(output, "c promoted {}", stats.promoted_clauses).map_err(io_error)?;
        writeln!(output, "c tier1_protections {}", stats.tier1_protections).map_err(io_error)?;
        writeln!(output, "c tier2_protections {}", stats.tier2_protections).map_err(io_error)?;
        writeln!(
            output,
            "c clause_usage_bcp_increments {}",
            stats.clause_usage_bcp_increments
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c clause_usage_analysis_increments {}",
            stats.clause_usage_analysis_increments
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c clause_usage_decay_passes {}",
            stats.clause_usage_decay_passes
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c clause_usage_scores_decayed {}",
            stats.clause_usage_scores_decayed
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c clause_usage_positive_protections {}",
            stats.clause_usage_positive_protections
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c clause_usage_zero_candidates {}",
            stats.clause_usage_zero_candidates
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c clause_scan_debt_literal_checks {}",
            stats.clause_scan_debt_literal_checks
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c clause_scan_debt_nonzero_resets {}",
            stats.clause_scan_debt_nonzero_resets
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c clause_scan_debt_peak {}",
            stats.clause_scan_debt_peak
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c clause_scan_debt_selection_displacements {}",
            stats.clause_scan_debt_selection_displacements
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c clause_scan_debt_positive_deletions {}",
            stats.clause_scan_debt_positive_deletions
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c clause_scan_debt_zero_rescues {}",
            stats.clause_scan_debt_zero_rescues
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c regularity_resolution_pivots {}",
            stats.regularity_resolution_pivots
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c regularity_sampled_repeat_witnesses {}",
            stats.regularity_sampled_repeat_witnesses
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c regularity_nonregular_learned_clauses {}",
            stats.regularity_nonregular_learned_clauses
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c regularity_nonregular_zero_candidates {}",
            stats.regularity_nonregular_zero_candidates
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c regularity_selection_displacements {}",
            stats.regularity_selection_displacements
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c regularity_nonregular_rescues {}",
            stats.regularity_nonregular_rescues
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c regularity_nonregular_deletions {}",
            stats.regularity_nonregular_deletions
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c regularity_metadata_bytes {}",
            stats.regularity_metadata_bytes
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c shadow_clauses_started {}",
            stats.shadow_clauses_started
        )
        .map_err(io_error)?;
        writeln!(output, "c shadow_active_peak {}", stats.shadow_active_peak).map_err(io_error)?;
        writeln!(
            output,
            "c shadow_watch_visits {}",
            stats.shadow_watch_visits
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c shadow_literal_checks {}",
            stats.shadow_literal_checks
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c shadow_unit_triggers {}",
            stats.shadow_unit_triggers
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c shadow_conflict_triggers {}",
            stats.shadow_conflict_triggers
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c shadow_reactivated_clauses {}",
            stats.shadow_reactivated_clauses
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c shadow_expired_clauses {}",
            stats.shadow_expired_clauses
        )
        .map_err(io_error)?;
        writeln!(output, "c shadow_root_units {}", stats.shadow_root_units).map_err(io_error)?;
        writeln!(
            output,
            "c shadow_root_conflicts {}",
            stats.shadow_root_conflicts
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c shadow_capacity_skips {}",
            stats.shadow_capacity_skips
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c shadow_effective_removals {}",
            stats.shadow_effective_removals
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c shadow_observation_conflicts {}",
            stats.shadow_observation_conflicts
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c shadow_metadata_bytes {}",
            stats.shadow_metadata_bytes
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c counterfactual_phase_deletion_offers {}",
            stats.counterfactual_phase_deletion_offers
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c counterfactual_phase_sample_insertions {}",
            stats.counterfactual_phase_sample_insertions
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c counterfactual_phase_sample_replacements {}",
            stats.counterfactual_phase_sample_replacements
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c counterfactual_phase_sample_peak {}",
            stats.counterfactual_phase_sample_peak
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c counterfactual_phase_live_samples {}",
            stats.counterfactual_phase_live_samples
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c counterfactual_phase_snapshots {}",
            stats.counterfactual_phase_snapshots
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c counterfactual_phase_clauses_scanned {}",
            stats.counterfactual_phase_clauses_scanned
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c counterfactual_phase_literal_checks {}",
            stats.counterfactual_phase_literal_checks
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c counterfactual_phase_satisfied_clauses {}",
            stats.counterfactual_phase_satisfied_clauses
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c counterfactual_phase_open_clauses {}",
            stats.counterfactual_phase_open_clauses
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c counterfactual_phase_unit_clauses {}",
            stats.counterfactual_phase_unit_clauses
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c counterfactual_phase_conflict_clauses {}",
            stats.counterfactual_phase_conflict_clauses
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c counterfactual_phase_unit_votes {}",
            stats.counterfactual_phase_unit_votes
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c counterfactual_phase_unanimous_variables {}",
            stats.counterfactual_phase_unanimous_variables
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c counterfactual_phase_disagreeing_variables {}",
            stats.counterfactual_phase_disagreeing_variables
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c counterfactual_phase_root_assigned_skips {}",
            stats.counterfactual_phase_root_assigned_skips
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c counterfactual_phase_writes {}",
            stats.counterfactual_phase_writes
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c counterfactual_phase_changes {}",
            stats.counterfactual_phase_changes
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c counterfactual_phase_metadata_bytes {}",
            stats.counterfactual_phase_metadata_bytes
        )
        .map_err(io_error)?;
        writeln!(
            output,
            "c peak_active_learned {}",
            stats.peak_active_learned_clauses
        )
        .map_err(io_error)?;
        writeln!(output, "c solve_seconds {:.6}", elapsed.as_secs_f64()).map_err(io_error)?;
    }

    match result {
        SolveResult::Sat(model) => {
            writeln!(output, "s SATISFIABLE").map_err(io_error)?;
            if options.model {
                write_model(&mut output, &model)?;
            }
            output.flush().map_err(io_error)?;
            Ok(SAT_EXIT)
        }
        SolveResult::Unsat => {
            writeln!(output, "s UNSATISFIABLE").map_err(io_error)?;
            output.flush().map_err(io_error)?;
            Ok(UNSAT_EXIT)
        }
        SolveResult::Unknown(_) => {
            writeln!(output, "s UNKNOWN").map_err(io_error)?;
            output.flush().map_err(io_error)?;
            Ok(0)
        }
    }
}

fn io_error(error: io::Error) -> String {
    error.to_string()
}

fn write_model(output: &mut impl Write, model: &sat::Model) -> Result<(), String> {
    if model.is_empty() {
        writeln!(output, "v 0").map_err(io_error)?;
        return Ok(());
    }

    for (index, value) in model.iter().enumerate() {
        if index % 16 == 0 {
            if index > 0 {
                writeln!(output, " 0").map_err(io_error)?;
            }
            write!(output, "v").map_err(io_error)?;
        }
        let variable = i64::try_from(index + 1).map_err(|_| "model is too large".to_owned())?;
        let literal = if value { variable } else { -variable };
        write!(output, " {literal}").map_err(io_error)?;
    }
    writeln!(output, " 0").map_err(io_error)
}

fn read_input(path: Option<&PathBuf>) -> Result<Vec<u8>, String> {
    match path {
        Some(path) if path.as_os_str() != "-" => {
            fs::read(path).map_err(|error| format!("could not read `{}`: {error}", path.display()))
        }
        _ => {
            let mut bytes = Vec::new();
            io::stdin()
                .read_to_end(&mut bytes)
                .map_err(|error| format!("could not read standard input: {error}"))?;
            Ok(bytes)
        }
    }
}

#[derive(Debug)]
struct Options {
    input: Option<PathBuf>,
    stats: bool,
    model: bool,
    minimize: bool,
    binary_resolution_minimization: bool,
    compact_clause_arena: bool,
    bounded_variable_elimination: bool,
    bounded_variable_addition: bool,
    macro_bounded_variable_addition: bool,
    failed_literal_probing: bool,
    clause_vivification: bool,
    clause_subsumption: bool,
    binary_fast_path: bool,
    restart_policy: RestartPolicy,
    block_lbd_restarts: bool,
    search_strategy: SearchStrategy,
    tiered_clause_management: bool,
    lbd_free_clause_management: bool,
    scan_debt_clause_management: bool,
    nonregular_clause_retention: bool,
    shadow_clause_reactivation: bool,
    counterfactual_phase_voting: bool,
    promote_clause_lbd: bool,
    chronological_backtracking: bool,
    systematic_rephasing: bool,
    restart_trail_reuse: RestartTrailReuse,
    proof: Option<PathBuf>,
}

#[derive(Debug)]
enum Action {
    Solve(Options),
    Help,
    Version,
}

fn parse_args(arguments: impl IntoIterator<Item = OsString>) -> Result<Action, String> {
    let mut input = None;
    let mut stats = false;
    let mut model = true;
    let mut minimize = true;
    let mut binary_resolution_minimization = false;
    let mut compact_clause_arena = false;
    let mut bounded_variable_elimination = false;
    let mut bounded_variable_addition = false;
    let mut macro_bounded_variable_addition = false;
    let mut failed_literal_probing = false;
    let mut clause_vivification = false;
    let mut clause_subsumption = false;
    let mut binary_fast_path = true;
    let mut restart_policy = RestartPolicy::Luby;
    let mut block_lbd_restarts = true;
    let mut search_strategy = SearchStrategy::Evsids;
    let mut tiered_clause_management = false;
    let mut lbd_free_clause_management = true;
    let mut scan_debt_clause_management = false;
    let mut nonregular_clause_retention = false;
    let mut shadow_clause_reactivation = false;
    let mut counterfactual_phase_voting = false;
    let mut promote_clause_lbd = true;
    let mut chronological_backtracking = true;
    let mut systematic_rephasing = false;
    let mut restart_trail_reuse = RestartTrailReuse::Never;
    let mut proof = None;
    let mut positional_only = false;

    let mut arguments = arguments.into_iter();
    while let Some(argument) = arguments.next() {
        if !positional_only {
            match argument.to_str() {
                Some("--help" | "-h") => return Ok(Action::Help),
                Some("--version" | "-V") => return Ok(Action::Version),
                Some("--stats") => {
                    stats = true;
                    continue;
                }
                Some("--no-model") => {
                    model = false;
                    continue;
                }
                Some("--no-minimize") => {
                    minimize = false;
                    continue;
                }
                Some("--binary-minimize") => {
                    binary_resolution_minimization = true;
                    continue;
                }
                Some("--no-binary-minimize") => {
                    binary_resolution_minimization = false;
                    continue;
                }
                Some("--compact-arena") => {
                    compact_clause_arena = true;
                    continue;
                }
                Some("--no-compact-arena") => {
                    compact_clause_arena = false;
                    continue;
                }
                Some("--eliminate") => {
                    bounded_variable_elimination = true;
                    continue;
                }
                Some("--no-eliminate") => {
                    bounded_variable_elimination = false;
                    continue;
                }
                Some("--factor") => {
                    bounded_variable_addition = true;
                    macro_bounded_variable_addition = false;
                    continue;
                }
                Some("--factor-macro") => {
                    bounded_variable_addition = true;
                    macro_bounded_variable_addition = true;
                    continue;
                }
                Some("--no-factor") => {
                    bounded_variable_addition = false;
                    macro_bounded_variable_addition = false;
                    continue;
                }
                Some("--probe") => {
                    failed_literal_probing = true;
                    continue;
                }
                Some("--no-probe") => {
                    failed_literal_probing = false;
                    continue;
                }
                Some("--vivify") => {
                    clause_vivification = true;
                    continue;
                }
                Some("--no-vivify") => {
                    clause_vivification = false;
                    continue;
                }
                Some("--subsume") => {
                    clause_subsumption = true;
                    continue;
                }
                Some("--no-subsume") => {
                    clause_subsumption = false;
                    continue;
                }
                Some("--no-binary-fast-path") => {
                    binary_fast_path = false;
                    continue;
                }
                Some("--no-tiers") => {
                    tiered_clause_management = false;
                    continue;
                }
                Some("--tiers") => {
                    tiered_clause_management = true;
                    continue;
                }
                Some("--lbd-free-reduction") => {
                    lbd_free_clause_management = true;
                    continue;
                }
                Some("--no-lbd-free-reduction") => {
                    lbd_free_clause_management = false;
                    continue;
                }
                Some("--scan-debt-reduction") => {
                    scan_debt_clause_management = true;
                    continue;
                }
                Some("--no-scan-debt-reduction") => {
                    scan_debt_clause_management = false;
                    continue;
                }
                Some("--nonregular-retention") => {
                    nonregular_clause_retention = true;
                    continue;
                }
                Some("--no-nonregular-retention") => {
                    nonregular_clause_retention = false;
                    continue;
                }
                Some("--shadow-reactivation") => {
                    shadow_clause_reactivation = true;
                    continue;
                }
                Some("--no-shadow-reactivation") => {
                    shadow_clause_reactivation = false;
                    continue;
                }
                Some("--counterfactual-phase") => {
                    counterfactual_phase_voting = true;
                    continue;
                }
                Some("--no-counterfactual-phase") => {
                    counterfactual_phase_voting = false;
                    continue;
                }
                Some("--no-lbd-promotion") => {
                    promote_clause_lbd = false;
                    continue;
                }
                Some("--chrono") => {
                    chronological_backtracking = true;
                    continue;
                }
                Some("--no-chrono") => {
                    chronological_backtracking = false;
                    continue;
                }
                Some("--rephase") => {
                    systematic_rephasing = true;
                    continue;
                }
                Some("--no-rephase") => {
                    systematic_rephasing = false;
                    continue;
                }
                Some("--reuse-trail") => {
                    restart_trail_reuse = RestartTrailReuse::Always;
                    continue;
                }
                Some("--no-reuse-trail") => {
                    restart_trail_reuse = RestartTrailReuse::Never;
                    continue;
                }
                Some(option) if option.starts_with("--reuse-trail=") => {
                    restart_trail_reuse = parse_restart_trail_reuse(&OsString::from(
                        option.trim_start_matches("--reuse-trail="),
                    ))?;
                    continue;
                }
                Some("--restart") => {
                    let value = arguments
                        .next()
                        .ok_or_else(|| "--restart requires lbd or luby".to_owned())?;
                    restart_policy = parse_restart_policy(&value)?;
                    continue;
                }
                Some("--no-block-restarts") => {
                    block_lbd_restarts = false;
                    continue;
                }
                Some("--search") => {
                    let value = arguments.next().ok_or_else(search_strategy_error)?;
                    search_strategy = parse_search_strategy(&value)?;
                    continue;
                }
                Some(option) if option.starts_with("--search=") => {
                    search_strategy = parse_search_strategy(&OsString::from(
                        option.trim_start_matches("--search="),
                    ))?;
                    continue;
                }
                Some(option) if option.starts_with("--restart=") => {
                    restart_policy = parse_restart_policy(&OsString::from(
                        option.trim_start_matches("--restart="),
                    ))?;
                    continue;
                }
                Some("--proof") => {
                    let path = arguments
                        .next()
                        .ok_or_else(|| "--proof requires a file path".to_owned())?;
                    if proof.replace(PathBuf::from(path)).is_some() {
                        return Err("--proof may only be specified once".to_owned());
                    }
                    continue;
                }
                Some(option) if option.starts_with("--proof=") => {
                    let path = option.trim_start_matches("--proof=");
                    if path.is_empty() {
                        return Err("--proof requires a nonempty file path".to_owned());
                    }
                    if proof.replace(PathBuf::from(path)).is_some() {
                        return Err("--proof may only be specified once".to_owned());
                    }
                    continue;
                }
                Some("--") => {
                    positional_only = true;
                    continue;
                }
                Some(option) if option.starts_with('-') && option != "-" => {
                    return Err(format!("unknown option `{option}`; try --help"));
                }
                _ => {}
            }
        }

        if input.replace(PathBuf::from(argument)).is_some() {
            return Err("expected at most one DIMACS input file".to_owned());
        }
    }

    if scan_debt_clause_management && !lbd_free_clause_management {
        return Err(
            "--scan-debt-reduction requires --lbd-free-reduction; remove --no-lbd-free-reduction"
                .to_owned(),
        );
    }
    if nonregular_clause_retention && !lbd_free_clause_management {
        return Err(
            "--nonregular-retention requires --lbd-free-reduction; remove --no-lbd-free-reduction"
                .to_owned(),
        );
    }
    if nonregular_clause_retention && scan_debt_clause_management {
        return Err(
            "--nonregular-retention cannot be combined with --scan-debt-reduction".to_owned(),
        );
    }
    if shadow_clause_reactivation && !lbd_free_clause_management {
        return Err(
            "--shadow-reactivation requires --lbd-free-reduction; remove --no-lbd-free-reduction"
                .to_owned(),
        );
    }
    if shadow_clause_reactivation && scan_debt_clause_management {
        return Err(
            "--shadow-reactivation cannot be combined with --scan-debt-reduction".to_owned(),
        );
    }
    if shadow_clause_reactivation && nonregular_clause_retention {
        return Err(
            "--shadow-reactivation cannot be combined with --nonregular-retention".to_owned(),
        );
    }
    if shadow_clause_reactivation && restart_trail_reuse != RestartTrailReuse::Never {
        return Err(
            "--shadow-reactivation requires root restarts; use --reuse-trail=never".to_owned(),
        );
    }
    if shadow_clause_reactivation && compact_clause_arena {
        return Err("--shadow-reactivation cannot be combined with --compact-arena".to_owned());
    }
    if counterfactual_phase_voting && !lbd_free_clause_management {
        return Err(
            "--counterfactual-phase requires --lbd-free-reduction; remove --no-lbd-free-reduction"
                .to_owned(),
        );
    }
    if counterfactual_phase_voting && scan_debt_clause_management {
        return Err(
            "--counterfactual-phase cannot be combined with --scan-debt-reduction".to_owned(),
        );
    }
    if counterfactual_phase_voting && nonregular_clause_retention {
        return Err(
            "--counterfactual-phase cannot be combined with --nonregular-retention".to_owned(),
        );
    }
    if counterfactual_phase_voting && shadow_clause_reactivation {
        return Err(
            "--counterfactual-phase cannot be combined with --shadow-reactivation".to_owned(),
        );
    }
    if counterfactual_phase_voting && restart_trail_reuse != RestartTrailReuse::Never {
        return Err(
            "--counterfactual-phase requires root restarts; use --reuse-trail=never".to_owned(),
        );
    }
    if counterfactual_phase_voting && compact_clause_arena {
        return Err("--counterfactual-phase cannot be combined with --compact-arena".to_owned());
    }
    if counterfactual_phase_voting && systematic_rephasing {
        return Err("--counterfactual-phase cannot be combined with --rephase".to_owned());
    }

    Ok(Action::Solve(Options {
        input,
        stats,
        model,
        minimize,
        binary_resolution_minimization,
        compact_clause_arena,
        bounded_variable_elimination,
        bounded_variable_addition,
        macro_bounded_variable_addition,
        failed_literal_probing,
        clause_vivification,
        clause_subsumption,
        binary_fast_path,
        restart_policy,
        block_lbd_restarts,
        search_strategy,
        tiered_clause_management,
        lbd_free_clause_management,
        scan_debt_clause_management,
        nonregular_clause_retention,
        shadow_clause_reactivation,
        counterfactual_phase_voting,
        promote_clause_lbd,
        chronological_backtracking,
        systematic_rephasing,
        restart_trail_reuse,
        proof,
    }))
}

fn parse_restart_policy(value: &OsString) -> Result<RestartPolicy, String> {
    match value.to_str() {
        Some("lbd") => Ok(RestartPolicy::Lbd),
        Some("luby") => Ok(RestartPolicy::Luby),
        _ => Err("--restart requires lbd or luby".to_owned()),
    }
}

fn parse_restart_trail_reuse(value: &OsString) -> Result<RestartTrailReuse, String> {
    match value.to_str() {
        Some("never") => Ok(RestartTrailReuse::Never),
        Some("always") => Ok(RestartTrailReuse::Always),
        Some("adaptive") => Ok(RestartTrailReuse::Adaptive),
        _ => Err("--reuse-trail requires never, always, or adaptive".to_owned()),
    }
}

fn parse_search_strategy(value: &OsString) -> Result<SearchStrategy, String> {
    match value.to_str() {
        Some("evsids") => Ok(SearchStrategy::Evsids),
        Some("lrb") => Ok(SearchStrategy::Lrb),
        Some("transfer") => Ok(SearchStrategy::Transfer),
        Some("chb") => Ok(SearchStrategy::Chb),
        Some("vmtf") => Ok(SearchStrategy::Vmtf),
        Some("focused") => Ok(SearchStrategy::Focused),
        Some("probe-evsids") => Ok(SearchStrategy::ProbeEvsids),
        Some("probe-vmtf") => Ok(SearchStrategy::ProbeVmtf),
        Some("focused-stable") => Ok(SearchStrategy::FocusedStable),
        _ => Err(search_strategy_error()),
    }
}

fn search_strategy_error() -> String {
    "--search requires evsids, lrb, transfer, chb, vmtf, focused, probe-evsids, probe-vmtf, or focused-stable".to_owned()
}

fn print_help() {
    println!(
        "sat {version}\n\
         Experimental CDCL SAT solver\n\n\
         USAGE:\n\
           sat [OPTIONS] [FILE]\n\n\
         ARGS:\n\
           <FILE>  DIMACS CNF input, or - / omitted for standard input\n\n\
         OPTIONS:\n\
           --stats      Print solver counters and elapsed solve time\n\
           --no-model   Do not print a satisfying assignment\n\
           --no-minimize  Disable recursive learned-clause minimization\n\
           --binary-minimize\n\
                        Enable one-hop binary-resolution minimization\n\
           --no-binary-minimize\n\
                        Disable binary-resolution minimization (default)\n\
           --compact-arena\n\
                        Reclaim deleted clause-arena payloads after reductions\n\
           --no-compact-arena\n\
                        Keep the clause arena append-only (default)\n\
           --eliminate  Run zero-growth bounded variable elimination\n\
           --no-eliminate\n\
                        Disable bounded variable elimination (default)\n\
           --factor     Factor exact short-clause products with fresh variables\n\
           --factor-macro\n\
                        Gate factoring on dense input and macro products\n\
           --no-factor  Disable bounded variable addition (default)\n\
           --probe      Run bounded failed-literal probing before search\n\
           --no-probe   Disable failed-literal probing (default)\n\
           --vivify    Run bounded original-clause vivification before search\n\
           --no-vivify Disable clause vivification (default)\n\
           --subsume   Run bounded short-clause subsumption and SSR\n\
           --no-subsume\n\
                       Disable clause subsumption and SSR (default)\n\
           --no-binary-fast-path\n\
                        Disable specialized binary-clause propagation\n\
           --tiers      Enable experimental usage-aged low-LBD retention\n\
           --no-tiers   Disable tiered learned-clause retention (default)\n\
           --lbd-free-reduction\n\
                        Use decaying clause usage and length-only reduction (default)\n\
           --no-lbd-free-reduction\n\
                        Use legacy LBD/activity learned-clause reduction\n\
           --scan-debt-reduction\n\
                        Rank the fixed usage-policy deletion quota by post-use scan debt\n\
           --no-scan-debt-reduction\n\
                        Disable experimental scan-debt ranking (default)\n\
           --nonregular-retention\n\
                        Protect sampled nonregular derivations in zero-use reduction\n\
           --no-nonregular-retention\n\
                        Disable sampled nonregular retention (default)\n\
           --shadow-reactivation\n\
                        Observe selected deletions noncausally and reactivate triggers\n\
           --no-shadow-reactivation\n\
                        Disable counterfactual shadow reactivation (default)\n\
           --counterfactual-phase\n\
                        Let unanimous would-unit deletions update saved phases at root restarts\n\
           --no-counterfactual-phase\n\
                        Disable counterfactual unit phase voting (default)\n\
           --no-lbd-promotion\n\
                        Keep learned-clause LBD fixed after creation\n\
           --chrono     Enable 100-level chronological backtracking (default)\n\
           --no-chrono  Disable chronological backtracking for ablation\n\
           --rephase    Enable experimental systematic phase resets\n\
           --no-rephase\n\
                        Disable systematic phase resets (default)\n\
           --reuse-trail\n\
                        Preserve high-priority EVSIDS levels across restarts\n\
           --reuse-trail=adaptive\n\
                        Select root or reused restarts from online productivity\n\
           --no-reuse-trail\n\
                        Backtrack to level zero at every restart (default)\n\
           --restart <lbd|luby>\n\
                        Select dynamic LBD or static Luby restarts (default)\n\
           --no-block-restarts\n\
                        Disable deep-trail blocking of dynamic LBD restarts\n\
           --search <STRATEGY>\n\
                        Select branching/restart regime (default: evsids)\n\
                        Choices: evsids, lrb, transfer, chb, vmtf, focused, probe-evsids,\n\
                        probe-vmtf, focused-stable\n\
           --proof <FILE>\n\
                        Stream a textual DRAT proof (meaningful for UNSAT)\n\
           -h, --help   Print help\n\
           -V, --version\n\n\
         EXIT STATUS:\n\
           10 SATISFIABLE, 20 UNSATISFIABLE, 1 input or runtime error",
        version = env!("CARGO_PKG_VERSION")
    );
}

#[cfg(test)]
mod tests {
    use std::ffi::OsString;

    use super::{Action, parse_args};

    #[test]
    fn parses_solver_options_and_input() {
        let action = parse_args([
            OsString::from("--stats"),
            OsString::from("--no-model"),
            OsString::from("example.cnf"),
        ])
        .unwrap();
        let Action::Solve(options) = action else {
            panic!("expected solve action");
        };
        assert!(options.stats);
        assert!(!options.model);
        assert!(options.minimize);
        assert!(!options.binary_resolution_minimization);
        assert!(!options.compact_clause_arena);
        assert!(!options.bounded_variable_elimination);
        assert!(!options.failed_literal_probing);
        assert!(!options.clause_vivification);
        assert!(!options.clause_subsumption);
        assert!(options.binary_fast_path);
        assert!(!options.tiered_clause_management);
        assert!(options.lbd_free_clause_management);
        assert!(!options.scan_debt_clause_management);
        assert!(!options.nonregular_clause_retention);
        assert!(!options.shadow_clause_reactivation);
        assert!(!options.counterfactual_phase_voting);
        assert!(options.promote_clause_lbd);
        assert!(options.chronological_backtracking);
        assert!(!options.systematic_rephasing);
        assert_eq!(options.restart_trail_reuse, sat::RestartTrailReuse::Never);
        assert_eq!(options.restart_policy, sat::RestartPolicy::Luby);
        assert!(options.block_lbd_restarts);
        assert_eq!(options.search_strategy, sat::SearchStrategy::Evsids);
        assert!(options.proof.is_none());
        assert_eq!(options.input.unwrap().to_string_lossy(), "example.cnf");
    }

    #[test]
    fn rejects_unknown_options_and_multiple_inputs() {
        assert!(parse_args([OsString::from("--wat")]).is_err());
        assert!(parse_args([OsString::from("one.cnf"), OsString::from("two.cnf")]).is_err());
        assert!(parse_args([OsString::from("--restart=nope")]).is_err());
        assert!(parse_args([OsString::from("--reuse-trail=nope")]).is_err());
        assert!(parse_args([OsString::from("--search=nope")]).is_err());
    }

    #[test]
    fn parses_tier_ablation() {
        let Action::Solve(options) = parse_args([
            OsString::from("--tiers"),
            OsString::from("--no-lbd-promotion"),
        ])
        .expect("valid tier ablation") else {
            panic!("expected solve action");
        };
        assert!(options.tiered_clause_management);
        assert!(!options.promote_clause_lbd);
    }

    #[test]
    fn parses_lbd_free_clause_management_ablation() {
        let Action::Solve(enabled) = parse_args([OsString::from("--lbd-free-reduction")])
            .expect("valid LBD-free clause-management policy")
        else {
            panic!("expected solve action");
        };
        assert!(enabled.lbd_free_clause_management);

        let Action::Solve(disabled) = parse_args([
            OsString::from("--lbd-free-reduction"),
            OsString::from("--no-lbd-free-reduction"),
        ])
        .expect("valid LBD-free clause-management ablation") else {
            panic!("expected solve action");
        };
        assert!(!disabled.lbd_free_clause_management);
    }

    #[test]
    fn parses_scan_debt_clause_management_ablation_and_rejects_legacy_reduction() {
        let Action::Solve(enabled) = parse_args([OsString::from("--scan-debt-reduction")])
            .expect("valid scan-debt clause-management policy")
        else {
            panic!("expected solve action");
        };
        assert!(enabled.lbd_free_clause_management);
        assert!(enabled.scan_debt_clause_management);

        let Action::Solve(disabled) = parse_args([
            OsString::from("--scan-debt-reduction"),
            OsString::from("--no-scan-debt-reduction"),
        ])
        .expect("valid scan-debt clause-management ablation") else {
            panic!("expected solve action");
        };
        assert!(!disabled.scan_debt_clause_management);

        assert!(
            parse_args([
                OsString::from("--scan-debt-reduction"),
                OsString::from("--no-lbd-free-reduction"),
            ])
            .is_err()
        );
    }

    #[test]
    fn parses_nonregular_retention_and_rejects_incompatible_reducers() {
        let Action::Solve(enabled) = parse_args([OsString::from("--nonregular-retention")])
            .expect("valid nonregular-retention policy")
        else {
            panic!("expected solve action");
        };
        assert!(enabled.lbd_free_clause_management);
        assert!(enabled.nonregular_clause_retention);

        let Action::Solve(disabled) = parse_args([
            OsString::from("--nonregular-retention"),
            OsString::from("--no-nonregular-retention"),
        ])
        .expect("valid nonregular-retention ablation") else {
            panic!("expected solve action");
        };
        assert!(!disabled.nonregular_clause_retention);

        assert!(
            parse_args([
                OsString::from("--nonregular-retention"),
                OsString::from("--no-lbd-free-reduction"),
            ])
            .is_err()
        );
        assert!(
            parse_args([
                OsString::from("--nonregular-retention"),
                OsString::from("--scan-debt-reduction"),
            ])
            .is_err()
        );
    }

    #[test]
    fn parses_shadow_reactivation_and_rejects_incompatible_policies() {
        let Action::Solve(enabled) = parse_args([OsString::from("--shadow-reactivation")])
            .expect("valid counterfactual shadow policy")
        else {
            panic!("expected solve action");
        };
        assert!(enabled.lbd_free_clause_management);
        assert!(enabled.shadow_clause_reactivation);

        let Action::Solve(disabled) = parse_args([
            OsString::from("--shadow-reactivation"),
            OsString::from("--no-shadow-reactivation"),
        ])
        .expect("valid shadow-reactivation ablation") else {
            panic!("expected solve action");
        };
        assert!(!disabled.shadow_clause_reactivation);

        for incompatible in [
            "--no-lbd-free-reduction",
            "--scan-debt-reduction",
            "--nonregular-retention",
            "--reuse-trail",
            "--compact-arena",
        ] {
            assert!(
                parse_args([
                    OsString::from("--shadow-reactivation"),
                    OsString::from(incompatible),
                ])
                .is_err(),
                "{incompatible} must be rejected"
            );
        }
    }

    #[test]
    fn parses_counterfactual_phase_and_rejects_incompatible_policies() {
        let Action::Solve(enabled) = parse_args([OsString::from("--counterfactual-phase")])
            .expect("valid counterfactual phase policy")
        else {
            panic!("expected solve action");
        };
        assert!(enabled.lbd_free_clause_management);
        assert!(enabled.counterfactual_phase_voting);

        let Action::Solve(disabled) = parse_args([
            OsString::from("--counterfactual-phase"),
            OsString::from("--no-counterfactual-phase"),
        ])
        .expect("valid counterfactual phase ablation") else {
            panic!("expected solve action");
        };
        assert!(!disabled.counterfactual_phase_voting);

        for incompatible in [
            "--no-lbd-free-reduction",
            "--scan-debt-reduction",
            "--nonregular-retention",
            "--shadow-reactivation",
            "--reuse-trail",
            "--compact-arena",
            "--rephase",
        ] {
            assert!(
                parse_args([
                    OsString::from("--counterfactual-phase"),
                    OsString::from(incompatible),
                ])
                .is_err(),
                "{incompatible} must be rejected"
            );
        }
    }

    #[test]
    fn parses_binary_resolution_minimization_ablation() {
        let Action::Solve(enabled) = parse_args([OsString::from("--binary-minimize")])
            .expect("valid binary minimization policy")
        else {
            panic!("expected solve action");
        };
        assert!(enabled.binary_resolution_minimization);

        let Action::Solve(disabled) = parse_args([
            OsString::from("--binary-minimize"),
            OsString::from("--no-binary-minimize"),
        ])
        .expect("valid binary minimization ablation") else {
            panic!("expected solve action");
        };
        assert!(!disabled.binary_resolution_minimization);
    }

    #[test]
    fn parses_clause_arena_compaction_ablation() {
        let Action::Solve(enabled) = parse_args([OsString::from("--compact-arena")])
            .expect("valid clause-arena compaction policy")
        else {
            panic!("expected solve action");
        };
        assert!(enabled.compact_clause_arena);

        let Action::Solve(disabled) = parse_args([
            OsString::from("--compact-arena"),
            OsString::from("--no-compact-arena"),
        ])
        .expect("valid clause-arena compaction ablation") else {
            panic!("expected solve action");
        };
        assert!(!disabled.compact_clause_arena);
    }

    #[test]
    fn parses_bounded_variable_elimination_ablation() {
        let Action::Solve(enabled) = parse_args([OsString::from("--eliminate")])
            .expect("valid bounded variable elimination policy")
        else {
            panic!("expected solve action");
        };
        assert!(enabled.bounded_variable_elimination);

        let Action::Solve(disabled) = parse_args([
            OsString::from("--eliminate"),
            OsString::from("--no-eliminate"),
        ])
        .expect("valid bounded variable elimination ablation") else {
            panic!("expected solve action");
        };
        assert!(!disabled.bounded_variable_elimination);
    }

    #[test]
    fn parses_bounded_variable_addition_ablation() {
        let Action::Solve(enabled) =
            parse_args([OsString::from("--factor")]).expect("valid factorization policy")
        else {
            panic!("expected solve action");
        };
        assert!(enabled.bounded_variable_addition);
        assert!(!enabled.macro_bounded_variable_addition);

        let Action::Solve(macro_enabled) = parse_args([OsString::from("--factor-macro")])
            .expect("valid macro factorization policy")
        else {
            panic!("expected solve action");
        };
        assert!(macro_enabled.bounded_variable_addition);
        assert!(macro_enabled.macro_bounded_variable_addition);

        let Action::Solve(disabled) = parse_args([
            OsString::from("--factor-macro"),
            OsString::from("--no-factor"),
        ])
        .expect("valid factorization ablation") else {
            panic!("expected solve action");
        };
        assert!(!disabled.bounded_variable_addition);
        assert!(!disabled.macro_bounded_variable_addition);
    }

    #[test]
    fn parses_failed_literal_probing_ablation() {
        let Action::Solve(enabled) =
            parse_args([OsString::from("--probe")]).expect("valid probing policy")
        else {
            panic!("expected solve action");
        };
        assert!(enabled.failed_literal_probing);

        let Action::Solve(disabled) =
            parse_args([OsString::from("--probe"), OsString::from("--no-probe")])
                .expect("valid probing ablation")
        else {
            panic!("expected solve action");
        };
        assert!(!disabled.failed_literal_probing);
    }

    #[test]
    fn parses_clause_vivification_ablation() {
        let Action::Solve(enabled) =
            parse_args([OsString::from("--vivify")]).expect("valid vivification policy")
        else {
            panic!("expected solve action");
        };
        assert!(enabled.clause_vivification);

        let Action::Solve(disabled) =
            parse_args([OsString::from("--vivify"), OsString::from("--no-vivify")])
                .expect("valid vivification ablation")
        else {
            panic!("expected solve action");
        };
        assert!(!disabled.clause_vivification);
    }

    #[test]
    fn parses_clause_subsumption_ablation() {
        let Action::Solve(enabled) =
            parse_args([OsString::from("--subsume")]).expect("valid subsumption policy")
        else {
            panic!("expected solve action");
        };
        assert!(enabled.clause_subsumption);

        let Action::Solve(disabled) =
            parse_args([OsString::from("--subsume"), OsString::from("--no-subsume")])
                .expect("valid subsumption ablation")
        else {
            panic!("expected solve action");
        };
        assert!(!disabled.clause_subsumption);
    }

    #[test]
    fn parses_chronological_backtracking_ablation() {
        let Action::Solve(enabled) =
            parse_args([OsString::from("--chrono")]).expect("valid chronological policy")
        else {
            panic!("expected solve action");
        };
        assert!(enabled.chronological_backtracking);

        let Action::Solve(disabled) =
            parse_args([OsString::from("--chrono"), OsString::from("--no-chrono")])
                .expect("valid chronological ablation")
        else {
            panic!("expected solve action");
        };
        assert!(!disabled.chronological_backtracking);
    }

    #[test]
    fn parses_systematic_rephasing_ablation() {
        let Action::Solve(enabled) =
            parse_args([OsString::from("--rephase")]).expect("valid rephase policy")
        else {
            panic!("expected solve action");
        };
        assert!(enabled.systematic_rephasing);

        let Action::Solve(disabled) =
            parse_args([OsString::from("--rephase"), OsString::from("--no-rephase")])
                .expect("valid rephase ablation")
        else {
            panic!("expected solve action");
        };
        assert!(!disabled.systematic_rephasing);
    }

    #[test]
    fn parses_restart_trail_reuse_ablation() {
        let Action::Solve(enabled) =
            parse_args([OsString::from("--reuse-trail")]).expect("valid trail reuse policy")
        else {
            panic!("expected solve action");
        };
        assert_eq!(enabled.restart_trail_reuse, sat::RestartTrailReuse::Always);

        let Action::Solve(adaptive) = parse_args([OsString::from("--reuse-trail=adaptive")])
            .expect("valid adaptive trail reuse policy")
        else {
            panic!("expected solve action");
        };
        assert_eq!(
            adaptive.restart_trail_reuse,
            sat::RestartTrailReuse::Adaptive
        );

        let Action::Solve(disabled) = parse_args([
            OsString::from("--reuse-trail"),
            OsString::from("--no-reuse-trail"),
        ])
        .expect("valid trail reuse ablation") else {
            panic!("expected solve action");
        };
        assert_eq!(disabled.restart_trail_reuse, sat::RestartTrailReuse::Never);
    }

    #[test]
    fn parses_restart_policy_in_both_forms() {
        let Action::Solve(luby) =
            parse_args([OsString::from("--restart=luby")]).expect("valid Luby policy")
        else {
            panic!("expected solve action");
        };
        assert_eq!(luby.restart_policy, sat::RestartPolicy::Luby);

        let Action::Solve(lbd) = parse_args([OsString::from("--restart"), OsString::from("lbd")])
            .expect("valid LBD policy")
        else {
            panic!("expected solve action");
        };
        assert_eq!(lbd.restart_policy, sat::RestartPolicy::Lbd);
    }

    #[test]
    fn parses_search_strategies() {
        let Action::Solve(options) =
            parse_args([OsString::from("--search=lrb")]).expect("valid LRB strategy")
        else {
            panic!("expected solve action");
        };
        assert_eq!(options.search_strategy, sat::SearchStrategy::Lrb);

        let Action::Solve(options) =
            parse_args([OsString::from("--search=transfer")]).expect("valid transfer strategy")
        else {
            panic!("expected solve action");
        };
        assert_eq!(options.search_strategy, sat::SearchStrategy::Transfer);

        let Action::Solve(options) =
            parse_args([OsString::from("--search=chb")]).expect("valid CHB strategy")
        else {
            panic!("expected solve action");
        };
        assert_eq!(options.search_strategy, sat::SearchStrategy::Chb);

        let Action::Solve(options) =
            parse_args([OsString::from("--search=focused-stable")]).expect("valid search strategy")
        else {
            panic!("expected solve action");
        };
        assert_eq!(options.search_strategy, sat::SearchStrategy::FocusedStable);

        let Action::Solve(options) =
            parse_args([OsString::from("--search"), OsString::from("vmtf")])
                .expect("valid VMTF strategy")
        else {
            panic!("expected solve action");
        };
        assert_eq!(options.search_strategy, sat::SearchStrategy::Vmtf);
    }
}
