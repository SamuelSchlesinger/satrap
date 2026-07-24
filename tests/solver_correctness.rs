use sat::{
    IncrementalError, Lit, Model, RestartPolicy, RestartTrailReuse, SearchStrategy, SolveLimits,
    SolveResult, Solver, SolverConfig, UnknownReason, Var,
};

#[test]
fn differential_against_brute_force_on_small_random_formulas() {
    let mut random = XorShift64::new(0x6a09_e667_f3bc_c909);

    for case in 0..2_000 {
        let variable_count = random.range(8);
        let clause_count = random.range(28);
        let mut clauses = Vec::with_capacity(clause_count);

        for _ in 0..clause_count {
            let clause_length = if variable_count == 0 {
                0
            } else {
                random.range(variable_count + 3)
            };
            let mut clause = Vec::with_capacity(clause_length);
            for _ in 0..clause_length {
                let variable = Var::new(random.range(variable_count) as u32);
                clause.push(Lit::new(variable, random.next() & 1 == 0));
            }
            clauses.push(clause);
        }

        let expected = brute_force(variable_count, &clauses);
        let (actual, stats) = solve(variable_count, &clauses);
        assert_eq!(
            actual.is_sat(),
            expected.is_some(),
            "SAT mismatch in generated case {case}: {clauses:?}; stats={stats:?}"
        );
        if let SolveResult::Sat(model) = &actual {
            assert_eq!(model.len(), variable_count, "case {case}");
            assert!(satisfies(model, &clauses), "invalid model in case {case}");
        }

        let (unminimized, stats) = solve_with_config(
            variable_count,
            &clauses,
            SolverConfig {
                minimize_learned_clauses: false,
                ..SolverConfig::default()
            },
        );
        assert_eq!(
            unminimized.is_sat(),
            expected.is_some(),
            "unminimized SAT mismatch in generated case {case}: {clauses:?}; stats={stats:?}"
        );
        assert_eq!(stats.minimized_literals, 0);
        if let SolveResult::Sat(model) = &unminimized {
            assert!(
                satisfies(model, &clauses),
                "invalid unminimized model in case {case}"
            );
        }

        let (probed, stats) = solve_with_config(
            variable_count,
            &clauses,
            SolverConfig {
                failed_literal_probing: true,
                ..SolverConfig::default()
            },
        );
        assert_eq!(
            probed.is_sat(),
            expected.is_some(),
            "probed SAT mismatch in generated case {case}: {clauses:?}; stats={stats:?}"
        );
        if let SolveResult::Sat(model) = &probed {
            assert!(
                satisfies(model, &clauses),
                "invalid probed model in case {case}"
            );
        }

        let (vivified, stats) = solve_with_config(
            variable_count,
            &clauses,
            SolverConfig {
                clause_vivification: true,
                ..SolverConfig::default()
            },
        );
        assert_eq!(
            vivified.is_sat(),
            expected.is_some(),
            "vivified SAT mismatch in generated case {case}: {clauses:?}; stats={stats:?}"
        );
        if let SolveResult::Sat(model) = &vivified {
            assert!(
                satisfies(model, &clauses),
                "invalid vivified model in case {case}"
            );
        }

        let (subsumed, stats) = solve_with_config(
            variable_count,
            &clauses,
            SolverConfig {
                clause_subsumption: true,
                ..SolverConfig::default()
            },
        );
        assert_eq!(
            subsumed.is_sat(),
            expected.is_some(),
            "subsumed SAT mismatch in generated case {case}: {clauses:?}; stats={stats:?}"
        );
        if let SolveResult::Sat(model) = &subsumed {
            assert!(
                satisfies(model, &clauses),
                "invalid subsumed model in case {case}"
            );
        }

        let (binary_minimized, stats) = solve_with_config(
            variable_count,
            &clauses,
            SolverConfig {
                binary_resolution_minimization: true,
                ..SolverConfig::default()
            },
        );
        assert_eq!(
            binary_minimized.is_sat(),
            expected.is_some(),
            "binary-minimized SAT mismatch in generated case {case}: {clauses:?}; stats={stats:?}"
        );
        if let SolveResult::Sat(model) = &binary_minimized {
            assert!(
                satisfies(model, &clauses),
                "invalid binary-minimized model in case {case}"
            );
        }

        let (arena_compacted, stats) = solve_with_config(
            variable_count,
            &clauses,
            SolverConfig {
                compact_clause_arena: true,
                ..SolverConfig::default()
            },
        );
        assert_eq!(
            arena_compacted.is_sat(),
            expected.is_some(),
            "arena-compacted SAT mismatch in generated case {case}: {clauses:?}; stats={stats:?}"
        );
        if let SolveResult::Sat(model) = &arena_compacted {
            assert!(
                satisfies(model, &clauses),
                "invalid arena-compacted model in case {case}"
            );
        }

        let (eliminated, stats) = solve_with_config(
            variable_count,
            &clauses,
            SolverConfig {
                bounded_variable_elimination: true,
                ..SolverConfig::default()
            },
        );
        assert_eq!(
            eliminated.is_sat(),
            expected.is_some(),
            "eliminated SAT mismatch in generated case {case}: {clauses:?}; stats={stats:?}"
        );
        if let SolveResult::Sat(model) = &eliminated {
            assert!(
                satisfies(model, &clauses),
                "invalid reconstructed model in case {case}"
            );
        }

        let (factored, stats) = solve_with_config(
            variable_count,
            &clauses,
            SolverConfig {
                bounded_variable_addition: true,
                ..SolverConfig::default()
            },
        );
        assert_eq!(
            factored.is_sat(),
            expected.is_some(),
            "factored SAT mismatch in generated case {case}: {clauses:?}; stats={stats:?}"
        );
        if let SolveResult::Sat(model) = &factored {
            assert_eq!(model.len(), variable_count, "factored case {case}");
            assert!(
                satisfies(model, &clauses),
                "invalid factored model in case {case}"
            );
        }

        let (macro_factored, stats) = solve_with_config(
            variable_count,
            &clauses,
            SolverConfig {
                bounded_variable_addition: true,
                macro_bounded_variable_addition: true,
                ..SolverConfig::default()
            },
        );
        assert_eq!(
            macro_factored.is_sat(),
            expected.is_some(),
            "macro-factored SAT mismatch in generated case {case}: {clauses:?}; stats={stats:?}"
        );
        if let SolveResult::Sat(model) = &macro_factored {
            assert_eq!(model.len(), variable_count, "macro-factored case {case}");
            assert!(
                satisfies(model, &clauses),
                "invalid macro-factored model in case {case}"
            );
        }

        let (generic_binary, stats) = solve_with_config(
            variable_count,
            &clauses,
            SolverConfig {
                binary_fast_path: false,
                ..SolverConfig::default()
            },
        );
        assert_eq!(
            generic_binary.is_sat(),
            expected.is_some(),
            "generic-binary SAT mismatch in generated case {case}: {clauses:?}; stats={stats:?}"
        );
        assert_eq!(stats.binary_watch_visits, 0);
        if let SolveResult::Sat(model) = &generic_binary {
            assert!(
                satisfies(model, &clauses),
                "invalid generic-binary model in case {case}"
            );
        }

        let (tiered, stats) = solve_with_config(
            variable_count,
            &clauses,
            SolverConfig {
                tiered_clause_management: true,
                ..SolverConfig::default()
            },
        );
        assert_eq!(
            tiered.is_sat(),
            expected.is_some(),
            "tiered SAT mismatch in generated case {case}: {clauses:?}; stats={stats:?}"
        );
        if let SolveResult::Sat(model) = &tiered {
            assert!(
                satisfies(model, &clauses),
                "invalid tiered model in case {case}"
            );
        }

        let (lbd_free, stats) = solve_with_config(
            variable_count,
            &clauses,
            SolverConfig {
                lbd_free_clause_management: true,
                ..SolverConfig::default()
            },
        );
        assert_eq!(
            lbd_free.is_sat(),
            expected.is_some(),
            "LBD-free clause-management SAT mismatch in generated case {case}: {clauses:?}; stats={stats:?}"
        );
        if let SolveResult::Sat(model) = &lbd_free {
            assert!(
                satisfies(model, &clauses),
                "invalid LBD-free clause-management model in case {case}"
            );
        }

        let (scan_debt, stats) = solve_with_config(
            variable_count,
            &clauses,
            SolverConfig {
                scan_debt_clause_management: true,
                ..SolverConfig::default()
            },
        );
        assert_eq!(
            scan_debt.is_sat(),
            expected.is_some(),
            "scan-debt clause-management SAT mismatch in generated case {case}: {clauses:?}; stats={stats:?}"
        );
        if let SolveResult::Sat(model) = &scan_debt {
            assert!(
                satisfies(model, &clauses),
                "invalid scan-debt clause-management model in case {case}"
            );
        }

        let (nonregular_retention, stats) = solve_with_config(
            variable_count,
            &clauses,
            SolverConfig {
                nonregular_clause_retention: true,
                ..SolverConfig::default()
            },
        );
        assert_eq!(
            nonregular_retention.is_sat(),
            expected.is_some(),
            "nonregular-retention SAT mismatch in generated case {case}: {clauses:?}; stats={stats:?}"
        );
        if let SolveResult::Sat(model) = &nonregular_retention {
            assert!(
                satisfies(model, &clauses),
                "invalid nonregular-retention model in case {case}"
            );
        }

        let (shadow_reactivation, stats) = solve_with_config(
            variable_count,
            &clauses,
            SolverConfig {
                shadow_clause_reactivation: true,
                ..SolverConfig::default()
            },
        );
        assert_eq!(
            shadow_reactivation.is_sat(),
            expected.is_some(),
            "shadow-reactivation SAT mismatch in generated case {case}: {clauses:?}; stats={stats:?}"
        );
        if let SolveResult::Sat(model) = &shadow_reactivation {
            assert!(
                satisfies(model, &clauses),
                "invalid shadow-reactivation model in case {case}"
            );
        }

        let (counterfactual_phase, stats) = solve_with_config(
            variable_count,
            &clauses,
            SolverConfig {
                counterfactual_phase_voting: true,
                ..SolverConfig::default()
            },
        );
        assert_eq!(
            counterfactual_phase.is_sat(),
            expected.is_some(),
            "counterfactual-phase SAT mismatch in generated case {case}: {clauses:?}; stats={stats:?}"
        );
        if let SolveResult::Sat(model) = &counterfactual_phase {
            assert!(
                satisfies(model, &clauses),
                "invalid counterfactual-phase model in case {case}"
            );
        }

        let (chronological, stats) = solve_with_config(
            variable_count,
            &clauses,
            SolverConfig {
                chronological_backtracking: true,
                ..SolverConfig::default()
            },
        );
        assert_eq!(
            chronological.is_sat(),
            expected.is_some(),
            "chronological SAT mismatch in generated case {case}: {clauses:?}; stats={stats:?}"
        );
        if let SolveResult::Sat(model) = &chronological {
            assert!(
                satisfies(model, &clauses),
                "invalid chronological model in case {case}"
            );
        }

        let (rephased, stats) = solve_with_config(
            variable_count,
            &clauses,
            SolverConfig {
                systematic_rephasing: true,
                ..SolverConfig::default()
            },
        );
        assert_eq!(
            rephased.is_sat(),
            expected.is_some(),
            "rephased SAT mismatch in generated case {case}: {clauses:?}; stats={stats:?}"
        );
        if let SolveResult::Sat(model) = &rephased {
            assert!(
                satisfies(model, &clauses),
                "invalid rephased model in case {case}"
            );
        }

        let (trail_reuse, stats) = solve_with_config(
            variable_count,
            &clauses,
            SolverConfig {
                restart_trail_reuse: RestartTrailReuse::Always,
                ..SolverConfig::default()
            },
        );
        assert_eq!(
            trail_reuse.is_sat(),
            expected.is_some(),
            "trail-reuse SAT mismatch in generated case {case}: {clauses:?}; stats={stats:?}"
        );
        if let SolveResult::Sat(model) = &trail_reuse {
            assert!(
                satisfies(model, &clauses),
                "invalid trail-reuse model in case {case}"
            );
        }

        let (adaptive_trail_reuse, stats) = solve_with_config(
            variable_count,
            &clauses,
            SolverConfig {
                restart_trail_reuse: RestartTrailReuse::Adaptive,
                ..SolverConfig::default()
            },
        );
        assert_eq!(
            adaptive_trail_reuse.is_sat(),
            expected.is_some(),
            "adaptive-trail-reuse SAT mismatch in generated case {case}: {clauses:?}; stats={stats:?}"
        );
        if let SolveResult::Sat(model) = &adaptive_trail_reuse {
            assert!(
                satisfies(model, &clauses),
                "invalid adaptive-trail-reuse model in case {case}"
            );
        }

        let (lbd_restart, stats) = solve_with_config(
            variable_count,
            &clauses,
            SolverConfig {
                restart_policy: RestartPolicy::Lbd,
                ..SolverConfig::default()
            },
        );
        assert_eq!(
            lbd_restart.is_sat(),
            expected.is_some(),
            "LBD-restart SAT mismatch in generated case {case}: {clauses:?}; stats={stats:?}"
        );
        if let SolveResult::Sat(model) = &lbd_restart {
            assert!(
                satisfies(model, &clauses),
                "invalid LBD-restart model in case {case}"
            );
        }

        let (lrb, stats) = solve_with_config(
            variable_count,
            &clauses,
            SolverConfig {
                search_strategy: SearchStrategy::Lrb,
                ..SolverConfig::default()
            },
        );
        assert_eq!(
            lrb.is_sat(),
            expected.is_some(),
            "LRB SAT mismatch in generated case {case}: {clauses:?}; stats={stats:?}"
        );
        if let SolveResult::Sat(model) = &lrb {
            assert!(
                satisfies(model, &clauses),
                "invalid LRB model in case {case}"
            );
        }

        let (transfer, stats) = solve_with_config(
            variable_count,
            &clauses,
            SolverConfig {
                search_strategy: SearchStrategy::Transfer,
                ..SolverConfig::default()
            },
        );
        assert_eq!(
            transfer.is_sat(),
            expected.is_some(),
            "transfer SAT mismatch in generated case {case}: {clauses:?}; stats={stats:?}"
        );
        if let SolveResult::Sat(model) = &transfer {
            assert!(
                satisfies(model, &clauses),
                "invalid transfer model in case {case}"
            );
        }

        let (chb, stats) = solve_with_config(
            variable_count,
            &clauses,
            SolverConfig {
                search_strategy: SearchStrategy::Chb,
                ..SolverConfig::default()
            },
        );
        assert_eq!(
            chb.is_sat(),
            expected.is_some(),
            "CHB SAT mismatch in generated case {case}: {clauses:?}; stats={stats:?}"
        );
        if let SolveResult::Sat(model) = &chb {
            assert!(
                satisfies(model, &clauses),
                "invalid CHB model in case {case}"
            );
        }

        let (focused_stable, stats) = solve_with_config(
            variable_count,
            &clauses,
            SolverConfig {
                search_strategy: SearchStrategy::FocusedStable,
                ..SolverConfig::default()
            },
        );
        assert_eq!(
            focused_stable.is_sat(),
            expected.is_some(),
            "focused/stable SAT mismatch in generated case {case}: {clauses:?}; stats={stats:?}"
        );
        if let SolveResult::Sat(model) = &focused_stable {
            assert!(
                satisfies(model, &clauses),
                "invalid focused/stable model in case {case}"
            );
        }
    }
}

#[test]
fn incremental_assumption_queries_differential_against_brute_force() {
    let mut random = XorShift64::new(0xbb67_ae85_84ca_a73b);

    for case in 0..500 {
        let variable_count = 1 + random.range(6);
        let clause_count = random.range(18);
        let mut clauses = Vec::with_capacity(clause_count);
        for _ in 0..clause_count {
            let clause_length = random.range(variable_count + 2);
            let clause = (0..clause_length)
                .map(|_| {
                    let variable = Var::new(random.range(variable_count) as u32);
                    Lit::new(variable, random.next() & 1 == 0)
                })
                .collect::<Vec<_>>();
            clauses.push(clause);
        }

        let mut solver = Solver::new();
        solver.reserve_variables(variable_count);
        for clause in &clauses {
            solver.add_clause(clause);
        }

        for query in 0..20 {
            let assumption_count = random.range(variable_count + 3);
            let assumptions = (0..assumption_count)
                .map(|_| {
                    let variable = Var::new(random.range(variable_count) as u32);
                    Lit::new(variable, random.next() & 1 == 0)
                })
                .collect::<Vec<_>>();
            let mut augmented = clauses.clone();
            augmented.extend(assumptions.iter().copied().map(|literal| vec![literal]));
            let expected = brute_force(variable_count, &augmented);
            let actual = solver.solve_assuming(&assumptions);

            assert_eq!(
                actual.is_sat(),
                expected.is_some(),
                "assumption mismatch in case {case}, query {query}: \
                 clauses={clauses:?}, assumptions={assumptions:?}, \
                 failed={:?}, stats={:?}",
                solver.failed_assumptions(),
                solver.stats()
            );
            if let SolveResult::Sat(model) = &actual {
                assert!(satisfies(model, &clauses));
                assert!(
                    assumptions
                        .iter()
                        .all(|&literal| model.literal_value(literal)),
                    "model violates an assumption in case {case}, query {query}"
                );
                assert!(solver.failed_assumptions().is_empty());
            } else if brute_force(variable_count, &clauses).is_some() {
                assert!(
                    !solver.failed_assumptions().is_empty(),
                    "an assumption-only contradiction needs a failed subset"
                );
                let mut core_formula = clauses.clone();
                core_formula.extend(
                    solver
                        .failed_assumptions()
                        .iter()
                        .copied()
                        .map(|literal| vec![literal]),
                );
                assert!(
                    brute_force(variable_count, &core_formula).is_none(),
                    "reported failed assumptions are satisfiable in case {case}, query {query}"
                );
            }
        }
    }
}

/// Configurations that differ only in deep-search machinery. Every entry must
/// agree on every instance; disagreement is a soundness bug in one of them.
fn deep_search_configurations() -> Vec<(&'static str, SolverConfig)> {
    let default = SolverConfig::default();
    vec![
        ("default", default),
        (
            "legacy-reduction",
            SolverConfig {
                lbd_free_clause_management: false,
                ..default
            },
        ),
        (
            "tiered-legacy-reduction",
            SolverConfig {
                lbd_free_clause_management: false,
                tiered_clause_management: true,
                ..default
            },
        ),
        (
            "scan-debt",
            SolverConfig {
                scan_debt_clause_management: true,
                ..default
            },
        ),
        (
            "nonregular-retention",
            SolverConfig {
                nonregular_clause_retention: true,
                ..default
            },
        ),
        (
            "shadow-reactivation",
            SolverConfig {
                shadow_clause_reactivation: true,
                ..default
            },
        ),
        (
            "counterfactual-phase",
            SolverConfig {
                counterfactual_phase_voting: true,
                ..default
            },
        ),
        (
            "compact-arena",
            SolverConfig {
                compact_clause_arena: true,
                ..default
            },
        ),
        (
            "lbd-restarts",
            SolverConfig {
                restart_policy: RestartPolicy::Lbd,
                ..default
            },
        ),
        (
            "unblocked-lbd-restarts",
            SolverConfig {
                restart_policy: RestartPolicy::Lbd,
                block_lbd_restarts: false,
                ..default
            },
        ),
        (
            "trail-reuse",
            SolverConfig {
                restart_trail_reuse: RestartTrailReuse::Always,
                ..default
            },
        ),
        (
            "adaptive-trail-reuse",
            SolverConfig {
                restart_trail_reuse: RestartTrailReuse::Adaptive,
                ..default
            },
        ),
        (
            "rephase",
            SolverConfig {
                systematic_rephasing: true,
                ..default
            },
        ),
        (
            "no-chrono",
            SolverConfig {
                chronological_backtracking: false,
                ..default
            },
        ),
        (
            "binary-minimize",
            SolverConfig {
                binary_resolution_minimization: true,
                ..default
            },
        ),
        (
            "preprocessing",
            SolverConfig {
                failed_literal_probing: true,
                clause_vivification: true,
                clause_subsumption: true,
                bounded_variable_elimination: true,
                ..default
            },
        ),
        (
            "factor",
            SolverConfig {
                bounded_variable_addition: true,
                ..default
            },
        ),
        (
            "lrb",
            SolverConfig {
                search_strategy: SearchStrategy::Lrb,
                ..default
            },
        ),
        (
            "chb",
            SolverConfig {
                search_strategy: SearchStrategy::Chb,
                ..default
            },
        ),
        (
            "vmtf",
            SolverConfig {
                search_strategy: SearchStrategy::Vmtf,
                ..default
            },
        ),
        (
            "transfer",
            SolverConfig {
                search_strategy: SearchStrategy::Transfer,
                ..default
            },
        ),
        (
            "focused",
            SolverConfig {
                search_strategy: SearchStrategy::Focused,
                ..default
            },
        ),
        (
            "probe-evsids",
            SolverConfig {
                search_strategy: SearchStrategy::ProbeEvsids,
                ..default
            },
        ),
        (
            "probe-vmtf",
            SolverConfig {
                search_strategy: SearchStrategy::ProbeVmtf,
                ..default
            },
        ),
        (
            "focused-stable",
            SolverConfig {
                search_strategy: SearchStrategy::FocusedStable,
                ..default
            },
        ),
    ]
}

#[test]
fn deep_search_configurations_agree_beyond_reduction_and_restart_thresholds() {
    // The small differential harness above never crosses the first database
    // reduction (1,000 conflicts) or more than a restart or two, so clause
    // deletion, usage decay, rephasing, and trail reuse would otherwise only
    // be reached by hand-built unit tests. Pigeonhole 8/7 drives every
    // configuration through thousands of conflicts and multiple reductions.
    let unsatisfiable = pigeonhole(8, 7);
    for (name, config) in deep_search_configurations() {
        let (result, stats) = solve_with_config(56, &unsatisfiable, config);
        assert_eq!(
            result,
            SolveResult::Unsat,
            "{name} must prove pigeonhole 8/7"
        );
        assert!(
            stats.conflicts > 500,
            "{name} should search deeply, saw {} conflicts",
            stats.conflicts
        );
    }
}

#[test]
fn deep_search_configurations_agree_on_medium_random_formulas() {
    // 50-variable formulas are far beyond the brute-force oracle, so the
    // configurations check each other: any SAT model is validated directly
    // and every configuration must reach the same satisfiability verdict.
    let mut random = XorShift64::new(0x1f83_d9ab_fb41_bd6b);
    let configurations = deep_search_configurations();

    for case in 0..20 {
        let variable_count = 50;
        let clauses = (0..213)
            .map(|_| {
                let mut variables = Vec::with_capacity(3);
                while variables.len() < 3 {
                    let variable = random.range(variable_count) as u32;
                    if !variables.contains(&variable) {
                        variables.push(variable);
                    }
                }
                variables
                    .into_iter()
                    .map(|variable| Lit::new(Var::new(variable), random.next() & 1 == 0))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();

        let (reference, _) = solve_with_config(variable_count, &clauses, SolverConfig::default());
        if let SolveResult::Sat(model) = &reference {
            assert!(
                satisfies(model, &clauses),
                "invalid default model in case {case}"
            );
        }
        for (name, config) in &configurations {
            let (result, stats) = solve_with_config(variable_count, &clauses, *config);
            assert_eq!(
                result.is_sat(),
                reference.is_sat(),
                "{name} disagrees with the default configuration in case {case}; stats={stats:?}"
            );
            if let SolveResult::Sat(model) = &result {
                assert!(
                    satisfies(model, &clauses),
                    "invalid {name} model in case {case}"
                );
            }
        }
    }
}

#[test]
fn pigeonhole_principle_exercises_learning() {
    let unsatisfiable = pigeonhole(5, 4);
    let (result, stats) = solve(20, &unsatisfiable);
    assert_eq!(result, SolveResult::Unsat);
    assert!(stats.conflicts > 0);
    assert!(stats.learned_clauses > 0);
    assert!(stats.minimized_literals > 0);

    let satisfiable = pigeonhole(5, 5);
    let (result, _) = solve(25, &satisfiable);
    let SolveResult::Sat(model) = result else {
        panic!("equal numbers of pigeons and holes should be satisfiable");
    };
    assert!(satisfies(&model, &satisfiable));
}

#[test]
fn learning_rate_branching_exercises_all_reward_paths() {
    let unsatisfiable = pigeonhole(6, 5);
    let (result, stats) = solve_with_config(
        30,
        &unsatisfiable,
        SolverConfig {
            search_strategy: SearchStrategy::Lrb,
            ..SolverConfig::default()
        },
    );
    assert_eq!(result, SolveResult::Unsat);
    assert!(stats.lrb_unassign_updates > 0);
    assert!(stats.lrb_reason_side_rewards > 0);
    assert!(stats.lrb_anti_exploration_decays > 0);
}

#[test]
fn conflict_history_branching_exercises_all_reward_paths() {
    let unsatisfiable = pigeonhole(6, 5);
    let (result, stats) = solve_with_config(
        30,
        &unsatisfiable,
        SolverConfig {
            search_strategy: SearchStrategy::Chb,
            ..SolverConfig::default()
        },
    );
    assert_eq!(result, SolveResult::Unsat);
    assert!(stats.chb_score_updates > 0);
    assert!(stats.chb_conflict_score_updates > 0);
    assert!(stats.chb_conflict_history_updates > 0);
    assert!(stats.chb_score_updates > stats.chb_conflict_score_updates);
}

#[test]
fn solving_twice_returns_the_same_cached_result() {
    let x = Lit::positive(Var::new(0));
    let clauses = vec![vec![x], vec![!x]];
    let mut solver = Solver::new();
    for clause in &clauses {
        solver.add_clause(clause);
    }
    let first = solver.solve();
    let stats = solver.stats();
    let second = solver.solve();
    assert_eq!(first, second);
    assert_eq!(stats, solver.stats());
}

#[test]
fn assumption_queries_are_temporary_and_return_a_failed_subset() {
    let a = Lit::positive(Var::new(0));
    let b = Lit::positive(Var::new(1));
    let c = Lit::positive(Var::new(2));
    let mut solver = Solver::new();
    solver.reserve_variables(3);
    solver.add_clause(&[!a, !b]);

    assert_eq!(solver.solve_assuming(&[c, a, b]), SolveResult::Unsat);
    assert_eq!(solver.failed_assumptions(), [a, b]);

    let SolveResult::Sat(model) = solver.solve_assuming(&[a, !b]) else {
        panic!("a compatible assumption query should remain satisfiable");
    };
    assert!(model.literal_value(a));
    assert!(model.literal_value(!b));
    assert!(solver.failed_assumptions().is_empty());

    let SolveResult::Sat(model) = solver.solve() else {
        panic!("an assumption conflict must not poison the permanent context");
    };
    assert!(model.literal_value(!a) || model.literal_value(!b));
}

#[test]
fn contradictory_assumptions_report_both_literals() {
    let a = Lit::positive(Var::new(0));
    let mut solver = Solver::new();
    solver.reserve_variables(1);

    assert_eq!(solver.solve_assuming(&[a, !a]), SolveResult::Unsat);
    assert_eq!(solver.failed_assumptions(), [a, !a]);
    assert!(solver.solve_assuming(&[a]).is_sat());
    assert!(solver.solve_assuming(&[!a]).is_sat());
}

#[test]
fn assumption_unsat_after_search_does_not_make_the_base_unsat() {
    let gate = Lit::positive(Var::new(0));
    let x = Lit::positive(Var::new(1));
    let y = Lit::positive(Var::new(2));
    let mut solver = Solver::new();
    for clause in [
        vec![!gate, x, y],
        vec![!gate, x, !y],
        vec![!gate, !x, y],
        vec![!gate, !x, !y],
    ] {
        solver.add_clause(&clause);
    }

    assert_eq!(solver.solve_assuming(&[gate]), SolveResult::Unsat);
    assert_eq!(solver.failed_assumptions(), [gate]);
    let conflicts = solver.stats().conflicts;
    assert!(
        conflicts > 0,
        "the gated contradiction should exercise CDCL"
    );

    let SolveResult::Sat(model) = solver.solve() else {
        panic!("disabling the gate should satisfy the permanent formula");
    };
    assert!(model.literal_value(!gate));
    assert!(solver.stats().conflicts >= conflicts);
}

#[test]
fn repeated_identical_assumption_query_uses_the_cached_result() {
    let a = Lit::positive(Var::new(0));
    let mut solver = Solver::new();
    solver.reserve_variables(1);
    solver.add_clause(&[!a]);

    let first = solver.solve_assuming(&[a]);
    let failed = solver.failed_assumptions().to_vec();
    let stats = solver.stats();
    let second = solver.solve_assuming(&[a]);
    assert_eq!(first, SolveResult::Unsat);
    assert_eq!(second, first);
    assert_eq!(solver.failed_assumptions(), failed);
    assert_eq!(solver.stats(), stats);
}

#[test]
fn assumption_unsat_does_not_emit_a_global_empty_drat_clause() {
    #[derive(Clone)]
    struct SharedBuffer(std::sync::Arc<std::sync::Mutex<Vec<u8>>>);

    impl std::io::Write for SharedBuffer {
        fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
            self.0.lock().unwrap().extend_from_slice(bytes);
            Ok(bytes.len())
        }

        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }

    let a = Lit::positive(Var::new(0));
    let b = Lit::positive(Var::new(1));
    let output = SharedBuffer(std::sync::Arc::default());
    let mut solver = Solver::new();
    solver.add_clause(&[a, b]);
    solver.enable_drat_proof(output.clone());

    assert_eq!(solver.solve_assuming(&[!a, !b]), SolveResult::Unsat);
    let proof = output.0.lock().unwrap().clone();
    assert!(
        !proof.split(|&byte| byte == b'\n').any(|line| line == b"0"),
        "the base formula is satisfiable, so its proof stream must not conclude globally"
    );
    assert!(solver.solve().is_sat());
}

#[test]
fn permanent_clauses_can_be_added_between_queries() {
    let a = Lit::positive(Var::new(0));
    let b = Lit::positive(Var::new(1));
    let mut solver = Solver::new();
    solver.add_clause(&[a, b]);
    assert!(solver.solve().is_sat());

    assert!(solver.try_add_clause(&[!a]).unwrap());
    let SolveResult::Sat(model) = solver.solve() else {
        panic!("the first incremental unit should imply b");
    };
    assert!(model.literal_value(!a));
    assert!(model.literal_value(b));

    assert!(!solver.try_add_clause(&[!b]).unwrap());
    assert_eq!(solver.solve(), SolveResult::Unsat);
}

#[test]
fn nested_clause_scopes_deactivate_only_popped_assertions() {
    let a = Lit::positive(Var::new(0));
    let b = Lit::positive(Var::new(1));
    let mut solver = Solver::new();
    solver.reserve_variables(2);
    solver.add_clause(&[a, b]);

    solver.push().unwrap();
    solver.add_clause(&[!a]);
    assert_eq!(solver.scope_depth(), 1);
    let SolveResult::Sat(model) = solver.solve() else {
        panic!("the outer scope should be satisfiable");
    };
    assert!(model.literal_value(!a));
    assert!(model.literal_value(b));

    solver.push().unwrap();
    solver.add_clause(&[!b]);
    assert_eq!(solver.scope_depth(), 2);
    assert_eq!(solver.solve(), SolveResult::Unsat);
    assert!(
        solver.failed_assumptions().is_empty(),
        "scope selectors are internal assumptions"
    );

    solver.pop(1).unwrap();
    assert_eq!(solver.scope_depth(), 1);
    let SolveResult::Sat(model) = solver.solve() else {
        panic!("popping the inner assertion should restore satisfiability");
    };
    assert!(model.literal_value(!a));
    assert!(model.literal_value(b));

    solver.pop(1).unwrap();
    assert_eq!(solver.scope_depth(), 0);
    assert!(solver.solve().is_sat());
    assert_eq!(solver.pop(1), Err(IncrementalError::ScopeUnderflow));
}

#[test]
fn an_empty_scoped_clause_does_not_poison_the_base_context() {
    let mut solver = Solver::new();
    solver.push().unwrap();
    assert!(solver.add_clause(&[]));
    assert_eq!(solver.solve(), SolveResult::Unsat);
    solver.pop(1).unwrap();
    assert!(solver.solve().is_sat());
}

#[test]
fn variables_can_be_allocated_after_a_query() {
    let mut solver = Solver::new();
    assert!(solver.solve().is_sat());
    let variable = solver.new_variable().unwrap();
    let literal = Lit::positive(variable);
    solver.add_clause(&[literal]);
    let SolveResult::Sat(model) = solver.solve() else {
        panic!("a newly declared constrained variable should be satisfiable");
    };
    assert_eq!(model.len(), 1);
    assert!(model.literal_value(literal));
}

#[test]
fn irreversible_preprocessing_is_rejected_by_incremental_mutations() {
    for config in [
        SolverConfig {
            bounded_variable_elimination: true,
            ..SolverConfig::default()
        },
        SolverConfig {
            bounded_variable_addition: true,
            ..SolverConfig::default()
        },
    ] {
        let mut solver = Solver::with_config(config);
        solver.reserve_variables(1);
        assert_eq!(
            solver.push(),
            Err(IncrementalError::IrreversiblePreprocessing)
        );
        assert!(solver.solve().is_sat());
        assert_eq!(
            solver.try_add_clause(&[Lit::positive(Var::new(0))]),
            Err(IncrementalError::IrreversiblePreprocessing)
        );
    }
}

#[test]
fn deterministic_limits_return_unknown_and_leave_the_context_reusable() {
    let x = Lit::positive(Var::new(0));
    let y = Lit::positive(Var::new(1));
    let mut solver = Solver::new();
    for clause in [vec![x, y], vec![x, !y], vec![!x, y], vec![!x, !y]] {
        solver.add_clause(&clause);
    }

    assert_eq!(
        solver.solve_with_limits(SolveLimits {
            conflicts: Some(0),
            propagations: None,
        }),
        SolveResult::Unknown(UnknownReason::ConflictLimit)
    );
    assert!(solver.failed_assumptions().is_empty());
    assert_eq!(solver.solve(), SolveResult::Unsat);
}

#[test]
fn propagation_limit_is_relative_to_each_query() {
    let a = Lit::positive(Var::new(0));
    let b = Lit::positive(Var::new(1));
    let mut solver = Solver::new();
    solver.add_clause(&[!a, b]);

    let before = solver.stats().propagations;
    assert_eq!(
        solver.solve_with_limits(SolveLimits {
            conflicts: None,
            propagations: Some(1),
        }),
        SolveResult::Unknown(UnknownReason::PropagationLimit)
    );
    assert_eq!(solver.stats().propagations - before, 1);

    let SolveResult::Sat(model) = solver.solve() else {
        panic!("a limited query must leave a reusable context");
    };
    assert!(model.literal_value(!a) || model.literal_value(b));
}

#[test]
fn an_external_interrupt_can_be_cleared_for_a_later_query() {
    let a = Lit::positive(Var::new(0));
    let mut solver = Solver::new();
    solver.reserve_variables(1);
    let interrupter = solver.interrupter();
    interrupter.interrupt();
    assert!(interrupter.is_interrupted());
    assert_eq!(
        solver.solve(),
        SolveResult::Unknown(UnknownReason::Interrupted)
    );

    interrupter.clear();
    assert!(!interrupter.is_interrupted());
    let SolveResult::Sat(model) = solver.solve_assuming(&[a]) else {
        panic!("clearing interruption should permit another query");
    };
    assert!(model.literal_value(a));
}

#[test]
fn random_push_pop_add_and_check_sequences_match_brute_force() {
    const USER_VARIABLES: usize = 5;
    let mut random = XorShift64::new(0x3c6e_f372_fe94_f82b);

    for case in 0..200 {
        let mut solver = Solver::new();
        solver.reserve_variables(USER_VARIABLES);
        let mut frames = vec![Vec::<Vec<Lit>>::new()];

        for operation in 0..100 {
            match random.range(5) {
                0 if frames.len() < 5 => {
                    solver.push().unwrap();
                    frames.push(Vec::new());
                }
                1 if frames.len() > 1 => {
                    solver.pop(1).unwrap();
                    frames.pop();
                }
                2 | 3 => {
                    let length = random.range(5);
                    let clause = (0..length)
                        .map(|_| {
                            let variable = Var::new(random.range(USER_VARIABLES) as u32);
                            Lit::new(variable, random.next() & 1 == 0)
                        })
                        .collect::<Vec<_>>();
                    solver.add_clause(&clause);
                    frames
                        .last_mut()
                        .expect("base frame is permanent")
                        .push(clause);
                }
                _ => {
                    let active = frames
                        .iter()
                        .flat_map(|frame| frame.iter().cloned())
                        .collect::<Vec<_>>();
                    let expected = brute_force(USER_VARIABLES, &active);
                    let actual = solver.solve();
                    assert_eq!(
                        actual.is_sat(),
                        expected.is_some(),
                        "scope mismatch in case {case}, operation {operation}: \
                         depth={}, active={active:?}, stats={:?}",
                        solver.scope_depth(),
                        solver.stats()
                    );
                    if let SolveResult::Sat(model) = actual {
                        assert!(
                            satisfies(&model, &active),
                            "invalid scoped model in case {case}, operation {operation}"
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn binary_fast_path_is_exercised_by_an_implication() {
    let x = Lit::positive(Var::new(0));
    let y = Lit::positive(Var::new(1));
    let mut solver = Solver::new();
    solver.add_clause(&[!x, y]);
    solver.add_clause(&[x]);
    let SolveResult::Sat(model) = solver.solve() else {
        panic!("implication should be satisfiable");
    };
    assert!(model.literal_value(y));
    assert!(solver.stats().binary_watch_visits > 0);
}

#[test]
fn focused_probe_transitions_once_on_a_harder_unsat_formula() {
    let unsatisfiable = pigeonhole(7, 6);
    let (result, stats) = solve_with_config(
        42,
        &unsatisfiable,
        SolverConfig {
            search_strategy: SearchStrategy::ProbeEvsids,
            ..SolverConfig::default()
        },
    );
    assert_eq!(result, SolveResult::Unsat);
    assert_eq!(stats.mode_switches, 1);
    assert_eq!(stats.focused_conflicts, 100);
    assert!(stats.conflicts > stats.focused_conflicts);
}

#[test]
fn chronological_backtracking_is_exercised_by_a_deep_gated_conflict() {
    let gate = Lit::positive(Var::new(0));
    let left = Lit::positive(Var::new(111));
    let right = Lit::positive(Var::new(112));
    let clauses = vec![
        vec![!gate, left, right],
        vec![!gate, left, !right],
        vec![!gate, !left, right],
        vec![!gate, !left, !right],
    ];
    let (result, stats) = solve_with_config(
        113,
        &clauses,
        SolverConfig {
            chronological_backtracking: true,
            ..SolverConfig::default()
        },
    );
    let SolveResult::Sat(model) = result else {
        panic!("the gated contradiction is satisfiable by disabling its gate");
    };
    assert!(satisfies(&model, &clauses));
    assert!(stats.chronological_backtracks > 0);
    assert!(stats.chronological_levels_preserved > 100);
}

fn solve(variable_count: usize, clauses: &[Vec<Lit>]) -> (SolveResult, sat::SolverStats) {
    solve_with_config(variable_count, clauses, SolverConfig::default())
}

fn solve_with_config(
    variable_count: usize,
    clauses: &[Vec<Lit>],
    config: SolverConfig,
) -> (SolveResult, sat::SolverStats) {
    let mut solver = Solver::with_config(config);
    solver.reserve_variables(variable_count);
    for clause in clauses {
        solver.add_clause(clause);
    }
    let result = solver.solve();
    (result, solver.stats())
}

fn brute_force(variable_count: usize, clauses: &[Vec<Lit>]) -> Option<Vec<bool>> {
    for assignment in 0_u64..(1_u64 << variable_count) {
        let values = (0..variable_count)
            .map(|variable| assignment & (1 << variable) != 0)
            .collect::<Vec<_>>();
        if clauses.iter().all(|clause| {
            clause
                .iter()
                .any(|literal| values[literal.var().index()] == literal.is_positive())
        }) {
            return Some(values);
        }
    }
    None
}

fn satisfies(model: &Model, clauses: &[Vec<Lit>]) -> bool {
    clauses
        .iter()
        .all(|clause| clause.iter().any(|&literal| model.literal_value(literal)))
}

fn pigeonhole(pigeons: usize, holes: usize) -> Vec<Vec<Lit>> {
    let variable =
        |pigeon: usize, hole: usize| Lit::positive(Var::new((pigeon * holes + hole) as u32));
    let mut clauses = Vec::new();

    for pigeon in 0..pigeons {
        clauses.push((0..holes).map(|hole| variable(pigeon, hole)).collect());
    }
    for hole in 0..holes {
        for first in 0..pigeons {
            for second in first + 1..pigeons {
                clauses.push(vec![!variable(first, hole), !variable(second, hole)]);
            }
        }
    }
    clauses
}

struct XorShift64(u64);

impl XorShift64 {
    const fn new(seed: u64) -> Self {
        Self(seed)
    }

    fn next(&mut self) -> u64 {
        let mut value = self.0;
        value ^= value << 13;
        value ^= value >> 7;
        value ^= value << 17;
        self.0 = value;
        value
    }

    fn range(&mut self, upper: usize) -> usize {
        if upper == 0 {
            0
        } else {
            self.next() as usize % upper
        }
    }
}
