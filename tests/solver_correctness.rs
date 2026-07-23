use sat::{
    Lit, Model, RestartPolicy, RestartTrailReuse, SearchStrategy, SolveResult, Solver,
    SolverConfig, Var,
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
