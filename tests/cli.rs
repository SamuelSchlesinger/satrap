use std::io::Write;
use std::process::{Command, Stdio};
use std::time::{SystemTime, UNIX_EPOCH};

#[test]
fn reports_sat_with_a_machine_checkable_model() {
    let output = run(b"p cnf 3 3\n1 2 0\n-1 3 0\n-2 -3 0\n", &["--stats"]);
    assert_eq!(output.status.code(), Some(10));
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("c conflicts "));
    assert!(stdout.contains("s SATISFIABLE\n"));
    let assignment = parse_model(&stdout, 3);
    assert!(assignment[0] || assignment[1]);
    assert!(!assignment[0] || assignment[2]);
    assert!(!assignment[1] || !assignment[2]);
}

#[test]
fn reports_unsat_and_uses_competition_exit_code() {
    let output = run(b"p cnf 1 2\n1 0\n-1 0\n", &[]);
    assert_eq!(output.status.code(), Some(20));
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        "s UNSATISFIABLE\n"
    );
}

#[test]
fn rejects_malformed_dimacs() {
    let output = run(b"p cnf 2 1\n3 0\n", &[]);
    assert_eq!(output.status.code(), Some(1));
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(stderr.contains("DIMACS error at 2:1"));
}

#[test]
fn streams_a_drat_proof_for_unsat() {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let proof_path =
        std::env::temp_dir().join(format!("sat-proof-{}-{nonce}.drat", std::process::id()));
    let output = run(
        b"p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n",
        &["--probe", "--proof", proof_path.to_str().unwrap()],
    );
    assert_eq!(output.status.code(), Some(20));
    let proof = std::fs::read_to_string(&proof_path).unwrap();
    std::fs::remove_file(proof_path).unwrap();
    assert!(
        proof.lines().count() > 1,
        "proof should contain a probe-derived unit"
    );
    assert_eq!(proof.lines().next(), Some("-1 0"));
    assert_eq!(proof.lines().last(), Some("0"));
}

#[test]
fn streams_a_vivified_prefix_in_the_drat_proof() {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let proof_path = std::env::temp_dir().join(format!(
        "sat-vivify-proof-{}-{nonce}.drat",
        std::process::id()
    ));
    let output = run(
        b"p cnf 6 7\n1 2 3 0\n1 2 4 0\n1 2 -4 0\n-1 5 0\n-1 -5 0\n-2 6 0\n-2 -6 0\n",
        &["--vivify", "--proof", proof_path.to_str().unwrap()],
    );
    assert_eq!(output.status.code(), Some(20));
    let proof = std::fs::read_to_string(&proof_path).unwrap();
    std::fs::remove_file(proof_path).unwrap();
    assert_eq!(proof.lines().next(), Some("1 2 0"));
    assert_eq!(proof.lines().last(), Some("0"));
}

#[test]
fn streams_a_self_subsumed_clause_in_the_drat_proof() {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let proof_path =
        std::env::temp_dir().join(format!("sat-ssr-proof-{}-{nonce}.drat", std::process::id()));
    let output = run(
        b"p cnf 3 4\n1 2 0\n-1 2 0\n-2 3 0\n-2 -3 0\n",
        &["--subsume", "--proof", proof_path.to_str().unwrap()],
    );
    assert_eq!(output.status.code(), Some(20));
    let proof = std::fs::read_to_string(&proof_path).unwrap();
    std::fs::remove_file(proof_path).unwrap();
    assert_eq!(proof.lines().next(), Some("2 0"));
    assert_eq!(proof.lines().last(), Some("0"));
}

#[test]
fn streams_a_binary_resolution_minimized_clause_in_the_drat_proof() {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let proof_path = std::env::temp_dir().join(format!(
        "sat-binary-minimize-proof-{}-{nonce}.drat",
        std::process::id()
    ));
    let output = run(
        include_bytes!("../benchmarks/smoke/binary-minimize-unsat.cnf"),
        &[
            "--stats",
            "--binary-minimize",
            "--proof",
            proof_path.to_str().unwrap(),
        ],
    );
    assert_eq!(output.status.code(), Some(20));
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("c binary_minimized_literals 1\n"));
    let proof = std::fs::read_to_string(&proof_path).unwrap();
    std::fs::remove_file(proof_path).unwrap();
    assert_eq!(proof.lines().nth(2), Some("-8 0"));
    assert_eq!(proof.lines().last(), Some("0"));
}

#[test]
fn compacts_deleted_clause_payloads_through_the_cli() {
    let input = pigeonhole_dimacs(8, 7);
    let output = run(
        input.as_bytes(),
        &["--stats", "--compact-arena", "--no-model"],
    );
    assert_eq!(output.status.code(), Some(20));
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stat(&stdout, "conflicts") >= 2_000);
    assert!(stat(&stdout, "arena_compactions") > 0);
    assert!(stat(&stdout, "arena_moved_literals") > 0);
    assert!(stat(&stdout, "arena_reclaimed_literals") > 0);
    assert_eq!(stat(&stdout, "arena_garbage_literals"), 0);
}

#[test]
fn reports_scan_debt_clause_management_counters_through_the_cli() {
    let input = pigeonhole_dimacs(8, 7);
    let output = run(
        input.as_bytes(),
        &["--stats", "--scan-debt-reduction", "--no-model"],
    );
    assert_eq!(output.status.code(), Some(20));
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stat(&stdout, "clause_scan_debt_literal_checks") > 0);
    assert!(stat(&stdout, "clause_scan_debt_nonzero_resets") > 0);
    assert!(stat(&stdout, "clause_scan_debt_peak") > 0);
    assert!(stat(&stdout, "reductions") > 0);
}

#[test]
fn reports_sampled_nonregular_retention_counters_through_the_cli() {
    let input = pigeonhole_dimacs(8, 7);
    let output = run(
        input.as_bytes(),
        &["--stats", "--nonregular-retention", "--no-model"],
    );
    assert_eq!(output.status.code(), Some(20));
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stat(&stdout, "regularity_resolution_pivots") > 0);
    assert!(stat(&stdout, "regularity_sampled_repeat_witnesses") > 0);
    assert!(stat(&stdout, "regularity_nonregular_learned_clauses") > 0);
    assert!(stat(&stdout, "regularity_nonregular_zero_candidates") > 0);
    assert!(stat(&stdout, "regularity_nonregular_deletions") > 0);
    assert!(stat(&stdout, "regularity_metadata_bytes") > 0);
    assert!(stat(&stdout, "reductions") > 0);
}

#[test]
fn reports_counterfactual_shadow_counters_through_the_cli() {
    let input = pigeonhole_dimacs(8, 7);
    let output = run(
        input.as_bytes(),
        &["--stats", "--shadow-reactivation", "--no-model"],
    );
    assert_eq!(output.status.code(), Some(20));
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stat(&stdout, "shadow_clauses_started") > 0);
    assert!(stat(&stdout, "shadow_active_peak") > 0);
    assert!(stat(&stdout, "shadow_watch_visits") > 0);
    assert!(stat(&stdout, "shadow_literal_checks") > 0);
    assert!(stat(&stdout, "shadow_unit_triggers") + stat(&stdout, "shadow_conflict_triggers") > 0);
    assert!(stat(&stdout, "shadow_reactivated_clauses") > 0);
    assert!(stat(&stdout, "shadow_expired_clauses") > 0);
    assert!(stat(&stdout, "shadow_effective_removals") > 0);
    assert!(stat(&stdout, "shadow_metadata_bytes") > 0);
    assert!(stat(&stdout, "reductions") > 0);
}

#[test]
fn reports_counterfactual_phase_counters_through_the_cli() {
    let input = pigeonhole_dimacs(8, 7);
    let output = run(
        input.as_bytes(),
        &["--stats", "--counterfactual-phase", "--no-model"],
    );
    assert_eq!(output.status.code(), Some(20));
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stat(&stdout, "counterfactual_phase_deletion_offers") > 0);
    assert!(stat(&stdout, "counterfactual_phase_sample_insertions") > 0);
    assert!(stat(&stdout, "counterfactual_phase_sample_peak") > 0);
    assert!(stat(&stdout, "counterfactual_phase_snapshots") > 0);
    assert!(stat(&stdout, "counterfactual_phase_clauses_scanned") > 0);
    assert!(stat(&stdout, "counterfactual_phase_literal_checks") > 0);
    assert!(stat(&stdout, "counterfactual_phase_metadata_bytes") > 0);
    assert!(stat(&stdout, "reductions") > 0);
}

#[test]
fn reconstructs_an_eliminated_variable_in_the_cli_model() {
    let output = run(b"p cnf 2 2\n-1 2 0\n-1 -2 0\n", &["--stats", "--eliminate"]);
    assert_eq!(output.status.code(), Some(10));
    let stdout = String::from_utf8(output.stdout).unwrap();
    let model = parse_model(&stdout, 2);
    assert!(
        !model[0],
        "the eliminated pivot must be reconstructed false"
    );
    assert!(stat(&stdout, "eliminated_variables") > 0);
    assert!(stat(&stdout, "elimination_extension_clauses") >= 2);
}

#[test]
fn streams_a_variable_elimination_resolvent_in_the_drat_proof() {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let proof_path = std::env::temp_dir().join(format!(
        "sat-elimination-proof-{}-{nonce}.drat",
        std::process::id()
    ));
    let output = run(
        include_bytes!("../benchmarks/smoke/eliminate-unsat.cnf"),
        &[
            "--stats",
            "--eliminate",
            "--proof",
            proof_path.to_str().unwrap(),
        ],
    );
    assert_eq!(output.status.code(), Some(20));
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stat(&stdout, "eliminated_variables") > 0);
    assert!(stat(&stdout, "elimination_resolvents") > 0);
    let proof = std::fs::read_to_string(&proof_path).unwrap();
    std::fs::remove_file(proof_path).unwrap();
    assert_eq!(proof.lines().next(), Some("2 3 0"));
    assert_eq!(proof.lines().last(), Some("0"));
}

#[test]
fn reports_factorization_without_leaking_extension_variables_into_the_model() {
    let input = b"p cnf 6 9\n\
1 4 0\n1 5 0\n1 6 0\n\
2 4 0\n2 5 0\n2 6 0\n\
3 4 0\n3 5 0\n3 6 0\n";
    let output = run(input, &["--stats", "--factor"]);
    assert_eq!(output.status.code(), Some(10));
    let stdout = String::from_utf8(output.stdout).unwrap();
    let model = parse_model(&stdout, 6);
    assert_eq!(model.len(), 6);
    assert_eq!(stat(&stdout, "variables"), 6);
    assert_eq!(stat(&stdout, "factored_variables"), 1);
    assert_eq!(stat(&stdout, "factorization_clauses_removed"), 9);
    assert_eq!(stat(&stdout, "factorization_clauses_added"), 6);
    assert_eq!(stat(&stdout, "factorization_clause_reduction"), 3);
}

#[test]
fn macro_factorization_reports_a_sparse_input_skip() {
    let input = b"p cnf 6 9\n\
1 4 0\n1 5 0\n1 6 0\n\
2 4 0\n2 5 0\n2 6 0\n\
3 4 0\n3 5 0\n3 6 0\n";
    let output = run(input, &["--stats", "--factor-macro"]);
    assert_eq!(output.status.code(), Some(10));
    let stdout = String::from_utf8(output.stdout).unwrap();
    let model = parse_model(&stdout, 6);
    assert_eq!(model.len(), 6);
    assert_eq!(stat(&stdout, "factorization_input_short_clauses"), 9);
    assert_eq!(stat(&stdout, "factorization_density_checks"), 1);
    assert_eq!(stat(&stdout, "factorization_density_skips"), 1);
    assert_eq!(stat(&stdout, "factorization_rounds"), 0);
    assert_eq!(stat(&stdout, "factored_variables"), 0);
}

#[test]
fn streams_factor_extension_clauses_in_the_drat_proof() {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let proof_path = std::env::temp_dir().join(format!(
        "sat-factor-proof-{}-{nonce}.drat",
        std::process::id()
    ));
    let output = run(
        include_bytes!("../benchmarks/smoke/factor-unsat.cnf"),
        &[
            "--stats",
            "--factor",
            "--proof",
            proof_path.to_str().unwrap(),
        ],
    );
    assert_eq!(output.status.code(), Some(20));
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert_eq!(stat(&stdout, "factored_variables"), 1);
    let proof = std::fs::read_to_string(&proof_path).unwrap();
    std::fs::remove_file(proof_path).unwrap();
    let lines = proof.lines().collect::<Vec<_>>();
    assert!(lines.contains(&"11 1 0"));
    assert!(lines.contains(&"-11 4 0"));
    assert_eq!(lines.last(), Some(&"0"));
}

fn run(input: &[u8], arguments: &[&str]) -> std::process::Output {
    let mut child = Command::new(env!("CARGO_BIN_EXE_sat"))
        .args(arguments)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child.stdin.take().unwrap().write_all(input).unwrap();
    child.wait_with_output().unwrap()
}

fn parse_model(output: &str, variable_count: usize) -> Vec<bool> {
    let mut values = vec![None; variable_count];
    for line in output.lines().filter(|line| line.starts_with('v')) {
        for token in line[1..].split_ascii_whitespace() {
            let literal = token.parse::<i64>().unwrap();
            if literal == 0 {
                continue;
            }
            let index = literal.unsigned_abs() as usize - 1;
            values[index] = Some(literal > 0);
        }
    }
    values
        .into_iter()
        .map(|value| value.expect("model should assign every variable"))
        .collect()
}

fn stat(output: &str, name: &str) -> u64 {
    let prefix = format!("c {name} ");
    output
        .lines()
        .find_map(|line| line.strip_prefix(&prefix))
        .unwrap_or_else(|| panic!("missing statistic {name}"))
        .parse()
        .unwrap()
}

fn pigeonhole_dimacs(pigeons: usize, holes: usize) -> String {
    let variable = |pigeon: usize, hole: usize| pigeon * holes + hole + 1;
    let clause_count =
        pigeons + pigeons * holes * (holes - 1) / 2 + holes * pigeons * (pigeons - 1) / 2;
    let mut output = format!("p cnf {} {clause_count}\n", pigeons * holes);

    for pigeon in 0..pigeons {
        push_clause(
            &mut output,
            (0..holes).map(|hole| variable(pigeon, hole) as i64),
        );
        for left in 0..holes {
            for right in left + 1..holes {
                push_clause(
                    &mut output,
                    [
                        -(variable(pigeon, left) as i64),
                        -(variable(pigeon, right) as i64),
                    ],
                );
            }
        }
    }
    for hole in 0..holes {
        for upper in 0..pigeons {
            for lower in upper + 1..pigeons {
                push_clause(
                    &mut output,
                    [
                        -(variable(upper, hole) as i64),
                        -(variable(lower, hole) as i64),
                    ],
                );
            }
        }
    }
    output
}

fn push_clause(output: &mut String, literals: impl IntoIterator<Item = i64>) {
    for literal in literals {
        output.push_str(&literal.to_string());
        output.push(' ');
    }
    output.push_str("0\n");
}
