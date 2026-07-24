//! Independent replay of SMT-LIB unsat cores and failed assumptions.

use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;
use std::io::Write;
use std::process::{Command, Output, Stdio};

#[derive(Clone, Copy)]
struct Oracle {
    name: &'static str,
    program: &'static str,
    arguments: &'static [&'static str],
}

const Z3: Oracle = Oracle {
    name: "Z3",
    program: "z3",
    arguments: &["-in", "-smt2"],
};
const CVC5: Oracle = Oracle {
    name: "cvc5",
    program: "cvc5",
    arguments: &["--lang=smt2", "--incremental", "--arrays-exp"],
};
const BITWUZLA: Oracle = Oracle {
    name: "Bitwuzla",
    program: "bitwuzla",
    arguments: &["--lang", "smt2"],
};
const GENERAL_ORACLES: &[Oracle] = &[Z3, CVC5];
const FINITE_ORACLES: &[Oracle] = &[Z3, CVC5, BITWUZLA];

struct CoreCase {
    name: &'static str,
    logic: &'static str,
    oracle_logic: Option<&'static str>,
    declarations: &'static [&'static str],
    assertions: &'static [&'static str],
    oracles: &'static [Oracle],
}

#[test]
fn named_cores_are_independently_unsat_in_every_advertised_fragment() {
    let cases = core_cases();
    assert_eq!(cases.len(), 14);
    for case in cases {
        validate_named_core(&case);
    }
}

#[test]
fn named_core_and_failed_assumptions_are_independently_unsat_together() {
    let declarations = [
        "(declare-const p Bool)",
        "(declare-const q Bool)",
        "(declare-const activate-not-q Bool)",
    ];
    let named = [
        ("implication", "(=> p q)"),
        ("premise", "p"),
        ("activation", "(= activate-not-q (not q))"),
    ];
    let mut script = String::from(
        "(set-option :produce-unsat-cores true)\n\
         (set-option :produce-unsat-assumptions true)\n\
         (set-logic QF_UF)\n",
    );
    for declaration in declarations {
        writeln!(script, "{declaration}").unwrap();
    }
    for (name, assertion) in named {
        writeln!(script, "(assert (! {assertion} :named {name}))").unwrap();
    }
    script.push_str(
        "(check-sat-assuming (activate-not-q))\n\
         (get-unsat-core)\n\
         (get-unsat-assumptions)\n\
         (exit)\n",
    );

    let output = run_ours("named assertions with an assumption", &script);
    let lines = output.lines().collect::<Vec<_>>();
    assert_eq!(
        lines.len(),
        3,
        "unexpected core/assumption output:\n{output}"
    );
    assert_eq!(lines[0], "unsat");
    let core = parse_flat_list(lines[1], "unsat core");
    let assumptions = parse_flat_list(lines[2], "unsat assumptions");
    assert_eq!(assumptions, ["activate-not-q"]);

    let named = named.into_iter().collect::<HashMap<_, _>>();
    let mut validation = String::from("(set-logic QF_UF)\n");
    for declaration in declarations {
        writeln!(validation, "{declaration}").unwrap();
    }
    for name in &core {
        let assertion = named
            .get(name.as_str())
            .unwrap_or_else(|| panic!("solver returned unknown core name `{name}`"));
        writeln!(validation, "(assert {assertion})").unwrap();
    }
    for assumption in assumptions {
        writeln!(validation, "(assert {assumption})").unwrap();
    }
    validation.push_str("(check-sat)\n(exit)\n");
    assert_oracles_unsat(
        "named assertions with an assumption",
        &validation,
        GENERAL_ORACLES,
    );
}

fn validate_named_core(case: &CoreCase) {
    let mut named = vec![("base".to_owned(), "true")];
    named.extend(
        case.assertions
            .iter()
            .enumerate()
            .map(|(index, &assertion)| (format!("core_{index}"), assertion)),
    );

    let mut script = String::from("(set-option :produce-unsat-cores true)\n");
    writeln!(script, "(set-logic {})", case.logic).unwrap();
    for declaration in case.declarations {
        writeln!(script, "{declaration}").unwrap();
    }
    script.push_str("(assert (! true :named base))\n(push 1)\n");
    for (name, assertion) in named.iter().skip(1) {
        writeln!(script, "(assert (! {assertion} :named {name}))").unwrap();
    }
    script.push_str(
        "(check-sat)\n\
         (get-unsat-core)\n\
         (pop 1)\n\
         (check-sat)\n\
         (exit)\n",
    );

    let output = run_ours(case.name, &script);
    let lines = output.lines().collect::<Vec<_>>();
    assert_eq!(
        lines.len(),
        3,
        "unexpected output for {}:\n{output}",
        case.name
    );
    assert_eq!(lines[0], "unsat", "{} was not unsat", case.name);
    assert_eq!(
        lines[2], "sat",
        "{} did not recover after popping its unsat scope",
        case.name
    );
    let core = parse_flat_list(lines[1], "unsat core");
    assert!(!core.is_empty(), "{} returned an empty core", case.name);
    let unique = core.iter().collect::<HashSet<_>>();
    assert_eq!(
        unique.len(),
        core.len(),
        "{} returned duplicate core names: {core:?}",
        case.name
    );

    let named = named.into_iter().collect::<HashMap<_, _>>();
    let mut validation = String::new();
    writeln!(
        validation,
        "(set-logic {})",
        case.oracle_logic.unwrap_or(case.logic)
    )
    .unwrap();
    for declaration in case.declarations {
        writeln!(validation, "{declaration}").unwrap();
    }
    for name in core {
        let assertion = named
            .get(&name)
            .unwrap_or_else(|| panic!("{} returned unknown core name `{name}`", case.name));
        writeln!(validation, "(assert {assertion})").unwrap();
    }
    validation.push_str("(check-sat)\n(exit)\n");
    assert_oracles_unsat(case.name, &validation, case.oracles);
}

fn parse_flat_list(line: &str, role: &str) -> Vec<String> {
    let contents = line
        .strip_prefix('(')
        .and_then(|line| line.strip_suffix(')'))
        .unwrap_or_else(|| panic!("{role} is not an SMT-LIB list: {line}"));
    contents
        .split_ascii_whitespace()
        .map(str::to_owned)
        .collect()
}

fn run_ours(case_name: &str, script: &str) -> String {
    let output = run_solver(env!("CARGO_BIN_EXE_smt"), &[], script);
    assert!(
        output.status.success(),
        "our solver failed on {case_name}:\nscript:\n{script}\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).expect("our solver output must be UTF-8")
}

fn assert_oracles_unsat(case_name: &str, script: &str, oracles: &[Oracle]) {
    for &oracle in oracles {
        if !oracle_is_available(oracle) {
            eprintln!(
                "skipping {case_name} core replay with {} because {} is not installed",
                oracle.name, oracle.program
            );
            continue;
        }
        let output = run_solver(oracle.program, oracle.arguments, script);
        assert!(
            output.status.success(),
            "{} rejected the core replay for {case_name}:\n\
             script:\n{script}\nstdout:\n{}\nstderr:\n{}",
            oracle.name,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        let stdout = String::from_utf8(output.stdout).expect("oracle output must be UTF-8");
        assert_eq!(
            check_results(&stdout),
            ["unsat"],
            "{} did not validate the returned core for {case_name}:\n\
             script:\n{script}\nstdout:\n{stdout}",
            oracle.name
        );
    }
}

fn oracle_is_available(oracle: Oracle) -> bool {
    Command::new(oracle.program)
        .arg("--version")
        .output()
        .is_ok_and(|output| output.status.success())
}

fn run_solver(program: &str, arguments: &[&str], script: &str) -> Output {
    let mut child = Command::new(program)
        .args(arguments)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap_or_else(|error| panic!("could not start {program}: {error}"));
    child
        .stdin
        .as_mut()
        .expect("piped input")
        .write_all(script.as_bytes())
        .unwrap();
    child
        .wait_with_output()
        .expect("solver process should finish")
}

fn check_results(output: &str) -> Vec<&str> {
    output
        .lines()
        .filter(|line| matches!(*line, "sat" | "unsat" | "unknown"))
        .collect()
}

fn core_cases() -> Vec<CoreCase> {
    vec![
        CoreCase {
            name: "QF_BOOL core",
            logic: "QF_BOOL",
            oracle_logic: Some("QF_UF"),
            declarations: &["(declare-const p Bool)"],
            assertions: &["p", "(not p)", "(or p (not p))"],
            oracles: GENERAL_ORACLES,
        },
        CoreCase {
            name: "QF_BV core",
            logic: "QF_BV",
            oracle_logic: None,
            declarations: &["(declare-const x (_ BitVec 4))"],
            assertions: &["(= x #b0011)", "(= x #b0101)", "(bvule x #b1111)"],
            oracles: FINITE_ORACLES,
        },
        CoreCase {
            name: "QF_UF core",
            logic: "QF_UF",
            oracle_logic: None,
            declarations: &[
                "(declare-sort U 0)",
                "(declare-const a U)",
                "(declare-const b U)",
                "(declare-fun f (U) U)",
            ],
            assertions: &["(= a b)", "(distinct (f a) (f b))", "(= (f a) (f a))"],
            oracles: GENERAL_ORACLES,
        },
        CoreCase {
            name: "QF_UFBV core",
            logic: "QF_UFBV",
            oracle_logic: None,
            declarations: &[
                "(declare-sort U 0)",
                "(declare-const a U)",
                "(declare-const b U)",
                "(declare-fun color (U) (_ BitVec 4))",
            ],
            assertions: &[
                "(= a b)",
                "(distinct (color a) (color b))",
                "(bvule (color a) #b1111)",
            ],
            oracles: GENERAL_ORACLES,
        },
        CoreCase {
            name: "QF_ABV core",
            logic: "QF_ABV",
            oracle_logic: None,
            declarations: &[
                "(declare-const a (Array (_ BitVec 2) (_ BitVec 3)))",
                "(declare-const i (_ BitVec 2))",
                "(declare-const j (_ BitVec 2))",
            ],
            assertions: &[
                "(distinct i j)",
                "(distinct (select (store a i #b111) j) (select a j))",
                "(= (select a i) (select a i))",
            ],
            oracles: FINITE_ORACLES,
        },
        CoreCase {
            name: "QF_AUFBV core",
            logic: "QF_AUFBV",
            oracle_logic: None,
            declarations: &[
                "(declare-const a (Array (_ BitVec 2) (_ BitVec 3)))",
                "(declare-const i (_ BitVec 2))",
                "(declare-const j (_ BitVec 2))",
                "(declare-fun f ((_ BitVec 3)) (_ BitVec 3))",
            ],
            assertions: &[
                "(distinct i j)",
                "(= (f (select (store a i #b111) j)) #b001)",
                "(= (f (select a j)) #b010)",
            ],
            oracles: FINITE_ORACLES,
        },
        CoreCase {
            name: "QF_IDL core",
            logic: "QF_IDL",
            oracle_logic: None,
            declarations: &["(declare-const x Int)", "(declare-const y Int)"],
            assertions: &["(<= (- x y) 2)", "(<= (- y x) (- 3))", "(<= (- x x) 0)"],
            oracles: GENERAL_ORACLES,
        },
        CoreCase {
            name: "QF_LIA core",
            logic: "QF_LIA",
            oracle_logic: None,
            declarations: &["(declare-const x Int)"],
            assertions: &["(<= (* 2 x) 1)", "(>= (* 2 x) 1)", "(<= x 10)"],
            oracles: GENERAL_ORACLES,
        },
        CoreCase {
            name: "QF_RDL core",
            logic: "QF_RDL",
            oracle_logic: None,
            declarations: &["(declare-const x Real)", "(declare-const y Real)"],
            assertions: &[
                "(<= (- x y) (/ 1.0 3.0))",
                "(<= (- y x) (- (/ 1.0 2.0)))",
                "(<= (- x x) 0.0)",
            ],
            oracles: GENERAL_ORACLES,
        },
        CoreCase {
            name: "QF_LRA core",
            logic: "QF_LRA",
            oracle_logic: None,
            declarations: &["(declare-const x Real)", "(declare-const y Real)"],
            assertions: &[
                "(<= (+ (* 2.0 x) (* 3.0 y)) (/ 1.0 3.0))",
                "(>= (+ (* 2.0 x) (* 3.0 y)) (/ 1.0 2.0))",
                "(<= x 10.0)",
            ],
            oracles: GENERAL_ORACLES,
        },
        CoreCase {
            name: "QF_UFIDL core",
            logic: "QF_UFIDL",
            oracle_logic: None,
            declarations: &[
                "(declare-const x Int)",
                "(declare-const y Int)",
                "(declare-fun f (Int) Int)",
            ],
            assertions: &["(= x y)", "(<= (- (f x) (f y)) (- 1))", "(<= (- x y) 0)"],
            oracles: GENERAL_ORACLES,
        },
        CoreCase {
            name: "QF_UFLIA core",
            logic: "QF_UFLIA",
            oracle_logic: None,
            declarations: &[
                "(declare-const x Int)",
                "(declare-const y Int)",
                "(declare-fun f (Int) Int)",
            ],
            assertions: &["(= x y)", "(<= (* 2 (f x)) 1)", "(>= (* 2 (f y)) 1)"],
            oracles: GENERAL_ORACLES,
        },
        CoreCase {
            name: "QF_UFLRA core",
            logic: "QF_UFLRA",
            oracle_logic: None,
            declarations: &[
                "(declare-const x Real)",
                "(declare-const y Real)",
                "(declare-fun f (Real) Real)",
            ],
            assertions: &[
                "(= x y)",
                "(<= (- (f x) (f y)) (- (/ 1.0 3.0)))",
                "(<= x 10.0)",
            ],
            oracles: GENERAL_ORACLES,
        },
        CoreCase {
            name: "QF_AUFLIA core",
            logic: "QF_AUFLIA",
            oracle_logic: None,
            declarations: &[
                "(declare-const a (Array Int Int))",
                "(declare-const x Int)",
                "(declare-const y Int)",
                "(declare-fun f (Int) Int)",
            ],
            assertions: &[
                "(= y (+ x 1))",
                "(= (f (select (store a x 7) y)) 1)",
                "(= (f (select a y)) 0)",
            ],
            oracles: GENERAL_ORACLES,
        },
    ]
}
