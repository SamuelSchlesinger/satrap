//! Deterministic differential corpora and independent model replay.

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
const Z3_ONLY: &[Oracle] = &[Z3];
const GENERAL_ORACLES: &[Oracle] = &[Z3, CVC5];
const ALL_ORACLES: &[Oracle] = &[Z3, CVC5, BITWUZLA];

#[test]
fn deterministic_qf_bv_corpus_agrees_with_reference_solvers() {
    assert_differential_corpus_with_oracles("QF_BV", &differential_script(), 544, ALL_ORACLES);
}

#[test]
fn deterministic_qf_uf_and_ufbv_corpora_agree_with_reference_solvers() {
    assert_differential_corpus_with_oracles(
        "QF_UF",
        &uf_differential_script(),
        384,
        GENERAL_ORACLES,
    );
    assert_differential_corpus_with_oracles(
        "QF_UFBV",
        &ufbv_differential_script(),
        256,
        GENERAL_ORACLES,
    );
}

#[test]
fn deterministic_extensional_array_corpora_agree_with_reference_solvers() {
    assert_differential_corpus_with_oracles(
        "QF_ABV",
        &abv_differential_script(),
        256,
        GENERAL_ORACLES,
    );
    assert_differential_corpus_with_oracles("QF_AUFBV", &aufbv_differential_script(), 128, Z3_ONLY);
}

#[test]
fn deterministic_finite_aufbv_corpus_agrees_with_three_reference_solvers() {
    assert_differential_corpus_with_oracles(
        "finite QF_AUFBV",
        &finite_aufbv_differential_script(),
        256,
        ALL_ORACLES,
    );
}

#[test]
fn deterministic_exact_arithmetic_corpora_agree_with_reference_solvers() {
    for (name, script, expected) in [
        ("QF_IDL", idl_differential_script(), 384),
        ("QF_LIA", lia_differential_script(), 384),
        ("QF_RDL", rdl_differential_script(), 256),
        ("QF_LRA", lra_differential_script(), 384),
    ] {
        assert_differential_corpus_with_oracles(name, &script, expected, GENERAL_ORACLES);
    }
}

#[test]
fn deterministic_qf_ufidl_corpus_agrees_with_reference_solvers() {
    assert_differential_corpus("QF_UFIDL", &ufidl_differential_script(), 256);
}

#[test]
fn deterministic_qf_uflia_corpus_agrees_with_reference_solvers() {
    assert_differential_corpus("QF_UFLIA", &uflia_differential_script(64), 64);
}

#[test]
fn deterministic_qf_uflra_corpus_agrees_with_reference_solvers() {
    assert_differential_corpus("QF_UFLRA", &uflra_differential_script(), 256);
}

#[test]
fn deterministic_qf_auflia_corpus_agrees_with_reference_solvers() {
    assert_differential_corpus("QF_AUFLIA", &auflia_differential_script(64), 64);
}

fn assert_differential_corpus(name: &str, script: &str, expected: usize) {
    assert_differential_corpus_with_oracles(name, script, expected, GENERAL_ORACLES);
}

fn assert_differential_corpus_with_oracles(
    name: &str,
    script: &str,
    expected: usize,
    oracles: &[Oracle],
) {
    let ours = run_solver(env!("CARGO_BIN_EXE_smt"), &[], script);
    assert!(
        ours.status.success(),
        "our solver failed on {name}:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&ours.stdout),
        String::from_utf8_lossy(&ours.stderr)
    );
    let ours_stdout = String::from_utf8(ours.stdout).expect("our output must be UTF-8");
    let ours_results = check_results(&ours_stdout);
    assert_eq!(
        ours_results.len(),
        expected,
        "our solver did not answer every {name} query:\n{ours_stdout}"
    );
    assert!(
        !ours_results.contains(&"unknown"),
        "our solver returned unknown on its advertised {name} fragment"
    );

    for &oracle in oracles {
        if !oracle_is_available(oracle) {
            eprintln!(
                "skipping {name} comparison with {} because {} is not installed",
                oracle.name, oracle.program
            );
            continue;
        }
        let reference = run_solver(oracle.program, oracle.arguments, script);
        assert!(
            reference.status.success(),
            "{} failed on {name}:\nstdout:\n{}\nstderr:\n{}",
            oracle.name,
            String::from_utf8_lossy(&reference.stdout),
            String::from_utf8_lossy(&reference.stderr)
        );
        let reference_stdout =
            String::from_utf8(reference.stdout).expect("oracle output must be UTF-8");
        let reference_results = check_results(&reference_stdout);
        assert_eq!(
            reference_results.len(),
            expected,
            "{} did not answer every {name} query:\n{reference_stdout}",
            oracle.name
        );
        let mismatch = ours_results
            .iter()
            .zip(&reference_results)
            .position(|(ours, reference)| ours != reference);
        assert_eq!(
            mismatch,
            None,
            "{name} differential mismatch against {} at query {mismatch:?}: \
             ours={:?}, reference={:?}",
            oracle.name,
            mismatch.map(|index| ours_results[index]),
            mismatch.map(|index| reference_results[index])
        );
    }
}

fn oracle_is_available(oracle: Oracle) -> bool {
    Command::new(oracle.program)
        .arg("--version")
        .output()
        .is_ok_and(|output| output.status.success())
}

#[test]
fn exact_arithmetic_models_are_independently_validated() {
    let cases = arithmetic_model_cases();
    assert_eq!(cases.len(), 72);
    for case in cases {
        let script = case.solver_script();
        let ours = run_solver(env!("CARGO_BIN_EXE_smt"), &[], &script);
        assert!(
            ours.status.success(),
            "our solver failed on {}:\nscript:\n{}\nstdout:\n{}\nstderr:\n{}",
            case.name,
            script,
            String::from_utf8_lossy(&ours.stdout),
            String::from_utf8_lossy(&ours.stderr)
        );
        let ours_stdout = String::from_utf8(ours.stdout).expect("our output must be UTF-8");
        assert_eq!(
            check_results(&ours_stdout),
            ["sat"],
            "our solver did not produce a model for {}:\n{ours_stdout}",
            case.name
        );

        let validation_script = case.validation_script(&ours_stdout);
        assert_model_replay(&case.name, &validation_script, &ours_stdout);
    }
}

#[test]
fn arithmetic_combination_models_are_independently_validated() {
    let cases = arithmetic_combination_model_cases();
    assert_eq!(cases.len(), 16);
    for case in cases {
        let script = case.solver_script();
        let ours = run_solver(env!("CARGO_BIN_EXE_smt"), &[], &script);
        assert!(
            ours.status.success(),
            "our solver failed on {}:\nscript:\n{}\nstdout:\n{}\nstderr:\n{}",
            case.name,
            script,
            String::from_utf8_lossy(&ours.stdout),
            String::from_utf8_lossy(&ours.stderr)
        );
        let ours_stdout = String::from_utf8(ours.stdout).expect("our output must be UTF-8");
        assert_eq!(
            check_results(&ours_stdout),
            ["sat"],
            "our solver did not produce a model for {}:\n{ours_stdout}",
            case.name
        );

        let validation_script = case.validation_script(&ours_stdout);
        assert_model_replay(&case.name, &validation_script, &ours_stdout);
    }
}

fn assert_model_replay(case_name: &str, validation_script: &str, solver_output: &str) {
    for &oracle in GENERAL_ORACLES {
        if !oracle_is_available(oracle) {
            eprintln!(
                "skipping model replay with {} because {} is not installed",
                oracle.name, oracle.program
            );
            continue;
        }
        let reference = run_solver(oracle.program, oracle.arguments, validation_script);
        assert!(
            reference.status.success(),
            "{} rejected the validation script for {case_name}:\n\
             script:\n{validation_script}\nstdout:\n{}\nstderr:\n{}",
            oracle.name,
            String::from_utf8_lossy(&reference.stdout),
            String::from_utf8_lossy(&reference.stderr)
        );
        let reference_stdout =
            String::from_utf8(reference.stdout).expect("oracle output must be UTF-8");
        assert_eq!(
            check_results(&reference_stdout),
            ["sat"],
            "our model does not satisfy {case_name} according to {}:\n\
             solver output:\n{solver_output}\nvalidation output:\n{reference_stdout}",
            oracle.name
        );
    }
}

fn differential_script() -> String {
    const WORD_EXPRESSIONS: &[(&str, u32)] = &[
        ("(bvnot x)", 4),
        ("(bvneg x)", 4),
        ("(bvand x y)", 4),
        ("(bvor x y)", 4),
        ("(bvxor x y)", 4),
        ("(bvnand x y)", 4),
        ("(bvnor x y)", 4),
        ("(bvxnor x y)", 4),
        ("(bvcomp x y)", 1),
        ("(bvadd x y)", 4),
        ("(bvsub x y)", 4),
        ("(bvmul x y)", 4),
        ("(bvudiv x y)", 4),
        ("(bvurem x y)", 4),
        ("(bvsdiv x y)", 4),
        ("(bvsrem x y)", 4),
        ("(bvsmod x y)", 4),
        ("(bvshl x y)", 4),
        ("(bvlshr x y)", 4),
        ("(bvashr x y)", 4),
        ("(concat x y)", 8),
        ("((_ extract 2 1) x)", 2),
        ("((_ repeat 2) x)", 8),
        ("((_ zero_extend 3) x)", 7),
        ("((_ sign_extend 3) x)", 7),
        ("((_ rotate_left 3) x)", 4),
        ("((_ rotate_right 3) x)", 4),
    ];
    const PREDICATES: &[&str] = &[
        "(bvult x y)",
        "(bvule x y)",
        "(bvugt x y)",
        "(bvuge x y)",
        "(bvslt x y)",
        "(bvsle x y)",
        "(bvsgt x y)",
        "(bvsge x y)",
        "(bvnego x)",
        "(bvuaddo x y)",
        "(bvsaddo x y)",
        "(bvumulo x y)",
        "(bvsmulo x y)",
        "(bvusubo x y)",
        "(bvssubo x y)",
        "(bvsdivo x y)",
    ];

    let mut script = String::from(
        "(set-logic QF_BV)\n\
         (declare-const x (_ BitVec 4))\n\
         (declare-const y (_ BitVec 4))\n",
    );
    let mut state = 0x9e37_79b9_u32;
    for query in 0..544 {
        state = state.wrapping_mul(1_664_525).wrapping_add(1_013_904_223);
        let left = (state >> 4) & 0xf;
        let right = (state >> 12) & 0xf;
        writeln!(script, "(push 1)").unwrap();
        writeln!(script, "(assert (= x (_ bv{left} 4)))").unwrap();
        writeln!(script, "(assert (= y (_ bv{right} 4)))").unwrap();

        if query % 2 == 0 {
            let (expression, width) = WORD_EXPRESSIONS[query % WORD_EXPRESSIONS.len()];
            let target = (state >> 20) & ((1_u32 << width) - 1);
            writeln!(script, "(assert (= {expression} (_ bv{target} {width})))").unwrap();
        } else {
            let predicate = PREDICATES[query % PREDICATES.len()];
            let assertion = if state & 1 == 0 {
                predicate.to_owned()
            } else {
                format!("(not {predicate})")
            };
            writeln!(script, "(assert {assertion})").unwrap();
        }

        writeln!(script, "(check-sat)").unwrap();
        writeln!(script, "(pop 1)").unwrap();
    }
    script.push_str("(exit)\n");
    script
}

fn uf_differential_script() -> String {
    const TERMS: &[&str] = &[
        "a",
        "b",
        "c",
        "d",
        "(f a)",
        "(f b)",
        "(f c)",
        "(f d)",
        "(g a)",
        "(g b)",
        "(g c)",
        "(g d)",
        "(f (g a))",
        "(f (g b))",
        "(g (f c))",
        "(g (f d))",
        "(h a b)",
        "(h b a)",
        "(h c d)",
        "(h d c)",
    ];
    let mut script = String::from(
        "(set-logic QF_UF)\n\
         (declare-sort U 0)\n\
         (declare-const a U)\n\
         (declare-const b U)\n\
         (declare-const c U)\n\
         (declare-const d U)\n\
         (declare-const q Bool)\n\
         (declare-fun f (U) U)\n\
         (declare-fun g (U) U)\n\
         (declare-fun h (U U) U)\n\
         (declare-fun p (U) Bool)\n",
    );
    let mut state = 0x243f_6a88_u32;
    for query in 0..384 {
        writeln!(script, "(push 1)").unwrap();
        for assertion in 0..5 {
            state = state.wrapping_mul(1_103_515_245).wrapping_add(12_345);
            let left = TERMS[(state as usize >> 3) % TERMS.len()];
            let right = TERMS[(state as usize >> 11) % TERMS.len()];
            let relation = if state & 1 == 0 { "=" } else { "distinct" };
            writeln!(script, "(assert ({relation} {left} {right}))").unwrap();
            if assertion == 2 && query % 7 == 0 {
                writeln!(script, "(assert (= (p a) (p b)))").unwrap();
            }
        }
        match query % 6 {
            0 => {
                writeln!(script, "(assert (= a b))").unwrap();
                writeln!(script, "(assert (distinct (f a) (f b)))").unwrap();
            }
            1 => {
                writeln!(script, "(assert (= a b))").unwrap();
                writeln!(script, "(assert (= b c))").unwrap();
                writeln!(script, "(assert (distinct (h a d) (h c d)))").unwrap();
            }
            2 => {
                writeln!(script, "(assert q)").unwrap();
                writeln!(script, "(assert (distinct (ite q a b) a))").unwrap();
            }
            3 => {
                writeln!(script, "(assert (= a b))").unwrap();
                writeln!(script, "(assert (xor (p a) (p b)))").unwrap();
            }
            _ => {}
        }
        writeln!(script, "(check-sat)").unwrap();
        writeln!(script, "(pop 1)").unwrap();
    }
    script.push_str("(exit)\n");
    script
}

fn ufbv_differential_script() -> String {
    let mut script = String::from(
        "(set-logic QF_UFBV)\n\
         (declare-sort U 0)\n\
         (declare-const a U)\n\
         (declare-const b U)\n\
         (declare-const c U)\n\
         (declare-fun color (U) (_ BitVec 4))\n\
         (declare-fun step (U (_ BitVec 4)) U)\n",
    );
    let mut state = 0xb7e1_5163_u32;
    for query in 0..256 {
        state = state.wrapping_mul(22_695_477).wrapping_add(1);
        let value = (state >> 12) & 0xf;
        writeln!(script, "(push 1)").unwrap();
        if query % 3 == 0 {
            writeln!(script, "(assert (= a b))").unwrap();
        } else {
            writeln!(script, "(assert (distinct a b))").unwrap();
        }
        writeln!(
            script,
            "(assert (= (bvadd (color a) (_ bv{value} 4)) (color c)))"
        )
        .unwrap();
        if query % 4 == 0 {
            writeln!(script, "(assert (distinct (color a) (color b)))").unwrap();
        }
        if query % 5 == 0 {
            writeln!(
                script,
                "(assert (distinct (step a (color c)) (step b (color c))))"
            )
            .unwrap();
        }
        writeln!(script, "(check-sat)").unwrap();
        writeln!(script, "(pop 1)").unwrap();
    }
    script.push_str("(exit)\n");
    script
}

fn abv_differential_script() -> String {
    const ARRAYS: &[&str] = &[
        "a",
        "b",
        "(store a i x)",
        "(store a j y)",
        "(store b i y)",
        "(store (store a i x) j y)",
        "((as const (Array (_ BitVec 2) (_ BitVec 3))) #b000)",
        "((as const (Array (_ BitVec 2) (_ BitVec 3))) #b101)",
    ];
    let mut script = String::from(
        "(set-logic QF_ABV)\n\
         (declare-const a (Array (_ BitVec 2) (_ BitVec 3)))\n\
         (declare-const b (Array (_ BitVec 2) (_ BitVec 3)))\n\
         (declare-const i (_ BitVec 2))\n\
         (declare-const j (_ BitVec 2))\n\
         (declare-const x (_ BitVec 3))\n\
         (declare-const y (_ BitVec 3))\n",
    );
    let mut state = 0xa409_3822_u32;
    for query in 0..256 {
        state = state.wrapping_mul(1_664_525).wrapping_add(1_013_904_223);
        let left = ARRAYS[(state as usize >> 4) % ARRAYS.len()];
        let right = ARRAYS[(state as usize >> 13) % ARRAYS.len()];
        writeln!(script, "(push 1)").unwrap();
        writeln!(script, "(assert (= i (_ bv{} 2)))", (state >> 20) & 3).unwrap();
        writeln!(script, "(assert (= j (_ bv{} 2)))", (state >> 22) & 3).unwrap();
        writeln!(script, "(assert (= x (_ bv{} 3)))", (state >> 24) & 7).unwrap();
        writeln!(script, "(assert (= y (_ bv{} 3)))", (state >> 27) & 7).unwrap();
        if state & 1 == 0 {
            writeln!(script, "(assert (= {left} {right}))").unwrap();
        } else {
            writeln!(script, "(assert (distinct {left} {right}))").unwrap();
        }
        match query % 5 {
            0 => {
                writeln!(script, "(assert (= a b))").unwrap();
                writeln!(script, "(assert (distinct (select a i) (select b i)))").unwrap();
            }
            1 => {
                writeln!(script, "(assert (distinct a b))").unwrap();
                for index in 0..4 {
                    writeln!(
                        script,
                        "(assert (= (select a (_ bv{index} 2)) \
                         (select b (_ bv{index} 2))))"
                    )
                    .unwrap();
                }
            }
            2 => {
                writeln!(script, "(assert (distinct (select (store a i x) i) x))").unwrap();
            }
            3 => {
                writeln!(script, "(assert (distinct i j))").unwrap();
                writeln!(
                    script,
                    "(assert (distinct (select (store a i x) j) (select a j)))"
                )
                .unwrap();
            }
            _ => {}
        }
        writeln!(script, "(check-sat)").unwrap();
        writeln!(script, "(pop 1)").unwrap();
    }
    script.push_str("(exit)\n");
    script
}

fn aufbv_differential_script() -> String {
    let mut script = String::from(
        "(set-logic QF_AUFBV)\n\
         (declare-sort U 0)\n\
         (declare-const a (Array (_ BitVec 2) U))\n\
         (declare-const b (Array (_ BitVec 2) U))\n\
         (declare-const u U)\n\
         (declare-const v U)\n\
         (declare-fun observe ((Array (_ BitVec 2) U)) (_ BitVec 3))\n\
         (declare-fun next (U) U)\n",
    );
    for query in 0..128 {
        let index = query % 4;
        writeln!(script, "(push 1)").unwrap();
        match query % 4 {
            0 => {
                writeln!(script, "(assert (= a b))").unwrap();
                writeln!(script, "(assert (distinct (observe a) (observe b)))").unwrap();
            }
            1 => {
                writeln!(script, "(assert (= u v))").unwrap();
                writeln!(
                    script,
                    "(assert (distinct (store a (_ bv{index} 2) u) \
                     (store a (_ bv{index} 2) v)))"
                )
                .unwrap();
            }
            2 => {
                writeln!(script, "(assert (distinct u v))").unwrap();
                writeln!(
                    script,
                    "(assert (= a ((as const (Array (_ BitVec 2) U)) u)))"
                )
                .unwrap();
                writeln!(script, "(assert (= (select a (_ bv{index} 2)) v))").unwrap();
            }
            _ => {
                writeln!(
                    script,
                    "(assert (= (select (store a (_ bv{index} 2) (next u)) \
                     (_ bv{index} 2)) (next u)))"
                )
                .unwrap();
            }
        }
        writeln!(script, "(check-sat)").unwrap();
        writeln!(script, "(pop 1)").unwrap();
    }
    script.push_str("(exit)\n");
    script
}

fn finite_aufbv_differential_script() -> String {
    let mut script = String::from(
        "(set-logic QF_AUFBV)\n\
         (declare-const a (Array (_ BitVec 2) (_ BitVec 3)))\n\
         (declare-const b (Array (_ BitVec 2) (_ BitVec 3)))\n\
         (declare-const i (_ BitVec 2))\n\
         (declare-const j (_ BitVec 2))\n\
         (declare-const x (_ BitVec 3))\n\
         (declare-const y (_ BitVec 3))\n\
         (declare-fun f ((_ BitVec 3)) (_ BitVec 3))\n\
         (declare-fun p ((_ BitVec 3)) Bool)\n",
    );
    let mut state = 0x4528_21e6_u32;
    for query in 0..256 {
        state = state.wrapping_mul(22_695_477).wrapping_add(1);
        let i = (state >> 4) & 3;
        let j = (state >> 9) & 3;
        let x = (state >> 14) & 7;
        let y = (state >> 20) & 7;
        writeln!(script, "(push 1)").unwrap();
        writeln!(script, "(assert (= i (_ bv{i} 2)))").unwrap();
        writeln!(script, "(assert (= j (_ bv{j} 2)))").unwrap();
        writeln!(script, "(assert (= x (_ bv{x} 3)))").unwrap();
        writeln!(script, "(assert (= y (_ bv{y} 3)))").unwrap();
        match query % 8 {
            0 => {
                writeln!(script, "(assert (distinct (select (store a i x) i) x))").unwrap();
            }
            1 => {
                writeln!(script, "(assert (distinct i j))").unwrap();
                writeln!(
                    script,
                    "(assert (distinct (select (store a i x) j) (select a j)))"
                )
                .unwrap();
            }
            2 => {
                writeln!(script, "(assert (= (select a i) x))").unwrap();
                writeln!(script, "(assert (distinct (f (select a i)) (f x)))").unwrap();
            }
            3 => {
                writeln!(script, "(assert (= x y))").unwrap();
                writeln!(script, "(assert (xor (p x) (p y)))").unwrap();
            }
            4 => {
                writeln!(script, "(assert (= (select a i) x))").unwrap();
                writeln!(script, "(assert (= (select b j) (f x)))").unwrap();
            }
            5 => {
                writeln!(script, "(assert (= (select (store a i (f x)) i) (f x)))").unwrap();
            }
            6 => {
                writeln!(script, "(assert (= (f x) (bvadd y #b001)))").unwrap();
                writeln!(script, "(assert (= (select a i) (f x)))").unwrap();
            }
            _ => {
                writeln!(script, "(assert (= (select a i) x))").unwrap();
                writeln!(
                    script,
                    "(assert (= (select (store a j y) i) (ite (= i j) y x)))"
                )
                .unwrap();
            }
        }
        writeln!(script, "(check-sat)").unwrap();
        writeln!(script, "(pop 1)").unwrap();
    }
    script.push_str("(exit)\n");
    script
}

fn idl_differential_script() -> String {
    const VARIABLES: &[&str] = &["x", "y", "z"];
    let mut script = String::from(
        "(set-logic QF_IDL)\n\
         (declare-const x Int)\n\
         (declare-const y Int)\n\
         (declare-const z Int)\n",
    );
    let mut state = 0x1319_8a2e_u32;
    for query in 0..384 {
        writeln!(script, "(push 1)").unwrap();
        for assertion in 0..5 {
            state = state.wrapping_mul(1_664_525).wrapping_add(1_013_904_223);
            let left = VARIABLES[(state as usize >> 4) % VARIABLES.len()];
            let right = VARIABLES[(state as usize >> 12) % VARIABLES.len()];
            let bound = i32::try_from((state >> 20) % 17).unwrap() - 8;
            let relation = ["<=", "<", ">=", ">"][(state as usize >> 2) & 3];
            let bound = smt_integer(bound);
            if assertion == 3 && query % 5 == 0 {
                writeln!(
                    script,
                    "(assert (or ({relation} (- {left} {right}) {bound}) \
                     (distinct {left} {right})))"
                )
                .unwrap();
            } else if assertion == 4 && query % 7 == 0 {
                writeln!(script, "(assert (= (- {left} {right}) {bound}))").unwrap();
            } else {
                writeln!(script, "(assert ({relation} (- {left} {right}) {bound}))").unwrap();
            }
        }
        match query % 6 {
            0 => {
                writeln!(script, "(assert (<= (- x y) 2))").unwrap();
                writeln!(script, "(assert (<= (- y z) 3))").unwrap();
                writeln!(script, "(assert (<= (- z x) (- 6)))").unwrap();
            }
            1 => {
                writeln!(script, "(assert (< x y))").unwrap();
                writeln!(script, "(assert (<= y x))").unwrap();
            }
            2 => {
                writeln!(script, "(assert (= (- x y) 4))").unwrap();
                writeln!(script, "(assert (distinct (- x y) 4))").unwrap();
            }
            _ => {}
        }
        writeln!(script, "(check-sat)").unwrap();
        writeln!(script, "(pop 1)").unwrap();
    }
    script.push_str("(exit)\n");
    script
}

fn lia_differential_script() -> String {
    const COEFFICIENTS: &[i32] = &[-4, -3, -2, -1, 1, 2, 3, 4];
    let mut script = String::from(
        "(set-logic QF_LIA)\n\
         (declare-const x Int)\n\
         (declare-const y Int)\n\
         (declare-const z Int)\n\
         (assert (and (<= (- 12) x) (<= x 12)))\n\
         (assert (and (<= (- 12) y) (<= y 12)))\n\
         (assert (and (<= (- 12) z) (<= z 12)))\n",
    );
    let mut state = 0x082e_fa98_u32;
    for query in 0..384 {
        writeln!(script, "(push 1)").unwrap();
        for assertion in 0..5 {
            state = state.wrapping_mul(1_664_525).wrapping_add(1_013_904_223);
            let a = COEFFICIENTS[(state as usize >> 2) % COEFFICIENTS.len()];
            let b = COEFFICIENTS[(state as usize >> 9) % COEFFICIENTS.len()];
            let c = COEFFICIENTS[(state as usize >> 16) % COEFFICIENTS.len()];
            let bound = i32::try_from((state >> 23) % 25).unwrap() - 12;
            let relation = ["<=", "<", ">=", ">"][(state as usize >> 5) & 3];
            let atom = format!(
                "({relation} (+ (* {} x) (* {} y) (* {} z)) {})",
                smt_integer(a),
                smt_integer(b),
                smt_integer(c),
                smt_integer(bound)
            );
            if assertion == 3 && query % 5 == 0 {
                writeln!(script, "(assert (or {atom} (= (+ x y) z)))").unwrap();
            } else if assertion == 4 && query % 7 == 0 {
                writeln!(script, "(assert (not {atom}))").unwrap();
            } else {
                writeln!(script, "(assert {atom})").unwrap();
            }
        }
        match query % 8 {
            0 => {
                writeln!(script, "(assert (= (+ (* 2 x) (* 2 y)) 1))").unwrap();
            }
            1 => {
                writeln!(script, "(assert (= (+ (* 3 x) (* 5 y) (* (- 2) z)) 7))").unwrap();
            }
            2 => {
                writeln!(script, "(assert (distinct (* 2 (+ x y)) 1))").unwrap();
            }
            3 => {
                writeln!(script, "(assert (= (ite (< x y) (+ x z) (- y z)) 4))").unwrap();
            }
            _ => {}
        }
        writeln!(script, "(check-sat)").unwrap();
        writeln!(script, "(pop 1)").unwrap();
    }
    script.push_str("(exit)\n");
    script
}

fn ufidl_differential_script() -> String {
    const TERMS: &[&str] = &["x", "y", "z", "(f x)", "(f y)", "(f z)"];
    let mut script = String::from(
        "(set-logic QF_UFIDL)\n\
         (declare-const x Int)\n\
         (declare-const y Int)\n\
         (declare-const z Int)\n\
         (declare-fun f (Int) Int)\n",
    );
    let mut state = 0x4528_21e6_u32;
    for query in 0..256 {
        writeln!(script, "(push 1)").unwrap();
        for _ in 0..4 {
            state = state.wrapping_mul(22_695_477).wrapping_add(1);
            let left = TERMS[(state as usize >> 3) % TERMS.len()];
            let right = TERMS[(state as usize >> 11) % TERMS.len()];
            let bound = i32::try_from((state >> 19) % 17).unwrap() - 8;
            let relation = ["<=", "<", ">=", ">"][(state as usize >> 1) & 3];
            writeln!(
                script,
                "(assert ({relation} (- {left} {right}) {}))",
                smt_integer(bound)
            )
            .unwrap();
        }
        match query % 6 {
            0 => {
                writeln!(script, "(assert (= x y))").unwrap();
                writeln!(script, "(assert (distinct (f x) (f y)))").unwrap();
            }
            1 => {
                writeln!(script, "(assert (distinct x y))").unwrap();
                writeln!(script, "(assert (= (f x) (f y)))").unwrap();
            }
            2 => {
                writeln!(script, "(assert (= (- x y) 0))").unwrap();
                writeln!(script, "(assert (> (f x) (f y)))").unwrap();
            }
            3 => {
                writeln!(script, "(assert (= y z))").unwrap();
                writeln!(script, "(assert (= (f x) y))").unwrap();
                writeln!(script, "(assert (distinct (f x) z))").unwrap();
            }
            _ => {}
        }
        writeln!(script, "(check-sat)").unwrap();
        writeln!(script, "(pop 1)").unwrap();
    }
    script.push_str("(exit)\n");
    script
}

fn uflia_differential_script(query_count: usize) -> String {
    const COEFFICIENTS: &[i32] = &[-3, -2, -1, 1, 2, 3];
    const TERMS: &[&str] = &["x", "y", "z", "(f x)", "(f y)", "(f z)"];
    let mut script = String::from(
        "(set-logic QF_UFLIA)\n\
         (declare-const x Int)\n\
         (declare-const y Int)\n\
         (declare-const z Int)\n\
         (declare-fun f (Int) Int)\n\
         (assert (and (<= (- 8) x) (<= x 8)))\n\
         (assert (and (<= (- 8) y) (<= y 8)))\n\
         (assert (and (<= (- 8) z) (<= z 8)))\n\
         (assert (and (<= (- 8) (f x)) (<= (f x) 8)))\n\
         (assert (and (<= (- 8) (f y)) (<= (f y) 8)))\n\
         (assert (and (<= (- 8) (f z)) (<= (f z) 8)))\n",
    );
    let mut state = 0x38d0_1377_u32;
    for query in 0..query_count {
        writeln!(script, "(push 1)").unwrap();
        for assertion in 0..4 {
            state = state.wrapping_mul(1_103_515_245).wrapping_add(12_345);
            let a = COEFFICIENTS[(state as usize >> 2) % COEFFICIENTS.len()];
            let b = COEFFICIENTS[(state as usize >> 9) % COEFFICIENTS.len()];
            let left = TERMS[(state as usize >> 16) % TERMS.len()];
            let right = TERMS[(state as usize >> 22) % TERMS.len()];
            let bound = i32::try_from((state >> 26) % 13).unwrap() - 6;
            let relation = ["<=", "<", ">=", ">"][(state as usize >> 5) & 3];
            let atom = format!(
                "({relation} (+ (* {} {left}) (* {} {right})) {})",
                smt_integer(a),
                smt_integer(b),
                smt_integer(bound)
            );
            if assertion == 3 && query % 7 == 0 {
                writeln!(script, "(assert (or {atom} (= x y)))").unwrap();
            } else {
                writeln!(script, "(assert {atom})").unwrap();
            }
        }
        match query % 7 {
            0 => {
                writeln!(script, "(assert (= (+ (* 2 x) (* 2 y)) 1))").unwrap();
            }
            1 => {
                writeln!(script, "(assert (= x y))").unwrap();
                writeln!(script, "(assert (distinct (f x) (f y)))").unwrap();
            }
            2 => {
                writeln!(script, "(assert (= (+ (* 2 x) y) (+ x (* 2 y))))").unwrap();
                writeln!(script, "(assert (> (f x) (f y)))").unwrap();
            }
            3 => {
                writeln!(script, "(assert (distinct x y))").unwrap();
                writeln!(script, "(assert (= (f x) (f y)))").unwrap();
            }
            _ => {}
        }
        writeln!(script, "(check-sat)").unwrap();
        writeln!(script, "(pop 1)").unwrap();
    }
    script.push_str("(exit)\n");
    script
}

fn uflra_differential_script() -> String {
    const COEFFICIENTS: &[i32] = &[-3, -2, -1, 1, 2, 3];
    const TERMS: &[&str] = &["x", "y", "z", "(f x)", "(f y)", "(f z)"];
    let mut script = String::from(
        "(set-logic QF_UFLRA)\n\
         (declare-const x Real)\n\
         (declare-const y Real)\n\
         (declare-const z Real)\n\
         (declare-fun f (Real) Real)\n",
    );
    let mut state = 0xbe54_66cf_u32;
    for query in 0..256 {
        writeln!(script, "(push 1)").unwrap();
        for assertion in 0..4 {
            state = state.wrapping_mul(1_664_525).wrapping_add(1_013_904_223);
            let a = COEFFICIENTS[(state as usize >> 2) % COEFFICIENTS.len()];
            let b = COEFFICIENTS[(state as usize >> 9) % COEFFICIENTS.len()];
            let left = TERMS[(state as usize >> 16) % TERMS.len()];
            let right = TERMS[(state as usize >> 22) % TERMS.len()];
            let bound = i32::try_from((state >> 26) % 13).unwrap() - 6;
            let relation = ["<=", "<", ">=", ">"][(state as usize >> 5) & 3];
            let atom = format!(
                "({relation} (+ (* {} {left}) (* {} {right})) {})",
                smt_integer(a),
                smt_integer(b),
                smt_integer(bound)
            );
            if assertion == 3 && query % 5 == 0 {
                writeln!(script, "(assert (not {atom}))").unwrap();
            } else {
                writeln!(script, "(assert {atom})").unwrap();
            }
        }
        match query % 6 {
            0 => {
                writeln!(script, "(assert (= x y))").unwrap();
                writeln!(script, "(assert (distinct (f x) (f y)))").unwrap();
            }
            1 => {
                writeln!(script, "(assert (= (- x y) 0.0))").unwrap();
                writeln!(script, "(assert (> (f x) (f y)))").unwrap();
            }
            2 => {
                writeln!(script, "(assert (distinct x y))").unwrap();
                writeln!(script, "(assert (= (f x) (f y)))").unwrap();
            }
            _ => {}
        }
        writeln!(script, "(check-sat)").unwrap();
        writeln!(script, "(pop 1)").unwrap();
    }
    script.push_str("(exit)\n");
    script
}

fn auflia_differential_script(query_count: usize) -> String {
    let mut script = String::new();
    let mut state = 0x34e9_0c6c_u32;
    for query in 0..query_count {
        if query % 8 == 0 {
            if query != 0 {
                script.push_str("(reset)\n");
            }
            script.push_str(
                "(set-logic QF_AUFLIA)\n\
                 (declare-const a (Array Int Int))\n\
                 (declare-const b (Array Int Int))\n\
                 (declare-const x Int)\n\
                 (declare-const y Int)\n\
                 (declare-const v Int)\n\
                 (declare-fun observe ((Array Int Int)) Int)\n\
                 (assert (and (<= (- 6) x) (<= x 6)))\n\
                 (assert (and (<= (- 6) y) (<= y 6)))\n\
                 (assert (and (<= (- 6) v) (<= v 6)))\n",
            );
        }
        writeln!(script, "(push 1)").unwrap();
        state = state.wrapping_mul(1_664_525).wrapping_add(1_013_904_223);
        let bound = i32::try_from((state >> 21) % 13).unwrap() - 6;
        let relation = ["<=", "<", ">=", ">"][(state as usize >> 4) & 3];
        writeln!(
            script,
            "(assert ({relation} (+ (* 2 x) (* (- 3) y) v) {}))",
            smt_integer(bound)
        )
        .unwrap();
        match query % 8 {
            0 => {
                writeln!(script, "(assert (= x y))").unwrap();
                writeln!(script, "(assert (distinct (select (store a x v) y) v))").unwrap();
            }
            1 => {
                writeln!(script, "(assert (= a b))").unwrap();
                writeln!(script, "(assert (distinct (observe a) (observe b)))").unwrap();
            }
            2 => {
                writeln!(script, "(assert (= a b))").unwrap();
                writeln!(script, "(assert (= x y))").unwrap();
                writeln!(script, "(assert (distinct (select a x) (select b y)))").unwrap();
            }
            3 => {
                writeln!(script, "(assert (distinct a b))").unwrap();
                writeln!(script, "(assert (= (select a x) (select b x)))").unwrap();
            }
            4 => {
                writeln!(script, "(assert (= x y))").unwrap();
                writeln!(script, "(assert (= (store a x v) (store a y v)))").unwrap();
            }
            _ => {}
        }
        writeln!(script, "(check-sat)").unwrap();
        writeln!(script, "(pop 1)").unwrap();
    }
    script.push_str("(exit)\n");
    script
}

fn rdl_differential_script() -> String {
    const VARIABLES: &[&str] = &["x", "y", "z"];
    const BOUNDS: &[&str] = &[
        "(- 2.5)",
        "(- 1.25)",
        "(- (/ 1 3))",
        "0.0",
        "(/ 1 3)",
        "1.25",
        "2.5",
    ];
    let mut script = String::from(
        "(set-logic QF_RDL)\n\
         (declare-const x Real)\n\
         (declare-const y Real)\n\
         (declare-const z Real)\n",
    );
    let mut state = 0x0370_7344_u32;
    for query in 0..256 {
        writeln!(script, "(push 1)").unwrap();
        for assertion in 0..5 {
            state = state.wrapping_mul(22_695_477).wrapping_add(1);
            let left = VARIABLES[(state as usize >> 5) % VARIABLES.len()];
            let right = VARIABLES[(state as usize >> 13) % VARIABLES.len()];
            let bound = BOUNDS[(state as usize >> 21) % BOUNDS.len()];
            let relation = ["<=", "<", ">=", ">"][(state as usize >> 2) & 3];
            let negated = assertion == 3 && query % 7 == 0;
            if negated {
                writeln!(
                    script,
                    "(assert (not ({relation} (- {left} {right}) {bound})))"
                )
                .unwrap();
            } else {
                writeln!(script, "(assert ({relation} (- {left} {right}) {bound}))").unwrap();
            }
        }
        match query % 5 {
            0 => {
                writeln!(script, "(assert (< (- x y) (/ 1 3)))").unwrap();
                writeln!(script, "(assert (<= (- y z) (/ 1 3)))").unwrap();
                writeln!(script, "(assert (<= (- z x) (- (/ 2 3))))").unwrap();
            }
            1 => {
                writeln!(script, "(assert (< x y))").unwrap();
                writeln!(script, "(assert (<= y x))").unwrap();
            }
            _ => {}
        }
        writeln!(script, "(check-sat)").unwrap();
        writeln!(script, "(pop 1)").unwrap();
    }
    script.push_str("(exit)\n");
    script
}

fn lra_differential_script() -> String {
    const COEFFICIENTS: &[i32] = &[-3, -2, -1, 1, 2, 3];
    let mut script = String::from(
        "(set-logic QF_LRA)\n\
         (declare-const x Real)\n\
         (declare-const y Real)\n\
         (declare-const z Real)\n",
    );
    let mut state = 0xa458_fea3_u32;
    for query in 0..384 {
        writeln!(script, "(push 1)").unwrap();
        for assertion in 0..5 {
            state = state.wrapping_mul(1_103_515_245).wrapping_add(12_345);
            let a = COEFFICIENTS[(state as usize >> 3) % COEFFICIENTS.len()];
            let b = COEFFICIENTS[(state as usize >> 10) % COEFFICIENTS.len()];
            let c = COEFFICIENTS[(state as usize >> 17) % COEFFICIENTS.len()];
            let bound = i32::try_from((state >> 24) % 13).unwrap() - 6;
            let relation = ["<=", "<", ">=", ">"][(state as usize >> 1) & 3];
            let atom = format!(
                "({relation} (+ (* {} x) (* {} y) (* {} z)) {})",
                smt_integer(a),
                smt_integer(b),
                smt_integer(c),
                smt_integer(bound)
            );
            if assertion == 3 && query % 4 == 0 {
                writeln!(script, "(assert (or {atom} (> x 0.0)))").unwrap();
            } else if assertion == 4 && query % 9 == 0 {
                writeln!(script, "(assert (not {atom}))").unwrap();
            } else {
                writeln!(script, "(assert {atom})").unwrap();
            }
        }
        match query % 7 {
            0 => {
                writeln!(script, "(assert (> x 0.0))").unwrap();
                writeln!(script, "(assert (> y 0.0))").unwrap();
                writeln!(script, "(assert (= (+ x y) 1.0))").unwrap();
                writeln!(script, "(assert (> (+ x y) 2.0))").unwrap();
            }
            1 => {
                writeln!(script, "(assert (= (+ x y z) (/ 1 3)))").unwrap();
            }
            2 => {
                writeln!(script, "(assert (distinct (+ x y) (+ y x)))").unwrap();
            }
            _ => {}
        }
        writeln!(script, "(check-sat)").unwrap();
        writeln!(script, "(pop 1)").unwrap();
    }
    script.push_str("(exit)\n");
    script
}

struct ArithmeticModelCase {
    name: String,
    logic: &'static str,
    sort: &'static str,
    assertions: Vec<String>,
}

struct CombinationModelCase {
    name: String,
    logic: &'static str,
    declarations: Vec<String>,
    assertions: Vec<String>,
}

impl CombinationModelCase {
    fn solver_script(&self) -> String {
        let mut script = String::from("(set-option :produce-models true)\n");
        writeln!(script, "(set-logic {})", self.logic).unwrap();
        for declaration in &self.declarations {
            writeln!(script, "{declaration}").unwrap();
        }
        for assertion in &self.assertions {
            writeln!(script, "(assert {assertion})").unwrap();
        }
        script.push_str("(check-sat)\n(get-model)\n(exit)\n");
        script
    }

    fn validation_script(&self, solver_output: &str) -> String {
        let mut script = format!("(set-logic {})\n", self.logic);
        let definitions = solver_output
            .lines()
            .map(str::trim)
            .filter(|line| line.starts_with("(define-fun "))
            .collect::<Vec<_>>();
        assert_eq!(
            definitions.len(),
            self.declarations.len(),
            "model definition count differs from declarations for {}:\n{solver_output}",
            self.name
        );
        for definition in definitions {
            writeln!(script, "{definition}").unwrap();
        }
        for assertion in &self.assertions {
            writeln!(script, "(assert {assertion})").unwrap();
        }
        script.push_str("(check-sat)\n(exit)\n");
        script
    }
}

impl ArithmeticModelCase {
    fn solver_script(&self) -> String {
        let mut script = String::from("(set-option :produce-models true)\n");
        self.write_problem(&mut script);
        script.push_str("(check-sat)\n(get-model)\n(exit)\n");
        script
    }

    fn validation_script(&self, solver_output: &str) -> String {
        let mut script = String::new();
        self.write_problem(&mut script);
        for name in ["x", "y", "z"] {
            let value = extract_constant_model_value(solver_output, name, self.sort);
            writeln!(script, "(assert (= {name} {value}))").unwrap();
        }
        script.push_str("(check-sat)\n(exit)\n");
        script
    }

    fn write_problem(&self, script: &mut String) {
        writeln!(script, "(set-logic {})", self.logic).unwrap();
        for name in ["x", "y", "z"] {
            writeln!(script, "(declare-const {name} {})", self.sort).unwrap();
        }
        for assertion in &self.assertions {
            writeln!(script, "(assert {assertion})").unwrap();
        }
    }
}

fn extract_constant_model_value(output: &str, name: &str, sort: &str) -> String {
    let prefix = format!("(define-fun {name} () {sort} ");
    let definition = output
        .lines()
        .map(str::trim)
        .find(|line| line.starts_with(&prefix))
        .unwrap_or_else(|| panic!("model does not define {name} as {sort}:\n{output}"));
    definition
        .strip_prefix(&prefix)
        .and_then(|value| value.strip_suffix(')'))
        .unwrap_or_else(|| panic!("malformed model definition for {name}:\n{definition}"))
        .to_owned()
}

fn arithmetic_model_cases() -> Vec<ArithmeticModelCase> {
    let mut cases = Vec::with_capacity(72);

    for query in 0_i32..16 {
        let x = (query * 7).rem_euclid(19) - 9;
        let y = (query * 11).rem_euclid(17) - 8;
        let z = (query * 13).rem_euclid(23) - 11;
        let slack = query.rem_euclid(4);
        let mut assertions = vec![
            format!("(<= (- x y) {})", smt_integer(x - y + slack)),
            format!("(>= (- y z) {})", smt_integer(y - z - slack)),
            format!("(< (- z x) {})", smt_integer(z - x + slack + 1)),
            format!("(> (- x z) {})", smt_integer(x - z - slack - 1)),
        ];
        match query.rem_euclid(3) {
            0 => assertions.push(format!("(= (- x y) {})", smt_integer(x - y))),
            1 => assertions.push(format!("(or (= (- y z) {}) (< x y))", smt_integer(y - z))),
            _ => assertions.push(format!(
                "(not (> (- z x) {}))",
                smt_integer(z - x + slack + 1)
            )),
        }
        cases.push(ArithmeticModelCase {
            name: format!("QF_IDL model {query}"),
            logic: "QF_IDL",
            sort: "Int",
            assertions,
        });
    }

    const LIA_COEFFICIENTS: &[(i32, i32, i32)] = &[(2, 3, -5), (-4, 3, 2), (5, -2, 3), (-3, -4, 5)];
    for query in 0_i32..16 {
        let x = (query * 5).rem_euclid(17) - 8;
        let y = (query * 7).rem_euclid(19) - 9;
        let z = (query * 11).rem_euclid(23) - 11;
        let (a, b, c) = LIA_COEFFICIENTS[query as usize % LIA_COEFFICIENTS.len()];
        let linear = a * x + b * y + c * z;
        let expression = format!(
            "(+ (* {} x) (* {} y) (* {} z))",
            smt_integer(a),
            smt_integer(b),
            smt_integer(c)
        );
        let mut assertions = vec![
            format!("(= {expression} {})", smt_integer(linear)),
            format!("(>= x {})", smt_integer(x - 3)),
            format!("(<= y {})", smt_integer(y + 3)),
            format!("(>= (- z x) {})", smt_integer(z - x - 2)),
            format!("(<= (+ x y) {})", smt_integer(x + y + 2)),
        ];
        match query.rem_euclid(4) {
            0 => assertions.push(format!(
                "(= (ite (< x {}) (+ y 1) (- z 2)) {})",
                smt_integer(x + 1),
                smt_integer(y + 1)
            )),
            1 => assertions.push(format!(
                "(or (= (+ (* 2 x) (* 3 y)) {}) (> z {}))",
                smt_integer(2 * x + 3 * y),
                smt_integer(z - 1)
            )),
            2 => assertions.push(format!("(not (> {expression} {}))", smt_integer(linear))),
            _ => assertions.push(format!(
                "(distinct (+ (* 2 x) y) {})",
                smt_integer(2 * x + y + 1)
            )),
        }
        cases.push(ArithmeticModelCase {
            name: format!("QF_LIA model {query}"),
            logic: "QF_LIA",
            sort: "Int",
            assertions,
        });
    }

    for query in 0_i32..16 {
        let x = (query * 11).rem_euclid(31) - 15;
        let y = (query * 17).rem_euclid(29) - 14;
        let z = (query * 19).rem_euclid(37) - 18;
        let slack = query.rem_euclid(5) + 1;
        let mut assertions = vec![
            format!("(<= (- x y) {})", smt_sixths(x - y + slack)),
            format!("(>= (- y z) {})", smt_sixths(y - z - slack)),
            format!("(< (- z x) {})", smt_sixths(z - x + slack)),
            format!("(> (- x z) {})", smt_sixths(x - z - slack)),
        ];
        if query % 2 == 0 {
            assertions.push(format!("(= (- x y) {})", smt_sixths(x - y)));
        } else {
            assertions.push(format!(
                "(or (= (- y z) {}) (> x {}))",
                smt_sixths(y - z),
                smt_sixths(x - 1)
            ));
        }
        cases.push(ArithmeticModelCase {
            name: format!("QF_RDL model {query}"),
            logic: "QF_RDL",
            sort: "Real",
            assertions,
        });
    }

    const COEFFICIENTS: &[(i32, i32, i32)] = &[(1, 2, -3), (-2, 3, 1), (3, -1, 2), (-3, -2, 1)];
    for query in 0_i32..24 {
        let x = (query * 5).rem_euclid(23) - 11;
        let y = (query * 7).rem_euclid(19) - 9;
        let z = (query * 11).rem_euclid(29) - 14;
        let (a, b, c) = COEFFICIENTS[query as usize % COEFFICIENTS.len()];
        let linear = a * x + b * y + c * z;
        let expression = format!(
            "(+ (* {} x) (* {} y) (* {} z))",
            smt_integer(a),
            smt_integer(b),
            smt_integer(c)
        );
        let mut assertions = vec![
            format!("(= {expression} {})", smt_sixths(linear)),
            format!("(> x {})", smt_sixths(x - 2)),
            format!("(< y {})", smt_sixths(y + 2)),
            format!("(<= (+ x y) {})", smt_sixths(x + y + 1)),
            format!("(>= (- z x) {})", smt_sixths(z - x - 1)),
        ];
        match query.rem_euclid(4) {
            0 => assertions.push(format!(
                "(= (ite (< x {}) (+ y (/ 1.0 6.0)) \
                 (+ z (/ 1.0 3.0))) {})",
                smt_sixths(x + 1),
                smt_sixths(y + 1)
            )),
            1 => assertions.push(format!(
                "(or (= (+ x y) {}) (> z {}))",
                smt_sixths(x + y),
                smt_sixths(z - 1)
            )),
            2 => assertions.push(format!("(not (> {expression} {}))", smt_sixths(linear))),
            _ => assertions.push(format!("(distinct (+ x y) {})", smt_sixths(x + y + 1))),
        }
        cases.push(ArithmeticModelCase {
            name: format!("QF_LRA model {query}"),
            logic: "QF_LRA",
            sort: "Real",
            assertions,
        });
    }

    cases
}

fn arithmetic_combination_model_cases() -> Vec<CombinationModelCase> {
    let mut cases = Vec::with_capacity(16);
    for query in 0_i32..4 {
        let x = query - 2;
        let y = query + 3;
        cases.push(CombinationModelCase {
            name: format!("QF_UFIDL model {query}"),
            logic: "QF_UFIDL",
            declarations: vec![
                "(declare-const x Int)".to_owned(),
                "(declare-const y Int)".to_owned(),
                "(declare-fun f (Int) Int)".to_owned(),
            ],
            assertions: vec![
                format!("(= x {})", smt_integer(x)),
                format!("(= (- x y) {})", smt_integer(x - y)),
                format!("(= (f x) {})", smt_integer(2 * x + 1)),
                format!("(= (f y) {})", smt_integer(2 * y + 1)),
            ],
        });
    }
    for query in 0_i32..4 {
        let x = query - 1;
        let y = 4 - query;
        cases.push(CombinationModelCase {
            name: format!("QF_UFLIA model {query}"),
            logic: "QF_UFLIA",
            declarations: vec![
                "(declare-const x Int)".to_owned(),
                "(declare-const y Int)".to_owned(),
                "(declare-fun f (Int) Int)".to_owned(),
            ],
            assertions: vec![
                format!("(= (+ (* 2 x) (* 3 y)) {})", smt_integer(2 * x + 3 * y)),
                format!("(= x {})", smt_integer(x)),
                format!("(= (f x) {})", smt_integer(x - y)),
                format!("(= (f y) {})", smt_integer(y - x)),
            ],
        });
    }
    for query in 0_i32..4 {
        let x = query - 2;
        let y = query + 1;
        cases.push(CombinationModelCase {
            name: format!("QF_UFLRA model {query}"),
            logic: "QF_UFLRA",
            declarations: vec![
                "(declare-const x Real)".to_owned(),
                "(declare-const y Real)".to_owned(),
                "(declare-fun f (Real) Real)".to_owned(),
            ],
            assertions: vec![
                format!("(= (+ (* 2 x) (* 3 y)) {})", smt_integer(2 * x + 3 * y)),
                format!("(= x {})", smt_integer(x)),
                format!("(= (f x) (/ {} 2))", smt_integer(2 * x + 1)),
                format!("(= (f y) (/ {} 2))", smt_integer(2 * y + 1)),
            ],
        });
    }
    for query in 0_i32..4 {
        let x = query - 1;
        let value = 2 * query + 3;
        cases.push(CombinationModelCase {
            name: format!("QF_AUFLIA model {query}"),
            logic: "QF_AUFLIA",
            declarations: vec![
                "(declare-const a (Array Int Int))".to_owned(),
                "(declare-const x Int)".to_owned(),
                "(declare-const v Int)".to_owned(),
                "(declare-fun observe ((Array Int Int)) Int)".to_owned(),
            ],
            assertions: vec![
                format!("(= x {})", smt_integer(x)),
                format!("(= v {})", smt_integer(value)),
                "(= (select a x) v)".to_owned(),
                "(= (select (store a x (+ v 1)) x) (+ v 1))".to_owned(),
                format!("(= (observe a) {})", smt_integer(value - x)),
            ],
        });
    }
    cases
}

fn smt_sixths(numerator: i32) -> String {
    match numerator {
        0 => "0.0".to_owned(),
        value if value < 0 => format!("(- (/ {}.0 6.0))", value.unsigned_abs()),
        value => format!("(/ {value}.0 6.0)"),
    }
}

fn smt_integer(value: i32) -> String {
    if value < 0 {
        format!("(- {})", value.unsigned_abs())
    } else {
        value.to_string()
    }
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
