use std::fmt::Write as _;
use std::io::Write;
use std::process::{Command, Output, Stdio};

#[test]
fn deterministic_qf_bv_corpus_agrees_with_z3() {
    if Command::new("z3").arg("--version").output().is_err() {
        eprintln!("skipping QF_BV differential test because z3 is not installed");
        return;
    }

    let script = differential_script();
    let ours = run_solver(env!("CARGO_BIN_EXE_smt"), &[], &script);
    let z3 = run_solver("z3", &["-in", "-smt2"], &script);

    assert!(
        ours.status.success(),
        "our solver failed:\n{}",
        String::from_utf8_lossy(&ours.stderr)
    );
    assert!(
        z3.status.success(),
        "z3 failed:\n{}",
        String::from_utf8_lossy(&z3.stderr)
    );

    let ours_stdout = String::from_utf8(ours.stdout).expect("our output must be UTF-8");
    let z3_stdout = String::from_utf8(z3.stdout).expect("z3 output must be UTF-8");
    let ours_results = check_results(&ours_stdout);
    let z3_results = check_results(&z3_stdout);

    assert_eq!(
        ours_results.len(),
        544,
        "our solver did not answer every generated query:\n{ours_stdout}"
    );
    assert_eq!(
        z3_results.len(),
        544,
        "z3 did not answer every generated query:\n{z3_stdout}"
    );
    assert_eq!(ours_results, z3_results, "QF_BV differential mismatch");
}

#[test]
fn deterministic_qf_uf_and_ufbv_corpora_agree_with_z3() {
    if Command::new("z3").arg("--version").output().is_err() {
        eprintln!("skipping QF_UF differential test because z3 is not installed");
        return;
    }

    for (name, script, expected) in [
        ("QF_UF", uf_differential_script(), 384),
        ("QF_UFBV", ufbv_differential_script(), 256),
    ] {
        let ours = run_solver(env!("CARGO_BIN_EXE_smt"), &[], &script);
        let z3 = run_solver("z3", &["-in", "-smt2"], &script);
        assert!(
            ours.status.success(),
            "our solver failed on {name}:\n{}",
            String::from_utf8_lossy(&ours.stderr)
        );
        assert!(
            z3.status.success(),
            "z3 failed on {name}:\n{}",
            String::from_utf8_lossy(&z3.stderr)
        );
        let ours_stdout = String::from_utf8(ours.stdout).expect("our output must be UTF-8");
        let z3_stdout = String::from_utf8(z3.stdout).expect("z3 output must be UTF-8");
        let ours_results = check_results(&ours_stdout);
        let z3_results = check_results(&z3_stdout);
        assert_eq!(
            ours_results.len(),
            expected,
            "our solver did not answer every {name} query:\n{ours_stdout}"
        );
        assert_eq!(
            z3_results.len(),
            expected,
            "z3 did not answer every {name} query:\n{z3_stdout}"
        );
        let mismatch = ours_results
            .iter()
            .zip(&z3_results)
            .position(|(ours, z3)| ours != z3);
        assert_eq!(
            mismatch,
            None,
            "{name} differential mismatch at query {mismatch:?}: ours={:?}, z3={:?}",
            mismatch.map(|index| ours_results[index]),
            mismatch.map(|index| z3_results[index])
        );
    }
}

#[test]
fn deterministic_extensional_array_corpora_agree_with_z3() {
    if Command::new("z3").arg("--version").output().is_err() {
        eprintln!("skipping array differential test because z3 is not installed");
        return;
    }
    for (name, script, expected) in [
        ("QF_ABV", abv_differential_script(), 256),
        ("QF_AUFBV", aufbv_differential_script(), 128),
    ] {
        let ours = run_solver(env!("CARGO_BIN_EXE_smt"), &[], &script);
        let z3 = run_solver("z3", &["-in", "-smt2"], &script);
        assert!(
            ours.status.success(),
            "our solver failed on {name}:\n{}",
            String::from_utf8_lossy(&ours.stderr)
        );
        assert!(
            z3.status.success(),
            "z3 failed on {name}:\n{}",
            String::from_utf8_lossy(&z3.stderr)
        );
        let ours_stdout = String::from_utf8(ours.stdout).expect("our output must be UTF-8");
        let z3_stdout = String::from_utf8(z3.stdout).expect("z3 output must be UTF-8");
        let ours_results = check_results(&ours_stdout);
        let z3_results = check_results(&z3_stdout);
        assert_eq!(
            ours_results.len(),
            expected,
            "our solver did not answer every {name} query:\n{ours_stdout}"
        );
        assert_eq!(
            z3_results.len(),
            expected,
            "z3 did not answer every {name} query:\n{z3_stdout}"
        );
        assert_eq!(ours_results, z3_results, "{name} differential mismatch");
    }
}

#[test]
fn deterministic_exact_arithmetic_corpora_agree_with_z3() {
    if Command::new("z3").arg("--version").output().is_err() {
        eprintln!("skipping arithmetic differential test because z3 is not installed");
        return;
    }
    for (name, script, expected) in [
        ("QF_IDL", idl_differential_script(), 384),
        ("QF_LIA", lia_differential_script(), 384),
        ("QF_RDL", rdl_differential_script(), 256),
        ("QF_LRA", lra_differential_script(), 384),
    ] {
        let ours = run_solver(env!("CARGO_BIN_EXE_smt"), &[], &script);
        let z3 = run_solver("z3", &["-in", "-smt2"], &script);
        assert!(
            ours.status.success(),
            "our solver failed on {name}:\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&ours.stdout),
            String::from_utf8_lossy(&ours.stderr)
        );
        assert!(
            z3.status.success(),
            "z3 failed on {name}:\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&z3.stdout),
            String::from_utf8_lossy(&z3.stderr)
        );
        let ours_stdout = String::from_utf8(ours.stdout).expect("our output must be UTF-8");
        let z3_stdout = String::from_utf8(z3.stdout).expect("z3 output must be UTF-8");
        let ours_results = check_results(&ours_stdout);
        let z3_results = check_results(&z3_stdout);
        assert_eq!(
            ours_results.len(),
            expected,
            "our solver did not answer every {name} query:\n{ours_stdout}"
        );
        assert_eq!(
            z3_results.len(),
            expected,
            "z3 did not answer every {name} query:\n{z3_stdout}"
        );
        let mismatch = ours_results
            .iter()
            .zip(&z3_results)
            .position(|(ours, z3)| ours != z3);
        assert_eq!(
            mismatch,
            None,
            "{name} differential mismatch at query {mismatch:?}: ours={:?}, z3={:?}",
            mismatch.map(|index| ours_results[index]),
            mismatch.map(|index| z3_results[index])
        );
    }
}

#[test]
fn exact_arithmetic_models_are_independently_validated_by_z3() {
    if Command::new("z3").arg("--version").output().is_err() {
        eprintln!("skipping arithmetic model validation because z3 is not installed");
        return;
    }

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

        let validation_script = case.z3_validation_script(&ours_stdout);
        let z3 = run_solver("z3", &["-in", "-smt2"], &validation_script);
        assert!(
            z3.status.success(),
            "z3 rejected the validation script for {}:\nscript:\n{}\nstdout:\n{}\nstderr:\n{}",
            case.name,
            validation_script,
            String::from_utf8_lossy(&z3.stdout),
            String::from_utf8_lossy(&z3.stderr)
        );
        let z3_stdout = String::from_utf8(z3.stdout).expect("z3 output must be UTF-8");
        assert_eq!(
            check_results(&z3_stdout),
            ["sat"],
            "our model does not satisfy {} according to z3:\n\
             solver output:\n{ours_stdout}\nvalidation output:\n{z3_stdout}",
            case.name
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

impl ArithmeticModelCase {
    fn solver_script(&self) -> String {
        let mut script = String::from("(set-option :produce-models true)\n");
        self.write_problem(&mut script);
        script.push_str("(check-sat)\n(get-model)\n(exit)\n");
        script
    }

    fn z3_validation_script(&self, solver_output: &str) -> String {
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
