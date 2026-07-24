#![no_main]

use std::fmt::Write as _;
use std::io::{BufReader, Cursor};

use libfuzzer_sys::fuzz_target;
use sat::smt;

struct Fragment {
    logic: &'static str,
    declarations: &'static str,
    assertions: &'static [&'static str],
    values: &'static str,
}

const FRAGMENTS: &[Fragment] = &[
    Fragment {
        logic: "QF_BV",
        declarations: "\
(declare-const q Bool)
(declare-const x (_ BitVec 4))
(declare-const y (_ BitVec 4))
",
        assertions: &[
            "(= (bvadd x y) #b0110)",
            "(bvult x y)",
            "(bvsle (bvneg x) y)",
            "(= (bvmul x y) #b1100)",
            "(bvuaddo x y)",
            "(= ((_ rotate_left 1) x) y)",
            "(distinct ((_ extract 2 1) x) #b00)",
            "(= (ite q x y) x)",
        ],
        values: "(x y (bvadd x y) (bvult x y))",
    },
    Fragment {
        logic: "QF_UF",
        declarations: "\
(declare-sort U 0)
(declare-const q Bool)
(declare-const a U)
(declare-const b U)
(declare-fun f (U) U)
(declare-fun p (U) Bool)
",
        assertions: &[
            "(= a b)",
            "(distinct a b)",
            "(= (f a) (f b))",
            "(distinct (f a) (f b))",
            "(= (p a) (p b))",
            "(xor (p a) (p b))",
            "(= (ite q a b) a)",
            "(distinct (f (f a)) (f b))",
        ],
        values: "(a b (f a) (p a))",
    },
    Fragment {
        logic: "QF_AUFBV",
        declarations: "\
(declare-const q Bool)
(declare-const a (Array (_ BitVec 2) (_ BitVec 3)))
(declare-const i (_ BitVec 2))
(declare-const j (_ BitVec 2))
(declare-const x (_ BitVec 3))
(declare-fun f ((_ BitVec 3)) (_ BitVec 3))
",
        assertions: &[
            "(= (select (store a i x) i) x)",
            "(distinct (select (store a i x) i) x)",
            "(or (= i j) (= (select (store a i x) j) (select a j)))",
            "(= (f (select a i)) (f x))",
            "(distinct (f (select a i)) (f x))",
            "(= (select a i) x)",
            "(= (f x) (bvadd x #b001))",
            "(= (select (ite q a (store a i x)) i) x)",
        ],
        values: "(i j x (select a i) (f x))",
    },
    Fragment {
        logic: "QF_LIA",
        declarations: "\
(declare-const q Bool)
(declare-const x Int)
(declare-const y Int)
",
        assertions: &[
            "(<= (+ (* 2 x) (* 3 y)) 7)",
            "(> (- x y) 4)",
            "(= (+ x y) 3)",
            "(distinct (+ (* 2 x) y) 1)",
            "(<= (- 8) x)",
            "(<= x 8)",
            "(= (ite q x y) x)",
            "(or (= x y) (< x y))",
        ],
        values: "(x y (+ x y) (<= x y))",
    },
    Fragment {
        logic: "QF_LRA",
        declarations: "\
(declare-const q Bool)
(declare-const x Real)
(declare-const y Real)
",
        assertions: &[
            "(<= (+ (* 2.0 x) (* 3.0 y)) (/ 7.0 2.0))",
            "(> (- x y) (/ 1.0 3.0))",
            "(= (+ x y) 3.0)",
            "(distinct (+ (* 2.0 x) y) (/ 1.0 2.0))",
            "(<= (- 8.0) x)",
            "(<= x 8.0)",
            "(= (ite q x y) x)",
            "(or (= x y) (< x y))",
        ],
        values: "(x y (+ x y) (<= x y))",
    },
    Fragment {
        logic: "QF_UFLIA",
        declarations: "\
(declare-const q Bool)
(declare-const x Int)
(declare-const y Int)
(declare-fun f (Int) Int)
",
        assertions: &[
            "(= x y)",
            "(distinct (f x) (f y))",
            "(<= (+ (f x) (* 2 y)) 9)",
            "(= (f (+ x 1)) (+ (f x) 1))",
            "(distinct x y)",
            "(= (ite q (f x) y) x)",
            "(<= (- x y) 3)",
            "(or (= (f x) y) (> x y))",
        ],
        values: "(x y (f x) (+ (f x) y))",
    },
    Fragment {
        logic: "QF_AUFLIA",
        declarations: "\
(declare-const q Bool)
(declare-const a (Array Int Int))
(declare-const x Int)
(declare-const y Int)
(declare-fun f (Int) Int)
",
        assertions: &[
            "(= (select (store a x y) x) y)",
            "(distinct (select (store a x y) x) y)",
            "(or (= x y) (= (select (store a x y) y) (select a y)))",
            "(= (f (select a x)) (f y))",
            "(<= (+ (select a x) (f y)) 7)",
            "(= (select a x) y)",
            "(= (f x) (+ y 1))",
            "(= (select (ite q a (store a x y)) x) y)",
        ],
        values: "(x y (select a x) (f x))",
    },
    Fragment {
        logic: "QF_UFIDL",
        declarations: "\
(declare-const q Bool)
(declare-const x Int)
(declare-const y Int)
(declare-fun f (Int) Int)
",
        assertions: &[
            "(<= (- x y) 3)",
            "(<= (- y x) (- 4))",
            "(= x y)",
            "(distinct (f x) (f y))",
            "(<= (- (f x) y) 2)",
            "(= (f x) y)",
            "(= (ite q x y) x)",
            "(or (= x y) (< x y))",
        ],
        values: "(x y (f x) (- x y))",
    },
];

fuzz_target!(|data: &[u8]| {
    let script = structured_script(data);
    let mut output = Vec::new();
    let _ = smt::run(BufReader::new(Cursor::new(script.as_bytes())), &mut output);
});

fn structured_script(data: &[u8]) -> String {
    let fragment = &FRAGMENTS[data.first().copied().unwrap_or(0) as usize % FRAGMENTS.len()];
    let mut script = String::from(
        "(set-option :produce-models true)\n\
         (set-option :produce-unsat-cores true)\n\
         (set-option :produce-unsat-assumptions true)\n",
    );
    writeln!(script, "(set-logic {})", fragment.logic).unwrap();
    script.push_str(fragment.declarations);

    let mut depth = 0_usize;
    let mut label = 0_usize;
    for &byte in data.iter().skip(1).take(96) {
        let assertion = fragment.assertions[(byte as usize >> 4) % fragment.assertions.len()];
        match byte % 10 {
            0 if depth < 4 => {
                script.push_str("(push 1)\n");
                depth += 1;
            }
            1 if depth > 0 => {
                script.push_str("(pop 1)\n");
                depth -= 1;
            }
            2..=5 => {
                writeln!(script, "(assert {assertion})").unwrap();
            }
            6 => {
                script.push_str("(check-sat)\n(get-model)\n");
                writeln!(script, "(get-value {})", fragment.values).unwrap();
            }
            7 => {
                script.push_str(
                    "(check-sat-assuming (q (not q)))\n\
                     (get-unsat-assumptions)\n",
                );
            }
            8 => {
                writeln!(script, "(push 1)").unwrap();
                writeln!(script, "(assert (! q :named fuzz_{label}))").unwrap();
                label += 1;
                writeln!(script, "(assert (! (not q) :named fuzz_{label}))").unwrap();
                label += 1;
                script.push_str("(check-sat)\n(get-unsat-core)\n(pop 1)\n");
            }
            9 => {
                script.push_str("(reset-assertions)\n");
                depth = 0;
            }
            _ => {
                writeln!(script, "(assert {assertion})").unwrap();
            }
        }
    }
    script.push_str("(check-sat)\n(get-model)\n");
    writeln!(script, "(get-value {})", fragment.values).unwrap();
    script.push_str("(get-proof)\n(exit)\n");
    script
}
