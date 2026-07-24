#![no_main]

use std::io::{self, Write};
use std::sync::{Arc, Mutex};

use libfuzzer_sys::fuzz_target;
use sat::{Lit, SolveResult, Solver, Var};

#[derive(Clone, Default)]
struct SharedBuffer(Arc<Mutex<Vec<u8>>>);

impl Write for SharedBuffer {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        self.0.lock().expect("proof buffer lock").extend(bytes);
        Ok(bytes.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

fuzz_target!(|data: &[u8]| {
    if data.is_empty() || data.len() > 4096 {
        return;
    }

    let variable_count = usize::from(data[0] % 8) + 1;
    let mut solver = Solver::new();
    let variables = (0..variable_count)
        .map(|_| solver.new_variable().expect("bounded variable allocation"))
        .collect::<Vec<_>>();
    let proof = SharedBuffer::default();
    solver.enable_drat_proof(proof.clone());

    let mut clauses = Vec::new();
    let mut cursor = 1;
    while cursor < data.len() && clauses.len() < 64 {
        let length = usize::from(data[cursor] % 5);
        cursor += 1;
        let mut clause = Vec::with_capacity(length);
        for _ in 0..length {
            if cursor >= data.len() {
                break;
            }
            let byte = data[cursor];
            cursor += 1;
            let variable = variables[usize::from(byte >> 1) % variable_count];
            clause.push(if byte & 1 == 0 {
                Lit::positive(variable)
            } else {
                Lit::negative(variable)
            });
        }
        solver
            .try_add_clause(&clause)
            .expect("bounded clause insertion");
        clauses.push(clause);
    }

    if data[0] & 0x80 != 0 {
        add_nontrivial_unsat_core(&mut solver, &mut clauses, &variables);
    }

    let expected_sat = brute_force_sat(variable_count, &clauses);
    let result = solver.solve();
    assert!(solver.proof_error().is_none());
    let proof = proof.0.lock().expect("proof buffer lock").clone();
    validate_proof_syntax(&proof, variable_count);

    match result {
        SolveResult::Sat(model) => {
            assert!(expected_sat);
            for clause in &clauses {
                assert!(clause.iter().any(|&literal| model.literal_value(literal)));
            }
        }
        SolveResult::Unsat => {
            assert!(!expected_sat);
            let last_line = proof
                .split(|&byte| byte == b'\n')
                .rfind(|line| !line.is_empty());
            assert_eq!(last_line, Some(b"0".as_slice()));
        }
        SolveResult::Unknown(reason) => panic!("unlimited bounded solve returned {reason:?}"),
    }
});

fn add_nontrivial_unsat_core(solver: &mut Solver, clauses: &mut Vec<Vec<Lit>>, variables: &[Var]) {
    let x = Lit::positive(variables[0]);
    let y = Lit::positive(variables.get(1).copied().unwrap_or(variables[0]));
    for clause in [[x, y], [x, !y], [!x, y], [!x, !y]] {
        let clause = clause.to_vec();
        solver
            .try_add_clause(&clause)
            .expect("bounded clause insertion");
        clauses.push(clause);
    }
}

fn brute_force_sat(variable_count: usize, clauses: &[Vec<Lit>]) -> bool {
    (0_u16..(1_u16 << variable_count)).any(|assignment| {
        clauses.iter().all(|clause| {
            clause.iter().any(|literal| {
                let value = assignment & (1 << literal.var().index()) != 0;
                value == literal.is_positive()
            })
        })
    })
}

fn validate_proof_syntax(proof: &[u8], variable_count: usize) {
    let proof = std::str::from_utf8(proof).expect("DRAT proof must be UTF-8");
    for line in proof.lines() {
        let mut tokens = line.split_ascii_whitespace();
        let first = tokens.next().expect("proof line must not be empty");
        let mut saw_zero = false;
        for token in std::iter::once(first)
            .filter(|token| *token != "d")
            .chain(tokens)
        {
            assert!(!saw_zero, "DRAT terminator must be the final token");
            let literal = token.parse::<i64>().expect("DRAT token must be an integer");
            if literal == 0 {
                saw_zero = true;
            } else {
                assert!(literal.unsigned_abs() <= variable_count as u64);
            }
        }
        assert!(saw_zero, "DRAT line must end in zero");
    }
}
