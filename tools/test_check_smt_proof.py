import unittest
from itertools import product

from check_smt_proof import (
    INT_SORT,
    ArithmeticProblem,
    CnfEncoder,
    LinearConstraint,
    ProofCheckError,
    ProofSession,
    SExprReader,
    UfLowering,
    integer_linear_constraints_unsat,
    linear_expression,
    validate_encoding,
)

SCRIPT = """
(set-option :produce-proofs true)
(set-logic QF_BOOL)
(declare-const p Bool)
(assert p)
(assert (not p))
(check-sat)
(get-proof)
"""

PROOF = """unsat
(satrap-edrat :version 1 :logic QF_BOOL :variables 1
 :premises ("p" "(not p)")
 :clauses ((formula 1) (formula -1))
 :drat "0
")
"""

IDL_SCRIPT = """
(set-option :produce-proofs true)
(set-logic QF_IDL)
(declare-const x Int)
(declare-const y Int)
(assert (<= (- x y) 1))
(assert (<= (- y x) (- 2)))
(check-sat)
(get-proof)
"""

IDL_PROOF = """unsat
(satrap-edrat :version 1 :logic QF_IDL :variables 2
 :premises ("(<= (- x y) 1)" "(<= (- y x) (- 2))")
 :clauses ((formula 1) (formula 2) (theory -1 -2))
 :drat "0
")
"""

LIA_SCRIPT = """
(set-option :produce-proofs true)
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (= (+ (* 2 x) (* 4 y)) 1))
(check-sat)
(get-proof)
"""

LIA_PROOF = """unsat
(satrap-edrat :version 1 :logic QF_LIA :variables 3
 :premises ("(= (+ (* 2 x) (* 4 y)) 1)")
 :clauses ((encoding 1 -3) (encoding 2 -3) (encoding -1 -2 3)
           (formula 3) (theory -1 -2))
 :drat "0
")
"""

RDL_SCRIPT = """
(set-option :produce-proofs true)
(set-logic QF_RDL)
(declare-const x Real)
(declare-const y Real)
(assert (< x y))
(assert (<= y x))
(check-sat)
(get-proof)
"""

RDL_PROOF = """unsat
(satrap-edrat :version 1 :logic QF_RDL :variables 2
 :premises ("(< x y)" "(<= y x)")
 :clauses ((formula 1) (formula 2) (theory -1 -2))
 :drat "0
")
"""

LRA_SCRIPT = """
(set-option :produce-proofs true)
(set-logic QF_LRA)
(declare-const x Real)
(declare-const y Real)
(assert (> (+ (* 2.0 x) y) 4.0))
(assert (<= x 1.0))
(assert (<= y 2.0))
(check-sat)
(get-proof)
"""

LRA_PROOF = """unsat
(satrap-edrat :version 1 :logic QF_LRA :variables 3
 :premises ("(> (+ (* 2.0 x) y) 4.0)" "(<= x 1.0)" "(<= y 2.0)")
 :clauses ((formula 1) (formula 2) (formula 3) (theory -1 -2 -3))
 :drat "0
")
"""


def cnf_satisfiable(encoder: CnfEncoder, clauses) -> bool:
    pending = tuple(frozenset(literals) for _, literals in clauses)
    self_check = {abs(literal) for clause in pending for literal in clause if literal != 0}
    if self_check and max(self_check) > encoder.variable_count:
        raise AssertionError("test CNF contains an out-of-range variable")

    def simplify(current, literal):
        return tuple(clause - {-literal} for clause in current if literal not in clause)

    def search(current):
        while current:
            if any(not clause for clause in current):
                return False
            unit = next((next(iter(clause)) for clause in current if len(clause) == 1), None)
            if unit is not None:
                current = simplify(current, unit)
                continue
            literals = set().union(*current)
            pure = next(
                (
                    literal
                    for literal in sorted(literals, key=lambda item: (abs(item), item < 0))
                    if -literal not in literals
                ),
                None,
            )
            if pure is not None:
                current = simplify(current, pure)
                continue
            branch = next(iter(min(current, key=len)))
            return search(simplify(current, branch)) or search(simplify(current, -branch))
        return True

    return search(pending)


def lower_script(script: str):
    queries = ProofSession().execute_all(SExprReader(script).read_all())
    if len(queries) != 1:
        raise AssertionError("test script must expose exactly one proof query")
    roots, axioms = UfLowering(queries[0].roots).lower_roots(queries[0].roots)
    encoder = CnfEncoder()
    return encoder, encoder.build(roots, axioms), axioms


def combined_integer_encoding_is_satisfiable(script: str) -> bool:
    queries = ProofSession().execute_all(SExprReader(script).read_all())
    if len(queries) != 1:
        raise AssertionError("test script must expose exactly one proof query")
    roots, axioms = UfLowering(queries[0].roots).lower_roots(queries[0].roots)
    problem = ArithmeticProblem(INT_SORT, (*roots, *axioms))
    encoder = CnfEncoder()
    encoder.build(roots, axioms)
    required_literals = {
        expression: encoder.encode(expression) for expression in sorted(problem.required)
    }
    required = tuple(sorted(problem.required))
    for values in product((False, True), repeat=len(required)):
        assignment = dict(zip(required, values, strict=True))
        if not integer_linear_constraints_unsat(problem.constraints(assignment)):
            continue
        encoder.add_clause(
            "theory",
            [
                -required_literals[expression]
                if assignment[expression]
                else required_literals[expression]
                for expression in required
            ],
        )
    return cnf_satisfiable(encoder, encoder.clauses)


class SmtProofCheckerTests(unittest.TestCase):
    def test_reconstructs_an_unsatisfiable_active_context(self):
        certificate = validate_encoding(SCRIPT, PROOF)
        self.assertEqual(certificate.variable_count, 1)
        self.assertEqual(certificate.drat, "0\n")

    def test_rejects_a_changed_original_premise(self):
        with self.assertRaisesRegex(
            ProofCheckError,
            "premises do not match",
        ):
            validate_encoding(SCRIPT.replace("(assert p)", "(assert (not p))"), PROOF)

    def test_rejects_a_changed_encoding_clause(self):
        with self.assertRaisesRegex(
            ProofCheckError,
            "clauses do not match",
        ):
            validate_encoding(SCRIPT, PROOF.replace("(formula -1)", "(formula 1)"))

    def test_rejects_duplicate_certificate_fields(self):
        with self.assertRaisesRegex(
            ProofCheckError,
            "duplicate satrap-edrat field",
        ):
            validate_encoding(
                SCRIPT,
                PROOF.replace(":version 1", ":version 1 :version 1"),
            )

    def test_rejects_a_certificate_without_a_get_proof_site(self):
        with self.assertRaisesRegex(
            ProofCheckError,
            "premises do not match",
        ):
            validate_encoding(SCRIPT.replace("(get-proof)", ""), PROOF)

    def test_rejects_get_proof_after_nonempty_assumptions(self):
        script = """
        (set-option :produce-proofs true)
        (set-logic QF_BOOL)
        (declare-const p Bool)
        (assert p)
        (check-sat-assuming ((not p)))
        (get-proof)
        """
        with self.assertRaisesRegex(
            ProofCheckError,
            "nonempty assumption set",
        ):
            validate_encoding(script, PROOF)

    def test_global_declarations_survive_a_popped_scope(self):
        script = """
        (set-option :produce-proofs true)
        (set-option :global-declarations true)
        (set-logic QF_BOOL)
        (push 1)
        (declare-const p Bool)
        (pop 1)
        (assert p)
        (assert (not p))
        (check-sat)
        (get-proof)
        """
        certificate = validate_encoding(script, PROOF)
        self.assertEqual(certificate.premises, ("p", "(not p)"))

    def test_scopes_definitions_lets_and_boolean_rewrites_are_canonical(self):
        script = """
        (set-option :produce-proofs true)
        (set-logic QF_BOOL)
        (declare-const a Bool)
        (declare-const b Bool)
        (define-const c Bool (=> a b))
        (push 1)
        (assert (let ((x c) (y (not b))) (and x y)))
        (pop 1)
        (assert (= (xor a b) (xor b a)))
        (assert (not (= true true)))
        (check-sat)
        (get-proof)
        """
        proof = """(satrap-edrat :version 1 :logic QF_BOOL :variables 1
        :premises ("(= (xor a b) (xor b a))" "(not (= true true))")
        :clauses ((encoding 1) (formula 1) (formula -1))
        :drat "0
        ")"""
        certificate = validate_encoding(script, proof)
        self.assertEqual(certificate.clauses[-1], ("formula", (-1,)))

    def test_inline_labels_follow_postorder_and_preserve_original_premises(self):
        script = """
        (set-option :produce-proofs true)
        (set-logic QF_BOOL)
        (declare-const p Bool)
        (declare-const q Bool)
        (assert (or (! p :named alias) q))
        (assert (not alias))
        (assert (not q))
        (check-sat)
        (get-proof)
        """
        queries = ProofSession().execute_all(SExprReader(script).read_all())
        self.assertEqual(len(queries), 1)
        self.assertEqual(
            queries[0].premises,
            (
                "(or (! p :named alias) q)",
                "(not alias)",
                "(not q)",
            ),
        )
        encoder = CnfEncoder()
        self.assertFalse(cnf_satisfiable(encoder, encoder.build(queries[0].roots, ())))

    def test_inline_label_forward_references_are_rejected(self):
        script = """
        (set-logic QF_BOOL)
        (declare-const p Bool)
        (assert (and alias (! p :named alias)))
        """
        with self.assertRaisesRegex(
            ProofCheckError,
            "inline label `alias` is used before its definition",
        ):
            ProofSession().execute_all(SExprReader(script).read_all())

    def test_inline_labels_must_be_closed_over_function_parameters(self):
        script = """
        (set-logic QF_BOOL)
        (define-fun f ((x Bool)) Bool (! x :named captured))
        """
        with self.assertRaisesRegex(ProofCheckError, "unknown term symbol `x`"):
            ProofSession().execute_all(SExprReader(script).read_all())

    def test_reconstructs_a_qf_bv_bit_blast(self):
        script = """
        (set-option :produce-proofs true)
        (set-logic QF_BV)
        (declare-const x (_ BitVec 1))
        (assert (= x #b0))
        (assert (= x #b1))
        (check-sat)
        (get-proof)
        """
        proof = """(satrap-edrat :version 1 :logic QF_BV :variables 1
        :premises ("(= x #b0)" "(= x #b1)")
        :clauses ((formula -1) (formula 1))
        :drat "0
        ")"""
        certificate = validate_encoding(script, proof)
        self.assertEqual(certificate.logic, "QF_BV")
        self.assertEqual(certificate.clauses, (("formula", (-1,)), ("formula", (1,))))

    def test_rejects_a_certificate_with_the_wrong_logic(self):
        qf_bv_script = SCRIPT.replace("QF_BOOL", "QF_BV")
        with self.assertRaisesRegex(
            ProofCheckError,
            "premises do not match",
        ):
            validate_encoding(qf_bv_script, PROOF)

    def test_boolean_certificates_cannot_smuggle_theory_clauses(self):
        with self.assertRaisesRegex(
            ProofCheckError,
            "QF_BOOL proof contains forbidden `theory` clause",
        ):
            validate_encoding(
                SCRIPT,
                PROOF.replace("(formula 1)", "(theory 1)", 1),
            )

    def test_ground_uf_lowering_makes_congruence_refutation_propositional(self):
        script = """
        (set-option :produce-proofs true)
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (declare-fun f (U) U)
        (assert (= a b))
        (assert (distinct (f a) (f b)))
        (check-sat)
        (get-proof)
        """
        queries = ProofSession().execute_all(SExprReader(script).read_all())
        self.assertEqual(len(queries), 1)
        roots, axioms = UfLowering(queries[0].roots).lower_roots(queries[0].roots)
        self.assertEqual(len(axioms), 1)
        encoder = CnfEncoder()
        clauses = encoder.build(roots, axioms)
        self.assertFalse(cnf_satisfiable(encoder, clauses))

    def test_ground_uf_lowering_does_not_identify_distinct_argument_tuples(self):
        script = """
        (set-option :produce-proofs true)
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (declare-fun f (U) U)
        (assert (distinct a b))
        (assert (distinct (f a) (f b)))
        (check-sat)
        (get-proof)
        """
        queries = ProofSession().execute_all(SExprReader(script).read_all())
        self.assertEqual(len(queries), 1)
        roots, axioms = UfLowering(queries[0].roots).lower_roots(queries[0].roots)
        encoder = CnfEncoder()
        clauses = encoder.build(roots, axioms)
        self.assertTrue(cnf_satisfiable(encoder, clauses))

    def test_ground_array_lowering_enforces_read_over_write(self):
        script = """
        (set-option :produce-proofs true)
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 1) (_ BitVec 1)))
        (assert (distinct (select (store a #b0 #b1) #b0) #b1))
        (check-sat)
        (get-proof)
        """
        encoder, clauses, axioms = lower_script(script)
        self.assertGreater(len(axioms), 0)
        self.assertFalse(cnf_satisfiable(encoder, clauses))

    def test_ground_array_lowering_enforces_extensionality(self):
        script = """
        (set-option :produce-proofs true)
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 1) (_ BitVec 1)))
        (declare-const b (Array (_ BitVec 1) (_ BitVec 1)))
        (assert (= (select a #b0) (select b #b0)))
        (assert (= (select a #b1) (select b #b1)))
        (assert (distinct a b))
        (check-sat)
        (get-proof)
        """
        encoder, clauses, axioms = lower_script(script)
        self.assertGreater(len(axioms), 0)
        self.assertFalse(cnf_satisfiable(encoder, clauses))

    def test_ground_array_lowering_preserves_distinct_array_models(self):
        script = """
        (set-option :produce-proofs true)
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 1) (_ BitVec 1)))
        (declare-const b (Array (_ BitVec 1) (_ BitVec 1)))
        (assert (distinct a b))
        (check-sat)
        (get-proof)
        """
        encoder, clauses, axioms = lower_script(script)
        self.assertGreater(len(axioms), 0)
        self.assertTrue(cnf_satisfiable(encoder, clauses))

    def test_mixed_lowering_combines_integer_arithmetic_with_congruence(self):
        script = """
        (set-option :produce-proofs true)
        (set-logic QF_UFLIA)
        (declare-const x Int)
        (declare-fun f (Int) Int)
        (assert (= x 0))
        (assert (= (f x) 0))
        (assert (= (f 0) 1))
        (check-sat)
        (get-proof)
        """
        self.assertFalse(combined_integer_encoding_is_satisfiable(script))

    def test_mixed_lowering_preserves_distinct_integer_argument_models(self):
        script = """
        (set-option :produce-proofs true)
        (set-logic QF_UFLIA)
        (declare-const x Int)
        (declare-fun f (Int) Int)
        (assert (= x 1))
        (assert (= (f x) 0))
        (assert (= (f 0) 1))
        (check-sat)
        (get-proof)
        """
        self.assertTrue(combined_integer_encoding_is_satisfiable(script))

    def test_mixed_lowering_supports_integer_array_witnesses(self):
        script = """
        (set-option :produce-proofs true)
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (assert (distinct (store a i (select a i)) a))
        (check-sat)
        (get-proof)
        """
        self.assertFalse(combined_integer_encoding_is_satisfiable(script))

    def test_integer_difference_theory_clause_is_independently_validated(self):
        certificate = validate_encoding(IDL_SCRIPT, IDL_PROOF)
        self.assertEqual(certificate.logic, "QF_IDL")
        self.assertEqual(certificate.clauses[-1], ("theory", (-1, -2)))

    def test_real_strict_cycle_is_independently_validated(self):
        certificate = validate_encoding(RDL_SCRIPT, RDL_PROOF)
        self.assertEqual(certificate.logic, "QF_RDL")

    def test_general_linear_integer_clause_is_independently_validated(self):
        certificate = validate_encoding(LIA_SCRIPT, LIA_PROOF)
        self.assertEqual(certificate.logic, "QF_LIA")
        self.assertEqual(certificate.clauses[-1], ("theory", (-1, -2)))

    def test_rejects_a_linear_integer_clause_that_blocks_a_satisfiable_assignment(self):
        with self.assertRaisesRegex(
            ProofCheckError,
            "blocks a satisfiable theory assignment",
        ):
            validate_encoding(
                LIA_SCRIPT,
                LIA_PROOF.replace("(theory -1 -2)", "(theory 1 -2)"),
            )

    def test_cooper_checker_matches_bounded_exhaustive_search(self):
        x = (0, INT_SORT, "x")
        y = (0, INT_SORT, "y")
        bounds = [
            LinearConstraint(INT_SORT, linear_expression(-2, {x: 1}), False),
            LinearConstraint(INT_SORT, linear_expression(-2, {x: -1}), False),
            LinearConstraint(INT_SORT, linear_expression(-2, {y: 1}), False),
            LinearConstraint(INT_SORT, linear_expression(-2, {y: -1}), False),
        ]
        for left in range(-3, 4):
            for right in range(-3, 4):
                if left == 0 and right == 0:
                    continue
                for target in range(-6, 7):
                    equation = linear_expression(-target, {x: left, y: right})
                    constraints = [
                        *bounds,
                        LinearConstraint(INT_SORT, equation, False),
                        LinearConstraint(
                            INT_SORT,
                            linear_expression(target, {x: -left, y: -right}),
                            False,
                        ),
                    ]
                    expected = not any(
                        left * x_value + right * y_value == target
                        for x_value in range(-2, 3)
                        for y_value in range(-2, 3)
                    )
                    self.assertEqual(
                        integer_linear_constraints_unsat(constraints),
                        expected,
                        f"{left}*x + {right}*y = {target}",
                    )

    def test_general_linear_real_clause_is_independently_validated(self):
        certificate = validate_encoding(LRA_SCRIPT, LRA_PROOF)
        self.assertEqual(certificate.logic, "QF_LRA")
        self.assertEqual(certificate.clauses[-1], ("theory", (-1, -2, -3)))

    def test_rejects_a_linear_real_clause_that_blocks_a_satisfiable_assignment(self):
        with self.assertRaisesRegex(
            ProofCheckError,
            "blocks a satisfiable theory assignment",
        ):
            validate_encoding(
                LRA_SCRIPT,
                LRA_PROOF.replace("(theory -1 -2 -3)", "(theory 1 -2 -3)"),
            )

    def test_rejects_a_difference_clause_that_blocks_a_satisfiable_assignment(self):
        with self.assertRaisesRegex(
            ProofCheckError,
            "blocks a satisfiable theory assignment",
        ):
            validate_encoding(
                IDL_SCRIPT,
                IDL_PROOF.replace("(theory -1 -2)", "(theory 1 -2)"),
            )

    def test_rejects_an_incomplete_difference_assignment_clause(self):
        with self.assertRaisesRegex(
            ProofCheckError,
            "does not block a complete required assignment",
        ):
            validate_encoding(
                IDL_SCRIPT,
                IDL_PROOF.replace("(theory -1 -2)", "(theory -1)"),
            )

    def test_nested_arrays_are_outside_the_proof_boundary(self):
        script = """
        (set-option :produce-proofs true)
        (set-logic QF_ABV)
        (declare-const nested
          (Array (_ BitVec 1) (Array (_ BitVec 1) (_ BitVec 1))))
        """
        with self.assertRaisesRegex(
            ProofCheckError,
            "nested arrays are outside the proof boundary",
        ):
            ProofSession().execute_all(SExprReader(script).read_all())


if __name__ == "__main__":
    unittest.main()
