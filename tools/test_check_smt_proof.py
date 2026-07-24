import unittest

from check_smt_proof import (
    CnfEncoder,
    ProofCheckError,
    ProofSession,
    SExprReader,
    UfLowering,
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


def cnf_satisfiable(encoder: CnfEncoder, clauses) -> bool:
    for assignment in range(1 << encoder.variable_count):
        if all(
            any(
                bool(assignment & (1 << (abs(literal) - 1))) == (literal > 0)
                for literal in literals
            )
            for _, literals in clauses
        ):
            return True
    return False


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


if __name__ == "__main__":
    unittest.main()
