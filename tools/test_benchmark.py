from __future__ import annotations

import contextlib
import io
import sys
import tempfile
import unittest
from pathlib import Path

import benchmark


class StreamingModelValidationTests(unittest.TestCase):
    def formula(self, contents: str) -> tuple[tempfile.TemporaryDirectory[str], benchmark.Formula]:
        directory = tempfile.TemporaryDirectory()
        path = Path(directory.name) / "case.cnf"
        path.write_text(contents, encoding="utf-8")
        return directory, benchmark.parse_formula(path)

    def test_accepts_valid_model_and_multiline_clause(self) -> None:
        directory, formula = self.formula("c example\np cnf 3 2\n1 -2\n3 0\n2 0\n")
        with directory:
            self.assertEqual(
                benchmark.validate_model(formula, "s SATISFIABLE\nv 1 2 -3 0\n"), "valid"
            )

    def test_rejects_unsatisfied_clause(self) -> None:
        directory, formula = self.formula("p cnf 2 2\n1 0\n-1 2 0\n")
        with directory:
            self.assertEqual(
                benchmark.validate_model(formula, "v -1 2 0\n"),
                "invalid: clause 1 is not satisfied",
            )

    def test_rejects_contradictory_model(self) -> None:
        directory, formula = self.formula("p cnf 1 1\n1 0\n")
        with directory:
            self.assertEqual(
                benchmark.validate_model(formula, "v 1 -1 0\n"),
                "invalid: contradictory values for variable 1",
            )

    def test_formula_descriptor_does_not_materialize_clauses(self) -> None:
        directory, formula = self.formula("p cnf 10000000 1\n10000000 0\n")
        with directory:
            self.assertEqual(formula.variable_count, 10_000_000)
            self.assertEqual(formula.clause_count, 1)
            self.assertFalse(hasattr(formula, "clauses"))


class ReportedStatusTests(unittest.TestCase):
    def test_rejects_unexpected_nonzero_exit(self) -> None:
        self.assertEqual(
            benchmark.reported_status("", 1),
            ("INVALID", "unexpected exit code 1"),
        )

    def test_accepts_conventional_exit_status_without_text(self) -> None:
        self.assertEqual(benchmark.reported_status("", 10), ("SAT", None))


class ProofConfigurationTests(unittest.TestCase):
    def test_rejects_checker_for_unknown_solver(self) -> None:
        solver = benchmark.SolverSpec("known", ("solver",), None)
        with self.assertRaisesRegex(ValueError, "unknown solver"):
            benchmark.attach_proof_checkers(
                [solver],
                ["other=checker {instance} {proof}"],
            )

    def test_rejects_checker_without_required_placeholders(self) -> None:
        solver = benchmark.SolverSpec(
            "solver",
            ("solver", "--proof", "{proof}"),
            None,
        )
        with self.assertRaisesRegex(ValueError, r"must contain \{instance\}"):
            benchmark.attach_proof_checkers(
                [solver],
                ["solver=checker {proof}"],
            )
        with self.assertRaisesRegex(ValueError, r"must contain \{proof\}"):
            benchmark.attach_proof_checkers(
                [solver],
                ["solver=checker {instance}"],
            )

    def test_rejects_proof_path_without_checker(self) -> None:
        solver = benchmark.SolverSpec(
            "solver",
            ("solver", "--proof", "{proof}"),
            None,
        )
        with self.assertRaisesRegex(ValueError, "but no proof checker"):
            benchmark.attach_proof_checkers([solver], [])

    def test_rejects_checker_when_solver_cannot_write_proof(self) -> None:
        solver = benchmark.SolverSpec("solver", ("solver",), None)
        with self.assertRaisesRegex(ValueError, r"needs a \{proof\} placeholder"):
            benchmark.attach_proof_checkers(
                [solver],
                ["solver=checker {instance} {proof}"],
            )


class ProofValidationTests(unittest.TestCase):
    def formula(self, directory: Path) -> benchmark.Formula:
        path = directory / "unsat.cnf"
        path.write_text("p cnf 1 2\n1 0\n-1 0\n", encoding="utf-8")
        return benchmark.parse_formula(path)

    def solver(
        self,
        checker_program: str,
        *,
        write_proof: bool = True,
    ) -> benchmark.SolverSpec:
        if write_proof:
            solver_program = (
                "from pathlib import Path; import sys; "
                "Path(sys.argv[1]).write_text('0\\n', encoding='utf-8'); "
                "print('s UNSATISFIABLE'); raise SystemExit(20)"
            )
        else:
            solver_program = "print('s UNSATISFIABLE'); raise SystemExit(20)"
        solver_command = (
            sys.executable,
            "-c",
            solver_program,
            "{proof}",
            "{instance}",
        )
        checker_command = (
            sys.executable,
            "-c",
            checker_program,
            "{instance}",
            "{proof}",
        )
        return benchmark.SolverSpec(
            "fake",
            solver_command,
            benchmark.executable_hash(solver_command),
            benchmark.ProofCheckerSpec(
                checker_command,
                benchmark.executable_hash(checker_command),
            ),
        )

    def run_benchmark(
        self,
        directory: Path,
        spec: benchmark.SolverSpec,
    ) -> dict[str, object]:
        formula = self.formula(directory)
        return benchmark.run_solver(
            spec,
            formula.path,
            timeout=2.0,
            run_index=0,
            seed=1,
            host={},
            revision=None,
            formula=formula,
            artifact_root=directory / "artifacts",
            retain_artifacts=True,
            proof_timeout=2.0,
        )

    def test_accepts_and_retains_independently_verified_proof(self) -> None:
        checker_program = (
            "from pathlib import Path; import sys; "
            "assert Path(sys.argv[1]).is_file(); "
            "assert Path(sys.argv[2]).read_text(encoding='utf-8') == '0\\n'; "
            "print('s VERIFIED')"
        )
        with tempfile.TemporaryDirectory() as temporary:
            row = self.run_benchmark(
                Path(temporary),
                self.solver(checker_program),
            )

            self.assertEqual(row["status"], "UNSAT")
            self.assertEqual(row["validation"], "valid")
            proof = row["proof"]
            self.assertIsInstance(proof, dict)
            assert isinstance(proof, dict)
            self.assertEqual(proof["checker_status"], "verified")
            self.assertEqual(proof["bytes"], 2)
            self.assertEqual(
                proof["sha256"],
                benchmark.sha256_bytes(b"0\n"),
            )
            self.assertTrue(Path(str(proof["path"])).is_file())

    def test_rejects_failed_checker(self) -> None:
        checker_program = "import sys; print('s NOT VERIFIED'); raise SystemExit(1)"
        with tempfile.TemporaryDirectory() as temporary:
            row = self.run_benchmark(
                Path(temporary),
                self.solver(checker_program),
            )

        self.assertEqual(row["status"], "UNSAT")
        self.assertEqual(
            row["validation"],
            "invalid: proof checker exited with status 1",
        )
        proof = row["proof"]
        assert isinstance(proof, dict)
        self.assertEqual(proof["checker_status"], "rejected")

    def test_requires_exact_verified_verdict(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            row = self.run_benchmark(
                Path(temporary),
                self.solver("print('verification completed')"),
            )

        self.assertEqual(
            row["validation"],
            "invalid: proof checker did not report s VERIFIED",
        )
        proof = row["proof"]
        assert isinstance(proof, dict)
        self.assertEqual(proof["checker_status"], "missing-verdict")

    def test_rejects_checker_that_mutates_proof(self) -> None:
        checker_program = (
            "from pathlib import Path; import sys; "
            "Path(sys.argv[2]).write_text('changed\\n', encoding='utf-8'); "
            "print('s VERIFIED')"
        )
        with tempfile.TemporaryDirectory() as temporary:
            row = self.run_benchmark(
                Path(temporary),
                self.solver(checker_program),
            )

        self.assertEqual(
            row["validation"],
            "invalid: proof checker changed proof artifact",
        )
        proof = row["proof"]
        assert isinstance(proof, dict)
        self.assertEqual(proof["checker_status"], "artifact-changed")

    def test_rejects_missing_proof(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            row = self.run_benchmark(
                Path(temporary),
                self.solver("print('s VERIFIED')", write_proof=False),
            )

        self.assertEqual(row["status"], "UNSAT")
        self.assertEqual(row["validation"], "invalid: missing proof artifact")
        proof = row["proof"]
        assert isinstance(proof, dict)
        self.assertEqual(proof["checker_status"], "missing-proof")

    def test_strict_summary_rejects_unchecked_unsat(self) -> None:
        row = {
            "solver": "fake",
            "instance": "case.cnf",
            "status": "UNSAT",
            "validation": "unchecked",
        }
        with contextlib.redirect_stderr(io.StringIO()):
            self.assertTrue(benchmark.summarize([row]))
            self.assertFalse(benchmark.summarize([row], require_unsat_proofs=True))


if __name__ == "__main__":
    unittest.main()
