from __future__ import annotations

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
            self.assertEqual(benchmark.validate_model(formula, "s SATISFIABLE\nv 1 2 -3 0\n"), "valid")

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


if __name__ == "__main__":
    unittest.main()
