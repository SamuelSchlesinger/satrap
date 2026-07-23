from __future__ import annotations

import io
import unittest

import generate_random_ksat


class RandomKsatTests(unittest.TestCase):
    def test_generation_is_reproducible_and_has_distinct_clause_variables(self) -> None:
        first = generate_random_ksat.clauses(20, 50, 3, 20260723)
        second = generate_random_ksat.clauses(20, 50, 3, 20260723)
        self.assertEqual(first, second)
        self.assertTrue(
            all(
                len(clause) == 3
                and len({abs(literal) for literal in clause}) == 3
                and all(1 <= abs(literal) <= 20 for literal in clause)
                for clause in first
            )
        )

    def test_seed_changes_formula(self) -> None:
        self.assertNotEqual(
            generate_random_ksat.clauses(20, 50, 3, 1),
            generate_random_ksat.clauses(20, 50, 3, 2),
        )

    def test_ratio_uses_nearest_integer(self) -> None:
        self.assertEqual(generate_random_ksat.clause_count_from_ratio(100, 4.267), 427)
        self.assertEqual(generate_random_ksat.clause_count_from_ratio(3, 0.5), 2)

    def test_dimacs_header_and_clause_count(self) -> None:
        output = io.StringIO()
        generated = [[1, -2, 3], [-1, 2, -3]]
        generate_random_ksat.write_dimacs(output, 3, generated, 3, 17)
        self.assertEqual(
            output.getvalue().splitlines(),
            [
                "c uniform random 3-SAT; variables=3; clauses=2; seed=17",
                "p cnf 3 2",
                "1 -2 3 0",
                "-1 2 -3 0",
            ],
        )

    def test_rejects_impossible_width(self) -> None:
        with self.assertRaisesRegex(ValueError, "cannot exceed"):
            generate_random_ksat.clauses(2, 1, 3, 1)


if __name__ == "__main__":
    unittest.main()
