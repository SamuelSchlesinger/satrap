from __future__ import annotations

import io
import unittest

import generate_pigeonhole


class PigeonholeGeneratorTests(unittest.TestCase):
    def test_generates_expected_variables_and_clause_count(self) -> None:
        generated = generate_pigeonhole.clauses(3, 2)
        self.assertEqual(len(generated), 12)
        self.assertEqual(generated[:3], [[1, 2], [-1, -2], [3, 4]])
        self.assertTrue(all(1 <= abs(literal) <= 6 for clause in generated for literal in clause))

        output = io.StringIO()
        generate_pigeonhole.write_dimacs(output, 3, 2)
        self.assertIn("p cnf 6 12\n", output.getvalue())


if __name__ == "__main__":
    unittest.main()
