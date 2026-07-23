from __future__ import annotations

import unittest

import summarize_benchmark


class SummarizeBenchmarkTests(unittest.TestCase):
    def test_majority_completion_and_par2_median(self) -> None:
        rows = [
            {"status": "SAT", "wall_seconds": 1.0},
            {"status": "SAT", "wall_seconds": 2.0},
            {"status": "TIMEOUT", "wall_seconds": 5.0},
        ]
        self.assertEqual(
            summarize_benchmark.median_record(rows, 5.0),
            {
                "status": "SAT",
                "completed_repetitions": 2,
                "repetitions": 3,
                "median_effective_seconds": 2.0,
            },
        )

    def test_majority_timeout_uses_par2_penalty(self) -> None:
        rows = [
            {"status": "UNSAT", "wall_seconds": 1.0},
            {"status": "TIMEOUT", "wall_seconds": 5.0},
            {"status": "TIMEOUT", "wall_seconds": 5.0},
        ]
        record = summarize_benchmark.median_record(rows, 5.0)
        self.assertEqual(record["status"], "TIMEOUT")
        self.assertEqual(record["median_effective_seconds"], 10.0)

    def test_rejects_contradictory_completed_statuses(self) -> None:
        rows = [
            {"status": "SAT", "wall_seconds": 1.0},
            {"status": "UNSAT", "wall_seconds": 1.0},
            {"status": "TIMEOUT", "wall_seconds": 5.0},
        ]
        with self.assertRaisesRegex(ValueError, "contradictory"):
            summarize_benchmark.median_record(rows, 5.0)


if __name__ == "__main__":
    unittest.main()
