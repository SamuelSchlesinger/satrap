#!/usr/bin/env python3
"""Summarize a repeated two-solver benchmark JSONL artifact."""

from __future__ import annotations

import argparse
import collections
import json
import math
import statistics
from pathlib import Path
from typing import Iterable


SOLVED = {"SAT", "UNSAT"}


def variable_count(path: Path) -> int:
    with path.open("r", encoding="utf-8", errors="strict") as source:
        for raw_line in source:
            fields = raw_line.split()
            if not fields or fields[0] == "c":
                continue
            if len(fields) != 4 or fields[:2] != ["p", "cnf"]:
                raise ValueError(f"{path}: expected p cnf header")
            return int(fields[2])
    raise ValueError(f"{path}: missing p cnf header")


def median_record(
    rows: list[dict[str, object]], timeout_seconds: float
) -> dict[str, object]:
    completed_statuses = {
        str(row["status"]) for row in rows if str(row["status"]) in SOLVED
    }
    if len(completed_statuses) > 1:
        raise ValueError(f"contradictory completed statuses: {completed_statuses}")
    completed = sum(str(row["status"]) in SOLVED for row in rows)
    required = len(rows) // 2 + 1
    status = (
        next(iter(completed_statuses))
        if completed >= required and completed_statuses
        else "TIMEOUT"
    )
    effective = [
        float(row["wall_seconds"])
        if str(row["status"]) in SOLVED
        else 2.0 * timeout_seconds
        for row in rows
    ]
    return {
        "status": status,
        "completed_repetitions": completed,
        "repetitions": len(rows),
        "median_effective_seconds": statistics.median(effective),
    }


def geometric_mean(values: Iterable[float]) -> float | None:
    values = list(values)
    if not values:
        return None
    if any(value <= 0.0 for value in values):
        raise ValueError("geometric mean requires positive values")
    return math.exp(math.fsum(math.log(value) for value in values) / len(values))


def summarize(
    rows: list[dict[str, object]],
    timeout_seconds: float,
    left: str,
    right: str,
) -> dict[str, object]:
    grouped: dict[tuple[str, str], list[dict[str, object]]] = collections.defaultdict(
        list
    )
    for row in rows:
        grouped[(str(row["solver"]), str(row["instance"]))].append(row)

    instances = sorted({instance for _, instance in grouped})
    solvers = {solver for solver, _ in grouped}
    if solvers != {left, right}:
        raise ValueError(f"expected solvers {left!r} and {right!r}, found {solvers}")

    records: dict[str, dict[str, dict[str, object]]] = {left: {}, right: {}}
    for solver in (left, right):
        for instance in instances:
            pair = grouped.get((solver, instance))
            if not pair:
                raise ValueError(f"missing rows for {solver} on {instance}")
            records[solver][instance] = median_record(pair, timeout_seconds)

    disagreements = []
    for instance in instances:
        statuses = {
            str(records[solver][instance]["status"])
            for solver in (left, right)
            if str(records[solver][instance]["status"]) in SOLVED
        }
        if len(statuses) > 1:
            disagreements.append(instance)

    def solver_summary(solver: str, subset: list[str]) -> dict[str, object]:
        subset_records = [records[solver][instance] for instance in subset]
        statuses = collections.Counter(str(record["status"]) for record in subset_records)
        effective = [
            float(record["median_effective_seconds"]) for record in subset_records
        ]
        return {
            "instances": len(subset),
            "solved": sum(statuses[status] for status in SOLVED),
            "sat": statuses["SAT"],
            "unsat": statuses["UNSAT"],
            "timeouts": statuses["TIMEOUT"],
            "par2_mean_seconds": statistics.mean(effective),
            "par2_total_seconds": math.fsum(effective),
        }

    sizes = {instance: variable_count(Path(instance)) for instance in instances}
    by_size: dict[str, object] = {}
    for size in sorted(set(sizes.values())):
        subset = [instance for instance in instances if sizes[instance] == size]
        jointly_solved = [
            instance
            for instance in subset
            if all(
                str(records[solver][instance]["status"]) in SOLVED
                for solver in (left, right)
            )
        ]
        by_size[str(size)] = {
            left: solver_summary(left, subset),
            right: solver_summary(right, subset),
            "jointly_solved": len(jointly_solved),
            f"{left}_geomean_seconds": geometric_mean(
                float(records[left][instance]["median_effective_seconds"])
                for instance in jointly_solved
            ),
            f"{right}_geomean_seconds": geometric_mean(
                float(records[right][instance]["median_effective_seconds"])
                for instance in jointly_solved
            ),
        }

    jointly_solved = [
        instance
        for instance in instances
        if all(
            str(records[solver][instance]["status"]) in SOLVED
            for solver in (left, right)
        )
    ]
    left_only = [
        instance
        for instance in instances
        if str(records[left][instance]["status"]) in SOLVED
        and str(records[right][instance]["status"]) not in SOLVED
    ]
    right_only = [
        instance
        for instance in instances
        if str(records[right][instance]["status"]) in SOLVED
        and str(records[left][instance]["status"]) not in SOLVED
    ]
    ratios = {
        instance: (
            float(records[right][instance]["median_effective_seconds"])
            / float(records[left][instance]["median_effective_seconds"])
        )
        for instance in jointly_solved
    }
    practical = {
        f"{left}_wins": sum(ratio > 1.1 for ratio in ratios.values()),
        f"{right}_wins": sum(ratio < 1.0 / 1.1 for ratio in ratios.values()),
        "within_ten_percent": sum(
            1.0 / 1.1 <= ratio <= 1.1 for ratio in ratios.values()
        ),
    }

    return {
        "instances": len(instances),
        "timeout_seconds": timeout_seconds,
        left: solver_summary(left, instances),
        right: solver_summary(right, instances),
        "disagreements": disagreements,
        "jointly_solved": len(jointly_solved),
        f"{left}_only": left_only,
        f"{right}_only": right_only,
        "practical_joint_wins": practical,
        f"{right}_over_{left}_median_speed_ratio_geomean": geometric_mean(
            ratios.values()
        ),
        "by_size": by_size,
        "per_instance": {
            instance: {
                "variables": sizes[instance],
                left: records[left][instance],
                right: records[right][instance],
                f"{right}_over_{left}_speed_ratio": ratios.get(instance),
            }
            for instance in instances
        },
    }


def parse_arguments() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--timeout", type=float, required=True)
    parser.add_argument("--left", required=True)
    parser.add_argument("--right", required=True)
    parser.add_argument("--output", type=Path)
    return parser.parse_args()


def main() -> int:
    arguments = parse_arguments()
    try:
        rows = [
            json.loads(line)
            for line in arguments.input.read_text(encoding="utf-8").splitlines()
        ]
        summary = summarize(rows, arguments.timeout, arguments.left, arguments.right)
        rendered = json.dumps(summary, indent=2, sort_keys=True) + "\n"
        if arguments.output is None:
            print(rendered, end="")
        else:
            with arguments.output.open("x", encoding="utf-8") as output:
                output.write(rendered)
    except (OSError, UnicodeError, ValueError, json.JSONDecodeError) as error:
        print(f"error: {error}")
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
