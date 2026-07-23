#!/usr/bin/env python3
"""Generate a deterministic uniform random k-SAT DIMACS instance."""

from __future__ import annotations

import argparse
import math
import random
import sys
from pathlib import Path
from typing import TextIO


def clauses(
    variable_count: int,
    clause_count: int,
    width: int,
    seed: int,
) -> list[list[int]]:
    if variable_count <= 0:
        raise ValueError("variable count must be positive")
    if clause_count < 0:
        raise ValueError("clause count must be nonnegative")
    if width <= 0:
        raise ValueError("clause width must be positive")
    if width > variable_count:
        raise ValueError("clause width cannot exceed the variable count")

    generator = random.Random(seed)
    generated: list[list[int]] = []
    population = range(1, variable_count + 1)
    for _ in range(clause_count):
        variables = generator.sample(population, width)
        generated.append(
            [variable if generator.getrandbits(1) else -variable for variable in variables]
        )
    return generated


def clause_count_from_ratio(variable_count: int, ratio: float) -> int:
    if not math.isfinite(ratio) or ratio < 0.0:
        raise ValueError("clause ratio must be a finite nonnegative number")
    return math.floor(variable_count * ratio + 0.5)


def write_dimacs(
    output: TextIO,
    variable_count: int,
    generated: list[list[int]],
    width: int,
    seed: int,
) -> None:
    print(
        f"c uniform random {width}-SAT; variables={variable_count}; "
        f"clauses={len(generated)}; seed={seed}",
        file=output,
    )
    print(f"p cnf {variable_count} {len(generated)}", file=output)
    for clause in generated:
        print(*clause, 0, file=output)


def parse_arguments() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate one deterministic uniform random k-SAT DIMACS formula."
    )
    parser.add_argument("--variables", type=int, required=True)
    count = parser.add_mutually_exclusive_group()
    count.add_argument("--clauses", type=int)
    count.add_argument(
        "--ratio",
        type=float,
        default=4.267,
        help="clauses per variable (default: 4.267, near the random 3-SAT threshold)",
    )
    parser.add_argument("--width", type=int, default=3)
    parser.add_argument("--seed", type=int, required=True)
    parser.add_argument(
        "--output",
        type=Path,
        help="output path (default: standard output; existing files are refused)",
    )
    return parser.parse_args()


def main() -> int:
    arguments = parse_arguments()
    try:
        clause_count = (
            arguments.clauses
            if arguments.clauses is not None
            else clause_count_from_ratio(arguments.variables, arguments.ratio)
        )
        generated = clauses(
            arguments.variables,
            clause_count,
            arguments.width,
            arguments.seed,
        )
        if arguments.output is None:
            write_dimacs(
                sys.stdout,
                arguments.variables,
                generated,
                arguments.width,
                arguments.seed,
            )
        else:
            arguments.output.parent.mkdir(parents=True, exist_ok=True)
            with arguments.output.open("x", encoding="utf-8") as output:
                write_dimacs(
                    output,
                    arguments.variables,
                    generated,
                    arguments.width,
                    arguments.seed,
                )
    except (OSError, ValueError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
