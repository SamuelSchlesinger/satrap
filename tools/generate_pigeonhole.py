#!/usr/bin/env python3
"""Generate a pigeonhole-principle DIMACS CNF instance."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path
from typing import TextIO


def clauses(pigeons: int, holes: int) -> list[list[int]]:
    def variable(pigeon: int, hole: int) -> int:
        return pigeon * holes + hole + 1

    result: list[list[int]] = []
    for pigeon in range(pigeons):
        result.append([variable(pigeon, hole) for hole in range(holes)])
        for left in range(holes):
            for right in range(left + 1, holes):
                result.append(
                    [-variable(pigeon, left), -variable(pigeon, right)]
                )
    for hole in range(holes):
        for first in range(pigeons):
            for second in range(first + 1, pigeons):
                result.append([-variable(first, hole), -variable(second, hole)])
    return result


def write_dimacs(output: TextIO, pigeons: int, holes: int) -> None:
    generated = clauses(pigeons, holes)
    print(f"c pigeonhole principle: {pigeons} pigeons, {holes} holes", file=output)
    print(f"p cnf {pigeons * holes} {len(generated)}", file=output)
    for clause in generated:
        print(*clause, 0, file=output)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("pigeons", type=int)
    parser.add_argument("holes", type=int)
    parser.add_argument("--output", type=Path)
    arguments = parser.parse_args()
    if arguments.pigeons < 1 or arguments.holes < 1:
        parser.error("pigeons and holes must be positive")

    if arguments.output is None:
        write_dimacs(sys.stdout, arguments.pigeons, arguments.holes)
    else:
        with arguments.output.open("w", encoding="ascii", newline="\n") as output:
            write_dimacs(output, arguments.pigeons, arguments.holes)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
