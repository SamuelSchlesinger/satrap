#!/usr/bin/env python3
"""Generate one UNSAT proof and validate it with an independent checker."""

from __future__ import annotations

import argparse
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


def parse_arguments() -> argparse.Namespace:
    root = Path(__file__).resolve().parent.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--solver", default=str(root / "target/release/sat"))
    parser.add_argument(
        "--solver-arg",
        action="append",
        default=[],
        help="repeat to pass an additional solver option before the proof arguments",
    )
    parser.add_argument("--checker", default="drat-trim")
    parser.add_argument("--formula", default=str(root / "benchmarks/smoke/unsat.cnf"))
    return parser.parse_args()


def executable(value: str) -> str:
    resolved = shutil.which(value)
    if resolved is not None:
        return resolved
    path = Path(value)
    if path.is_file():
        return str(path.resolve())
    raise ValueError(f"executable not found: {value}")


def main() -> int:
    arguments = parse_arguments()
    try:
        solver = executable(arguments.solver)
        checker = executable(arguments.checker)
        formula = Path(arguments.formula).resolve(strict=True)
    except (OSError, ValueError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2

    with tempfile.NamedTemporaryFile(prefix="sat-proof-", suffix=".drat") as proof:
        solved = subprocess.run(
            [
                solver,
                *arguments.solver_arg,
                "--no-model",
                "--proof",
                proof.name,
                str(formula),
            ],
            capture_output=True,
            text=True,
            check=False,
        )
        if solved.returncode != 20 or "s UNSATISFIABLE" not in solved.stdout:
            print(solved.stdout, file=sys.stderr)
            print(solved.stderr, file=sys.stderr)
            print("error: solver did not report UNSAT", file=sys.stderr)
            return 3

        checked = subprocess.run(
            [checker, str(formula), proof.name],
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            check=False,
        )
        if checked.returncode != 0 or "s VERIFIED" not in checked.stdout:
            print(checked.stdout, file=sys.stderr)
            print("error: checker rejected proof", file=sys.stderr)
            return 4
        print("DRAT proof independently VERIFIED")
        return 0


if __name__ == "__main__":
    raise SystemExit(main())
