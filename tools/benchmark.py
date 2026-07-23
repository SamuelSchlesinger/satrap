#!/usr/bin/env python3
"""Run reproducible, shell-free head-to-head DIMACS benchmarks."""

from __future__ import annotations

import argparse
import dataclasses
import datetime as dt
import hashlib
import json
import os
import platform
import random
import shlex
import shutil
import subprocess
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import IO, Iterable


@dataclasses.dataclass(frozen=True)
class SolverSpec:
    name: str
    command: tuple[str, ...]
    binary_sha256: str | None


@dataclasses.dataclass(frozen=True)
class Formula:
    path: Path
    variable_count: int
    clause_count: int


def parse_arguments() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Benchmark DIMACS solvers and write one JSON object per run."
    )
    parser.add_argument(
        "--instances",
        required=True,
        type=Path,
        help="a .cnf file or directory searched recursively for .cnf files",
    )
    parser.add_argument(
        "--solver",
        required=True,
        action="append",
        metavar="NAME=COMMAND",
        help="repeat for each solver; {instance} is optional in COMMAND",
    )
    parser.add_argument("--timeout", type=float, default=60.0, help="seconds per run")
    parser.add_argument("--repeat", type=int, default=1, help="runs per pair")
    parser.add_argument("--seed", type=int, default=1, help="task-order seed")
    parser.add_argument(
        "--output",
        required=True,
        help="new JSONL path, or - for standard output",
    )
    arguments = parser.parse_args()
    if arguments.timeout <= 0:
        parser.error("--timeout must be positive")
    if arguments.repeat <= 0:
        parser.error("--repeat must be positive")
    return arguments


def parse_solver(value: str) -> SolverSpec:
    name, separator, command_text = value.partition("=")
    if not separator or not name.strip() or not command_text.strip():
        raise ValueError(f"invalid solver specification {value!r}; expected NAME=COMMAND")
    command = tuple(shlex.split(command_text))
    if not command:
        raise ValueError(f"solver {name!r} has an empty command")
    executable = shutil.which(command[0])
    if executable is None and Path(command[0]).is_file():
        executable = str(Path(command[0]).resolve())
    binary_hash = sha256_path(Path(executable)) if executable else None
    return SolverSpec(name=name.strip(), command=command, binary_sha256=binary_hash)


def collect_instances(path: Path) -> list[Path]:
    if path.is_file():
        instances = [path]
    elif path.is_dir():
        instances = sorted(candidate for candidate in path.rglob("*.cnf") if candidate.is_file())
    else:
        raise ValueError(f"instance path does not exist: {path}")
    if not instances:
        raise ValueError(f"no .cnf instances found under {path}")
    return [instance.resolve() for instance in instances]


def render_command(spec: SolverSpec, instance: Path) -> list[str]:
    rendered = [part.replace("{instance}", str(instance)) for part in spec.command]
    if not any("{instance}" in part for part in spec.command):
        rendered.append(str(instance))
    return rendered


def run_solver(
    spec: SolverSpec,
    instance: Path,
    timeout: float,
    run_index: int,
    seed: int,
    host: dict[str, str],
    revision: str | None,
    formula: Formula,
) -> dict[str, object]:
    command = render_command(spec, instance)
    started_at = dt.datetime.now(dt.timezone.utc).isoformat()
    started = time.perf_counter()
    environment = os.environ.copy()
    environment["LC_ALL"] = "C"

    try:
        completed = subprocess.run(
            command,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            errors="replace",
            timeout=timeout,
            check=False,
            env=environment,
        )
        wall_seconds = time.perf_counter() - started
        stdout = completed.stdout
        stderr = completed.stderr
        exit_code: int | None = completed.returncode
        status, status_error = reported_status(stdout, exit_code)
        timed_out = False
    except subprocess.TimeoutExpired as error:
        wall_seconds = time.perf_counter() - started
        stdout = decode_timeout_stream(error.stdout)
        stderr = decode_timeout_stream(error.stderr)
        exit_code = None
        status = "TIMEOUT"
        status_error = None
        timed_out = True

    if status == "SAT":
        validation = validate_model(formula, stdout)
    elif status == "UNSAT":
        validation = "unchecked"
    elif status == "INVALID":
        validation = f"invalid-status: {status_error}"
    else:
        validation = "not-applicable"

    return {
        "schema": 1,
        "started_at": started_at,
        "solver": spec.name,
        "solver_command": command,
        "solver_binary_sha256": spec.binary_sha256,
        "instance": str(instance),
        "instance_sha256": sha256_path(instance),
        "run_index": run_index,
        "order_seed": seed,
        "timeout_seconds": timeout,
        "wall_seconds": wall_seconds,
        "timed_out": timed_out,
        "exit_code": exit_code,
        "status": status,
        "validation": validation,
        "stdout_sha256": sha256_bytes(stdout.encode("utf-8")),
        "stderr_tail": stderr[-2000:],
        "git_revision": revision,
        "host": host,
    }


def reported_status(stdout: str, exit_code: int | None) -> tuple[str, str | None]:
    statuses: set[str] = set()
    for raw_line in stdout.splitlines():
        line = raw_line.strip().upper()
        if line in {"S SATISFIABLE", "SAT", "SATISFIABLE"}:
            statuses.add("SAT")
        elif line in {"S UNSATISFIABLE", "UNSAT", "UNSATISFIABLE"}:
            statuses.add("UNSAT")
        elif line in {"S UNKNOWN", "UNKNOWN"}:
            statuses.add("UNKNOWN")

    if len(statuses) > 1:
        return "INVALID", f"contradictory status lines: {sorted(statuses)}"
    status = next(iter(statuses), None)
    exit_status = {10: "SAT", 20: "UNSAT"}.get(exit_code)
    if exit_code not in {None, 0, 10, 20}:
        return "INVALID", f"unexpected exit code {exit_code}"
    if status is not None and exit_status is not None and status != exit_status:
        return "INVALID", f"output says {status}, exit code says {exit_status}"
    if status is not None:
        return status, None
    if exit_status is not None:
        return exit_status, None
    return "UNKNOWN", None


def validate_model(formula: Formula, stdout: str) -> str:
    # One byte per variable keeps validation practical for multi-million-variable
    # competition instances. Zero is unassigned, one is false, and two is true.
    assignments = bytearray(formula.variable_count + 1)
    saw_model_line = False
    for raw_line in stdout.splitlines():
        fields = raw_line.split()
        if not fields or fields[0].lower() != "v":
            continue
        saw_model_line = True
        for token in fields[1:]:
            try:
                literal = int(token)
            except ValueError:
                return f"invalid: non-integer model token {token!r}"
            if literal == 0:
                continue
            variable = abs(literal)
            if variable > formula.variable_count:
                return f"invalid: model variable {variable} exceeds header"
            value = 2 if literal > 0 else 1
            previous = assignments[variable]
            if previous != 0 and previous != value:
                return f"invalid: contradictory values for variable {variable}"
            assignments[variable] = value
    if not saw_model_line:
        return "invalid: missing model lines"

    header_seen = False
    clause_count = 0
    clause_open = False
    clause_satisfied = False
    try:
        with formula.path.open("r", encoding="utf-8", errors="strict") as source:
            for line_number, raw_line in enumerate(source, 1):
                fields = raw_line.split()
                if not fields or fields[0] == "c":
                    continue
                if fields[0] == "p":
                    if (
                        header_seen
                        or len(fields) != 4
                        or fields[1] != "cnf"
                        or int(fields[2]) != formula.variable_count
                        or int(fields[3]) != formula.clause_count
                    ):
                        return f"invalid: malformed or changed header at line {line_number}"
                    header_seen = True
                    continue
                if not header_seen:
                    return f"invalid: clause data before header at line {line_number}"

                for token in fields:
                    if token == "c":
                        break
                    try:
                        literal = int(token)
                    except ValueError:
                        return f"invalid: non-integer DIMACS token {token!r}"
                    if literal == 0:
                        clause_count += 1
                        if not clause_satisfied:
                            return f"invalid: clause {clause_count} is not satisfied"
                        clause_open = False
                        clause_satisfied = False
                        continue

                    variable = abs(literal)
                    if variable > formula.variable_count:
                        return f"invalid: formula literal {literal} exceeds header"
                    clause_open = True
                    expected = 2 if literal > 0 else 1
                    clause_satisfied |= assignments[variable] == expected
    except (OSError, UnicodeError, ValueError) as error:
        return f"invalid: could not validate formula: {error}"

    if not header_seen:
        return "invalid: missing p cnf header"
    if clause_open:
        return "invalid: unterminated final clause"
    if clause_count != formula.clause_count:
        return (
            f"invalid: header declares {formula.clause_count} clauses, "
            f"found {clause_count}"
        )
    return "valid"


def parse_formula(path: Path) -> Formula:
    with path.open("r", encoding="utf-8", errors="strict") as source:
        for line_number, raw_line in enumerate(source, 1):
            fields = raw_line.split()
            if not fields or fields[0] == "c":
                continue
            if fields[0] != "p" or len(fields) != 4 or fields[1] != "cnf":
                raise ValueError(f"{path}:{line_number}: expected p cnf header")
            variable_count = int(fields[2])
            clause_count = int(fields[3])
            if variable_count < 0 or clause_count < 0:
                raise ValueError(f"{path}:{line_number}: negative header count")
            return Formula(path, variable_count, clause_count)
    raise ValueError(f"{path}: missing p cnf header")


def sha256_path(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def decode_timeout_stream(value: bytes | str | None) -> str:
    if value is None:
        return ""
    if isinstance(value, bytes):
        return value.decode("utf-8", errors="replace")
    return value


def git_revision() -> str | None:
    completed = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        text=True,
        check=False,
    )
    return completed.stdout.strip() if completed.returncode == 0 else None


def host_metadata() -> dict[str, str]:
    uname = platform.uname()
    return {
        "system": uname.system,
        "release": uname.release,
        "machine": uname.machine,
        "processor": uname.processor,
        "python": platform.python_version(),
    }


def open_output(value: str) -> tuple[IO[str], bool]:
    if value == "-":
        return sys.stdout, False
    path = Path(value)
    path.parent.mkdir(parents=True, exist_ok=True)
    try:
        return path.open("x", encoding="utf-8"), True
    except FileExistsError as error:
        raise ValueError(f"refusing to overwrite existing output: {path}") from error


def summarize(rows: Iterable[dict[str, object]]) -> bool:
    rows = list(rows)
    counts: dict[str, Counter[str]] = defaultdict(Counter)
    per_instance: dict[str, set[str]] = defaultdict(set)
    failed_validation = False
    invalid_execution = False
    for row in rows:
        solver = str(row["solver"])
        status = str(row["status"])
        counts[solver][status] += 1
        if status in {"SAT", "UNSAT"}:
            per_instance[str(row["instance"])].add(status)
        validation = str(row["validation"])
        if status == "SAT" and validation != "valid":
            failed_validation = True
        if status == "INVALID":
            invalid_execution = True

    for solver in sorted(counts):
        rendered = ", ".join(f"{key}={value}" for key, value in sorted(counts[solver].items()))
        print(f"summary {solver}: {rendered}", file=sys.stderr)
    disagreements = [instance for instance, statuses in per_instance.items() if len(statuses) > 1]
    for instance in disagreements:
        print(f"disagreement: {instance}: {sorted(per_instance[instance])}", file=sys.stderr)
    if failed_validation:
        print("one or more SAT models failed validation", file=sys.stderr)
    if invalid_execution:
        print("one or more solver executions had invalid status or exit behavior", file=sys.stderr)
    return not disagreements and not failed_validation and not invalid_execution


def main() -> int:
    arguments = parse_arguments()
    try:
        solvers = [parse_solver(value) for value in arguments.solver]
        if len({solver.name for solver in solvers}) != len(solvers):
            raise ValueError("solver names must be unique")
        instances = collect_instances(arguments.instances)
        formulas = {instance: parse_formula(instance) for instance in instances}
        output, should_close = open_output(arguments.output)
    except (OSError, UnicodeError, ValueError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2

    tasks = [
        (solver, instance, run_index)
        for run_index in range(arguments.repeat)
        for instance in instances
        for solver in solvers
    ]
    random.Random(arguments.seed).shuffle(tasks)
    revision = git_revision()
    host = host_metadata()
    rows: list[dict[str, object]] = []

    try:
        for task_index, (solver, instance, run_index) in enumerate(tasks, 1):
            print(
                f"[{task_index}/{len(tasks)}] {solver.name} {instance.name} run={run_index}",
                file=sys.stderr,
            )
            row = run_solver(
                solver,
                instance,
                arguments.timeout,
                run_index,
                arguments.seed,
                host,
                revision,
                formulas[instance],
            )
            rows.append(row)
            output.write(json.dumps(row, sort_keys=True) + "\n")
            output.flush()
    finally:
        if should_close:
            output.close()

    return 0 if summarize(rows) else 3


if __name__ == "__main__":
    raise SystemExit(main())
