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
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import IO, Iterable


@dataclasses.dataclass(frozen=True)
class ProofCheckerSpec:
    command: tuple[str, ...]
    binary_sha256: str | None


@dataclasses.dataclass(frozen=True)
class SolverSpec:
    name: str
    command: tuple[str, ...]
    binary_sha256: str | None
    proof_checker: ProofCheckerSpec | None = None


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
    parser.add_argument(
        "--proof-checker",
        action="append",
        default=[],
        metavar="NAME=COMMAND",
        help=(
            "bind a checker to a solver whose command contains {proof}; "
            "COMMAND must contain {instance} and {proof}"
        ),
    )
    parser.add_argument(
        "--artifacts",
        type=Path,
        help=(
            "new directory for proof artifacts; defaults beside file output, "
            "or to temporary storage when output is standard output"
        ),
    )
    parser.add_argument(
        "--proof-timeout",
        type=float,
        default=300.0,
        help="seconds per independent proof check",
    )
    parser.add_argument(
        "--require-unsat-proofs",
        action="store_true",
        help="fail the run if any solver reports UNSAT without a valid proof",
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
    if arguments.proof_timeout <= 0:
        parser.error("--proof-timeout must be positive")
    return arguments


def parse_named_command(value: str, kind: str) -> tuple[str, tuple[str, ...]]:
    name, separator, command_text = value.partition("=")
    if not separator or not name.strip() or not command_text.strip():
        raise ValueError(
            f"invalid {kind} specification {value!r}; expected NAME=COMMAND"
        )
    command = tuple(shlex.split(command_text))
    if not command:
        raise ValueError(f"{kind} {name!r} has an empty command")
    return name.strip(), command


def executable_hash(command: tuple[str, ...]) -> str | None:
    executable = shutil.which(command[0])
    if executable is None and Path(command[0]).is_file():
        executable = str(Path(command[0]).resolve())
    return sha256_path(Path(executable)) if executable else None


def parse_solver(value: str) -> SolverSpec:
    name, command = parse_named_command(value, "solver")
    return SolverSpec(
        name=name,
        command=command,
        binary_sha256=executable_hash(command),
    )


def attach_proof_checkers(
    solvers: list[SolverSpec], values: list[str]
) -> list[SolverSpec]:
    checkers: dict[str, ProofCheckerSpec] = {}
    solver_names = {solver.name for solver in solvers}
    for value in values:
        name, command = parse_named_command(value, "proof checker")
        if name not in solver_names:
            raise ValueError(f"proof checker names unknown solver {name!r}")
        if name in checkers:
            raise ValueError(f"duplicate proof checker for solver {name!r}")
        if not any("{instance}" in part for part in command):
            raise ValueError(f"proof checker for {name!r} must contain {{instance}}")
        if not any("{proof}" in part for part in command):
            raise ValueError(f"proof checker for {name!r} must contain {{proof}}")
        checkers[name] = ProofCheckerSpec(command, executable_hash(command))

    result = []
    for solver in solvers:
        checker = checkers.get(solver.name)
        has_proof_path = any("{proof}" in part for part in solver.command)
        if checker is not None and not has_proof_path:
            raise ValueError(
                f"solver {solver.name!r} needs a {{proof}} placeholder "
                "when a proof checker is configured"
            )
        if checker is None and has_proof_path:
            raise ValueError(
                f"solver {solver.name!r} has a {{proof}} placeholder "
                "but no proof checker"
            )
        result.append(dataclasses.replace(solver, proof_checker=checker))
    return result


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


def render_command(
    command: tuple[str, ...], instance: Path, proof: Path | None = None
) -> list[str]:
    if proof is None and any("{proof}" in part for part in command):
        raise ValueError("command contains {proof}, but no proof path was provided")
    rendered = []
    for part in command:
        part = part.replace("{instance}", str(instance))
        if proof is not None:
            part = part.replace("{proof}", str(proof))
        rendered.append(part)
    if not any("{instance}" in part for part in command):
        rendered.append(str(instance))
    return rendered


def safe_artifact_component(value: str) -> str:
    readable = re.sub(r"[^A-Za-z0-9_.-]+", "_", value).strip("._")
    readable = readable[:48] or "artifact"
    identity = sha256_bytes(value.encode("utf-8"))[:12]
    return f"{readable}-{identity}"


def proof_artifact_path(
    root: Path,
    spec: SolverSpec,
    formula: Formula,
    run_index: int,
) -> Path:
    solver_directory = root / safe_artifact_component(spec.name)
    solver_directory.mkdir(parents=True, exist_ok=True)
    instance_name = safe_artifact_component(formula.path.name)
    path_identity = sha256_bytes(str(formula.path).encode("utf-8"))[:12]
    return solver_directory / f"{instance_name}-{path_identity}-run-{run_index}.drat"


def proof_artifact_metadata(path: Path, retained: bool) -> dict[str, object]:
    present = path.is_file()
    return {
        "path": str(path) if retained else None,
        "retained": retained,
        "present": present,
        "bytes": path.stat().st_size if present else None,
        "sha256": sha256_path(path) if present else None,
    }


def unchecked_proof_metadata(
    checker: ProofCheckerSpec,
    formula: Formula,
    proof_path: Path,
    retained: bool,
) -> dict[str, object]:
    metadata = proof_artifact_metadata(proof_path, retained)
    metadata.update(
        {
            "checker_command": render_command(
                checker.command, formula.path, proof_path
            ),
            "checker_binary_sha256": checker.binary_sha256,
            "checker_status": "not-run",
            "checker_timeout_seconds": None,
            "checker_wall_seconds": None,
            "checker_timed_out": False,
            "checker_exit_code": None,
            "checker_stdout_sha256": None,
            "checker_stdout_tail": "",
            "checker_stderr_tail": "",
        }
    )
    return metadata


def validate_unsat_proof(
    checker: ProofCheckerSpec,
    formula: Formula,
    proof_path: Path,
    timeout: float,
    retained: bool,
    environment: dict[str, str],
) -> tuple[str, dict[str, object]]:
    command = render_command(checker.command, formula.path, proof_path)
    before = proof_artifact_metadata(proof_path, retained)
    if not before["present"]:
        metadata = unchecked_proof_metadata(
            checker, formula, proof_path, retained
        )
        metadata["checker_status"] = "missing-proof"
        metadata["checker_timeout_seconds"] = timeout
        return "invalid: missing proof artifact", metadata

    started = time.perf_counter()
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
        timed_out = False
        execution_error = None
    except subprocess.TimeoutExpired as error:
        wall_seconds = time.perf_counter() - started
        stdout = decode_timeout_stream(error.stdout)
        stderr = decode_timeout_stream(error.stderr)
        exit_code = None
        timed_out = True
        execution_error = None
    except OSError as error:
        wall_seconds = time.perf_counter() - started
        stdout = ""
        stderr = str(error)
        exit_code = None
        timed_out = False
        execution_error = error

    after = proof_artifact_metadata(proof_path, retained)
    metadata = after | {
        "checker_command": command,
        "checker_binary_sha256": checker.binary_sha256,
        "checker_status": "completed",
        "checker_timeout_seconds": timeout,
        "checker_wall_seconds": wall_seconds,
        "checker_timed_out": timed_out,
        "checker_exit_code": exit_code,
        "checker_stdout_sha256": sha256_bytes(stdout.encode("utf-8")),
        "checker_stdout_tail": stdout[-2000:],
        "checker_stderr_tail": stderr[-2000:],
    }

    if timed_out:
        metadata["checker_status"] = "timeout"
        return "invalid: proof checker timed out", metadata
    if execution_error is not None:
        metadata["checker_status"] = "execution-error"
        return f"invalid: could not execute proof checker: {execution_error}", metadata
    if not after["present"]:
        metadata["checker_status"] = "artifact-removed"
        return "invalid: proof checker removed proof artifact", metadata
    if after["sha256"] != before["sha256"]:
        metadata["checker_status"] = "artifact-changed"
        return "invalid: proof checker changed proof artifact", metadata
    if exit_code != 0:
        metadata["checker_status"] = "rejected"
        return f"invalid: proof checker exited with status {exit_code}", metadata
    if not any(line.strip() == "s VERIFIED" for line in stdout.splitlines()):
        metadata["checker_status"] = "missing-verdict"
        return "invalid: proof checker did not report s VERIFIED", metadata

    metadata["checker_status"] = "verified"
    return "valid", metadata


def run_solver(
    spec: SolverSpec,
    instance: Path,
    timeout: float,
    run_index: int,
    seed: int,
    host: dict[str, str],
    revision: str | None,
    formula: Formula,
    artifact_root: Path | None = None,
    retain_artifacts: bool = False,
    proof_timeout: float = 300.0,
) -> dict[str, object]:
    proof_path = None
    if spec.proof_checker is not None:
        if artifact_root is None:
            raise ValueError("a proof checker requires artifact storage")
        proof_path = proof_artifact_path(artifact_root, spec, formula, run_index)
        if proof_path.exists():
            raise ValueError(f"refusing to overwrite proof artifact: {proof_path}")

    command = render_command(spec.command, instance, proof_path)
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
    except OSError as error:
        wall_seconds = time.perf_counter() - started
        stdout = ""
        stderr = str(error)
        exit_code = None
        status = "INVALID"
        status_error = f"could not execute solver: {error}"
        timed_out = False

    proof: dict[str, object] | None = None
    if status == "SAT":
        validation = validate_model(formula, stdout)
    elif status == "UNSAT":
        if spec.proof_checker is None or proof_path is None:
            validation = "unchecked"
        else:
            validation, proof = validate_unsat_proof(
                spec.proof_checker,
                formula,
                proof_path,
                proof_timeout,
                retain_artifacts,
                environment,
            )
    elif status == "INVALID":
        validation = f"invalid-status: {status_error}"
    else:
        validation = "not-applicable"

    if proof is None and spec.proof_checker is not None and proof_path is not None:
        proof = unchecked_proof_metadata(
            spec.proof_checker,
            formula,
            proof_path,
            retain_artifacts,
        )

    return {
        "schema": 2,
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
        "proof": proof,
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


def summarize(
    rows: Iterable[dict[str, object]],
    require_unsat_proofs: bool = False,
) -> bool:
    rows = list(rows)
    counts: dict[str, Counter[str]] = defaultdict(Counter)
    per_instance: dict[str, set[str]] = defaultdict(set)
    failed_validation = False
    failed_proof = False
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
        if status == "UNSAT" and validation.startswith("invalid:"):
            failed_proof = True
        if (
            status == "UNSAT"
            and require_unsat_proofs
            and validation != "valid"
        ):
            failed_proof = True
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
    if failed_proof:
        print(
            "one or more UNSAT results lacked an independently valid proof",
            file=sys.stderr,
        )
    if invalid_execution:
        print("one or more solver executions had invalid status or exit behavior", file=sys.stderr)
    return (
        not disagreements
        and not failed_validation
        and not failed_proof
        and not invalid_execution
    )


def main() -> int:
    arguments = parse_arguments()
    temporary_artifacts: tempfile.TemporaryDirectory[str] | None = None
    created_artifact_root: Path | None = None
    try:
        solvers = [parse_solver(value) for value in arguments.solver]
        if len({solver.name for solver in solvers}) != len(solvers):
            raise ValueError("solver names must be unique")
        solvers = attach_proof_checkers(solvers, arguments.proof_checker)
        instances = collect_instances(arguments.instances)
        formulas = {instance: parse_formula(instance) for instance in instances}
        if arguments.output != "-" and Path(arguments.output).exists():
            raise ValueError(
                f"refusing to overwrite existing output: {arguments.output}"
            )

        proof_enabled = any(solver.proof_checker is not None for solver in solvers)
        if arguments.artifacts is not None and not proof_enabled:
            raise ValueError("--artifacts requires at least one --proof-checker")
        if proof_enabled:
            if arguments.artifacts is not None:
                artifact_root = arguments.artifacts.resolve()
                retain_artifacts = True
            elif arguments.output != "-":
                artifact_root = Path(f"{arguments.output}.artifacts").resolve()
                retain_artifacts = True
            else:
                temporary_artifacts = tempfile.TemporaryDirectory(
                    prefix="sat-benchmark-proofs-"
                )
                artifact_root = Path(temporary_artifacts.name)
                retain_artifacts = False
            if artifact_root.exists() and retain_artifacts:
                raise ValueError(
                    f"refusing to overwrite artifact directory: {artifact_root}"
                )
            artifact_root.mkdir(parents=True, exist_ok=not retain_artifacts)
            if retain_artifacts:
                created_artifact_root = artifact_root
        else:
            artifact_root = None
            retain_artifacts = False

        output, should_close = open_output(arguments.output)
    except (OSError, UnicodeError, ValueError) as error:
        if temporary_artifacts is not None:
            temporary_artifacts.cleanup()
        if created_artifact_root is not None:
            try:
                created_artifact_root.rmdir()
            except OSError:
                pass
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
                artifact_root,
                retain_artifacts,
                arguments.proof_timeout,
            )
            rows.append(row)
            output.write(json.dumps(row, sort_keys=True) + "\n")
            output.flush()
    finally:
        if should_close:
            output.close()
        if temporary_artifacts is not None:
            temporary_artifacts.cleanup()

    return 0 if summarize(rows, arguments.require_unsat_proofs) else 3


if __name__ == "__main__":
    raise SystemExit(main())
