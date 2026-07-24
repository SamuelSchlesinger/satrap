#!/usr/bin/env python3
"""Check repository invariants that formatters and compilers do not cover."""

from __future__ import annotations

import re
import stat
import subprocess
import sys
from pathlib import Path
from urllib.parse import unquote

ROOT = Path(__file__).resolve().parents[1]
TEXT_SUFFIXES = {
    ".json",
    ".lock",
    ".md",
    ".py",
    ".rs",
    ".sh",
    ".toml",
    ".txt",
    ".yaml",
    ".yml",
}
TEXT_FILENAMES = {".editorconfig", ".gitignore", "Makefile"}
MARKDOWN_LINK = re.compile(r"!?\[[^\]]*]\(([^)]+)\)")
VERSION = re.compile(r"\d+(?:[.-]\d+){1,2}")
REQUIRED_QUALITY_ASSETS = (
    Path("benchmarks/smt-proof-smoke/qf-bool-connectives.smt2"),
    Path("benchmarks/smt-proof-smoke/qf-bool-incremental.smt2"),
    Path("benchmarks/smt-proof-smoke/qf-bool-reset.smt2"),
    Path("benchmarks/smt-proof-smoke/qf-bool-scoped.smt2"),
    Path("benchmarks/smt-proof-smoke/qf-bv-arithmetic.smt2"),
    Path("benchmarks/smt-proof-smoke/qf-bv-operators.smt2"),
    Path("benchmarks/smt-proof-smoke/qf-bv-scoped.smt2"),
    Path("benchmarks/smt-proof-smoke/qf-abv-extensionality.smt2"),
    Path("benchmarks/smt-proof-smoke/qf-abv-features.smt2"),
    Path("benchmarks/smt-proof-smoke/qf-aufbv-arrays.smt2"),
    Path("benchmarks/smt-proof-smoke/qf-uf-congruence.smt2"),
    Path("benchmarks/smt-proof-smoke/qf-uf-features.smt2"),
    Path("benchmarks/smt-proof-smoke/qf-uf-scoped.smt2"),
    Path("benchmarks/smt-proof-smoke/qf-ufbv-congruence.smt2"),
    Path("benchmarks/smt-proof-smoke/qf-idl-cycle.smt2"),
    Path("benchmarks/smt-proof-smoke/qf-idl-ite.smt2"),
    Path("benchmarks/smt-proof-smoke/qf-lia-ite.smt2"),
    Path("benchmarks/smt-proof-smoke/qf-lia-parity.smt2"),
    Path("benchmarks/smt-proof-smoke/qf-lra-ite.smt2"),
    Path("benchmarks/smt-proof-smoke/qf-lra-linear.smt2"),
    Path("benchmarks/smt-proof-smoke/qf-rdl-rational.smt2"),
    Path("benchmarks/smt-proof-smoke/qf-rdl-strict.smt2"),
)


def repository_files() -> list[Path]:
    """Return checked-in and not-ignored new files, including staged additions."""
    result = subprocess.run(
        ["git", "ls-files", "--cached", "--others", "--exclude-standard", "-z"],
        cwd=ROOT,
        check=True,
        capture_output=True,
    )
    return [ROOT / Path(raw.decode("utf-8")) for raw in result.stdout.split(b"\0") if raw]


def is_text_file(path: Path) -> bool:
    return path.name in TEXT_FILENAMES or path.suffix in TEXT_SUFFIXES


def read_text(path: Path, errors: list[str]) -> str | None:
    try:
        return path.read_bytes().decode("utf-8")
    except UnicodeDecodeError:
        errors.append(f"{path.relative_to(ROOT)}: expected UTF-8 text")
        return None


def check_text_hygiene(files: list[Path], errors: list[str]) -> None:
    for path in files:
        if not path.is_file() or not is_text_file(path):
            continue
        text = read_text(path, errors)
        if text is None:
            continue
        relative = path.relative_to(ROOT)
        if text and not text.endswith("\n"):
            errors.append(f"{relative}: missing final newline")
        if "\r" in text:
            errors.append(f"{relative}: carriage return found; use LF line endings")
        for line_number, line in enumerate(text.splitlines(), start=1):
            if line.rstrip(" \t") != line:
                errors.append(f"{relative}:{line_number}: trailing whitespace")


def link_target(raw_target: str) -> str:
    target = raw_target.strip()
    if target.startswith("<"):
        closing = target.find(">")
        return target[1:closing] if closing >= 0 else target
    return target.split(maxsplit=1)[0]


def check_markdown_links(files: list[Path], errors: list[str]) -> None:
    for path in files:
        if path.suffix != ".md" or not path.is_file():
            continue
        text = read_text(path, errors)
        if text is None:
            continue
        in_fence = False
        for line_number, line in enumerate(text.splitlines(), start=1):
            if line.lstrip().startswith(("```", "~~~")):
                in_fence = not in_fence
                continue
            if in_fence:
                continue
            for match in MARKDOWN_LINK.finditer(line):
                target = unquote(link_target(match.group(1)))
                path_part = target.split("#", maxsplit=1)[0]
                if (
                    not path_part
                    or path_part.startswith("/")
                    or re.match(r"^[A-Za-z][A-Za-z0-9+.-]*:", path_part)
                ):
                    continue
                repository_root = ROOT.resolve()
                destination = (path.parent / path_part).resolve()
                try:
                    destination.relative_to(repository_root)
                except ValueError:
                    relative = path.relative_to(ROOT)
                    errors.append(
                        f"{relative}:{line_number}: local link leaves repository {target!r}"
                    )
                    continue
                if not destination.exists():
                    relative = path.relative_to(ROOT)
                    errors.append(f"{relative}:{line_number}: broken local link {target!r}")


def normalized_version(value: str) -> tuple[int, int, int] | None:
    match = VERSION.search(value)
    if match is None:
        return None
    parts = tuple(int(part) for part in re.split(r"[.-]", match.group(0)))
    return (*parts, 0, 0, 0)[:3]


def extract_version(path: Path, pattern: str, errors: list[str]) -> tuple[int, int, int] | None:
    text = read_text(path, errors)
    if text is None:
        return None
    match = re.search(pattern, text, flags=re.MULTILINE)
    if match is None:
        errors.append(f"{path.relative_to(ROOT)}: version declaration not found")
        return None
    version = normalized_version(match.group(1))
    if version is None:
        errors.append(f"{path.relative_to(ROOT)}: invalid version declaration")
    return version


def check_msrv(errors: list[str]) -> None:
    declarations = {
        "Cargo.toml": extract_version(
            ROOT / "Cargo.toml",
            r'^rust-version\s*=\s*"([^"]+)"',
            errors,
        ),
        "scripts/check-msrv.sh": extract_version(
            ROOT / "scripts/check-msrv.sh",
            r"cargo \+([0-9.]+)",
            errors,
        ),
        ".github/workflows/ci.yml": extract_version(
            ROOT / ".github/workflows/ci.yml",
            r"rustup toolchain install ([0-9.]+)",
            errors,
        ),
    }
    versions = {version for version in declarations.values() if version is not None}
    if len(versions) > 1:
        rendered = ", ".join(
            f"{name}={'.'.join(map(str, version))}"
            for name, version in declarations.items()
            if version is not None
        )
        errors.append(f"MSRV declarations disagree: {rendered}")


def check_audit_version(errors: list[str]) -> None:
    declarations = {
        "scripts/check-security.sh": extract_version(
            ROOT / "scripts/check-security.sh",
            r"^required_version=([0-9.]+)",
            errors,
        ),
        ".github/workflows/security.yml": extract_version(
            ROOT / ".github/workflows/security.yml",
            r"cargo-audit --version ([0-9.]+)",
            errors,
        ),
    }
    versions = {version for version in declarations.values() if version is not None}
    if len(versions) > 1:
        rendered = ", ".join(
            f"{name}={'.'.join(map(str, version))}"
            for name, version in declarations.items()
            if version is not None
        )
        errors.append(f"cargo-audit versions disagree: {rendered}")


def check_oracle_versions(errors: list[str]) -> None:
    for name, ci_variable, installer_variable in (
        ("Z3", "required_z3_version", "z3_version"),
        ("cvc5", "required_cvc5_version", "cvc5_version"),
        ("Bitwuzla", "required_bitwuzla_version", "bitwuzla_version"),
    ):
        declarations = {
            "scripts/ci.sh": extract_version(
                ROOT / "scripts/ci.sh",
                rf"^{ci_variable}=([0-9.]+)",
                errors,
            ),
            "scripts/install-smt-oracles.sh": extract_version(
                ROOT / "scripts/install-smt-oracles.sh",
                rf"^{installer_variable}=([0-9.]+)",
                errors,
            ),
        }
        versions = {version for version in declarations.values() if version is not None}
        if len(versions) > 1:
            rendered = ", ".join(
                f"{path}={'.'.join(map(str, version))}"
                for path, version in declarations.items()
                if version is not None
            )
            errors.append(f"{name} versions disagree: {rendered}")


def check_fuzz_tool_versions(errors: list[str]) -> None:
    for name, gate_variable, installer_variable in (
        ("cargo-fuzz", "required_cargo_fuzz_version", "cargo_fuzz_version"),
        ("fuzz nightly", "fuzz_nightly", "fuzz_nightly"),
    ):
        declarations = {
            "scripts/check-fuzz.sh": extract_version(
                ROOT / "scripts/check-fuzz.sh",
                rf"^{gate_variable}=(?:nightly-)?([0-9.-]+)",
                errors,
            ),
            "scripts/install-fuzz-tools.sh": extract_version(
                ROOT / "scripts/install-fuzz-tools.sh",
                rf"^{installer_variable}=(?:nightly-)?([0-9.-]+)",
                errors,
            ),
        }
        versions = {version for version in declarations.values() if version is not None}
        if len(versions) > 1:
            rendered = ", ".join(
                f"{path}={'.'.join(map(str, version))}"
                for path, version in declarations.items()
                if version is not None
            )
            errors.append(f"{name} versions disagree: {rendered}")


def check_python_tool_versions(errors: list[str]) -> None:
    declarations = {
        "scripts/check-python.sh": extract_version(
            ROOT / "scripts/check-python.sh",
            r"^required_ruff_version=([0-9.]+)",
            errors,
        ),
        "scripts/install-python-tools.sh": extract_version(
            ROOT / "scripts/install-python-tools.sh",
            r"^ruff_version=([0-9.]+)",
            errors,
        ),
        "scripts/ruff-requirements.txt": extract_version(
            ROOT / "scripts/ruff-requirements.txt",
            r"^ruff==([0-9.]+)",
            errors,
        ),
    }
    versions = {version for version in declarations.values() if version is not None}
    if len(versions) > 1:
        rendered = ", ".join(
            f"{path}={'.'.join(map(str, version))}"
            for path, version in declarations.items()
            if version is not None
        )
        errors.append(f"Ruff versions disagree: {rendered}")


def extract_revision(path: Path, pattern: str, errors: list[str]) -> str | None:
    text = read_text(path, errors)
    if text is None:
        return None
    match = re.search(pattern, text, flags=re.MULTILINE)
    if match is None:
        errors.append(f"{path.relative_to(ROOT)}: revision declaration not found")
        return None
    return match.group(1)


def check_proof_checker_revision(errors: list[str]) -> None:
    declarations = {
        "scripts/check-proofs.sh": extract_revision(
            ROOT / "scripts/check-proofs.sh",
            r"^required_drat_trim_revision=([0-9a-f]{40})",
            errors,
        ),
        "scripts/install-proof-checkers.sh": extract_revision(
            ROOT / "scripts/install-proof-checkers.sh",
            r"^drat_trim_revision=([0-9a-f]{40})",
            errors,
        ),
    }
    revisions = {revision for revision in declarations.values() if revision is not None}
    if len(revisions) > 1:
        rendered = ", ".join(
            f"{path}={revision}" for path, revision in declarations.items() if revision is not None
        )
        errors.append(f"DRAT-trim revisions disagree: {rendered}")


def extract_integer_declaration(
    path: Path,
    pattern: str,
    errors: list[str],
) -> int | None:
    text = read_text(path, errors)
    if text is None:
        return None
    match = re.search(pattern, text, flags=re.MULTILINE)
    if match is None:
        errors.append(f"{path.relative_to(ROOT)}: integer declaration not found")
        return None
    return int(match.group(1).replace("_", ""))


def check_integer_proof_limits(errors: list[str]) -> None:
    rust = ROOT / "src/smt/proof.rs"
    python = ROOT / "tools/check_smt_proof.py"
    for name in ("MAX_INTEGER_PROOF_VARIABLES", "MAX_INTEGER_PROOF_WORK"):
        declarations = {
            "src/smt/proof.rs": extract_integer_declaration(
                rust,
                rf"^const {name}: usize = ([0-9_]+);",
                errors,
            ),
            "tools/check_smt_proof.py": extract_integer_declaration(
                python,
                rf"^{name} = ([0-9_]+)",
                errors,
            ),
        }
        values = {value for value in declarations.values() if value is not None}
        if len(values) > 1:
            rendered = ", ".join(
                f"{path}={value}" for path, value in declarations.items() if value is not None
            )
            errors.append(f"{name} declarations disagree: {rendered}")


def require_commands(path: Path, commands: tuple[str, ...], errors: list[str]) -> None:
    text = read_text(path, errors)
    if text is None:
        return
    for command in commands:
        if command not in text:
            errors.append(f"{path.relative_to(ROOT)}: must invoke {command}")


def check_required_quality_assets(errors: list[str]) -> None:
    for relative in REQUIRED_QUALITY_ASSETS:
        path = ROOT / relative
        if not path.is_file():
            errors.append(f"{relative}: required quality asset is missing")
        elif path.stat().st_size == 0:
            errors.append(f"{relative}: required quality asset is empty")


def check_gate_wiring(errors: list[str]) -> None:
    require_commands(
        ROOT / ".githooks/pre-commit",
        ("scripts/check-fast.sh",),
        errors,
    )
    require_commands(
        ROOT / "scripts/check-fast.sh",
        ("scripts/check-python.sh",),
        errors,
    )
    shared_gates = ("scripts/ci.sh", "scripts/check-msrv.sh")
    require_commands(ROOT / ".githooks/pre-push", shared_gates, errors)
    require_commands(ROOT / ".github/workflows/ci.yml", shared_gates, errors)
    require_commands(
        ROOT / ".githooks/pre-push",
        ("scripts/check-security.sh",),
        errors,
    )
    require_commands(
        ROOT / "scripts/ci.sh",
        (
            "scripts/quality.sh",
            "scripts/check-fuzz.sh",
            "scripts/check-proofs.sh",
            "make smoke",
            "z3 --version",
            "cvc5 --version",
            "bitwuzla --version",
        ),
        errors,
    )
    require_commands(
        ROOT / "scripts/quality.sh",
        (
            "shellcheck",
            "actionlint",
            "scripts/check-python.sh",
            "tools/check_hygiene.py",
        ),
        errors,
    )
    require_commands(
        ROOT / ".github/workflows/security.yml",
        ("actions/checkout@v6", "scripts/check-security.sh"),
        errors,
    )
    require_commands(
        ROOT / ".github/workflows/ci.yml",
        (
            "actions/checkout@v6",
            "scripts/install-fuzz-tools.sh",
            "scripts/install-python-tools.sh",
            "scripts/install-smt-oracles.sh",
            "scripts/install-proof-checkers.sh",
        ),
        errors,
    )
    require_commands(
        ROOT / "scripts/install-smt-oracles.sh",
        ("Z3Prover/z3", "cvc5/cvc5", "bitwuzla/bitwuzla"),
        errors,
    )
    require_commands(
        ROOT / "scripts/install-proof-checkers.sh",
        ("marijnheule/drat-trim", "drat_trim_sha256"),
        errors,
    )
    require_commands(
        ROOT / "scripts/check-proofs.sh",
        (
            "tools/proof_smoke.py",
            "--probe",
            "--vivify",
            "--subsume",
            "--binary-minimize",
            "--eliminate",
            "--factor",
            "--factor-macro",
            "tools/check_smt_proof.py",
            "benchmarks/smt-proof-smoke",
        ),
        errors,
    )
    require_commands(
        ROOT / "Makefile",
        (
            "tools/benchmark.py",
            "--proof {proof}",
            "--proof-checker",
            "--require-unsat-proofs",
        ),
        errors,
    )
    require_commands(
        ROOT / "scripts/install-fuzz-tools.sh",
        ("--component clippy", "--component rust-src", "--component rustfmt"),
        errors,
    )
    require_commands(
        ROOT / "scripts/install-python-tools.sh",
        ("--require-hashes", "ruff-requirements.txt"),
        errors,
    )
    require_commands(
        ROOT / "scripts/check-python.sh",
        ("ruff check", "ruff format --check"),
        errors,
    )
    require_commands(
        ROOT / "scripts/check-fuzz.sh",
        (
            "--locked",
            "clippy",
            "smt_session_bytes",
            "smt_structured_session",
            "sat_proof",
        ),
        errors,
    )


def check_executable_scripts(errors: list[str]) -> None:
    paths = sorted((ROOT / "scripts").glob("*.sh"))
    paths.extend(sorted((ROOT / ".githooks").glob("*")))
    for path in paths:
        if path.is_file() and not path.stat().st_mode & stat.S_IXUSR:
            errors.append(f"{path.relative_to(ROOT)}: script is not executable")


def main() -> int:
    errors: list[str] = []
    files = repository_files()
    check_text_hygiene(files, errors)
    check_markdown_links(files, errors)
    check_msrv(errors)
    check_audit_version(errors)
    check_oracle_versions(errors)
    check_fuzz_tool_versions(errors)
    check_python_tool_versions(errors)
    check_proof_checker_revision(errors)
    check_integer_proof_limits(errors)
    check_required_quality_assets(errors)
    check_gate_wiring(errors)
    check_executable_scripts(errors)

    if errors:
        print("repository hygiene checks failed:", file=sys.stderr)
        for error in errors:
            print(f"  - {error}", file=sys.stderr)
        return 1

    print("repository hygiene checks passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
