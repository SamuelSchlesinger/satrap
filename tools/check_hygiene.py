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
VERSION = re.compile(r"\d+(?:\.\d+){1,2}")


def repository_files() -> list[Path]:
    """Return checked-in and not-ignored new files, including staged additions."""
    result = subprocess.run(
        ["git", "ls-files", "--cached", "--others", "--exclude-standard", "-z"],
        cwd=ROOT,
        check=True,
        capture_output=True,
    )
    return [
        ROOT / Path(raw.decode("utf-8"))
        for raw in result.stdout.split(b"\0")
        if raw
    ]


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
                    errors.append(
                        f"{relative}:{line_number}: broken local link {target!r}"
                    )


def normalized_version(value: str) -> tuple[int, int, int] | None:
    match = VERSION.search(value)
    if match is None:
        return None
    parts = tuple(int(part) for part in match.group(0).split("."))
    return (parts + (0, 0, 0))[:3]


def extract_version(path: Path, pattern: str, errors: list[str]) -> tuple[int, int, int] | None:
    text = read_text(path, errors)
    if text is None:
        return None
    match = re.search(pattern, text, flags=re.MULTILINE)
    if match is None:
        errors.append(f"{path.relative_to(ROOT)}: MSRV declaration not found")
        return None
    version = normalized_version(match.group(1))
    if version is None:
        errors.append(f"{path.relative_to(ROOT)}: invalid MSRV declaration")
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


def require_commands(path: Path, commands: tuple[str, ...], errors: list[str]) -> None:
    text = read_text(path, errors)
    if text is None:
        return
    for command in commands:
        if command not in text:
            errors.append(f"{path.relative_to(ROOT)}: must invoke {command}")


def check_gate_wiring(errors: list[str]) -> None:
    require_commands(
        ROOT / ".githooks/pre-commit",
        ("scripts/check-fast.sh",),
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
        ("scripts/quality.sh",),
        errors,
    )
    require_commands(
        ROOT / ".github/workflows/security.yml",
        ("rustsec/audit-check@v2.0.0",),
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
