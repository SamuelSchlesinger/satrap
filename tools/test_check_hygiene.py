from __future__ import annotations

import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import check_hygiene


class HygieneChecksTests(unittest.TestCase):
    def temporary_root(self) -> tuple[tempfile.TemporaryDirectory[str], Path]:
        directory = tempfile.TemporaryDirectory()
        return directory, Path(directory.name)

    def test_normalizes_two_and_three_component_versions(self) -> None:
        self.assertEqual(check_hygiene.normalized_version("Rust 1.85"), (1, 85, 0))
        self.assertEqual(check_hygiene.normalized_version("+1.85.0"), (1, 85, 0))
        self.assertIsNone(check_hygiene.normalized_version("stable"))

    def test_markdown_check_ignores_external_anchor_and_fenced_links(self) -> None:
        directory, root = self.temporary_root()
        with directory, patch.object(check_hygiene, "ROOT", root):
            (root / "present.md").write_text("# Present\n", encoding="utf-8")
            source = root / "README.md"
            source.write_text(
                "\n".join(
                    [
                        "[present](present.md)",
                        "[anchor](#section)",
                        "[external](https://example.com)",
                        "```md",
                        "[example](not-a-real-file.md)",
                        "```",
                        "[missing](missing.md)",
                        "",
                    ]
                ),
                encoding="utf-8",
            )
            errors: list[str] = []
            check_hygiene.check_markdown_links([source], errors)
            self.assertEqual(
                errors,
                ["README.md:7: broken local link 'missing.md'"],
            )

    def test_markdown_check_rejects_links_outside_repository(self) -> None:
        directory, root = self.temporary_root()
        with directory, patch.object(check_hygiene, "ROOT", root):
            source = root / "README.md"
            source.write_text("[outside](../outside.md)\n", encoding="utf-8")
            errors: list[str] = []
            check_hygiene.check_markdown_links([source], errors)
            self.assertEqual(
                errors,
                ["README.md:1: local link leaves repository '../outside.md'"],
            )

    def test_text_check_reports_line_end_and_whitespace_defects(self) -> None:
        directory, root = self.temporary_root()
        with directory, patch.object(check_hygiene, "ROOT", root):
            source = root / "bad.txt"
            source.write_bytes(b"trailing \r\nno-final-newline")
            errors: list[str] = []
            check_hygiene.check_text_hygiene([source], errors)
            self.assertEqual(
                errors,
                [
                    "bad.txt: missing final newline",
                    "bad.txt: carriage return found; use LF line endings",
                    "bad.txt:1: trailing whitespace",
                ],
            )

    def test_gate_wiring_detects_a_disconnected_quality_gate(self) -> None:
        directory, root = self.temporary_root()
        files = {
            ".githooks/pre-commit": "scripts/check-fast.sh\n",
            ".githooks/pre-push": (
                "scripts/ci.sh\nscripts/check-msrv.sh\nscripts/check-security.sh\n"
            ),
            ".github/workflows/ci.yml": (
                "actions/checkout@v6\nz3\nscripts/ci.sh\nscripts/check-msrv.sh\n"
            ),
            ".github/workflows/security.yml": (
                "actions/checkout@v6\nscripts/check-security.sh\n"
            ),
            "scripts/ci.sh": "scripts/quality.sh\nz3 --version\n",
            "scripts/quality.sh": "shellcheck\nactionlint\ntools/check_hygiene.py\n",
        }
        with directory, patch.object(check_hygiene, "ROOT", root):
            for relative, contents in files.items():
                path = root / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(contents, encoding="utf-8")

            errors: list[str] = []
            check_hygiene.check_gate_wiring(errors)
            self.assertEqual(errors, [])

            (root / "scripts/ci.sh").write_text("# disconnected\n", encoding="utf-8")
            check_hygiene.check_gate_wiring(errors)
            self.assertEqual(
                errors,
                [
                    "scripts/ci.sh: must invoke scripts/quality.sh",
                    "scripts/ci.sh: must invoke z3 --version",
                ],
            )

    def test_audit_version_check_detects_ci_drift(self) -> None:
        directory, root = self.temporary_root()
        with directory, patch.object(check_hygiene, "ROOT", root):
            script = root / "scripts/check-security.sh"
            workflow = root / ".github/workflows/security.yml"
            script.parent.mkdir(parents=True)
            workflow.parent.mkdir(parents=True)
            script.write_text("required_version=0.22.2\n", encoding="utf-8")
            workflow.write_text(
                "run: cargo install cargo-audit --version 0.22.1 --locked\n",
                encoding="utf-8",
            )
            errors: list[str] = []
            check_hygiene.check_audit_version(errors)
            self.assertEqual(
                errors,
                [
                    "cargo-audit versions disagree: "
                    "scripts/check-security.sh=0.22.2, "
                    ".github/workflows/security.yml=0.22.1"
                ],
            )

    def test_z3_version_check_detects_ci_drift(self) -> None:
        directory, root = self.temporary_root()
        with directory, patch.object(check_hygiene, "ROOT", root):
            script = root / "scripts/ci.sh"
            workflow = root / ".github/workflows/ci.yml"
            script.parent.mkdir(parents=True)
            workflow.parent.mkdir(parents=True)
            script.write_text("required_z3_version=4.16.0\n", encoding="utf-8")
            workflow.write_text('env:\n  Z3_VERSION: "4.15.8"\n', encoding="utf-8")
            errors: list[str] = []
            check_hygiene.check_z3_version(errors)
            self.assertEqual(
                errors,
                [
                    "Z3 versions disagree: "
                    "scripts/ci.sh=4.16.0, "
                    ".github/workflows/ci.yml=4.15.8"
                ],
            )


if __name__ == "__main__":
    unittest.main()
