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
        self.assertEqual(
            check_hygiene.normalized_version("nightly-2026-06-01"),
            (2026, 6, 1),
        )
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

    def test_required_quality_assets_reject_missing_and_empty_corpora(self) -> None:
        directory, root = self.temporary_root()
        with directory, patch.object(check_hygiene, "ROOT", root):
            for relative in check_hygiene.REQUIRED_QUALITY_ASSETS:
                path = root / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("(check-sat)\n", encoding="utf-8")
            missing = check_hygiene.REQUIRED_QUALITY_ASSETS[0]
            empty = check_hygiene.REQUIRED_QUALITY_ASSETS[-1]
            (root / missing).unlink()
            (root / empty).write_text("", encoding="utf-8")

            errors: list[str] = []
            check_hygiene.check_required_quality_assets(errors)
            self.assertEqual(
                errors,
                [
                    f"{missing}: required quality asset is missing",
                    f"{empty}: required quality asset is empty",
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
                "actions/checkout@v6\nscripts/install-fuzz-tools.sh\n"
                "scripts/install-python-tools.sh\n"
                "scripts/install-smt-oracles.sh\nscripts/install-proof-checkers.sh\n"
                "scripts/ci.sh\nscripts/check-msrv.sh\n"
            ),
            ".github/workflows/security.yml": ("actions/checkout@v6\nscripts/check-security.sh\n"),
            "scripts/ci.sh": (
                "scripts/quality.sh\nscripts/check-fuzz.sh\nscripts/check-proofs.sh\n"
                "make smoke\nz3 --version\ncvc5 --version\n"
                "bitwuzla --version\n"
            ),
            "scripts/check-fuzz.sh": (
                "--locked\nclippy\nsmt_session_bytes\nsmt_structured_session\nsat_proof\n"
            ),
            "scripts/install-smt-oracles.sh": ("Z3Prover/z3\ncvc5/cvc5\nbitwuzla/bitwuzla\n"),
            "scripts/install-fuzz-tools.sh": (
                "--component clippy\n--component rust-src\n--component rustfmt\n"
            ),
            "scripts/install-python-tools.sh": "--require-hashes\nruff-requirements.txt\n",
            "scripts/install-proof-checkers.sh": ("marijnheule/drat-trim\ndrat_trim_sha256\n"),
            "scripts/check-proofs.sh": (
                "tools/proof_smoke.py\n--probe\n--vivify\n--subsume\n"
                "--binary-minimize\n--eliminate\n--factor\n--factor-macro\n"
                "tools/check_smt_proof.py\nbenchmarks/smt-proof-smoke\n"
            ),
            "scripts/check-python.sh": "ruff check\nruff format --check\n",
            "scripts/check-fast.sh": "scripts/check-python.sh\n",
            "scripts/quality.sh": (
                "shellcheck\nactionlint\nscripts/check-python.sh\ntools/check_hygiene.py\n"
            ),
            "Makefile": (
                "tools/benchmark.py\n--proof {proof}\n--proof-checker\n--require-unsat-proofs\n"
            ),
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
                    "scripts/ci.sh: must invoke scripts/check-fuzz.sh",
                    "scripts/ci.sh: must invoke scripts/check-proofs.sh",
                    "scripts/ci.sh: must invoke make smoke",
                    "scripts/ci.sh: must invoke z3 --version",
                    "scripts/ci.sh: must invoke cvc5 --version",
                    "scripts/ci.sh: must invoke bitwuzla --version",
                ],
            )

    def test_proof_checker_revision_check_detects_installer_drift(self) -> None:
        directory, root = self.temporary_root()
        with directory, patch.object(check_hygiene, "ROOT", root):
            gate = root / "scripts/check-proofs.sh"
            installer = root / "scripts/install-proof-checkers.sh"
            gate.parent.mkdir(parents=True)
            gate.write_text(
                "required_drat_trim_revision=2e5e29cb0019d5cfd547d4208dca1b3ec290349f\n",
                encoding="utf-8",
            )
            installer.write_text(
                "drat_trim_revision=1111111111111111111111111111111111111111\n",
                encoding="utf-8",
            )
            errors: list[str] = []
            check_hygiene.check_proof_checker_revision(errors)
            self.assertEqual(
                errors,
                [
                    "DRAT-trim revisions disagree: "
                    "scripts/check-proofs.sh="
                    "2e5e29cb0019d5cfd547d4208dca1b3ec290349f, "
                    "scripts/install-proof-checkers.sh="
                    "1111111111111111111111111111111111111111"
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

    def test_oracle_version_check_detects_installer_drift(self) -> None:
        directory, root = self.temporary_root()
        with directory, patch.object(check_hygiene, "ROOT", root):
            script = root / "scripts/ci.sh"
            installer = root / "scripts/install-smt-oracles.sh"
            script.parent.mkdir(parents=True)
            script.write_text(
                "required_z3_version=4.16.0\n"
                "required_cvc5_version=1.3.3\n"
                "required_bitwuzla_version=0.9.1\n",
                encoding="utf-8",
            )
            installer.write_text(
                "z3_version=4.15.8\ncvc5_version=1.3.3\nbitwuzla_version=0.9.1\n",
                encoding="utf-8",
            )
            errors: list[str] = []
            check_hygiene.check_oracle_versions(errors)
            self.assertEqual(
                errors,
                [
                    "Z3 versions disagree: "
                    "scripts/ci.sh=4.16.0, "
                    "scripts/install-smt-oracles.sh=4.15.8"
                ],
            )

    def test_fuzz_tool_version_check_detects_nightly_drift(self) -> None:
        directory, root = self.temporary_root()
        with directory, patch.object(check_hygiene, "ROOT", root):
            gate = root / "scripts/check-fuzz.sh"
            installer = root / "scripts/install-fuzz-tools.sh"
            gate.parent.mkdir(parents=True)
            gate.write_text(
                "fuzz_nightly=nightly-2026-06-01\nrequired_cargo_fuzz_version=0.13.2\n",
                encoding="utf-8",
            )
            installer.write_text(
                "fuzz_nightly=nightly-2026-05-01\ncargo_fuzz_version=0.13.2\n",
                encoding="utf-8",
            )
            errors: list[str] = []
            check_hygiene.check_fuzz_tool_versions(errors)
            self.assertEqual(
                errors,
                [
                    "fuzz nightly versions disagree: "
                    "scripts/check-fuzz.sh=2026.6.1, "
                    "scripts/install-fuzz-tools.sh=2026.5.1"
                ],
            )

    def test_python_tool_version_check_detects_installer_drift(self) -> None:
        directory, root = self.temporary_root()
        with directory, patch.object(check_hygiene, "ROOT", root):
            gate = root / "scripts/check-python.sh"
            installer = root / "scripts/install-python-tools.sh"
            requirements = root / "scripts/ruff-requirements.txt"
            gate.parent.mkdir(parents=True)
            gate.write_text("required_ruff_version=0.15.22\n", encoding="utf-8")
            installer.write_text("ruff_version=0.15.21\n", encoding="utf-8")
            requirements.write_text("ruff==0.15.22\n", encoding="utf-8")
            errors: list[str] = []
            check_hygiene.check_python_tool_versions(errors)
            self.assertEqual(
                errors,
                [
                    "Ruff versions disagree: "
                    "scripts/check-python.sh=0.15.22, "
                    "scripts/install-python-tools.sh=0.15.21, "
                    "scripts/ruff-requirements.txt=0.15.22"
                ],
            )


if __name__ == "__main__":
    unittest.main()
