from __future__ import annotations

import os
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PRE_PUSH = ROOT / "scripts" / "pre-push.sh"


class PrePushTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary_directory = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary_directory.name)
        self.repo = self.root / "repo"
        self.repo.mkdir()
        self.run_git("init", "--quiet")
        self.run_git("config", "user.email", "quality@example.invalid")
        self.run_git("config", "user.name", "Quality Gate")

        scripts = self.repo / "scripts"
        scripts.mkdir()
        shutil.copyfile(PRE_PUSH, scripts / "pre-push.sh")
        (scripts / "pre-push.sh").chmod(0o755)
        for name in ("ci.sh", "check-msrv.sh", "check-security.sh"):
            gate = scripts / name
            gate.write_text(
                "#!/bin/sh\n"
                "set -eu\n"
                'name=$(basename "$0")\n'
                'printf "%s\\n" "$name" >> "$PRE_PUSH_TEST_LOG"\n'
                'if [ "${PRE_PUSH_TEST_FAIL:-}" = "$name" ]; then\n'
                "    exit 42\n"
                "fi\n",
                encoding="utf-8",
            )
            gate.chmod(0o755)

        (self.repo / "tracked.txt").write_text("initial\n", encoding="utf-8")
        self.run_git("add", ".")
        self.run_git("commit", "--quiet", "-m", "initial")
        self.head = self.git_output("rev-parse", "HEAD")
        self.log = self.root / "gates.log"

    def tearDown(self) -> None:
        self.temporary_directory.cleanup()

    def run_git(self, *arguments: str) -> None:
        subprocess.run(
            ["git", *arguments],
            cwd=self.repo,
            check=True,
            capture_output=True,
            text=True,
        )

    def git_output(self, *arguments: str) -> str:
        result = subprocess.run(
            ["git", *arguments],
            cwd=self.repo,
            check=True,
            capture_output=True,
            text=True,
        )
        return result.stdout.strip()

    def run_pre_push(
        self,
        local_oid: str | None = None,
        *,
        fail_gate: str | None = None,
    ) -> subprocess.CompletedProcess[str]:
        oid = local_oid or self.head
        environment = os.environ.copy()
        environment["PRE_PUSH_TEST_LOG"] = str(self.log)
        if fail_gate is not None:
            environment["PRE_PUSH_TEST_FAIL"] = fail_gate
        return subprocess.run(
            [self.repo / "scripts" / "pre-push.sh"],
            cwd=self.repo,
            input=f"refs/heads/main {oid} refs/heads/main {'0' * 40}\n",
            capture_output=True,
            text=True,
            env=environment,
            check=False,
        )

    def test_runs_every_gate_for_the_exact_clean_head(self) -> None:
        result = self.run_pre_push()

        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(
            self.log.read_text(encoding="utf-8").splitlines(),
            ["ci.sh", "check-msrv.sh", "check-security.sh"],
        )

    def test_rejects_a_dirty_checkout_before_running_gates(self) -> None:
        (self.repo / "tracked.txt").write_text("uncommitted\n", encoding="utf-8")

        result = self.run_pre_push()

        self.assertNotEqual(result.returncode, 0)
        self.assertIn("index and worktree must be clean", result.stderr)
        self.assertFalse(self.log.exists())

    def test_rejects_a_ref_other_than_the_tested_head(self) -> None:
        old_head = self.head
        (self.repo / "tracked.txt").write_text("second\n", encoding="utf-8")
        self.run_git("add", "tracked.txt")
        self.run_git("commit", "--quiet", "-m", "second")
        self.head = self.git_output("rev-parse", "HEAD")

        result = self.run_pre_push(old_head)

        self.assertNotEqual(result.returncode, 0)
        self.assertIn("gates are bound to checked-out HEAD", result.stderr)
        self.assertFalse(self.log.exists())

    def test_stops_at_the_first_failing_gate(self) -> None:
        result = self.run_pre_push(fail_gate="check-msrv.sh")

        self.assertEqual(result.returncode, 42)
        self.assertEqual(
            self.log.read_text(encoding="utf-8").splitlines(),
            ["ci.sh", "check-msrv.sh"],
        )
