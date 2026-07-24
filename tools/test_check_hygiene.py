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


if __name__ == "__main__":
    unittest.main()
