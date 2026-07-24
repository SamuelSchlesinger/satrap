#!/usr/bin/env python3
"""Fetch and verify a manifest-defined benchmark development corpus."""

from __future__ import annotations

import argparse
import hashlib
import json
import lzma
import os
import shutil
import sys
import tempfile
import urllib.request
from pathlib import Path
from typing import BinaryIO


def parse_arguments() -> argparse.Namespace:
    root = Path(__file__).resolve().parent.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--manifest",
        type=Path,
        default=root / "benchmarks/manifests/satcomp-2025-development.json",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=root / "benchmarks/downloaded/satcomp-2025-development",
    )
    return parser.parse_args()


def sha256_path(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def verified(path: Path, expected_size: int, expected_hash: str) -> bool:
    return (
        path.is_file()
        and path.stat().st_size == expected_size
        and sha256_path(path) == expected_hash
    )


def temporary_file(directory: Path, suffix: str) -> tuple[Path, BinaryIO]:
    descriptor, name = tempfile.mkstemp(prefix=".download-", suffix=suffix, dir=directory)
    return Path(name), os.fdopen(descriptor, "wb")


def fetch(instance: dict[str, object], output: Path) -> None:
    compressed = output / str(instance["compressed_name"])
    cnf = output / str(instance["cnf_name"])
    if verified(cnf, int(instance["cnf_bytes"]), str(instance["cnf_sha256"])):
        print(f"verified {cnf.name}")
        return

    if compressed.exists() and not verified(
        compressed,
        int(instance["compressed_bytes"]),
        str(instance["compressed_sha256"]),
    ):
        raise ValueError(f"existing compressed file does not match manifest: {compressed}")

    if not compressed.exists():
        temporary, destination = temporary_file(output, ".xz")
        try:
            print(f"downloading {instance['url']}")
            request = urllib.request.Request(
                str(instance["url"]),
                headers={"User-Agent": "sat-research-corpus-fetcher/1"},
            )
            with urllib.request.urlopen(request) as source, destination:
                shutil.copyfileobj(source, destination)
            if not verified(
                temporary,
                int(instance["compressed_bytes"]),
                str(instance["compressed_sha256"]),
            ):
                raise ValueError(f"downloaded file failed verification: {instance['url']}")
            os.replace(temporary, compressed)
        finally:
            temporary.unlink(missing_ok=True)

    temporary, destination = temporary_file(output, ".cnf")
    try:
        with lzma.open(compressed, "rb") as source, destination:
            shutil.copyfileobj(source, destination)
        if not verified(
            temporary,
            int(instance["cnf_bytes"]),
            str(instance["cnf_sha256"]),
        ):
            raise ValueError(f"decompressed file failed verification: {cnf.name}")
        os.replace(temporary, cnf)
        print(f"ready {cnf.name}")
    finally:
        temporary.unlink(missing_ok=True)


def main() -> int:
    arguments = parse_arguments()
    try:
        manifest = json.loads(arguments.manifest.read_text(encoding="utf-8"))
        if manifest.get("schema") != 1:
            raise ValueError("unsupported manifest schema")
        arguments.output.mkdir(parents=True, exist_ok=True)
        for instance in manifest["instances"]:
            fetch(instance, arguments.output)
    except (KeyError, OSError, ValueError, lzma.LZMAError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
