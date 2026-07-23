#!/usr/bin/env python3
"""Select a deterministic, family-disjoint held-out slice from a GBD database."""

from __future__ import annotations

import argparse
import hashlib
import json
import sqlite3
import sys
from collections import Counter
from pathlib import Path


DEFAULT_SEED = "sat-rs-main-2025-heldout-v1"


def parse_arguments() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--database", required=True, type=Path)
    parser.add_argument("--track", default="main_2025")
    parser.add_argument("--seed", default=DEFAULT_SEED)
    parser.add_argument("--sat", type=int, default=6)
    parser.add_argument("--unsat", type=int, default=6)
    parser.add_argument("--unknown", type=int, default=4)
    parser.add_argument(
        "--exclude-manifest",
        action="append",
        default=[],
        type=Path,
        help="exclude every database ID and family present in this manifest",
    )
    return parser.parse_args()


def sha256_path(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def excluded_values(manifests: list[Path]) -> tuple[set[str], set[str]]:
    ids: set[str] = set()
    families: set[str] = set()
    for path in manifests:
        document = json.loads(path.read_text(encoding="utf-8"))
        for instance in document["instances"]:
            ids.add(str(instance["database_id"]))
            families.add(str(instance["family"]))
    return ids, families


def database_rows(database: Path, track: str) -> list[dict[str, str]]:
    connection = sqlite3.connect(f"file:{database}?mode=ro", uri=True)
    try:
        rows = connection.execute(
            """
            SELECT f.hash, f.family, lower(f.result), min(n.value)
            FROM features AS f
            JOIN track AS t ON t.hash = f.hash
            LEFT JOIN filename AS n ON n.hash = f.hash
            WHERE t.value = ?
            GROUP BY f.hash, f.family, f.result
            """,
            (track,),
        )
        return [
            {
                "database_id": str(database_id),
                "family": str(family),
                "expected_status": str(result).upper(),
                "source_name": str(filename),
            }
            for database_id, family, result, filename in rows
        ]
    finally:
        connection.close()


def score(seed: str, instance: dict[str, str]) -> str:
    fields = (
        seed,
        instance["database_id"],
        instance["family"],
        instance["expected_status"],
    )
    return hashlib.sha256("\0".join(fields).encode("utf-8")).hexdigest()


def select(
    rows: list[dict[str, str]],
    seed: str,
    quotas: Counter[str],
    excluded_ids: set[str],
    excluded_families: set[str],
) -> list[dict[str, str]]:
    selected: list[dict[str, str]] = []
    used_families = set(excluded_families)
    for instance in sorted(rows, key=lambda item: (score(seed, item), item["database_id"])):
        status = instance["expected_status"]
        if (
            quotas[status] <= 0
            or instance["database_id"] in excluded_ids
            or instance["family"] in used_families
        ):
            continue
        selected.append(
            {
                **instance,
                "selection_sha256": score(seed, instance),
                "url": f"https://benchmark-database.de/file/{instance['database_id']}",
            }
        )
        quotas[status] -= 1
        used_families.add(instance["family"])
        if not any(quotas.values()):
            break

    missing = {status: count for status, count in quotas.items() if count}
    if missing:
        raise ValueError(f"could not fill quotas: {missing}")
    return sorted(selected, key=lambda instance: instance["database_id"])


def main() -> int:
    arguments = parse_arguments()
    try:
        requested = Counter(
            {"SAT": arguments.sat, "UNSAT": arguments.unsat, "UNKNOWN": arguments.unknown}
        )
        if any(count < 0 for count in requested.values()):
            raise ValueError("quotas must be non-negative")
        excluded_ids, excluded_families = excluded_values(arguments.exclude_manifest)
        instances = select(
            database_rows(arguments.database, arguments.track),
            arguments.seed,
            requested.copy(),
            excluded_ids,
            excluded_families,
        )
        document = {
            "schema": 1,
            "name": "satcomp-2025-heldout-selection",
            "role": "held-out",
            "source": "https://benchmark-database.de/?context=cnf&track=main_2025",
            "metadata_sha256": sha256_path(arguments.database),
            "track": arguments.track,
            "seed": arguments.seed,
            "selection_rule": (
                "Sort by SHA-256(seed NUL database_id NUL family NUL status); "
                "greedily fill the SAT, UNSAT, and UNKNOWN quotas while using each family "
                "once and excluding IDs and families in the supplied manifests."
            ),
            "excluded_manifests": [str(path) for path in arguments.exclude_manifest],
            "requested": {
                "SAT": arguments.sat,
                "UNSAT": arguments.unsat,
                "UNKNOWN": arguments.unknown,
            },
            "instances": instances,
        }
        json.dump(document, sys.stdout, indent=2)
        print()
    except (json.JSONDecodeError, KeyError, OSError, sqlite3.Error, ValueError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
