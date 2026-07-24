#!/bin/sh

set -eu

repo_root=$(git rev-parse --show-toplevel)
cd "$repo_root"

for tool in shellcheck actionlint; do
    if ! command -v "$tool" >/dev/null 2>&1; then
        echo "$tool is required by the quality gate" >&2
        exit 1
    fi
done

# Keep the manifest, lockfile, code, documentation, and repository policy in
# agreement. Tests and optimized builds belong to scripts/ci.sh.
cargo metadata --locked --no-deps --format-version 1 >/dev/null
cargo fmt --all -- --check
cargo clippy --all-targets --all-features --locked -- -D warnings
RUSTDOCFLAGS="-D warnings" cargo doc \
    --all-features \
    --document-private-items \
    --locked \
    --no-deps
sh -n scripts/*.sh .githooks/*
shellcheck scripts/*.sh .githooks/*
actionlint .github/workflows/*.yml
"$repo_root/scripts/check-python.sh"
"${PYTHON:-python3}" tools/check_hygiene.py
