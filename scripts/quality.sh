#!/bin/sh

set -eu

repo_root=$(git rev-parse --show-toplevel)
cd "$repo_root"

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
"${PYTHON:-python3}" tools/check_hygiene.py
