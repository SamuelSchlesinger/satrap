#!/bin/sh

set -eu

repo_root=$(git rev-parse --show-toplevel)
cd "$repo_root"

if ! command -v cargo-audit >/dev/null 2>&1; then
    echo "cargo-audit is required by the pre-push gate" >&2
    echo "install it with: cargo install cargo-audit --locked" >&2
    exit 1
fi

cargo audit --deny warnings
