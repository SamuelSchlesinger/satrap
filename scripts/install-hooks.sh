#!/bin/sh

set -eu

repo_root=$(git rev-parse --show-toplevel)
cd "$repo_root"

git config --local core.hooksPath .githooks
echo "Installed repository hooks from .githooks"

if ! command -v cargo-audit >/dev/null 2>&1; then
    echo "Install cargo-audit before pushing: cargo install cargo-audit --locked" >&2
fi
