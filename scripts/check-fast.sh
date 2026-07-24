#!/bin/sh

set -eu

repo_root=$(git rev-parse --show-toplevel)
cd "$repo_root"

cargo fmt --all -- --check
cargo check --all-targets --all-features --locked
sh -n scripts/*.sh .githooks/*
"$repo_root/scripts/check-python.sh"
"${PYTHON:-python3}" tools/check_hygiene.py
