#!/bin/sh

set -eu

repo_root=$(git rev-parse --show-toplevel)
cd "$repo_root"

"$repo_root/scripts/quality.sh"
cargo test --all-targets --locked
"${PYTHON:-python3}" -m unittest discover -s tools -p 'test_*.py'
cargo build --release --locked
