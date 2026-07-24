#!/bin/sh

set -eu

repo_root=$(git rev-parse --show-toplevel)
cd "$repo_root"

"$repo_root/scripts/quality.sh"

if ! command -v z3 >/dev/null 2>&1; then
    echo "z3 is required by the integration gate" >&2
    exit 1
fi
z3 --version

cargo test --all-targets --locked
"${PYTHON:-python3}" -m unittest discover -s tools -p 'test_*.py'
cargo build --release --locked
