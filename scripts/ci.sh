#!/bin/sh

set -eu

repo_root=$(git rev-parse --show-toplevel)
cd "$repo_root"

cargo fmt --all -- --check
cargo clippy --all-targets --all-features -- -D warnings
cargo test --all-targets
"${PYTHON:-python3}" -m unittest discover -s tools -p 'test_*.py'
cargo build --release
