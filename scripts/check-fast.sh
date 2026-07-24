#!/bin/sh

set -eu

repo_root=$(git rev-parse --show-toplevel)
cd "$repo_root"

cargo fmt --all -- --check
cargo check --all-targets --all-features
