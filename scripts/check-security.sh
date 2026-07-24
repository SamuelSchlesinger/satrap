#!/bin/sh

set -eu

repo_root=$(git rev-parse --show-toplevel)
cd "$repo_root"

required_version=0.22.2

if ! command -v cargo-audit >/dev/null 2>&1; then
    echo "cargo-audit is required by the pre-push gate" >&2
    echo "install it with: cargo install cargo-audit --version $required_version --locked" >&2
    exit 1
fi

installed_version=$(cargo audit --version | awk '{print $2}')
if [ "$installed_version" != "$required_version" ]; then
    echo "cargo-audit $required_version is required; found $installed_version" >&2
    echo "install it with: cargo install cargo-audit --version $required_version --locked" >&2
    exit 1
fi

cargo audit --deny warnings
