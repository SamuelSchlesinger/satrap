#!/bin/sh

set -eu

repo_root=$(git rev-parse --show-toplevel)
cd "$repo_root"
required_z3_version=4.16.0

"$repo_root/scripts/quality.sh"

if ! command -v z3 >/dev/null 2>&1; then
    echo "z3 is required by the integration gate" >&2
    exit 1
fi
actual_z3_version=$(z3 --version)
case "$actual_z3_version" in
    "Z3 version $required_z3_version"*) ;;
    *)
        echo "z3 $required_z3_version is required by the integration gate" >&2
        echo "found: $actual_z3_version" >&2
        exit 1
        ;;
esac
echo "$actual_z3_version"

cargo test --all-targets --locked
"${PYTHON:-python3}" -m unittest discover -s tools -p 'test_*.py'
cargo build --release --locked
