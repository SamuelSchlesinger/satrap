#!/bin/sh

set -eu

repo_root=$(git rev-parse --show-toplevel)
cache_root=${PYTHON_TOOL_CACHE:-"$repo_root/.cache/python-tools"}
venv_root="$cache_root/venv"
python=${PYTHON:-python3}
ruff_version=0.15.22

if ! command -v "$python" >/dev/null 2>&1; then
    echo "$python is required to install the Python quality tools" >&2
    exit 1
fi

"$python" -m venv "$venv_root"
"$venv_root/bin/python" -m pip install \
    --disable-pip-version-check \
    --no-deps \
    --only-binary=:all: \
    --require-hashes \
    --requirement "$repo_root/scripts/ruff-requirements.txt"

actual_version=$("$venv_root/bin/ruff" --version)
if [ "$actual_version" != "ruff $ruff_version" ]; then
    echo "installed Ruff version does not match $ruff_version" >&2
    echo "found: $actual_version" >&2
    exit 1
fi

echo "Installed Ruff $ruff_version in $venv_root"
