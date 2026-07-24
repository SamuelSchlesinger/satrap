#!/bin/sh

set -eu

repo_root=$(git rev-parse --show-toplevel)
cd "$repo_root"

python_tool_bin=${PYTHON_TOOL_CACHE:-"$repo_root/.cache/python-tools"}/venv/bin
if [ -d "$python_tool_bin" ]; then
    PATH="$python_tool_bin:$PATH"
    export PATH
fi

required_ruff_version=0.15.22
if ! command -v ruff >/dev/null 2>&1; then
    echo "Ruff is required by the Python quality gate" >&2
    echo "run 'make install-python-tools'" >&2
    exit 1
fi
actual_ruff_version=$(ruff --version)
if [ "$actual_ruff_version" != "ruff $required_ruff_version" ]; then
    echo "Ruff $required_ruff_version is required by the Python quality gate" >&2
    echo "found: $actual_ruff_version" >&2
    exit 1
fi

ruff check --no-cache tools
ruff format --check --no-cache tools
