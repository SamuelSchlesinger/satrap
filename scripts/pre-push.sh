#!/bin/sh

set -eu

repo_root=$(git rev-parse --show-toplevel)
cd "$repo_root"

tested_oid=$(git rev-parse --verify HEAD)

require_exact_tested_state() {
    current_oid=$(git rev-parse --verify HEAD)
    if [ "$current_oid" != "$tested_oid" ]; then
        echo "pre-push: HEAD changed while the quality gates were running" >&2
        echo "pre-push: commit the intended state and push again" >&2
        exit 1
    fi

    if [ -n "$(git status --porcelain=v1 --untracked-files=all)" ]; then
        echo "pre-push: the index and worktree must be clean" >&2
        echo "pre-push: commit or remove every non-ignored change before pushing" >&2
        exit 1
    fi
}

require_exact_tested_state

has_content_update=false
while read -r local_ref local_oid remote_ref _remote_oid; do
    [ -n "$local_ref" ] || continue

    case "$local_oid" in
        *[!0]*) ;;
        *) continue ;;
    esac

    if ! pushed_oid=$(git rev-parse --verify "${local_oid}^{commit}" 2>/dev/null); then
        echo "pre-push: $local_ref does not resolve to a commit" >&2
        exit 1
    fi
    if [ "$pushed_oid" != "$tested_oid" ]; then
        echo "pre-push: $local_ref -> $remote_ref would push $pushed_oid" >&2
        echo "pre-push: the gates are bound to checked-out HEAD $tested_oid" >&2
        echo "pre-push: check out the commit being pushed and try again" >&2
        exit 1
    fi
    has_content_update=true
done

# A deletion-only or already-up-to-date push publishes no source state.
if [ "$has_content_update" = false ]; then
    exit 0
fi

"$repo_root/scripts/ci.sh"
"$repo_root/scripts/check-msrv.sh"
"$repo_root/scripts/check-security.sh"

# A gate must not rewrite tracked or untracked source, and a concurrent commit
# must not make the tested revision differ from the revision Git will publish.
require_exact_tested_state
