#!/usr/bin/env bash
# Tier 1: the commit-on-main guard can fail. In a scratch repo with the hook installed, a commit on main is refused and a commit on a
# branch is allowed.
set -euo pipefail
cd "$(dirname "$0")/.."
# Hermetic git: ignore any ambient config (GIT_CONFIG_COUNT/KEY_n/VALUE_n, global, system) so the gate means the same for everyone.
for v in $(env | sed -n 's/^\(GIT_CONFIG_[A-Z]*_*[0-9]*\)=.*/\1/p'); do unset "$v"; done
export GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_SYSTEM=/dev/null GIT_CONFIG_NOSYSTEM=1
hook=$(pwd)/scripts/githooks
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
git init -q -b main "$T/r"; cd "$T/r"; git config user.email t@t; git config user.name t; git config core.hooksPath "$hook"
echo a > a; git add a
if git commit -qm "on main" 2>/dev/null; then echo "tier1: githook: a commit on main was allowed" >&2; exit 1; fi
git switch -q -c feature; git commit -qm "on a branch" || { echo "tier1: githook: a commit on a branch was refused" >&2; exit 1; }
cd - >/dev/null
# Whether THIS clone has the hook configured is a developer convenience (git config core.hooksPath scripts/githooks), not a gate: the lander never commits on main either.
echo "githook: a commit on main is refused, a commit on a branch is allowed: ok"
