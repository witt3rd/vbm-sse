#!/usr/bin/env bash
# Tier 1: scripts/land-direct (docs/decisions/0002-land-direct.md) is a pinned copy of vbm-land plus this repository's scripts/land.conf and scripts/land.d/ hooks. The lander's own
# behaviour (rebase, the retry loop, plain push, bounded steps, hold, freeze, regeneration, hooks, exit codes) is tested in vbm-land against every release; THIS test
# is about what this repository adds and depends on, with the REAL stub, config and hooks in a scratch repository (a local bare remote, a mise shim, stand-in gates):
#  the vendored copy is intact (scripts/land/bin/land-check) and a tampered copy, a stray file and an edited stub each FAIL the check and are refused by the lander (12); a commit lands as itself
#  (no branch, no PR, linear, one JSON line with specified_share); a conflicting rebase aborts naming the file; a baseline conflict regenerates by itself and a worsening one stops (12); a failing
#  Tier 1 lands nothing; the hold marker stops it; a bad subject and a production diff over 150 lines without
#  a Diff-Budget trailer stop; the gate-diff judge (main's copy: a change cannot replace it) refuses with 12; the relabel-attack suite runs exactly when a gate-defining file is touched and refuses with 12.
#  Negative self-test: the no-force scan is shown to catch a force push in a fixture.
export LC_ALL=C
set -euo pipefail
cd "$(dirname "$0")/.."
. scripts/lib-ran.sh   # ran_case counts each executed check, ran_done prints the evidence line `ran: NAME: N cases` (docs/decisions/0002-ran-evidence.md)
src=$(pwd)
fail() { echo "tier1: land-direct: $*" >&2; exit 1; }
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT; export T
# 0. the vendored copy is what its pin says; the check can fail (a tampered file, a stray file, an edited stub, an unpinned hook name); no force or delete push in anything that pushes
scripts/land/bin/land-check >/dev/null && ran_case || fail "the vendored copy of vbm-land differs from its pin (scripts/land/bin/land-check): edit vbm-land, not the copy"
for tamper in "echo '# local patch' >> scripts/land/bin/land-revert" "echo x > scripts/land/lib/stray.sh" "echo 'exit 0' > scripts/land-direct" "rm scripts/land/lib/infra-re.sh" "echo ':' > scripts/land.d/post-rebasee; chmod +x scripts/land.d/post-rebasee"; do
  rm -rf "$T/v"; mkdir -p "$T/v/scripts"; cp -a scripts/land scripts/land-direct scripts/land.conf scripts/land.d "$T/v/scripts/"; cp -a .agents "$T/v/"; ( cd "$T/v" && bash -c "$tamper" )
  if "$T/v/scripts/land/bin/land-check" --root "$T/v" >/dev/null 2>&1; then fail "negative self-test: land-check passes a tampered copy ($tamper)"; fi
done
[ ! -e scripts/infra-re.sh ] && ran_case || fail "scripts/infra-re.sh exists: the one infrastructure classifier is the pinned scripts/land/lib/infra-re.sh (a second copy is how the landers drifted apart)"
noforce() { grep -v '^[[:space:]]*#' "$1" | grep -E -- '--force|--mirror|--delete|push[^|;&]* -f |push[^|;&]* \+|push[^|;&]* :' || true; }
[ -z "$(noforce scripts/land/bin/land-direct)" ] && ran_case || fail "the vendored lander contains a force/delete push: $(noforce scripts/land/bin/land-direct)"
printf 'git push --force-with-lease origin x\n' > "$T/forced.sh"; [ -n "$(noforce "$T/forced.sh")" ] && ran_case || fail "negative self-test: the no-force scan missed a force push"
export GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_SYSTEM=/dev/null GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@t GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@t
# shims: mise (runs what follows `--`)
mkdir -p "$T/bin"; printf '#!/bin/sh\n[ "$1" = exec ] && shift; [ "$1" = -- ] && shift; exec "$@"\n' > "$T/bin/mise"
chmod +x "$T/bin/mise"; export PATH="$T/bin:$PATH"
git init -q --bare -b main "$T/remote.git"; git -C "$T/remote.git" config receive.denyNonFastForwards true
printf '#!/bin/sh\necho "$1 $2 $3" >> "$T/updates"\n' > "$T/remote.git/hooks/update"; chmod +x "$T/remote.git/hooks/update"
git clone -q "$T/remote.git" "$T/work" 2>/dev/null; cd "$T/work"; git config core.hooksPath /dev/null
git clone -q "$T/remote.git" "$T/other" 2>/dev/null; git -C "$T/other" config core.hooksPath /dev/null
# the scratch repository: this repository's REAL landing files, and stand-ins for the gates the hooks call
mkdir -p scripts; cp -a "$src/scripts/land" "$src/scripts/land-direct" "$src/scripts/land.conf" "$src/scripts/land.d" scripts/; cp -a "$src/.agents" .
sed -i '/^LAND_PROTECTED_LIST=/d' scripts/land.conf   # the lander-mechanics fixture has stand-in gates and no protected-paths list of its own: the list rule is judged on the real repository, not here
sed -i 's/^LAND_STEP_TIMEOUT=.*/LAND_STEP_TIMEOUT=120/' scripts/land.conf
cat > scripts/tier1.sh <<'SH'
test ! -e BAD || { echo "BAD exists" >&2; exit 1; }
echo "closure gate: spec 4 | boundary 0 | unverified 1 | total 5 | specified share 80.00% (floor 80.00%)"
SH
cat > scripts/regen-baselines.sh <<'SH'
for m in m1 m2 m3; do cur=$(cat $m); old=$(awk -v k=$m '$1==k{print $2}' base.txt); [ "$cur" -le "$old" ] || exit 3; done
for m in m1 m2 m3; do echo "$m $(cat $m)"; done > base.txt
SH
cat > scripts/gate-diff-improving.sh <<'SH'
case $1 in --touched) cat "$T/touched" 2>/dev/null || true;; --suite-judged) echo "FAIL scripts/tier1.sh: stand-in"; exit "$(cat "$T/gdrc" 2>/dev/null || echo 0)";; esac
SH
printf 'echo "$*" >> "$T/relabel.calls"; echo "stand-in attack output"; exit "$(cat "$T/relabelrc" 2>/dev/null || echo 0)"\n' > scripts/relabel-attacks.sh
printf 'exit "$(cat "$T/prc" 2>/dev/null || echo 0)"\n' > scripts/protected-set.sh
chmod +x scripts/*.sh
printf '10\n' > m1; printf '10\n' > m2; printf '10\n' > m3; printf 'm1 10\nm2 10\nm3 10\n' > base.txt; printf 'line1\nline2\nline3\n' > code.txt
printf '# generated\nbase.txt\n' > scripts/generated-paths.txt
cm() { git add -A; git commit -qm "${2:-feat(test): $1}"; }
cmo() { git -C "$T/other" add -A; git -C "$T/other" commit -qm "feat(test): $1"; }
cm base "chore(test): base"; git push -q origin HEAD:main; git -C "$T/other" pull -q origin main
land=$(pwd)/scripts/land-direct
sync() { git fetch -q origin; git checkout -q -B "$1" origin/main; }
run() { "$land" "$@" >"$T/out" 2>&1 && rc=0 || rc=$?; }
jf() { python3 -c 'import json,sys; print(json.loads(sys.stdin.read().splitlines()[-1])[sys.argv[1]])' "$1" < "$T/out"; }
main() { git ls-remote origin refs/heads/main | cut -f1; }
rgit() { git --git-dir="$T/remote.git" "$@"; }
# 1. the stub runs the pinned lander; a commit lands as itself, direct to main (no branch, no PR), linear, one JSON line carrying specified_share
[ "$("$land" --version)" = "land-direct $(cat scripts/land/VERSION)" ] && ran_case || fail "the stub does not run the vendored lander"
sync a; echo a > a.txt; cm a; head0=$(git rev-parse HEAD); : > "$T/updates"
run; [ "$rc" = 0 ] && [ "$(jf result)" = landed ] && [ "$(jf sha)" = "$(main)" ] && [ "$(jf commits)" = 1 ] && [ "$(jf specified_share)" = 80.0 ] && [[ "$(jf tier1_seconds)" =~ ^[0-9]+$ ]] && ran_case || fail "a did not land: $(cat "$T/out")"
[ "$(rgit log -1 --format=%s main)" = "feat(test): a" ] && grep -q "protected set" "$T/out" && ran_case || fail "a: the commit did not land as itself, or the protected-set line is missing"
[ "$(wc -l < "$T/updates")" = 1 ] && [ "$(rgit for-each-ref --format='%(refname)')" = refs/heads/main ] && ran_case || fail "a: the push touched more than main (no branch, no tag): $(cat "$T/updates")"
[ "$(git rev-parse HEAD)" = "$head0" ] && [ -z "$(git status --porcelain)" ] && ran_case || fail "a: the worker's own worktree was touched"
sync d1; echo d1 > d1.txt; cm d1; m0=$(main); run --dry-run; [ "$rc" = 0 ] && [ "$(jf result)" = would-land ] && [ "$(main)" = "$m0" ] && ran_case || fail "dry run: $(cat "$T/out")"
sync b; echo b1 > b1.txt; cm b1; echo b2 > b2.txt; cm b2; run; [ "$rc" = 0 ] && [ "$(jf commits)" = 2 ] && [ -z "$(rgit rev-list --merges main)" ] && ran_case || fail "b: two commits did not land linear: $(cat "$T/out")"
# 2. a conflicting rebase aborts naming the file (11); main untouched
sync cf; sed -i 2s/line2/mine/ code.txt; cm cf; git -C "$T/other" pull -q origin main; sed -i 2s/line2/theirs/ "$T/other/code.txt"; cmo mv; git -C "$T/other" push -q origin HEAD:main; m0=$(main)
run; [ "$rc" = 11 ] && [ "$(jf result)" = conflict ] && grep -q "code.txt" "$T/out" && [ "$(main)" = "$m0" ] && ran_case || fail "a code conflict was not stopped (exit $rc): $(cat "$T/out")"
# 3. a baseline both sides rewrote lands by itself; a worsening one stops (12)
sync g1; echo 8 > m1; printf 'm1 8\nm2 10\nm3 10\n' > base.txt; cm g1
git -C "$T/other" pull -q origin main; echo 7 > "$T/other/m2"; printf 'm1 10\nm2 7\nm3 10\n' > "$T/other/base.txt"; cmo g2; git -C "$T/other" push -q origin HEAD:main
run; [ "$rc" = 0 ] && grep -q "regenerating" "$T/out" && [ "$(rgit show main:base.txt)" = "$(printf 'm1 8\nm2 7\nm3 10')" ] && ran_case || fail "g1: a baseline conflict did not resolve by itself (exit $rc): $(cat "$T/out")"
git fetch -q origin; git checkout -q -B g3 "$(rgit log -1 --format=%H --grep='^feat(test): g2$' main)"; echo 9 > m2; printf 'm1 10\nm2 9\nm3 10\n' > base.txt; echo 12 > m3; cm g3; m0=$(main)
run; [ "$rc" = 12 ] && [ "$(main)" = "$m0" ] && ran_case || fail "a worsening baseline was not stopped (exit $rc): $(cat "$T/out")"
# 4. a failing Tier 1 lands nothing (13)
sync t; touch BAD; cm t; m0=$(main); run; [ "$rc" = 13 ] && [ "$(jf result)" = tier1 ] && [ "$(main)" = "$m0" ] && ran_case || fail "a failing Tier 1 was not stopped (exit $rc)"
# 5. the hold marker stops it (14)
sync h; echo h > h.txt; cm h; m0=$(main); "$land" --hold "maintenance" >/dev/null; run; [ "$rc" = 14 ] && [ "$(jf result)" = held ] && [ "$(main)" = "$m0" ] && ran_case || fail "the hold did not stop a landing (exit $rc)"
"$land" --release >/dev/null; run; [ "$rc" = 0 ] && ran_case || fail "released hold: $(cat "$T/out")"
# 7. land-time checks: a non-Conventional subject (1), over 150 production lines (under LeanSse/) without a Diff-Budget trailer (1), with one it lands
sync s1; echo s > s.txt; cm s "not conventional"; m0=$(main); run; [ "$rc" = 1 ] && [ "$(main)" = "$m0" ] && grep -q "Conventional" "$T/out" && ran_case || fail "a bad subject was not stopped (exit $rc)"
sync p1; mkdir -p LeanSse; seq 1 200 > LeanSse/big.lean; cm p1; m0=$(main); run; [ "$rc" = 1 ] && [ "$(main)" = "$m0" ] && grep -q "150-line budget" "$T/out" && ran_case || fail "a 200-line production diff was not stopped (exit $rc)"
git commit -q --amend -m "feat(test): p1" -m "Diff-Budget: part 1 of 2"; run; [ "$rc" = 0 ] && ran_case || fail "a Diff-Budget trailer did not waive the budget: $(cat "$T/out")"
# 8. the judges: the gate-diff judge's refusal is exit 12; the judge is MAIN's copy (a change that replaces it with a stub is still refused); the relabel suite runs exactly when a gate-defining file is touched
sync j1; echo j > j.txt; cm j; echo 1 > "$T/gdrc"; m0=$(main); run; [ "$rc" = 12 ] && [ "$(main)" = "$m0" ] && grep -q "not purely improving" "$T/out" && ran_case || fail "a refusal of the gate-diff judge did not stop the landing with 12 (exit $rc): $(cat "$T/out")"
printf 'exit 0\n' > scripts/gate-diff-improving.sh; cm j2; run; [ "$rc" = 12 ] && [ "$(main)" = "$m0" ] && ran_case || fail "a change replaced the gate-diff judge and landed (exit $rc): the judge must be main's copy"
echo 0 > "$T/gdrc"; : > "$T/relabel.calls"; sync j3; echo j3 > j3.txt; cm j3; run; [ "$rc" = 0 ] && [ ! -s "$T/relabel.calls" ] && ran_case || fail "the relabel suite ran for a change that touches no gate-defining file (exit $rc)"
echo "scripts/tier1.sh" > "$T/touched"; sync j4; echo j4 > j4.txt; cm j4; run; [ "$rc" = 0 ] && grep -q -- "--tree . --base origin/main" "$T/relabel.calls" && ran_case || fail "the relabel suite did not run for a gate-defining change (exit $rc): $(cat "$T/out")"
echo 1 > "$T/relabelrc"; sync j5; echo j5 > j5.txt; cm j5; m0=$(main); run; [ "$rc" = 12 ] && [ "$(main)" = "$m0" ] && grep -q "relabel-attack suite fails" "$T/out" && ran_case || fail "a failing relabel suite did not stop the landing with 12 (exit $rc): $(cat "$T/out")"
rm -f "$T/relabelrc" "$T/touched"
# 9. the lander refuses a change that edits its own vendored copy, or adds a file to it (12)
sync v1; echo '# local patch' >> scripts/land/bin/land-revert; cm v1 "fix(land): patch the vendored copy"; m0=$(main); run; [ "$rc" = 12 ] && [ "$(main)" = "$m0" ] && grep -q "differs from its pin" "$T/out" && ran_case || fail "an edit of the vendored copy was not stopped (exit $rc): $(cat "$T/out")"
sync v2; echo '# stray' > scripts/land/lib/stray.sh; cm v2 "chore(land): stray file"; run; [ "$rc" = 12 ] && [ "$(main)" = "$m0" ] && ran_case || fail "a stray file in the vendored tree was not stopped (exit $rc)"
ran_done test_land_direct
echo "tier1: land-direct: the vendored lander is intact and each tamper fails the check; lands as itself; conflict, worsening baseline, failing Tier 1, hold, bad subject and size budget stop; the gate-diff judge (main's copy) and the relabel suite (only for a gate-defining change) refuse with 12; an edit of the vendored copy is refused: ok"
