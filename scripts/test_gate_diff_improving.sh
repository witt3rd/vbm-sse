#!/usr/bin/env bash
# Tier 1: scripts/gate-diff-improving.sh can fail. In a scratch repo seeded with the real gate files, each mutation of the head is judged against the base: a fallen proved, a raised open or
# unverified mass, a fallen specified share, an unknown key, a baseline that disappears, a removed, changed, weakened or masked tier1 line, a changed list, a changed gate source and a
# hand-edited generated file FAIL (exit 1, naming the line); the matching improvements, an added tier1 test line and a re-rendered ledger PASS (exit 0); an unrelated file is not judged.
set -euo pipefail
cd "$(dirname "$0")/.."
. scripts/lib-ran.sh   # ran_case counts each executed check, ran_done prints the evidence line `ran: NAME: N cases` (docs/decisions/0002-ran-evidence.md)
[ "$(bash -c '. scripts/git-hermetic.sh; echo loaded')" = loaded ] && ran_case || { echo "tier1: scripts/git-hermetic.sh does not load (a stub that exits?)" >&2; exit 1; }
. scripts/git-hermetic.sh   # hermetic git: no ambient config, explicit identity and branch
root=$(pwd); gate=$root/scripts/gate-diff-improving.sh
fail() { echo "tier1: gate-diff-improving: $*" >&2; exit 1; }
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
git init -q -b main "$T/r"; cd "$T/r"; git config user.email t@t; git config user.name t; git config core.hooksPath /dev/null
mkdir -p scripts docs LeanSseProofs
files="scripts/closure-baseline.txt scripts/ledger-baseline.txt scripts/tier1.sh scripts/closure-entries.txt scripts/ledger-bridges.txt scripts/protected-paths.txt scripts/generated-paths.txt scripts/tests-map.txt
scripts/ClosureGate.lean scripts/LedgerGate.lean scripts/AxiomGate.lean scripts/land-direct docs/proof-ledger.md"
for f in $files; do cp "$root/$f" "$f"; done
echo "LeanSse.Mod 3" >> scripts/closure-baseline.txt   # a per-module line the real baseline does not carry today (the rules cover it)
echo "-- ledger" > LeanSseProofs/Ledger.lean; echo unrelated > docs/other.md
git add -A; git commit -qm base; base=$(git rev-parse HEAD)
# mut <name> <expected: pass|fail> <needle expected in the output> <command that mutates the tree>
mut() {
  local name=$1 want=$2 needle=$3; shift 3
  "$@"; git add -A; git commit -qm "$name" --allow-empty
  out=$("$gate" ${GDI_FLAGS:-} "$base" HEAD 2>&1) && rc=0 || rc=$?
  if [ "$want" = pass ]; then [ "$rc" = 0 ] && grep -qx PASS <<<"$out" && ran_case || fail "$name: an improving change was refused ($out)"
  else [ "$rc" = 1 ] && grep -qx FAIL <<<"$out" && ran_case || fail "$name: expected FAIL, got rc=$rc ($out)"; fi
  if [ -n "$needle" ] && ! grep -qF -- "$needle" <<<"$out"; then fail "$name: '$needle' not in the output ($out)"; fi
  git reset -q --hard "$base"
}
num() { sed -i -E "$1" "$2"; }
grep -q '^mass ' scripts/closure-baseline.txt && grep -q '^dep_mass ' scripts/closure-baseline.txt && grep -q '^specified_share ' scripts/closure-baseline.txt && grep -q '^proved ' scripts/ledger-baseline.txt && ran_case || fail "the real baselines no longer have the keys this self-test mutates: update it"
mut "no change"                 pass ""                       true
mut "unrelated file"            pass ""                       eval 'echo x >> docs/other.md'
mut "mass raised"               fail "mass"                   num 's/^mass ([0-9]+)/echo "mass $((\1+1))"/e' scripts/closure-baseline.txt
mut "unverified module raised"  fail "LeanSse.Mod"           num 's/^(LeanSse.Mod) 3/\1 4/' scripts/closure-baseline.txt
mut "unverified module lowered" pass "closure-baseline"       num 's/^(LeanSse.Mod) 3/\1 2/' scripts/closure-baseline.txt
mut "new unverified module"     fail "LeanSse.New"           eval 'echo "LeanSse.New 1" >> scripts/closure-baseline.txt'
mut "pinned-library mass raised" fail "dep_mass"             num 's/^dep_mass ([0-9]+)/echo "dep_mass $((\1+1))"/e' scripts/closure-baseline.txt
mut "pinned-library mass lowered" pass "closure-baseline"     num 's/^dep_mass ([0-9]+)/echo "dep_mass $((\1-1))"/e' scripts/closure-baseline.txt
mut "pinned-library mass key removed" fail "removed"          num '/^dep_mass /d' scripts/closure-baseline.txt
mut "mass key removed"          fail "removed"                num '/^mass /d' scripts/closure-baseline.txt
mut "specified share fell"      fail "specified_share"        num 's/^specified_share ([0-9]+) /specified_share 1 /' scripts/closure-baseline.txt
mut "specified share rose"      pass "closure-baseline"       num 's/^specified_share ([0-9]+) ([0-9]+)/echo "specified_share $((\1+1)) \2"/e' scripts/closure-baseline.txt
mut "unknown closure key"       fail "unknown key"            eval 'echo "free_lunch 0" >> scripts/closure-baseline.txt'
mut "ledger proved fell"        fail "proved"                 num 's/^proved ([0-9]+)/echo "proved $((\1-1))"/e' scripts/ledger-baseline.txt
mut "ledger open rose"          fail "open"                   num 's/^open ([0-9]+)/echo "open $((\1+1))"/e' scripts/ledger-baseline.txt
mut "ledger total fell"         fail "total"                  num 's/^total ([0-9]+)/echo "total $((\1-1))"/e' scripts/ledger-baseline.txt
mut "ledger improved + md"      pass "proof-ledger"           eval 'sed -i -E "s/^proved ([0-9]+)/echo \"proved \$((\1+1))\"/e" scripts/ledger-baseline.txt; echo x >> docs/proof-ledger.md'
mut "ledger md hand edit"       fail "proof-ledger"           eval 'echo x >> docs/proof-ledger.md'
mut "ledger md re-rendered"     pass "proof-ledger"           eval 'echo "-- ledger2" > LeanSseProofs/Ledger.lean; echo x >> docs/proof-ledger.md'
mut "baseline deleted"          fail "disappears"             git rm -q scripts/ledger-baseline.txt
mut "tier1 line added"          pass "only added lines"       eval 'sed -i "/^scripts\/lint-pipefail.sh/a par scripts\/test_new.sh" scripts/tier1.sh'
mut "tier1 line removed"        fail "removed/changed"        eval 'sed -i "/^scripts\/lint-pipefail.sh/d" scripts/tier1.sh'
mut "tier1 line changed"        fail "removed/changed"        eval 'sed -i "s/^scripts\/lint-pipefail.sh/scripts\/lint-pipefail.sh x/" scripts/tier1.sh'
mut "tier1 || true added"       fail "weakening"              eval 'sed -i "/^scripts\/lint-pipefail.sh/a scripts/test_new.sh || true" scripts/tier1.sh'
mut "tier1 exit 0 added"        fail "weakening"              eval 'sed -i "/^scripts\/lint-pipefail.sh/a exit 0" scripts/tier1.sh'
mut "tier1 joined line"         fail "joins"                  eval 'sed -i "/^scripts\/lint-pipefail.sh/i echo x \\\\" scripts/tier1.sh'
mut "map: a test line dropped"   fail "removed"                num '/^scripts\/test_githook.sh:/d' scripts/tests-map.txt
mut "map: a token lost"          fail "lost"                   num 's# scripts/tier1.sh##' scripts/tests-map.txt
mut "map: code to none"          fail "none:"                  num 's#^none:#none: LeanSse/#' scripts/tests-map.txt
mut "map: docs to none"          pass "only selects more"      num 's#^none:#none: docs/more/#' scripts/tests-map.txt
mut "map: a token added"         pass "only selects more"      num 's#^(scripts/test_githook.sh:)#\1 scripts/new.sh#' scripts/tests-map.txt
for f in scripts/closure-entries.txt scripts/ledger-bridges.txt scripts/protected-paths.txt scripts/generated-paths.txt; do
  mut "list $f changed"         fail "$f"                     eval "echo '# x' >> $f"
done
for f in scripts/ClosureGate.lean scripts/LedgerGate.lean scripts/AxiomGate.lean scripts/land-direct; do
  mut "gate source $f changed"  fail "$f"                     eval "echo '# x' >> $f"
done
mut "a gate source added"       fail "scripts/trust_ledger.py" eval 'echo x > scripts/trust_ledger.py'
# --suite-judged (what scripts/land-direct runs): lists and gate source are judged by the relabel-attack suite, not refused outright; everything else is judged as before
export GDI_FLAGS=--suite-judged
mut "suite: a list changed"             pass "judged by the relabel-attack suite" eval "echo '# x' >> scripts/closure-entries.txt"
mut "suite: gate source changed"        pass "judged by the relabel-attack suite" eval "echo '# x' >> scripts/ClosureGate.lean"
mut "suite: baseline raise still fails" fail "mass"           num 's/^mass ([0-9]+)/echo "mass $((\1+1))"/e' scripts/closure-baseline.txt
mut "suite: protected entry dropped"    fail "drops protection" eval "sed -i '/^LeanSse\\/\$/d' scripts/protected-paths.txt"
mut "suite: protected entry narrowed"   fail "drops protection" eval "sed -i 's|^LeanSse/\$|LeanSse/Value.lean|' scripts/protected-paths.txt"
mut "suite: protected entry added"      pass "still protected" eval "echo newdir/ >> scripts/protected-paths.txt"
mut "suite: tier1 guard added"          pass "only added lines" eval "sed -i '/^scripts\/lint-pipefail.sh/a [ -n \"\$x\" ] || { echo \"tier1: x\" >\&2; exit 1; }' scripts/tier1.sh"
tier1_add() { printf '%s\n' "$1" > l.tmp; sed -i '/^scripts\/lint-pipefail.sh/r l.tmp' scripts/tier1.sh; rm -f l.tmp; }
for bad in '! scripts/test_new.sh' 'scripts/test_new.sh && :' 'scripts/test_new.sh &' 'set +o errexit' ': $(scripts/test_new.sh)' 'if scripts/test_new.sh; then :; fi' "trap 'exit 0' EXIT"; do
  mut "suite: tier1 mask $bad"          fail "not a plain step"  tier1_add "$bad"
done
unset GDI_FLAGS
# A pathological long added line is judged in linear time (a nested-quantifier regex once ran 47 minutes on one and held the land lock): each shape FAILs as "not a plain step", fast, under a 20 s GDI_TIMEOUT.
for shape in "$(printf 'a%.0s' $(seq 1 6000))!" "$(printf '$a%.0s' $(seq 1 3000))!" "$(printf 'ab=1 %.0s' $(seq 1 1500))!" "$(printf '"x" %.0s' $(seq 1 1500))!"; do
  GDI_TIMEOUT=20 GDI_FLAGS=--suite-judged mut "long line ${shape:0:12}..." fail "not a plain step" tier1_add "$shape"
done
# GATE-EDIT APPROVALS: the lander hands over the approvals a landing consumes ($LAND_GATE_APPROVED_FILE, `FILE HASH`); the judge relaxes scripts/tier1.sh's removed/changed lines for the exact diff, and the fall of the
# specified_share row of scripts/closure-baseline.txt for the exact diff, and nothing else (no other baseline row, no list, no gate source, no other file)
. "$root/scripts/land/lib/approvals.sh"
LIST=$T/approved.txt
mut_ap() {   # mut_ap NAME want needle LISTSPEC FILE_FOR_HASH CMD...: LISTSPEC is a printf format with %s for the true hash of FILE_FOR_HASH's diff ("none": no list at all, "empty": an empty list)
  local name=$1 want=$2 needle=$3 spec=$4 hf=$5; shift 5
  "$@"; git add -A; git commit -qm "$name" --allow-empty
  local h; h=$(ga_hash . "$base" HEAD "$hf" || true); : > "$LIST"
  case $spec in none) unset LAND_GATE_APPROVED_FILE;; empty) export LAND_GATE_APPROVED_FILE=$LIST;; missing) export LAND_GATE_APPROVED_FILE=$T/nope;; *) printf "$spec\n" "$h" > "$LIST"; export LAND_GATE_APPROVED_FILE=$LIST;; esac
  out=$("$gate" ${GDI_FLAGS:-} "$base" HEAD 2>&1) && rc=0 || rc=$?
  unset LAND_GATE_APPROVED_FILE
  if [ "$want" = pass ]; then [ "$rc" = 0 ] && grep -qx PASS <<<"$out" && ran_case || fail "$name: an approved change was refused ($out)"
  else [ "$rc" = 1 ] && grep -qx FAIL <<<"$out" && ran_case || fail "$name: expected FAIL, got rc=$rc ($out)"; fi
  if [ -n "$needle" ] && ! grep -qF -- "$needle" <<<"$out"; then fail "$name: '$needle' not in the output ($out)"; fi
  git reset -q --hard "$base"
}
rm_t1='sed -i "/^scripts\/lint-pipefail.sh/d" scripts/tier1.sh'
share_fall='sed -i -E "s/^specified_share ([0-9]+) ([0-9]+)/specified_share 1 \2/" scripts/closure-baseline.txt'
mut_ap "approved: tier1 line removed"       pass "APPROVED"          'scripts/tier1.sh %s' scripts/tier1.sh eval "$rm_t1"
mut_ap "approved: tier1 line changed"       pass "APPROVED"          'scripts/tier1.sh %s' scripts/tier1.sh eval 'sed -i "s/^scripts\/lint-pipefail.sh/scripts\/lint-pipefail.sh x/" scripts/tier1.sh'
mut_ap "no list: tier1 removal"             fail "removed/changed"   none                  scripts/tier1.sh eval "$rm_t1"
mut_ap "empty list"                         fail "removed/changed"   empty                 scripts/tier1.sh eval "$rm_t1"
mut_ap "missing list file"                  fail "removed/changed"   missing               scripts/tier1.sh eval "$rm_t1"
mut_ap "a hash of another diff"             fail "removed/changed"   'scripts/tier1.sh 0000000000000000000000000000000000000000000000000000000000000000' scripts/tier1.sh eval "$rm_t1"
mut_ap "a hash prefix is no approval"       fail "removed/changed"   'scripts/tier1.sh %.12s' scripts/tier1.sh eval "$rm_t1"
mut_ap "another file named in the list"     fail "removed/changed"   'scripts/tier1.sh2 %s'  scripts/tier1.sh eval "$rm_t1"
mut_ap "a field more on the line"           fail "removed/changed"   'scripts/tier1.sh %s x' scripts/tier1.sh eval "$rm_t1"
mut_ap "approved: specified share fell"     pass "APPROVED"          'scripts/closure-baseline.txt %s' scripts/closure-baseline.txt eval "$share_fall"
mut_ap "no list: specified share fell"      fail "specified_share"   none                  scripts/closure-baseline.txt eval "$share_fall"
mut_ap "empty list: specified share fell"   fail "specified_share"   empty                 scripts/closure-baseline.txt eval "$share_fall"
mut_ap "share: a hash of another diff"      fail "specified_share"   'scripts/closure-baseline.txt 0000000000000000000000000000000000000000000000000000000000000000' scripts/closure-baseline.txt eval "$share_fall"
mut_ap "share: another file's hash"         fail "specified_share"   'scripts/closure-baseline.txt %s' scripts/tier1.sh eval "$share_fall"
# a base that does not carry the dep_mass row yet (the landing that introduces it): the row appears, 0 -> N, and only an approval lets it
base_full=$base; sed -i '/^dep_mass /d' scripts/closure-baseline.txt; git add -A; git commit -qm "a base without the dep_mass row" --allow-empty; base=$(git rev-parse HEAD)
dep_new='sed -i "/^dep_mass /d" scripts/closure-baseline.txt; echo "dep_mass 3122" >> scripts/closure-baseline.txt'
mut_ap "approved: the dep_mass row appears (and the share falls)" pass "APPROVED" 'scripts/closure-baseline.txt %s' scripts/closure-baseline.txt eval "$share_fall; $dep_new"
mut_ap "no approval: the dep_mass row appears"  fail "dep_mass"  none                  scripts/closure-baseline.txt eval "$dep_new"
git reset -q --hard "$base_full"; base=$base_full
mut_ap "baseline: approval does not relax a mass"  fail "mass"       'scripts/closure-baseline.txt %s' scripts/closure-baseline.txt num 's/^mass ([0-9]+)/echo "mass $((\1+1))"/e' scripts/closure-baseline.txt
mut_ap "baseline: approval does not relax mass beside a share fall" fail "mass" 'scripts/closure-baseline.txt %s' scripts/closure-baseline.txt eval "$share_fall; sed -i -E 's/^mass ([0-9]+)/echo \"mass \$((\1+1))\"/e' scripts/closure-baseline.txt"
mut_ap "approval: a rise of an existing dep_mass is not relaxed" fail "dep_mass" 'scripts/closure-baseline.txt %s' scripts/closure-baseline.txt num 's/^dep_mass ([0-9]+)/echo "dep_mass $((\1+1))"/e' scripts/closure-baseline.txt
mut_ap "tests-map: approval does not relax"  fail "lost"             'scripts/tests-map.txt %s' scripts/tests-map.txt num 's# scripts/tier1.sh##' scripts/tests-map.txt
mut_ap "list of gate source: not relaxed"    fail "owner"            'scripts/closure-entries.txt %s' scripts/closure-entries.txt eval 'echo x >> scripts/closure-entries.txt'
# the bound itself: a judge that never finishes is killed and reported (exit 2, a clear line), not waited for
mkdir -p "$T/slow"; printf '#!/bin/sh\nexec sleep 60\n' > "$T/slow/python3"; chmod +x "$T/slow/python3"
git reset -q --hard "$base"; echo x >> docs/other.md; git add -A; git commit -qm slow
t0=$SECONDS; out=$(PATH="$T/slow:$PATH" GDI_TIMEOUT=1 "$gate" "$base" HEAD 2>&1) && rc=0 || rc=$?
[ "$rc" = 2 ] && grep -qF "GDI_TIMEOUT=1s" <<<"$out" && [ $((SECONDS - t0)) -lt 30 ] && ran_case || fail "a never-finishing judge was not bounded (rc=$rc, $out)"
git reset -q --hard "$base"
# --touched: the lander's trigger: the gate-defining files the change touches, nothing for an unrelated one
git reset -q --hard "$base"; echo '# x' >> scripts/ClosureGate.lean; echo x >> docs/other.md; git add -A; git commit -qm touched
[ "$("$gate" --touched "$base" HEAD)" = scripts/ClosureGate.lean ] && ran_case || fail "--touched did not name exactly the gate-defining file"
git reset -q --hard "$base"; echo x >> docs/other.md; git add -A; git commit -qm untouched
[ -z "$("$gate" --touched "$base" HEAD)" ] && ran_case || fail "--touched named a file of an unrelated change"
ran_done test_gate_diff_improving
echo "gate-diff-improving: every worsening, mask, list or source change FAILS and every improvement passes: ok"
