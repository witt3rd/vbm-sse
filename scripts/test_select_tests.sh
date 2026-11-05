#!/usr/bin/env bash
# Negative-tested delta selection (scripts/select-tests.py, scripts/tests-map.txt): a change to the specification selects everything, one to the proofs or the docs no test (the gates in tier1.sh run anyway),
# a workflow delta the workflow lint, a gate or an unmapped file EVERYTHING; the fallbacks (TIER1_ALL, no base, empty delta) select everything; a test with no map line fails the drift check.
set -euo pipefail
cd "$(dirname "$0")/.."
. scripts/lib-ran.sh   # ran_case counts each executed check, ran_done prints the evidence line `ran: NAME: N cases` (docs/decisions/0002-ran-evidence.md)
unset TIER1_ALL TIER1_BASE   # Tier 2 runs Tier 1 with TIER1_ALL=1; this test pins the variable itself where it matters
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
sel() { python3 scripts/select-tests.py --files "$@" | tr '\n' ' '; }
fail() { echo "test_select_tests: $*" >&2; exit 1; }
all=$(python3 scripts/select-tests.py --files scripts/tier1.sh)
nall=$(wc -w <<<"$all"); [ "$nall" -ge 9 ] && ran_case || fail "the full set is only $nall tests"
[ "$(sel LeanSse/Spec.lean | wc -w)" = "$nall" ] && ran_case || fail "a specification delta does not select everything"
[ "$(sel LeanSse/Stream.lean LeanSse.lean | wc -w)" = "$nall" ] && ran_case || fail "a machine delta does not select everything"
[ "$(sel abi/vbm_sse.c | tr ' ' '\n' | sort | tr '\n' ' ')" = "scripts/test_abi.sh scripts/test_bindings.sh scripts/test_native.sh scripts/test_wasm.sh " ] && ran_case || fail "a C interface delta does not select exactly the tests of the C targets: $(sel abi/vbm_sse.c)"
[ "$(sel weird/place.c | wc -w)" = "$nall" ] && ran_case || fail "an unmapped C file does not select everything"
[ "$(sel docs/proof-ledger.md AGENTS.md)" = "" ] && ran_case || fail "a docs-only delta selects tests"
[ "$(sel LeanSseProofs/Stream.lean)" = "" ] && ran_case || fail "a proofs-only delta selects tests (the gates run anyway)"
[ "$(sel scripts/ClosureGate.lean scripts/closure-baseline.txt)" = "" ] && ran_case || fail "a gate-only delta selects tests (the gates always run in tier1.sh)"
[ "$(sel .github/workflows/core.yml)" = "scripts/test_lint_workflows.sh " ] && ran_case || fail "a workflow delta does not select exactly the workflow lint test"
[ "$(sel scripts/test_githook.sh)" = "scripts/test_githook.sh " ] && ran_case || fail "a test script does not select itself"
[ "$(sel scripts/protected-paths.txt docs/x.md)" = "scripts/test_protected_set.sh " ] && ran_case || fail "a mixed delta is not the union"
for f in scripts/tier1.sh scripts/select-tests.py scripts/tests-map.txt lakefile.lean lean-toolchain; do
  [ "$(python3 scripts/select-tests.py --files "$f")" = "$all" ] && ran_case || fail "a gate-defining change ($f) does not select everything"
done
[ "$(python3 scripts/select-tests.py --files no/such/place.txt docs/x.md)" = "$all" ] && ran_case || fail "an unmapped file does not select everything"
[ "$(python3 scripts/select-tests.py --files)" = "$all" ] && ran_case || fail "an empty delta does not select everything"
[ "$(TIER1_ALL=1 python3 scripts/select-tests.py)" = "$all" ] && ran_case || fail "TIER1_ALL=1 does not select everything"
[ "$(TIER1_BASE=0000000000000000000000000000000000000000 python3 scripts/select-tests.py)" = "$all" ] && ran_case || fail "an unresolvable base does not select everything"
# a scratch repo: the delta is read from git (committed, uncommitted and untracked)
g() { git -C "$tmp/r" "$@"; }
mkdir -p "$tmp/r/scripts" "$tmp/r/docs"; cp scripts/tests-map.txt "$tmp/r/scripts/"; cp scripts/select-tests.py "$tmp/r/scripts/"
g init -q -b main; g config user.email t@t; g config user.name t; echo a > "$tmp/r/docs/a.md"; g add -A; g commit -qm base
rsel() { (cd "$tmp/r" && TIER1_BASE=$(git rev-parse HEAD) python3 scripts/select-tests.py | tr '\n' ' '); }
echo b > "$tmp/r/docs/a.md"; [ "$(rsel)" = "" ] && ran_case || fail "an uncommitted docs change selects tests: $(rsel)"
mkdir -p "$tmp/r/LeanSse"; echo x > "$tmp/r/LeanSse/New.lean"; [ "$(rsel | wc -w)" = "$nall" ] && ran_case || fail "an untracked specification file does not select everything: $(rsel)"
echo y > "$tmp/r/weird.bin"; [ "$(rsel | wc -w)" = "$nall" ] && ran_case || fail "an untracked unmapped file does not select everything"
# the drift check can fail: a test with no map line is refused, the real tests pass
python3 scripts/select-tests.py --check scripts/test_githook.sh scripts/test_run_parallel.sh && ran_case || fail "a mapped test fails the drift check"
if python3 scripts/select-tests.py --check scripts/test_nonexistent.sh 2>"$tmp/err"; then fail "an unmapped test passes the drift check"; fi
grep -q 'no map line' "$tmp/err" && ran_case || fail "the drift failure says nothing"
ran_done test_select_tests
echo "test_select_tests: ok"
