#!/usr/bin/env bash
# Self-test of the bench (bench/gen_corpus.py, bench/run_bench.py; docs/bench.md), offline, with stub measurers: the corpus is deterministic and is the pinned one (twice the same bytes, the
# same sha256 as the pins), and the driver REFUSES a corpus that is not the pinned one, a subject whose event count differs from the reference, and a missing comparator directory; it prints the
# lines the scorecard reads when everything agrees. The measuring programs themselves (bench.c, Bench.lean, the comparators) are exercised by the scorecard's bench, not here.
set -euo pipefail
cd "$(dirname "$0")/.."
. scripts/lib-ran.sh
fail() { echo "test_bench: $*" >&2; exit 1; }
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
mkdir "$tmp/a" "$tmp/b"
python3 bench/gen_corpus.py "$tmp/a"; python3 bench/gen_corpus.py "$tmp/b"
for f in "$tmp"/a/*.sse; do cmp -s "$f" "$tmp/b/$(basename "$f")" || fail "$(basename "$f"): two runs of the generator differ"; ran_case; done
python3 bench/gen_corpus.py --sha256 | python3 -c '
import re, sys
pins = dict(re.findall(r"\"([a-z-]+)\": \"([0-9a-f]{64})\"", open("bench/run_bench.py").read().split("CHUNKS")[0]))
got = {l.split()[0]: l.split()[1] for l in sys.stdin}
sys.exit(0 if got == pins and len(pins) == 5 else "the generator does not give the pinned corpora: %s vs %s" % (got, pins))' || fail "the pinned corpora are not the generator's"
ran_case
# stub measurers: the subject and the Lean side print a fixed event count, the comparator stub a number and its own count
cat > "$tmp/subj" <<'S'
#!/bin/sh
echo "10.0 events ${SUBJ_EVENTS:-7}"
S
cat > "$tmp/lean" <<'S'
#!/bin/sh
echo "reference N 1.0 events 7"; echo "lean-fast 1 2.0 events 7"; echo "lean-fast 7 3.0 events 7"; echo "lean-fast 4096 4.0 events 7"
S
mkdir "$tmp/comp"
cat > "$tmp/comp/run-sse.sh" <<'S'
#!/bin/sh
for n in eventsource-parser eventsource-stream; do echo "comparator $n 50.0"; echo "events $n 6"; echo "provenance $n 1.0.0 $(printf '%064d' 1) $(printf '%064d' 2)"; done
S
chmod +x "$tmp/subj" "$tmp/lean" "$tmp/comp/run-sse.sh"
out=$(VBM_COMPARATORS="$tmp/comp" python3 bench/run_bench.py "$tmp/subj" "$tmp/lean") || fail "the driver failed on agreeing stubs"
grep -q '^corpus [0-9a-f]\{64\} [0-9]*$' <<<"$out" || fail "no corpus line"; ran_case
grep -q '^subject 10.0$' <<<"$out" || fail "no subject line"; ran_case
[ "$(grep -c '^corpusrow ' <<<"$out")" = 15 ] || fail "not 15 corpus rows"; ran_case
[ "$(grep -c '^provenance ' <<<"$out")" = 2 ] || fail "not 2 provenance lines"; ran_case
grep -q '^note small-events@1: eventsource-stream found 6 events, the reference 7$' <<<"$out" || fail "a comparator that differs is not named in a note"; ran_case
# the driver can fail
export VBM_COMPARATORS="$tmp/comp"
SUBJ_EVENTS=8 must_fail "a subject that finds other events than the reference is refused" python3 bench/run_bench.py "$tmp/subj" "$tmp/lean"
grep -q 'events differ' <<<"$MUST_FAIL_ERR" || fail "refused, but not for the event count: $MUST_FAIL_ERR"; ran_case
sed 's/"small-events": "[0-9a-f]\{64\}"/"small-events": "'"$(printf '%064d' 0)"'"/' bench/run_bench.py > "$tmp/tampered.py"
cp bench/gen_corpus.py "$tmp/"
must_fail "a corpus that is not the pinned one is refused" python3 "$tmp/tampered.py" "$tmp/subj" "$tmp/lean"
grep -q 'not the pinned' <<<"$MUST_FAIL_ERR" || fail "refused, but not for the pin: $MUST_FAIL_ERR"; ran_case
must_fail "no comparator directory is refused" env -u VBM_COMPARATORS python3 bench/run_bench.py "$tmp/subj" "$tmp/lean"
ran_done test_bench
