#!/usr/bin/env bash
# Tier 1: the shared vectors (vbm-sse-vectors-1). The generator builds; every row it emits comes from the reference and the machine agrees with the reference on every cut of every input
# (whole, byte by byte, every two-way split); the row set is pinned (scripts/vectors-baseline.txt: its size and sha256, so a change of the reference or of the corpus is visible and a
# regeneration is a decision, `scripts/test_vectors.sh --write`); the check can fail (a tampered, dropped or added row is rejected by `--selftest`, and a file edited here is rejected by `--check`).
# Run from the repo root as `mise exec -- scripts/test_vectors.sh`. It builds nothing but the generator (tier1.sh has built the libraries).
set -euo pipefail
cd "$(dirname "$0")/.."
. scripts/lib-ran.sh   # ran_case counts each executed check, ran_done prints the evidence line `ran: NAME: N cases` (docs/decisions/0002-ran-evidence.md)
base=scripts/vectors-baseline.txt; N=3
fail() { echo "test_vectors: $*" >&2; exit 1; }
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
lake build vbm-sse-vectors >/dev/null
gen() { lake exe vbm-sse-vectors --n "$N" --out "$T/rows.jsonl" 2>"$T/err" || { cat "$T/err" >&2; fail "the generator failed (the machine disagrees with the reference, or the build is broken)"; }; }
gen
rows=$(wc -l < "$T/rows.jsonl"); sum=$(sha256sum "$T/rows.jsonl" | cut -d' ' -f1)
if [ "${1:-}" = --write ]; then printf '# vbm-sse-vectors-1, n = %s: the row count and the sha256 of the generated file (scripts/test_vectors.sh --write regenerates it; a change is a change of the reference or of the corpus)\nrows %s\nsha256 %s\n' "$N" "$rows" "$sum" > "$base"; echo "test_vectors: wrote $base"; exit 0; fi
[ -f "$base" ] && ran_case || fail "$base is missing"
[ "$(sed -n 's/^rows //p' "$base")" = "$rows" ] && ran_case || fail "the row count is $rows, the baseline says $(sed -n 's/^rows //p' "$base")"
[ "$(sed -n 's/^sha256 //p' "$base")" = "$sum" ] && ran_case || fail "the sha256 of the generated rows changed (the reference or the corpus changed); regenerate with scripts/test_vectors.sh --write and review"
lake exe vbm-sse-vectors --check "$T/rows.jsonl" --n "$N" >/dev/null && ran_case || fail "the generated file does not pass its own check"
lake exe vbm-sse-vectors --selftest >/dev/null && ran_case || fail "the vector check cannot fail"
# negative: a file edited here, a row dropped and a row added are each rejected by --check
sed '5s/"retry":null/"retry":7/' "$T/rows.jsonl" > "$T/bad1.jsonl"; cmp -s "$T/rows.jsonl" "$T/bad1.jsonl" && fail "the tamper did not change the file"
! lake exe vbm-sse-vectors --check "$T/bad1.jsonl" --n "$N" >/dev/null 2>&1 && ran_case || fail "--check accepted a tampered row"
sed '5d' "$T/rows.jsonl" > "$T/bad2.jsonl"; ! lake exe vbm-sse-vectors --check "$T/bad2.jsonl" --n "$N" >/dev/null 2>&1 && ran_case || fail "--check accepted a dropped row"
cp "$T/rows.jsonl" "$T/bad3.jsonl"; echo '{"id":99999}' >> "$T/bad3.jsonl"; ! lake exe vbm-sse-vectors --check "$T/bad3.jsonl" --n "$N" >/dev/null 2>&1 && ran_case || fail "--check accepted an added row"
ran_done test_vectors
echo "test_vectors: ok ($rows rows, sha256 pinned; the machine agrees with the reference on every cut; tampered, dropped and added rows are rejected)"
