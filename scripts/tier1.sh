#!/usr/bin/env bash
# Tier 1 (pre-landing gate): forbidden constructs, the Init-only import rule, zero-warning build, the axiom gate, the obligation ledger (every claim tagged with a clause), the closure gate
# (specified share printed on every run), the trust ledger, the scrub gate (no internal name, path or secret in the tree), and the offline self-tests of the process scripts (protected set, land, commit-on-main hook).
# Every gate has a negative self-test and runs it here. Run from the repo root: mise exec -- scripts/tier1.sh.
set -euo pipefail
cd "$(dirname "$0")/.."
# A sourced library that has been replaced by a stub (`exit 0`) would end this script, and every test of it, with success: each is checked to define its function before it is sourced (the relabel-attack suite attacks this).
[ "$(grep -c '^nocrash_begin()' scripts/lib-no-crash-record.sh)" = 1 ] || { echo "tier1: scripts/lib-no-crash-record.sh does not define nocrash_begin" >&2; exit 1; }
# RAN-EVIDENCE (docs/decisions/0002-ran-evidence.md): a gate or self-test that never ran must not pass. Every test script and every concurrent gate ends with `ran: NAME: N cases` (N > 0, or the gate's own count line named in
# scripts/ran-gates.txt); scripts/run-tests-parallel.sh and the check below FAIL a job without it, and a refused tool, a SKIPPED check or a stop by a guard is a failure, never a pass (scripts/ran-evidence.sh, scripts/test_ran_evidence.sh).
[ "$(grep -c '^ran_done()' scripts/lib-ran.sh)" = 1 ] || { echo "tier1: scripts/lib-ran.sh does not define ran_done" >&2; exit 1; }
[ "$(grep -c '^must_fail()' scripts/lib-ran.sh)" = 1 ] || { echo "tier1: scripts/lib-ran.sh does not define must_fail" >&2; exit 1; }
[ "$(grep -c '^  check-dir)' scripts/ran-evidence.sh)" = 1 ] || { echo "tier1: scripts/ran-evidence.sh does not define check-dir" >&2; exit 1; }
# No test may leave a crash record (systemd-coredump, hence a desktop notification): the whole run is wrapped (scripts/lib-no-crash-record.sh; its self-test is test_no_crash_record.sh).
. scripts/lib-no-crash-record.sh; nocrash_begin

# The independent test scripts are declared with `par` where they are described below and run in parallel at the end (scripts/run-tests-parallel.sh):
# Tier 1 wall time is the longest script, not the sum. A test script must use its own temp dirs.
TIER2_ONLY=""
tests=(); par() { tests+=("$@"); }
# The gates after the build are independent of each other and of the tests: they run concurrently (`bg NAME CMD...`, output kept and shown on failure; `bgwait` below),
# so Tier 1 wall time is the longest of them, not the sum (docs/decisions/0004-tier1-speed.md).
bgdir=$(mktemp -d); bgnames=()
bg() { local n=$1; shift; bgnames+=("$n"); ( "$@" ) > "$bgdir/$n.log" 2>&1 & echo $! > "$bgdir/$n.pid"; }
bgwait() { local bad=0 n; for n in "${bgnames[@]}"; do if wait "$(cat "$bgdir/$n.pid")"; then cat "$bgdir/$n.log"; else echo "tier1: FAILED: $n" >&2; cat "$bgdir/$n.log" >&2; bad=1; fi; done; [ $bad = 0 ] || exit 1; }

# Lean sources under the roots that exist: LeanSse (spec + code), LeanSseProofs, abi and vectors (arrive with the C interface), and the two umbrella files.
lean_sources() { find LeanSse LeanSseProofs abi vectors -name '*.lean' 2>/dev/null; ls LeanSse.lean LeanSseProofs.lean 2>/dev/null; }

# 1. Forbidden constructs anywhere in Lean sources (AGENTS.md hard rules). Comments may mention them only on lines marked `-- tier1-allow`.
forbidden() { grep -HnE '\b(sorry|admit|axiom|unsafe|implemented_by|csimp)\b' "$@" | grep -v 'tier1-allow' || true; }
bad=$(forbidden $(lean_sources))
if [ -n "$bad" ]; then echo "tier1: forbidden construct(s):" >&2; echo "$bad" >&2; exit 1; fi
# the scan can fail: each forbidden word is flagged, and the tier1-allow marker (and only it) lets a comment mention one
st=$(mktemp); trap 'rm -f "$st"; rm -rf "$bgdir"' EXIT
for w in sorry admit axiom unsafe implemented_by csimp; do
  echo "theorem t : True := by $w" > "$st"; [ -n "$(forbidden "$st")" ] || { echo "tier1: the forbidden-constructs scan does not flag '$w'" >&2; exit 1; }
done
echo "-- a comment that says sorry -- tier1-allow" > "$st"; [ -z "$(forbidden "$st")" ] || { echo "tier1: the tier1-allow marker is not honoured" >&2; exit 1; }
echo "-- a comment that says sorry" > "$st"; [ -n "$(forbidden "$st")" ] || { echo "tier1: an unmarked comment is not flagged" >&2; exit 1; }
echo "tier1: forbidden-constructs scan: negative self-tests ok (each forbidden word is flagged, the tier1-allow marker is honoured)"

# 1a. LeanSse/ imports Init only (implicitly) and other LeanSse modules: no Std, no Lean, no LeanSseProofs, no `prelude`, nothing else. A Lean.* import in the
# library's closure forces the full runtime initialisation (docs/decisions/0001-vbm-sse.md); the proofs library is never linked.
bad_imports() { grep -HnE '^[[:space:]]*((public|meta|private)[[:space:]]+)*(import|prelude)\b' "$@" | grep -vE ':[0-9]+:import LeanSse(\.[A-Za-z0-9_]+)*[[:space:]]*$' || true; }
bad=$(bad_imports $(find LeanSse -name '*.lean') LeanSse.lean)
if [ -n "$bad" ]; then echo "tier1: LeanSse may import only LeanSse modules (Init is implicit):" >&2; echo "$bad" >&2; exit 1; fi
for imp in 'import Lean' 'import Std.Data.HashMap' 'import LeanSseProofs.Ledger' 'prelude' 'public import Lean.Data.Json' 'import LeanSseX'; do
  printf '%s\n' "$imp" > "$st"; [ -n "$(bad_imports "$st")" ] || { echo "tier1: the Init-only import scan does not flag: $imp" >&2; exit 1; }
done
printf 'import LeanSse.Value\n' > "$st"; [ -z "$(bad_imports "$st")" ] || { echo "tier1: the Init-only import scan flags a LeanSse import" >&2; exit 1; }
echo "tier1: Init-only import scan: negative self-tests ok (each non-Init import is flagged)"

# 1b. Pipefail-unsafe pipelines (an early-exiting consumer) are flaky by construction; the lint has a negative self-test.
scripts/lint-pipefail.sh
# Long runners (scripts/long-runners.txt) run under scripts/run-scoped.sh (a bounded transient scope, reaped on exit: an aborted run cannot orphan); the lint is negative-tested here (a guard against accidents: indirection is its stated limit).
scripts/lint-scoped-runners.sh --selftest

# 1c. Proofs by evaluation over big data (decide +kernel, native_decide, rfl/decide over a literal past the bound) overflowed the independent checker once; the lint
# has fixture self-tests (each banned pattern, just-under-the-bound, allowlist expiry), run here with `--selftest`.
scripts/lint-proof-eval.sh --selftest

# 2. Build both libraries; warningAsError is set in lakefile.lean, so any warning fails. The mechanism is checked: the option is set, and a file with a warning fails under it.
grep -q 'warningAsError, true' lakefile.lean || { echo "tier1: lakefile.lean does not set warningAsError" >&2; exit 1; }
printf 'def f (x : Nat) : Nat :=\n  let y := 1\n  2\n' > "$st"
if lake env lean -DwarningAsError=true "$st" >/dev/null 2>&1; then echo "tier1: a build with a warning succeeds under warningAsError (the zero-warning gate cannot fail)" >&2; exit 1; fi
echo "tier1: zero-warning build: negative self-test ok (a file with a warning fails under warningAsError)"
# The inline check above is the first version (it passes when lake is refused: the defect); scripts/check-zero-warning.sh is the check: the warning's own diagnostic is required, a clean file must pass, it prints `ran: zero-warning: 3 cases`.
scripts/check-zero-warning.sh
lake build LeanSse LeanSseProofs   # once, for the gates and every test (they build nothing more)

# 2a. The axiom gate: every constant of ours depends only on propext, Classical.choice, Quot.sound (--selftest: a non-standard axiom is rejected).
bg axiom-gate lake env lean --run scripts/AxiomGate.lean --selftest

# 2b. The obligation ledger: named theorems exist; proved may only rise, open may only fall. Renders docs/proof-ledger.md.
bg ledger-gate lake env lean --run scripts/LedgerGate.lean --selftest

# 2c. The closure gate: what the exports execute, classified; the specified share is printed on every run and may only rise; the unverified set may only shrink;
# nothing from Std, Lean or the proofs may be reachable. One Lean process runs the real gate then its negative self-tests (see ClosureGate.selfTests).
bg closure-gate lake env lean --run scripts/ClosureGate.lean --selftest

# 2d. The trust ledger (docs/trust-ledger.md): everything outside our control that vbm-sse runs or depends on has an entry; a new boundary with none FAILS;
# prints "trust ledger: N entries".
bg trust-ledger scripts/trust-ledger-check.sh

# 2e. The scrub gate: no internal name, host path or secret-shaped string in any file of the tree (scripts/scrub.py; its negative self-tests run in the same call).
bg scrub scripts/scrub.py --selftest

# 2e'. The shared vectors (vbm-sse-vectors-1; scripts/test_vectors.sh): the rows come from the Lean reference only, the machine agrees with it on every cut of every input, the row set is pinned by size and sha256, and
# the check is shown able to fail (tampered, dropped and added rows). Runs in parallel with the process scripts below.
par scripts/test_vectors.sh

# 2e''. The C interface and its targets (docs/decisions/0001-vbm-sse.md): the ABI description, the header and the report layout agree (test_abi); the freestanding native library (no libc) runs every vector on every cut (test_native);
# the WebAssembly module (no imports) does too (test_wasm; skipped without node, required by Tier 2). Each is shown able to fail (drifted headers, tampered rows, mutants of the shim and of the runtime).
par scripts/test_abi.sh
par scripts/test_native.sh
par scripts/test_wasm.sh
# The generated bindings equal their generator's output and run the vectors (test_bindings; Rust skipped without cargo, required by Tier 2); corrupted rows and mutants of each generated reader each fail.
par scripts/test_bindings.sh

# 2f. The workflow files are structurally valid (scripts/lint-workflows.py: one of uses/run per step, no with: under a run, jobs exist); its negative self-test is declared below.
python3 scripts/lint-workflows.py
par scripts/test_lint_workflows.sh

# 3. The process scripts, offline, in scratch repos.
# 3a. The protected set (scripts/protected-paths.txt, read by scripts/protected-set.sh): every class fails a fixture diff, a docs-only diff passes.
par scripts/test_protected_set.sh
# 3b. scripts/land-direct: lands direct to main (no PR, no force); a worsening baseline, a code conflict, a failing Tier 1, a hold and a red main stop; a second lander waits (local bare remote, gh shim).
par scripts/test_land_direct.sh
# 3b'. The pinned lander is intact (scripts/land/PIN, MANIFEST.sha256; offline, well under a second): edit vbm-land, not the copy. The test above shows the check can fail; the lander also runs it.
scripts/land/bin/land-check
# 3c. The commit-on-main guard (scripts/githooks/pre-commit).
par scripts/test_githook.sh
# 3d. scripts/run-tests-parallel.sh: a failing, missing or silently skipped script fails the run.
# 3c'. The ran-evidence mechanism (scripts/lib-ran.sh, scripts/ran-evidence.sh): the shared negative test: a refused, missing, skipped, silent or zero-count check FAILS.
par scripts/test_ran_evidence.sh
par scripts/test_run_parallel.sh
# 3e. The delta selection itself (scripts/select-tests.py): negative-tested; see 4.
par scripts/test_select_tests.sh
# 3f. The crash-record check and the quiet probe runner (scripts/lib-no-crash-record.sh): a coredumpctl entry fails the run (shim), a quiet crash leaves none.
par scripts/test_no_crash_record.sh
# 3f'. No script runs a known deliberate-crash probe binary (scripts/probe-binaries.txt) outside the helper scripts/land/bin/run-probe (private TMPDIR, ulimit -c 0 plus the dumpable-clear preload); the lint is negative-tested in vbm-land.
scripts/land/bin/run-probe --lint scripts/probe-binaries.txt .

# 3g. The diff judge of the gate-defining files (scripts/gate-diff-improving.sh): a worsening baseline, a masked or removed tier1 line, a loosened list and a shrunken protected set each FAIL.
par scripts/test_gate_diff_improving.sh
# 3h. The relabel-attack suite (scripts/relabel-attacks.sh, scripts/attacks/): every demonstrated way to relabel a gate is refused by the tree's own gates, and the suite fails when its gates are stubbed.
par scripts/test_relabel_attacks.sh

# 3f. scripts/run-scoped.sh (status, bound, an aborted run leaves no orphan; both the systemd and the fallback path) and scripts/lib-reap.sh (an aborted script leaves none of its background jobs).
par scripts/test_run_scoped.sh
par scripts/test_reap.sh

# 3i. The bench (bench/gen_corpus.py, bench/run_bench.py; docs/bench.md): a deterministic, pinned corpus; the driver refuses another corpus, a subject that disagrees with the reference and a missing comparator directory.
par scripts/test_bench.sh

# 4. The declared test scripts, in parallel; a failing, missing or silently skipped one fails Tier 1. Every scripts/test_*.sh must be declared.
for f in scripts/test_*.sh; do case " ${tests[*]} $TIER2_ONLY " in *" $f "*) ;; *) echo "tier1: $f is not declared with par" >&2; exit 1;; esac; done
# Delta selection (docs/decisions/0004-tier1-speed.md): only the tests the delta since the merge base can affect run (scripts/tests-map.txt; an unmapped file, a gate-defining file, no base: all of them).
# The gates above always run. TIER1_ALL=1 (Tier 2, the schedule, a dispatch) runs every test. A test with no map line fails here.
python3 scripts/select-tests.py --check "${tests[@]}"
mapfile -t selected < <(python3 scripts/select-tests.py)
echo "tier1: selected ${#selected[@]} of ${#tests[@]} tests: ${selected[*]:-none}"
[ ${#selected[@]} -eq 0 ] || bg tests scripts/run-tests-parallel.sh "${selected[@]}"
bgwait
scripts/ran-evidence.sh check-dir "$bgdir" scripts/ran-gates.txt   # every concurrent gate and the tests job ran something: its own count (scripts/ran-gates.txt) or a ran line
echo "tier1: ledger gate: negative self-tests ok (a baseline that claims too many proofs, or an open count that rose with no new claim, is rejected)"
nocrash_end

echo "tier1: ok"
