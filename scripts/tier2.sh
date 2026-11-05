#!/usr/bin/env bash
# Tier 2 (assurance gate, the SLOW checks; run on main after a merge, by CI: .github/workflows/core.yml):
#  1. Tier 1 (everything quick: forbidden constructs, zero-warning build, the gates with their negative self-tests).
#  2. The independent kernel re-check: `leanchecker --fresh` replays every declaration of LeanSse and LeanSseProofs in a fresh environment
#     (guards against a tampered or stale .olean).
#  3. An independent external checker (nanoda) over the exported proof of both libraries and their dependencies.
# (The axiom gate is Tier 1 here: it is instant on a library this size. The wasm32 and native builds, the bindings and the mutation metric arrive with the C interface.)
set -euo pipefail
cd "$(dirname "$0")/.."
LEAN_PREFIX=$(lean --print-prefix)

TIER1_ALL=1 scripts/tier1.sh   # every test, not the delta
echo "tier2: the pinned lander against its source (online drift check)"
scripts/land/bin/land-check --upstream
echo "tier2: the whole relabel-attack suite (the Lean attacks too; Tier 1 runs the others)"
scripts/relabel-attacks.sh
echo "tier2: leanchecker --fresh LeanSse"
lake env "$LEAN_PREFIX/bin/leanchecker" --fresh LeanSse
echo "tier2: leanchecker --fresh LeanSseProofs"
lake env "$LEAN_PREFIX/bin/leanchecker" --fresh LeanSseProofs
echo "tier2: external checker (nanoda) over the exported proof"
exp=$(mktemp); cfg=$(mktemp)
trap 'rm -f "$exp" "$cfg"' EXIT
lake env "$LEAN_PREFIX/bin/leanexport" LeanSse LeanSseProofs > "$exp"
cat > "$cfg" <<JSON
{"export_file_path":"$exp","permitted_axioms":["propext","Classical.choice","Quot.sound","Lean.trustCompiler"],"unpermitted_axiom_hard_error":false,"nat_extension":true,"string_extension":true,"print_success_message":true}
JSON
out=$("$LEAN_PREFIX/bin/nanoda_bin" "$cfg" 2>&1) || { echo "$out"; exit 1; }
grep -q "with no typechecker errors" <<<"$out" || { echo "$out"; exit 1; }
echo "$out" | sed -n 1p
echo "tier2: ok"
