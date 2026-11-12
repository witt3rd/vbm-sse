#!/usr/bin/env bash
# Tier 1 (the landing check): build, the guards that ARE the verified product, and the real tests. Nothing else refuses a landing.
#   guards: no sorry/axiom/unsafe in Lean sources; Init-only imports; the pinned library matches its lock; a warning-free build; only the standard axioms; a new trusted boundary has a trust-ledger entry; no secret or internal name in the tree.
#   reported, never gated: the specified share and the closure/ledger counts.
# Run from the repo root: mise exec -- scripts/tier1.sh.
set -euo pipefail
cd "$(dirname "$0")/.."

lean_sources() { find LeanSse LeanSseProofs abi vectors -name '*.lean' 2>/dev/null; ls LeanSse.lean LeanSseProofs.lean 2>/dev/null; }
# 1. Forbidden constructs in Lean sources; a comment may mention one only on a line marked `-- tier1-allow`.
bad=$(grep -HnE '\b(sorry|admit|axiom|unsafe|implemented_by|csimp)\b' $(lean_sources) | grep -v 'tier1-allow' || true)
if [ -n "$bad" ]; then echo "tier1: forbidden construct(s):" >&2; echo "$bad" >&2; exit 1; fi
# 1a. LeanSse imports Init (implicit), its own modules and the pinned VbmSimd only.
bad=$(grep -HnE '^[[:space:]]*((public|meta|private)[[:space:]]+)*(import|prelude)\b' $(find LeanSse -name '*.lean') LeanSse.lean | grep -vE ':[0-9]+:import (LeanSse|VbmSimd)(\.[A-Za-z0-9_]+)*[[:space:]]*$' || true)
if [ -n "$bad" ]; then echo "tier1: LeanSse may import only LeanSse modules and VbmSimd:" >&2; echo "$bad" >&2; exit 1; fi
# 1d. The pinned verified library is the locked one.
.land/tool/bin/land-pin verify
# 2. Build (warningAsError is set in lakefile.lean), once, for the guards and every test.
lake build LeanSse LeanSseProofs LandLedger
lake build LeanSse:static vbm-sse-vectors   # also once: the tests below each build these targets, and several cold builds in one tree race
# 2a. Only the standard axioms. 2d. A new trusted boundary has a trust-ledger entry. 2e. No secret or internal name in the tree.
.land/tool/bin/land-lean axiom
.land/tool/bin/land-lean trust
.land/tool/bin/land-lean recheck --selftest   # every proof replayed by Lean's own checker in a fresh process (vbm-land docs/lean-gates.md)
.land/tool/bin/land-lean ledger --selftest   # the obligation ledger: docs/proof-ledger.md rendered, every theorem checked, the clause tags, the reach rule and the ratchet (vbm-land docs/lean-gates.md)
scripts/scrub.py
# Reported, not gated: the specified share and the closure counts.
lake env lean --run scripts/ClosureGate.lean || true
# 4. The real tests, in parallel.
.land/tool/bin/run-tests-parallel scripts/test_vectors.sh scripts/test_abi.sh scripts/test_native.sh scripts/test_wasm.sh scripts/test_bindings.sh
echo "tier1: ok"
