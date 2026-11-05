#!/usr/bin/env bash
# Regenerate the generated paths (scripts/generated-paths.txt) from the tree as it is: build, then each gate's own --write (improvements only).
#   scripts/regen-baselines.sh      exit 0: written (or unchanged); exit 3: a gate does NOT pass against the baseline on disk, i.e. the measured value is WORSE
#                                   than the baseline (or the gate is broken): nothing of that gate is written. A deliberate worsening is a baseline edit made by
#                                   the PR's author and approved by the owner (the baselines are protected paths), never by this script.
# Used by scripts/land-direct after it took main's version of a conflicting baseline. Run from the repo root (mise exec -- ...).
set -euo pipefail
cd "$(dirname "$0")/.."
lake build LeanSse LeanSseProofs >/dev/null     # fresh .olean/IR: the gates read what the build just produced
worse() { echo "regen-baselines: $1 does not pass against the baseline on disk: the measured value is worse (or the gate is broken); not written" >&2; exit 3; }
lake env lean --run scripts/ClosureGate.lean >/dev/null || worse scripts/closure-baseline.txt
lake env lean --run scripts/ClosureGate.lean --write >/dev/null
lake env lean --run scripts/LedgerGate.lean >/dev/null || worse scripts/ledger-baseline.txt     # also renders docs/proof-ledger.md
lake env lean --run scripts/LedgerGate.lean --write >/dev/null
scripts/test_vectors.sh --write >/dev/null     # the vectors baseline: a change of the reference is a change of the row set (a bare regeneration, reviewed on main)
echo "regen-baselines: ok"
