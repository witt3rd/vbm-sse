#!/usr/bin/env bash
# Tier 1: the ABI description (abi/vbm_sse.abi.json), the C header (include/vbm_sse.h) and the report layout documented in LeanSse/Abi.lean agree (scripts/check_abi.py), shown able to fail on 17 drifted
# variants (a changed enumerator, a retyped or renamed parameter, a removed function, a reordered struct field, a report word reordered or renamed, ...). The compiled library and the vectors are
# scripts/test_native.sh; the generated bindings are scripts/test_bindings.sh. Run: mise exec -- scripts/test_abi.sh
set -euo pipefail
cd "$(dirname "$0")/.."
. scripts/lib-ran.sh   # ran_case / ran_done / must_fail: the self-tests count what they executed and a refused tool is a failure (docs/decisions/0002-ran-evidence.md)
python3 scripts/check_abi.py --selftest; ran_case
ran_done test_abi
echo "test_abi: ok"
