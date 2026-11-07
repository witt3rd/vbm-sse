#!/usr/bin/env bash
# Build the freestanding wasm32 module of the SSE reader: the generated C of the LeanSse modules (lake's IR output), the unmodified ABI shim abi/vbm_sse.c, and runtime/rt.c
# (the trusted freestanding runtime), compiled by the Lean toolchain's clang with --target=wasm32 -nostdlib and linked by its ld.lld (wasm flavour). No libc, no WASI, no imports.
# Env (self-tests only): VBM_RT_C replaces runtime/rt.c, VBM_ABI_C replaces abi/vbm_sse.c, VBM_LD_EXTRA adds linker flags.
# Usage: build_wasm.sh OUT.wasm [EXTRA.c...]   (run from anywhere; lake must have built LeanSse:static). Prints the size.
set -euo pipefail
here=$(cd "$(dirname "$0")/.." && pwd); cd "$here"
out=${1:?usage: build_wasm.sh OUT.wasm}; shift
tc=$(lean --print-prefix)
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
cf=(--target=wasm32 -nostdlib -O2 -ffreestanding -nostdlibinc -mbulk-memory -DNDEBUG -I"$here/runtime/include" -I"$tc/include")
objs=()
for f in Spec Stream Fast Abi; do
  [ -f ".lake/build/ir/LeanSse/$f.c" ] || { echo "build_wasm: .lake/build/ir/LeanSse/$f.c missing: run lake build LeanSse:static first" >&2; exit 1; }
  # Fast.c calls the search and the CPU test of the pinned vbm-simd (T13) directly: it is compiled with that package's trusted header, as the package's own modules are
  clang "${cf[@]}" -include .lake/packages/vbm-simd/include/vbm_simd.h -c ".lake/build/ir/LeanSse/$f.c" -o "$tmp/$f.o"; objs+=("$tmp/$f.o")
done
# the pinned verified library vbm-simd (lake package): the generated C of the modules the machine imports, compiled with its trusted header (include/vbm_simd.h of that package; its x86-64 AVX2 body is compiled only for x86-64)
dep=.lake/packages/vbm-simd
for f in Spec Lanes Shims Find; do
  [ -f "$dep/.lake/build/ir/VbmSimd/$f.c" ] || { echo "build_wasm: $dep/.lake/build/ir/VbmSimd/$f.c missing: run lake build LeanSse:static first" >&2; exit 1; }
  clang "${cf[@]}" -include "$dep/include/vbm_simd.h" -c "$dep/.lake/build/ir/VbmSimd/$f.c" -o "$tmp/simd$f.o"; objs+=("$tmp/simd$f.o")
done
clang "${cf[@]}" -Wall -Wextra -Werror -c "${VBM_ABI_C:-abi/vbm_sse.c}" -o "$tmp/abi.o"; objs+=("$tmp/abi.o")
clang "${cf[@]}" -Wall -Wextra -Werror -c "${VBM_RT_C:-runtime/rt.c}" -o "$tmp/rt.o"; objs+=("$tmp/rt.o")
for x in "$@"; do clang "${cf[@]}" -c "$x" -o "$tmp/x$(basename "$x").o"; objs+=("$tmp/x$(basename "$x").o"); done
ld.lld -flavor wasm -error-limit=0 --no-entry --gc-sections --export-memory -z stack-size=1048576 --max-memory=2147483648 \
  --export=vbm_sse_new --export=vbm_sse_feed --export=vbm_sse_free --export=vbm_sse_wasm_alloc --export=vbm_sse_wasm_dealloc --export=vbm_sse_wasm_live ${VBM_LD_EXTRA:-} -o "$out" "${objs[@]}"
echo "build_wasm: $out $(stat -c %s "$out") bytes"
