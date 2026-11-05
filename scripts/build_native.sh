#!/usr/bin/env bash
# Build the FREESTANDING native library of the SSE reader: the generated C of the LeanSse modules (lake's IR output), the ABI shim abi/vbm_sse.c and runtime/rt.c (the same trusted runtime the wasm
# build links), compiled with the Lean toolchain's clang -ffreestanding -nostdlib -nostdlibinc (the stub headers of runtime/include, never the system's) and combined into ONE relocatable object whose only
# global symbols are the ABI's (vbm_sse_new, vbm_sse_feed, vbm_sse_free): the runtime's own malloc/memcpy/... become local, so they cannot clash with, or be mistaken for, a libc. No libc symbol is referenced:
# `nm -u` of the result is EMPTY, and the script fails otherwise. Outputs in OUTDIR: libvbm_sse.a (static), libvbm_sse.so (links with no libc and no Lean prefix), vbm_sse.o.
# Env (self-tests only): VBM_RT_C replaces runtime/rt.c, VBM_ABI_C replaces abi/vbm_sse.c; VBM_EXTRA_C adds C files (compiled like the rest), VBM_KEEP adds global symbols to keep (to prove the nm check can fail).
# Usage: build_native.sh OUTDIR [--no-so]   (run from anywhere; lake must have built LeanSse:static first, this script does it). Prints the sizes.
set -euo pipefail
here=$(cd "$(dirname "$0")/.." && pwd); cd "$here"
out=${1:?usage: build_native.sh OUTDIR}; mkdir -p "$out"
lake build LeanSse:static >/dev/null
tc=$(lean --print-prefix)
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
cf=(-ffreestanding -nostdlib -nostdlibinc -fno-stack-protector -fno-builtin -ffunction-sections -fdata-sections -O2 -fPIC -DNDEBUG -I"$here/runtime/include" -I"$tc/include")
objs=()
for f in Spec Stream Fast Abi; do
  [ -f ".lake/build/ir/LeanSse/$f.c" ] || { echo "build_native: .lake/build/ir/LeanSse/$f.c missing" >&2; exit 1; }
  clang "${cf[@]}" -c ".lake/build/ir/LeanSse/$f.c" -o "$tmp/$f.o"; objs+=("$tmp/$f.o")
done
# the shim is compiled as the scorecard compiles it: freestanding, with the Lean include directory only (lean_mini.h stands in for lean.h); the runtime with the stub headers
clang -ffreestanding -nostdlib -nostdinc -ffunction-sections -fdata-sections -O2 -fPIC -DNDEBUG -Wall -Wextra -Werror -I include -I "$tc/include" -c "${VBM_ABI_C:-abi/vbm_sse.c}" -o "$tmp/abi.o"; objs+=("$tmp/abi.o")
clang "${cf[@]}" -Wall -Wextra -Werror -c "${VBM_RT_C:-runtime/rt.c}" -o "$tmp/rt.o"; objs+=("$tmp/rt.o")
for x in ${VBM_EXTRA_C:-}; do clang "${cf[@]}" -c "$x" -o "$tmp/x$(basename "$x").o"; objs+=("$tmp/x$(basename "$x").o"); done
keep=(vbm_sse_new vbm_sse_feed vbm_sse_free ${VBM_KEEP:-})
und_args=(); for k in "${keep[@]}"; do und_args+=(--undefined="$k"); done
ld.lld -r --gc-sections "${und_args[@]}" -o "$tmp/all.o" "${objs[@]}"
printf '%s\n' "${keep[@]}" > "$tmp/keep.txt"
objcopy --keep-global-symbols="$tmp/keep.txt" "$tmp/all.o" "$out/vbm_sse.o"
rm -f "$out/libvbm_sse.a"; llvm-ar rcs "$out/libvbm_sse.a" "$out/vbm_sse.o"
und=$(nm -u "$out/vbm_sse.o" | sed 's/^ *U //')
if [ -n "$und" ]; then echo "build_native: the library references symbols it does not define (a libc leak): $(echo $und)" >&2; exit 1; fi
if [ "${2:-}" != --no-so ]; then
  ld.lld -shared -z noexecstack --gc-sections --no-undefined -o "$out/libvbm_sse.so" "$out/vbm_sse.o"
  und=$(nm -D -u "$out/libvbm_sse.so" | sed 's/^ *U //')
  if [ -n "$und" ]; then echo "build_native: libvbm_sse.so imports symbols (a libc leak): $(echo $und)" >&2; exit 1; fi
fi
echo "build_native: $out: libvbm_sse.a $(stat -c %s "$out/libvbm_sse.a") bytes, vbm_sse.o $(stat -c %s "$out/vbm_sse.o") bytes, nm -u: none"
[ -f "$out/libvbm_sse.so" ] && echo "build_native: libvbm_sse.so $(stat -c %s "$out/libvbm_sse.so") bytes"
true
