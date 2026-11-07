#!/usr/bin/env bash
# docs/perf/run.sh OUT: build the freestanding library and docs/perf/prof.c in OUT, generate the corpora, print the 15-row table (MB/s, core cycles/byte, instructions/byte, events) and the load. Run from the repo root under `mise exec --`.
set -euo pipefail
here=$(cd "$(dirname "$0")/../.." && pwd); cd "$here"
out=${1:?usage: run.sh OUT}; mkdir -p "$out/corp"
scripts/build_native.sh "$out/lib" --no-so >/dev/null
cc -O2 -g -I include -o "$out/prof" docs/perf/prof.c "$out/lib/libvbm_sse.a"   # the library is freestanding: any C compiler links it
python3 bench/gen_corpus.py "$out/corp" >/dev/null
echo "load: $(cut -d' ' -f1-3 /proc/loadavg)"
printf '%-14s %6s %9s %9s %9s %8s\n' corpus chunk MB/s cyc/byte ins/byte events
for c in small-events large-data ends-crlf ends-cr ends-mixed; do for k in 1 7 4096; do
  read -r mb cpb ipb ev < <("$out/prof" "$out/corp/$c.sse" "$k" bench); printf '%-14s %6s %9s %9s %9s %8s\n' "$c" "$k" "$mb" "$cpb" "$ipb" "$ev"
done; done
echo "load: $(cut -d' ' -f1-3 /proc/loadavg)"
