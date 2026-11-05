/* The C side of the throughput bench (docs/bench.md): the compiled library (the freestanding build, scripts/build_native.sh) through its C interface, as a consumer calls it.
 *   bench FILE CHUNK     feeds FILE to a fresh reader in chunks of CHUNK bytes, five times, and prints  MB/S events E  for the fastest run (MB = 10^6 bytes).
 * The file is read before the clock starts; the report of every chunk is read for its event count (the first word), the way a consumer must, and nothing more. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "vbm_sse.h"

int main(int argc, char **argv) {
  if (argc != 3) { fprintf(stderr, "usage: bench FILE CHUNK\n"); return 2; }
  size_t chunk = (size_t)strtoul(argv[2], NULL, 10);
  FILE *f = fopen(argv[1], "rb");
  if (!f || chunk == 0) return 2;
  fseek(f, 0, SEEK_END); long n = ftell(f); rewind(f);
  unsigned char *b = malloc((size_t)n);
  if (!b || fread(b, 1, (size_t)n, f) != (size_t)n) return 2;
  fclose(f);
  double best = 1e18; unsigned long long evs = 0;
  for (int rep = 0; rep < 5; rep++) {
    vbm_sse *r; vbm_sse_report rp; unsigned long long e = 0;
    if (vbm_sse_new(&r) != VBM_SSE_OK) return 3;
    struct timespec a, z; clock_gettime(CLOCK_MONOTONIC, &a);
    for (long i = 0; i < n; i += (long)chunk) {
      size_t m = (size_t)(n - i) < chunk ? (size_t)(n - i) : chunk;
      if (vbm_sse_feed(r, b + i, m, &rp) != VBM_SSE_OK) return 3;
      unsigned long long c; memcpy(&c, rp.bytes, 8); e += c;
    }
    clock_gettime(CLOCK_MONOTONIC, &z);
    double el = (double)(z.tv_sec - a.tv_sec) + (double)(z.tv_nsec - a.tv_nsec) / 1e9;
    if (el < best) best = el;
    evs = e; vbm_sse_free(r);
  }
  printf("%.1f events %llu\n", (double)n / 1e6 / best, evs);
  return 0;
}
