/* docs/perf/prof.c: the profiling harness of docs/perf/README.md. NOT part of the library, not built by any gate. Feeds a file to the compiled library through the C ABI, in chunks.
 *   prof FILE CHUNK bench             -> "MB/s cycles_per_byte instructions_per_byte events" (best of the full passes of two seconds, at least five)
 *   prof FILE CHUNK isample SECONDS OUT -> the same, sampled every 2003 retired user instructions (perf_event_open overflow signal)
 *   prof FILE CHUNK sample SECONDS OUT -> SIGPROF sampler (ITIMER_PROF, 1 kHz): one instruction pointer per line (hex), first line the address of main; resolve with docs/perf/resolve.py */
#define _GNU_SOURCE
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <sys/time.h>
#include <time.h>
#include <ucontext.h>
#include <x86intrin.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/syscall.h>
#include <linux/perf_event.h>
#include "vbm_sse.h"

static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + t.tv_nsec / 1e9; }
static uintptr_t *samples; static size_t nsamp, capsamp;
static void on_prof(int sig, siginfo_t *si, void *uc) { (void)sig; (void)si; if (nsamp < capsamp) samples[nsamp++] = ((ucontext_t *)uc)->uc_mcontext.gregs[REG_RIP]; }

/* user-mode hardware counters of this thread (perf_event_open; needs perf_event_paranoid <= 2): instructions are deterministic, cycles survive load better than seconds.
 * The counters are shared with other users of the machine: a pass counts only if its counter ran for the whole pass (time_running == time_enabled). */
static int pe_open(unsigned long long cfg) { struct perf_event_attr a; memset(&a, 0, sizeof a); a.type = PERF_TYPE_HARDWARE; a.size = sizeof a; a.config = cfg; a.exclude_kernel = 1; a.exclude_hv = 1; a.read_format = PERF_FORMAT_TOTAL_TIME_ENABLED | PERF_FORMAT_TOTAL_TIME_RUNNING; return (int)syscall(SYS_perf_event_open, &a, 0, -1, -1, 0); }
struct pe { unsigned long long v, en, run; };
static struct pe pe_read(int fd) { struct pe p = {0, 0, 0}; if (fd < 0 || read(fd, &p, sizeof p) != (ssize_t)sizeof p) p.v = p.en = p.run = 0; return p; }

static unsigned long long pass(const unsigned char *b, long n, size_t chunk) {
  vbm_sse *r; vbm_sse_report rp; unsigned long long e = 0;
  if (vbm_sse_new(&r) != VBM_SSE_OK) exit(3);
  for (long i = 0; i < n; i += (long)chunk) {
    size_t m = (size_t)(n - i) < chunk ? (size_t)(n - i) : chunk;
    if (vbm_sse_feed(r, b + i, m, &rp) != VBM_SSE_OK) exit(3);
    unsigned long long c; memcpy(&c, rp.bytes, 8); e += c;
  }
  vbm_sse_free(r); return e;
}

int main(int argc, char **argv) {
  if (argc < 4) return 2;
  FILE *f = fopen(argv[1], "rb"); if (!f) return 2; fseek(f, 0, SEEK_END); long n = ftell(f); rewind(f);
  unsigned char *b = malloc(n); if (fread(b, 1, n, f) != (size_t)n) return 2; fclose(f);
  size_t chunk = strtoul(argv[2], NULL, 10); if (!chunk) return 2;
  unsigned long long evs = pass(b, n, chunk);   /* warm-up + runtime init */
  if (!strcmp(argv[3], "bench")) {
    int fi = pe_open(PERF_COUNT_HW_INSTRUCTIONS), fc = pe_open(PERF_COUNT_HW_CPU_CYCLES);
    double best = 1e18; unsigned long long bc = ~0ull, bi = ~0ull;
    double t0 = now(); int nv = 0; for (int w = 0; (w < 5 || now() - t0 < 2.0 || nv < 3) && now() - t0 < 15.0; w++) {
      struct pe i0 = pe_read(fi), c0 = pe_read(fc); double a = now(); pass(b, n, chunk); double e = now() - a; struct pe i1 = pe_read(fi), c1 = pe_read(fc);
      if (e < best) best = e;
      if (c1.en - c0.en == c1.run - c0.run && c1.run > c0.run && i1.en - i0.en == i1.run - i0.run && i1.run > i0.run) nv++;
      if (c1.en - c0.en == c1.run - c0.run && c1.run > c0.run && c1.v - c0.v < bc) bc = c1.v - c0.v;
      if (i1.en - i0.en == i1.run - i0.run && i1.run > i0.run && i1.v - i0.v < bi) bi = i1.v - i0.v; }
    printf("%.1f %.2f %.2f %llu\n", n / 1e6 / best, bc == ~0ull ? -1.0 : (double)bc / n, bi == ~0ull ? -1.0 : (double)bi / n, evs); return 0;   /* MB/s, core cycles per byte, instructions per byte, events */
  }
  if (!strcmp(argv[3], "sample") && argc > 5) {
    double secs = atof(argv[4]);
    capsamp = 1u << 22; samples = malloc(capsamp * sizeof *samples);
    struct sigaction sa; memset(&sa, 0, sizeof sa); sa.sa_sigaction = on_prof; sa.sa_flags = SA_SIGINFO | SA_RESTART; sigaction(SIGPROF, &sa, NULL);
    struct itimerval tv = { {0, 1000}, {0, 1000} }; setitimer(ITIMER_PROF, &tv, NULL);
    double a = now(); while (now() - a < secs) pass(b, n, chunk);
    memset(&tv, 0, sizeof tv); setitimer(ITIMER_PROF, &tv, NULL);
    FILE *o = fopen(argv[5], "w"); fprintf(o, "%lx\n", (unsigned long)(uintptr_t)&main);
    for (size_t i = 0; i < nsamp; i++) fprintf(o, "%lx\n", (unsigned long)samples[i]); fclose(o); return 0;
  }
  if (!strcmp(argv[3], "isample") && argc > 5) {   /* the same, but a sample every 2003 retired user instructions (counter overflow -> SIGIO): the profile is by instructions, deterministic, not by time */
    double secs = atof(argv[4]);
    capsamp = 1u << 22; samples = malloc(capsamp * sizeof *samples);
    struct sigaction sa; memset(&sa, 0, sizeof sa); sa.sa_sigaction = on_prof; sa.sa_flags = SA_SIGINFO | SA_RESTART; sigaction(SIGIO, &sa, NULL);
    struct perf_event_attr a; memset(&a, 0, sizeof a); a.type = PERF_TYPE_HARDWARE; a.size = sizeof a; a.config = PERF_COUNT_HW_INSTRUCTIONS; a.sample_period = 2003; a.exclude_kernel = 1; a.exclude_hv = 1; a.wakeup_events = 1;
    int fd = (int)syscall(SYS_perf_event_open, &a, 0, -1, -1, 0); if (fd < 0) { perror("perf_event_open"); return 2; }
    fcntl(fd, F_SETFL, O_ASYNC); fcntl(fd, F_SETSIG, SIGIO); fcntl(fd, F_SETOWN, (int)getpid());
    double t = now(); while (now() - t < secs) pass(b, n, chunk);
    close(fd);
    FILE *o = fopen(argv[5], "w"); fprintf(o, "%lx\n", (unsigned long)(uintptr_t)&main);
    for (size_t i = 0; i < nsamp; i++) fprintf(o, "%lx\n", (unsigned long)samples[i]); fclose(o); return 0;
  }
  return 2;
}
