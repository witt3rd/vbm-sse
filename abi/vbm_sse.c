/* abi/vbm_sse.c: the C edge of vbm-sse. TRUSTED, unverified (docs/trust-ledger.md). It moves bytes: it copies a chunk into a Lean ByteArray, calls the Lean exports (LeanSse/Abi.lean: the machine, and the
 * report's layout, are decided there), and hands the caller the report's bytes. Contract: include/vbm_sse.h. It decides nothing about SSE. */
#include "../include/vbm_sse.h"
#if __STDC_HOSTED__
#include <lean/lean.h>
#else
#include "lean_mini.h"   /* freestanding: no libc header is reachable (-ffreestanding -nostdinc); the few lean.h names this file uses, as lean.h defines them (tests/lean_layout.c checks that) */
#endif
/* No libc symbol is referenced from this file: no malloc/free (the reader lives in a Lean ByteArray), no memcpy (the loop below, which the compiler may not turn back into a call), no pthread_once. */
#ifndef memcpy   /* tests substitute their own */
__attribute__((no_builtin("memcpy"))) static void *vbm_copy_(void *d, const void *s, size_t n) {
  unsigned char *dp = d; const unsigned char *sp = s;
  while (n > 7) { uint64_t w; __builtin_memcpy_inline(&w, sp, 8); __builtin_memcpy_inline(dp, &w, 8); dp += 8; sp += 8; n -= 8; }
  while (n--) *dp++ = *sp++;
  return d;
}
#define memcpy vbm_copy_
#endif

_Static_assert(__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__, "the report is little-endian u64 words: a little-endian host is required");

lean_object *vbm_sse_lean_new(lean_object *unit);                     /* the Lean exports (LeanSse/Abi.lean) */
lean_object *vbm_sse_lean_feed(lean_object *state, lean_object *chunk);   /* consumes both, returns the new state */
lean_object *vbm_sse_lean_report(lean_object *state);                 /* consumes the state reference it is given, returns a ByteArray */
lean_object *initialize_vbm_x2dsse_LeanSse_Abi(uint8_t builtin);        /* Lean 4.35 names it package_Module; it also initialises the runtime and Init */

/* Once-only initialisation: 0 = not started, 1 = running, 2 = done. A concurrent first caller waits for the first to finish. */
static int once_state_;
static int init_ok_;

static void init_once_(void) {
  int expect = 0;
  if (__atomic_compare_exchange_n(&once_state_, &expect, 1, 0, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) {
    lean_object *r = initialize_vbm_x2dsse_LeanSse_Abi(1);
    init_ok_ = lean_io_result_is_ok(r);
    lean_dec_ref(r);
    lean_io_mark_end_initialization();
    __atomic_store_n(&once_state_, 2, __ATOMIC_RELEASE);
  } else {
    while (__atomic_load_n(&once_state_, __ATOMIC_ACQUIRE) != 2) { }
  }
}

/* A reader: the Lean state, and the report of the last chunk. It lives in the payload of a Lean ByteArray (the Lean heap is the only heap the library has); the two pointers are never traced by
 * Lean (a scalar array has no children), this file releases them. */
struct vbm_sse { lean_object *state; lean_object *report; };

static lean_object *box_of_(vbm_sse *r) { return (lean_object *)((unsigned char *)r - __builtin_offsetof(lean_sarray_object, m_data)); }

int vbm_sse_new(vbm_sse **out) {
  if (!out) return VBM_SSE_ARG;
  *out = 0;
  init_once_();
  if (!init_ok_) return VBM_SSE_INTERNAL;
  lean_object *b = lean_alloc_sarray(1, sizeof(struct vbm_sse), sizeof(struct vbm_sse));
  struct vbm_sse *r = (struct vbm_sse *)lean_sarray_cptr(b);
  r->state = vbm_sse_lean_new(lean_box(0));
  r->report = 0;
  *out = r;
  return VBM_SSE_OK;
}

int vbm_sse_feed(vbm_sse *r, const uint8_t *buf, size_t len, vbm_sse_report *rep) {
  if (rep) { rep->bytes = 0; rep->nbytes = 0; }
  if (!r || !rep || (!buf && len) || len >= (size_t)LEAN_MAX_SMALL_NAT) return VBM_SSE_ARG;
  if (r->report) { lean_dec_ref(r->report); r->report = 0; }
  lean_object *in = lean_alloc_sarray(1, len, len);
  if (len) memcpy(lean_sarray_cptr(in), buf, len);
  r->state = vbm_sse_lean_feed(r->state, in);          /* consumes the state and the chunk */
  lean_inc_ref(r->state);                              /* the report call consumes one reference; the reader keeps its own */
  r->report = vbm_sse_lean_report(r->state);
  rep->bytes = lean_sarray_cptr(r->report);
  rep->nbytes = lean_sarray_size(r->report);
  return VBM_SSE_OK;
}

void vbm_sse_free(vbm_sse *r) {
  if (!r) return;
  if (r->report) lean_dec_ref(r->report);
  lean_dec_ref(r->state);
  lean_dec_ref(box_of_(r));
}
