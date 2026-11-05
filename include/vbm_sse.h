/* vbm_sse.h: the C ABI of vbm-sse. A Server-Sent Events reader: the event-stream algorithm of the HTML Standard (9.2.5, 9.2.6), verified in Lean. What an event is, and how a stream is cut
 * into lines, fields and events, is decided in Lean only; this header and abi/vbm_sse.c move bytes. Prefix vbm_sse_ (functions, types) and VBM_SSE_ (constants). Stable within
 * ABI version VBM_SSE_ABI_VERSION; an ABI change is expand-and-contract.
 *
 * USE: vbm_sse_new makes a reader; each chunk of the stream, in order and cut anywhere (an empty chunk is allowed; a CR LF or a byte order mark may be split), goes to vbm_sse_feed, which
 * returns a REPORT: the events that chunk completed, the last event ID and the reconnection time. The events do not depend on how the stream is cut (theorem chunk_invariance).
 * There is no error in the stream: every byte string is a stream. The only refusals are a bad argument and a failure of the library itself.
 *
 * THE REPORT (little-endian u64 words; a little-endian host is required: the build refuses others), in this order:
 *   count      the number of events this chunk completed
 *   retry_set  1 if a `retry` field has set the reconnection time (on this stream so far), else 0
 *   retry      the reconnection time in milliseconds (0 if retry_set is 0); a longer number in the stream saturates at 2^64 - 1
 *   id_len     the length of the last event ID string (the string a reconnecting client sends as Last-Event-ID)
 *   then id_len bytes: the last event ID string
 *   then `count` events, in stream order, each: type_len, data_len, id_len (u64 words), then type_len bytes of type, data_len bytes of data, id_len bytes of last event ID at dispatch.
 * Values are byte strings (the stream's bytes, not decoded; the standard decodes them as UTF-8, a step a caller takes on each value).
 * MEMORY: the reader and its report are in the library's own heap (a Lean heap: no libc). The report is valid until the next vbm_sse_feed or vbm_sse_free on that reader; copy what you keep.
 * LIMITS: no bound on a line or on the data of an event (open claim `bounded-state`): a hostile stream grows the reader. A chunk of LEAN_MAX_SMALL_NAT bytes or more (2^63 - 1 on a 64-bit host, 2^31 - 1 in WebAssembly) is refused (VBM_SSE_ARG).
 * THREADS: the first call initialises the Lean runtime (once; an atomic flag, a concurrent first caller waits). A reader is for one thread at a time; concurrent calls on different readers are not yet tested or promised. */
#ifndef VBM_SSE_H
#define VBM_SSE_H
#if __STDC_HOSTED__
#include <stddef.h>
#include <stdint.h>
#else   /* freestanding (-ffreestanding -nostdinc): the types from the compiler's own macros, no header */
typedef __SIZE_TYPE__ size_t; typedef __UINTPTR_TYPE__ uintptr_t; typedef __UINT8_TYPE__ uint8_t; typedef __UINT64_TYPE__ uint64_t;
#endif
#ifdef __cplusplus
extern "C" {
#endif

#define VBM_SSE_ABI_VERSION 1u

/* Result codes. */
enum { VBM_SSE_OK = 0, VBM_SSE_ARG = 1, VBM_SSE_INTERNAL = 2 };

/* A reader (opaque). */
typedef struct vbm_sse vbm_sse;

/* A report: nbytes bytes at bytes, laid out as above. Valid until the next feed or free on its reader. */
typedef struct vbm_sse_report {
  const uint8_t *bytes;
  size_t nbytes;
} vbm_sse_report;

/* Make a reader: *out. VBM_SSE_OK, or VBM_SSE_ARG (out is NULL) or VBM_SSE_INTERNAL (the Lean runtime did not start); on a non-OK code *out is NULL. */
int vbm_sse_new(vbm_sse **out);

/* Feed buf[0..len) (the next chunk of the stream) to the reader and return its report in *rep. VBM_SSE_ARG: r or rep is NULL, buf is NULL with a nonzero len, or len is too large; *rep is zeroed. */
int vbm_sse_feed(vbm_sse *r, const uint8_t *buf, size_t len, vbm_sse_report *rep);

/* Release a reader and its last report. Safe on NULL. */
void vbm_sse_free(vbm_sse *r);

#ifdef __cplusplus
}
#endif
#endif
