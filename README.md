# vbm-sse

A Server-Sent Events (SSE) stream reader whose correctness is a machine-checked theorem, written once in Lean 4. It implements the event-stream algorithm of the [HTML Standard](https://html.spec.whatwg.org/multipage/server-sent-events.html#parsing-an-event-stream) (sections 9.2.5 and 9.2.6): line splitting on CR, LF and CR LF, field parsing, the byte order mark, event dispatch, `id` and `retry`.

> **Status: pre-release.** The specification, the reference reader, the incremental and array readers, their proofs, the C interface, the freestanding native library, the WebAssembly module and the generated Python and Rust bindings exist. Nothing is published to a package registry. Build from source.

## What is proved

**The events of a stream do not depend on how it arrives.** Cut the bytes into chunks anywhere (between a CR and its LF, inside a byte order mark, inside a field name, one byte at a time) and the incremental reader yields exactly the events, the last event ID and the reconnection time that the whole-buffer reference yields for the concatenation (`chunk_invariance`). A chunk with no line terminator completes nothing, and the unterminated end of a stream is discarded, never dispatched, as the standard says.

The reference is the standard's algorithm written as a pure Lean function over bytes, and the four examples of the standard are theorems about it. The claims, each tagged with the clause of the standard it is about, and which are proved, partial, open or a stated limit, are in [`docs/proof-ledger.md`](docs/proof-ledger.md) (generated). Only a `proved` claim is called verified anywhere in this repository. The array reader that the C interface runs is proved equal to the reference on every chunking (`fast_eq_parse`), and the report the C interface returns is proved to say what the reader holds (`report_decodes`). What is still open: decoding values as UTF-8 text (values are bytes today), a bound on line and buffer size, and a bulk scan for line terminators (the array reader still takes one byte at a time; see below for what that costs).

## Speed, stated honestly

The array reader takes one byte at a time (the bulk scan for line ends is not written yet), so it is **not fast**: on a 3.6 MB stream of small chat-completion-shaped events, cut into 4096-byte chunks, the compiled freestanding library runs at about 60 MB/s through its C interface on one core, where the npm package `eventsource-parser` runs at about 900 MB/s and the Rust crate `eventsource-stream` at about 130 MB/s on the same bytes (a local run; the scorecard's card, stamped with the commit, is the number of record). The bench, its deterministic corpus (five streams, three chunk sizes), the comparators and the known differences are in [`docs/bench.md`](docs/bench.md); it exists so that the next landing has a number to move. Verified here means the events are right, not that they are quick.

## Why

Hand-written SSE readers disagree on the details that matter: a CR LF split across two network reads becomes two line ends; `data:` lines are taken one message each instead of being joined; a leading byte order mark or a `:` comment shows up as data. The standard is short and exact, so here it is a theorem: one reader, one set of generated test vectors, the same answer for every chunking.

## The ethos: verified bare metal (VBM)

Part of the [VBM standard](https://github.com/witt3rd/vbm) family of small verified libraries (see also [vbm-json](https://github.com/witt3rd/vbm-json)). Verified: proofs, not tests. Bare metal: the core imports only Lean's `Init`, so the C and WebAssembly generated from it need no libc (`nm -u` of the native library is empty; the WebAssembly module has no imports). Correct by construction: the specification is the code that runs; the vectors are generated from the reference and run through every target and binding. Built agentically: coding agents wrote the specification and proofs under mechanical gates (no `sorry`, no new axiom, proved claims and specified share only go up, every gate has a negative self-test).

## Use it (Lean)

```lean
import LeanSse
open LeanSse

-- one chunk at a time: `feed` returns the new state and the events that chunk completed
def demo : List Event :=
  let (s, e1) := feed {} (ascii "data: hel")
  let (s, e2) := feed s (ascii "lo\r")        -- the CR ends a line; its LF arrives in the next chunk
  let (_, e3) := feed s (ascii "\n\r\n")      -- the LF is that CR's own; the lone CR ends the blank line
  e1 ++ e2 ++ e3                                -- one event: type "message", data "hello", last event ID ""
```


Values are byte strings (`List UInt8`); `LeanSse.Event` has `type`, `data` and `lastEventId`; the state's `p.lastEventId` and `p.retry` carry the stream's last event ID and reconnection time.

## Use it (C, WebAssembly, Python, Rust)

The C interface is [`include/vbm_sse.h`](include/vbm_sse.h): `vbm_sse_new`, `vbm_sse_feed` (one chunk in, a report out: the events that chunk completed, the last event ID, the reconnection time) and `vbm_sse_free`. `scripts/build_native.sh DIR` builds `libvbm_sse.a` and `.so` with no libc, `scripts/build_wasm.sh FILE.wasm` the WebAssembly module (about 23 KB, no imports). The Python and Rust bindings in [`bindings/`](bindings) are generated from [`abi/vbm_sse.abi.json`](abi/vbm_sse.abi.json):

```python
from vbm_sse import Reader
with Reader() as r:
    events = r.feed(b"data: hel").events + r.feed(b"lo\r").events + r.feed(b"\n\r\n").events   # one event: data b"hello"
```

## Build and test

```sh
mise install
mise exec -- scripts/tier1.sh      # the check: build with zero warnings, the guards and the real tests
```

Requires [mise](https://mise.jdx.dev) (it installs the pinned Lean, 4.35.0), `git`, `python3` and a C compiler. Tier 1 also runs the WebAssembly test (`node`, 18 or later) and the Rust binding test (`cargo`, 1.78 or later: the lock file is version 4; a distribution's older cargo fails): a check whose tool is missing is a FAILURE, not a skip, unless you say `VBM_ALLOW_SKIP=1` (the skipped part is then named as not run; Tier 2 requires every tool). A run from a clean `ubuntu:24.04` with these installed and no network after the fetch passes Tier 1 in about a minute once the toolchain is installed. Contributing: [`CONTRIBUTING.md`](CONTRIBUTING.md). Security: [`SECURITY.md`](SECURITY.md). Licence: Apache-2.0 ([`LICENSE`](LICENSE), [`NOTICE`](NOTICE)).
