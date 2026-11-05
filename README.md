# vbm-sse

A Server-Sent Events (SSE) stream reader whose correctness is a machine-checked theorem, written once in Lean 4. It implements the event-stream algorithm of the [HTML Standard](https://html.spec.whatwg.org/multipage/server-sent-events.html#parsing-an-event-stream) (sections 9.2.5 and 9.2.6): line splitting on CR, LF and CR LF, field parsing, the byte order mark, event dispatch, `id` and `retry`.

> **Status: pre-release.** The specification, the reference reader, the incremental reader and their proofs exist. The C and WebAssembly builds and the generated bindings are not built yet; nothing is published to a package registry. Build from source.

## What is proved

**The events of a stream do not depend on how it arrives.** Cut the bytes into chunks anywhere (between a CR and its LF, inside a byte order mark, inside a field name, one byte at a time) and the incremental reader yields exactly the events, the last event ID and the reconnection time that the whole-buffer reference yields for the concatenation (`chunk_invariance`). A chunk with no line terminator completes nothing, and the unterminated end of a stream is discarded, never dispatched, as the standard says.

The reference is the standard's algorithm written as a pure Lean function over bytes, and the four examples of the standard are theorems about it. The claims, each tagged with the clause of the standard it is about, and which are proved, partial, open or a stated limit, are in [`docs/proof-ledger.md`](docs/proof-ledger.md) (generated). Only a `proved` claim is called verified anywhere in this repository. What is still open: decoding values as UTF-8 text (values are bytes today), a bound on line and buffer size, and the compiled targets.

## Why

Hand-written SSE readers disagree on the details that matter: a CR LF split across two network reads becomes two line ends; `data:` lines are taken one message each instead of being joined; a leading byte order mark or a `:` comment shows up as data. The standard is short and exact, so here it is a theorem: one reader, one set of generated test vectors, the same answer for every chunking.

## The ethos: verified bare metal (VBM)

Part of the [VBM standard](https://github.com/witt3rd/vbm) family of small verified libraries (see also [vbm-json](https://github.com/witt3rd/vbm-json)). Verified: proofs, not tests. Bare metal: the core imports only Lean's `Init`, so the C and WebAssembly that will be generated from it need no libc. Correct by construction: the specification is the code that runs; the vectors will be generated from the reference. Built agentically: coding agents wrote the specification and proofs under mechanical gates (no `sorry`, no new axiom, proved claims and specified share only go up, every gate has a negative self-test).

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

## Build and test

```sh
mise install
mise exec -- scripts/tier1.sh      # the gate: build with zero warnings, every gate with its negative self-test
```

Requires [mise](https://mise.jdx.dev) (it installs the pinned Lean, 4.35.0), `python3` and `git`. Contributing: [`CONTRIBUTING.md`](CONTRIBUTING.md). Security: [`SECURITY.md`](SECURITY.md). Licence: Apache-2.0 ([`LICENSE`](LICENSE), [`NOTICE`](NOTICE)).
