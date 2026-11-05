# What vbm-sse specifies

The event-stream algorithm of the [HTML Standard](https://html.spec.whatwg.org/multipage/server-sent-events.html) (WHATWG; sections 9.2.5 "Parsing an event stream" and 9.2.6 "Interpreting an event stream"), pinned in `docs/spec-pin.txt`, as a pure function over bytes: no I/O, no clock, no allocation visible to the caller. Short clauses are quoted for reference; the standard is Copyright WHATWG, CC BY 4.0.

## Inputs and outputs

- **In:** bytes of the stream, in chunks of any size (an empty chunk is allowed), in order.
- **Out:** for each chunk, the events it completed, in order: `Event { type, data, lastEventId }`, each a byte string. And, as state: the **last event ID** (`Proc.lastEventId`, the event source's last event ID string) and the **reconnection time** (`Proc.retry`, `none` until a `retry` field arrives).
- **No refusal.** Every byte string is a stream: the algorithm ignores what it does not know. There is no error value.

## The algorithm, as written (`LeanSse/Spec.lean`)

1. One leading byte order mark (EF BB BF) is removed ("the UTF-8 decode algorithm strips one leading UTF-8 byte order mark"). Only one, only at the very start.
2. The stream is cut into lines, each ended by CR LF, a lone LF, or a lone CR ("a single U+000A LINE FEED (LF) character not preceded by a U+000D CARRIAGE RETURN (CR) character, and a single CR not followed by a LF"). A CR LF split across two chunks is one terminator.
3. Each line, in order: **empty** dispatches; **starts with a colon** is a comment and is ignored; **contains a colon**: the name is what precedes the first colon, the value what follows it with one leading space removed; **otherwise** the whole line is the name and the value is empty.
4. Fields (names compared literally): `event` sets the event type buffer; `data` appends the value and one LF to the data buffer; `id` sets the last event ID buffer unless the value contains NUL (then it is ignored); `retry` sets the reconnection time if the value is only ASCII digits; anything else is ignored.
5. **Dispatch**: the last event ID string is set from the last event ID buffer (always, even when no event results; the buffer is not reset); if the data buffer is empty the data and type buffers are cleared and nothing is dispatched; else the trailing LF is removed, an event is made (type `message` unless the type buffer is non-empty, data, last event ID string), and the data and type buffers are cleared.
6. At the end of the stream pending data is discarded: an unterminated last line, and the event it would have completed, are not dispatched.

## Named policies and limits

- **P-retry.** The standard says a `retry` value that "consists of only ASCII digits" sets the reconnection time. The empty string vacuously consists of only digits, but has no integer value; the library requires at least one digit, as the browser engines do. A value is an unbounded natural number (a consumer saturates it).
- **P-bytes.** Values are byte strings. The standard decodes the stream as UTF-8 (invalid sequences become U+FFFD) before reading it; the cuts the algorithm makes fall on ASCII bytes, which never occur inside a multi-byte sequence, so decoding each value after the cut gives the same text. Specifying and proving that is the open claim `values-are-decoded-as-utf-8`.
- **P-bounds.** The standard bounds neither a line nor the data buffer. The reference holds both without limit (open claim `bounded-state`); a cap and its typed refusal will be specified before the C interface.
- **Origin.** The web platform's event has an origin (the stream's URL); a stream has none, so the event here does not.
- **Fidelity.** That the reference says what the prose says is checked by review and by the standard's own examples, which are theorems (`LeanSseProofs/Examples.lean`); no machine decides it (the `limit` claim `reference-is-the-standard`).

## What is proved (the ledger, `docs/proof-ledger.md`)

One sentence per property: the three line terminators cut alike; a line comes back as it was; the field split; the field table; the dispatch steps; the byte order mark is stripped once; the incremental machine yields the reference's events and final state on the whole stream and, by that, on **every chunking** (`chunk_invariance`); the end of a stream discards pending data; an event is completed only by a line terminator.
