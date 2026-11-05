# 0001 vbm-sse: scope, representation, and the shape of the chunk-invariance proof

Status: accepted.

## Decision
1. **Scope.** Exactly the event-stream algorithm (9.2.5, 9.2.6). Not the `EventSource` API, not reconnection, not HTTP, not JSON: those are a client's. The consumers are stream decoders (an LLM provider's streaming reply, MCP's HTTP transport) that take a chunk and want events.
2. **Bytes, `List UInt8` in the reference.** The algorithm reads only ASCII bytes; keeping values as bytes makes the cuts commute with UTF-8 decoding (docs/spec.md, P-bytes) and keeps the C interface bytes-in. The reference uses lists (proofs); the compiled machine will use arrays, with a refinement proof.
3. **Two definitions, deliberately different.** The whole-buffer reference cuts lines by a right-to-left recursion (`splitLines`) and runs them (`runLines`); the incremental machine is a left-to-right byte step (`step`, `feed`). They are not one function in two guises: that the machine equals the reference (`feed_eq_parse`) is the theorem, and chunk invariance follows from it with `feed_append`. A machine proved only against itself would show nothing.
4. **The invariant.** The machine state between bytes is a held line (no terminator), a flag "the last byte was a CR" and the algorithm's state; the generalised statement (`feed_body`) says: from such a state, over any chunk, the output is the reference's on the held line followed by the chunk (with a pending CR's LF dropped), and the next state holds the reference's unterminated rest. The byte order mark is a three-state prefix matcher in front (`feed_bom`). The pattern carries over to other framings.
5. **Output as events plus state.** The retry time and the last event ID string are state, not items: they are what a reconnecting client reads. Chunk invariance is stated for the events and that final state together.
6. **No JSON, no `Std`.** `LeanSse` imports `Init` only. Where a consumer needs JSON it takes vbm-json as a pinned dependency itself.
7. **Gates copied from vbm-json** (until a shared kit exists), with the changes: every ledger claim carries a clause tag checked against `docs/spec-clauses.txt`; a scrub gate keeps internal names, paths and secrets out of the tree; the ABI, WebAssembly, binding and mutation gates arrive with the C interface.

## Consequences
The first landing carries the whole specification and its proofs, not a skeleton: the proof pattern is the pilot's result and is worth more than an empty scaffold. The next landings are vectors, then the C interface.
