# Results of the speed slices

User instructions per input byte (hardware counter, deterministic; `docs/perf/run.sh`), an x86-64 host with AVX2, chunk sizes 1 / 7 / 4096. Core cycles per byte and MB/s move by tens of percent with the load of a shared host, so each slice was also timed against the one before it with the two builds run alternately (minimum of three), and none of the 15 rows got slower in cycles.

## Instructions per byte, by slice

| corpus | before: 1 / 7 / 4096 | slice 1 | slice 2 | slice 3 | slice 4 | slice 5 | slice 6 | slice 7 |
|---|---|---|---|---|---|---|---|---|
| small-events (primary at 4096) | 913.2 / 170.9 / 13.61 | 666.2 / 159.3 / 11.97 | 495.8 / 140.7 / 10.48 | 495.8 / 140.7 / 9.39 | 495.8 / 140.7 / 8.20 | 492.8 / 140.2 / 7.86 | 492.8 / 140.2 / 6.38 | 492.7 / 141.0 / 6.27 |
| large-data | 877.8 / 148.5 / 4.78 | 649.5 / 138.8 / 4.64 | 476.6 / 116.2 / 4.64 | 476.6 / 116.2 / 4.46 | 476.6 / 116.2 / 4.47 | 473.6 / 115.8 / 4.44 | 473.6 / 115.8 / 3.72 | 472.6 / 115.7 / 3.62 |
| ends-crlf | 911.0 / 172.5 / 15.46 | 665.4 / 159.8 / 12.72 | 495.0 / 141.1 / 11.27 | 495.0 / 141.1 / 10.25 | 495.0 / 141.2 / 8.78 | 492.0 / 140.7 / 8.42 | 492.0 / 140.7 / 6.60 | 491.9 / 141.5 / 6.50 |
| ends-cr | 913.2 / 170.8 / 13.65 | 666.2 / 159.3 / 12.02 | 495.9 / 140.7 / 10.53 | 495.9 / 140.7 / 9.45 | 495.9 / 140.7 / 8.26 | 492.9 / 140.3 / 7.90 | 492.9 / 140.3 / 6.40 | 492.8 / 141.1 / 6.29 |
| ends-mixed | 911.8 / 170.8 / 13.85 | 665.5 / 159.0 / 12.00 | 494.5 / 139.8 / 10.69 | 494.5 / 139.8 / 9.72 | 494.5 / 139.8 / 8.75 | 491.5 / 139.4 / 8.44 | 491.5 / 139.4 / 6.81 | 491.3 / 140.1 / 6.71 |

Slices 6 on are the second round (below, "Round two"): same harness, same host, the library of slice 5 as the base.

## Where the instructions went (before)

small-events at 4096, sampled by instruction: `lean_byte_array_copy_slice` 23%, the byte search 17%, `feedFast` 11%, `malloc` 9%, `packEvent` 8%, `lean_dec_ref_cold` 7%, `ByteArray.extract` 5%, the rest in small helpers. At chunk 1 (a call per byte): the report (header appends and stores) about 40%, the machine step 30%, the C copy and call 15%.

## Slice 1: the cost of a call and of a copy

* a chunk of one or two bytes goes through the byte loop (`feedLoop`, proved equal to `feedBulk`) instead of the line search and a copy of the held line;
* a line end at the read position (every blank line, one per event) is answered by one test, with no call to the byte search (`scanFast`, `scanFast_eq`);
* `ByteArray.copySlice` has a first branch for the common call (all `Nat`s scalar, destination unshared and with room, source another array): the same arithmetic, no allocation, no overlap test; `ByteArray.extract` and the growth copy use the same two-step copy without a byte loop.

## Slice 2: the events are written once, in the report's layout; the empty report is not built

* the dispatched events are packed into the output buffer as they are dispatched (`FSt.outBuf`, `outN`), in the layout the report carries them in, instead of being allocated as records, collected in an array and packed by the report: no per-event record, array push, release walk or size pass. `fast_eq_parse` now says the buffer holds `encEvents` of the reference's events and `outN` their number;
* the buffer is made once per chunk with room for the chunk (no growth by doubling);
* the reader keeps the report of a state with no completed event together with the reconnection time and last event ID it was made from (`RSt`); a chunk that completes no event and changes neither is answered with it as it stands (`abi_feed_report` is stated for the reader and proved with `RInv`). The runtime's `Array.push` had no caller left and is removed with its two runtime mutants.

## Slice 3: the event header in one append

* an event of the default type is laid out by `packMessage`: the first two words and the type `message` are one constant (`hdrMessage`) appended once, the two lengths stored; an empty last event ID is not appended (`packEventT`, proved equal to `packEvent` with the default type in place: `packEventT_eq`);
* `dataLine` and `valStart` are inlined.

## Slice 4: the common event is written from the chunk

* a `data:` line that is whole in the chunk, with nothing held and no data buffered, followed by an empty line in the chunk (`blankAfter`: the next line end, or the LF of a CR LF and the one after it), completes its event in one step: the value is copied from the chunk straight into the output (`packMessageS`), with no data array made, no second pass over the empty line, no release of the array afterwards. `feedLoop_dataEvent` says the byte loop reaches the same state, `feedFast_eq` carries it to the machine; a `data:` line that is not followed by an empty line in the chunk, a second `data:` line and every other field take the path of slice 3.
* checked byte for byte against an independent reader of the standard on 600 kB of each corpus at chunks 1, 7, 63, 64, 1000 and 4096.

## Slice 5: inlining on the event path; the output buffer hint is bounded

* `blankAfter`, `packMessageS` and `packEventTS` are inlined into the loop (one call and one result record fewer per event);
* the room made for a chunk's output is at most 1 MiB (a hint: the buffer still grows when the events need more), so a very large chunk does not ask the arena for twice its size.

Tried and not kept: a first copy of a held line into a fresh buffer with room for 256 bytes (every line then costs an allocation: 3% more instructions at chunk 7); a scalar loop instead of the byte search for lines in fewer than 16 bytes (slower: the search's own tail loop is better compiled than Lean's loop); a vector copy loop in the C interface's copy of the chunk (no measurable change at 4096, seven instructions more per call at 1).

## Against the scalar comparators (MB/s, best of five runs, the runs alternating, on a shared host at load 20 to 35)

`eventsource-parser` is the best scalar comparator of the scorecard (JavaScript, JIT warmed up); `base` is the library before the work, `now` after slice 5. A shared host moves any one figure by tens of percent, so read the ratios, and the instruction counts above for the library's own cost.

| corpus | chunk | base | now | eventsource-parser | eventsource-stream | now / parser | base / parser |
|---|---|---|---|---|---|---|---|
| small-events | 1 | 15.6 | 26.5 | 18.3 | 7.7 | 145% | 85% |
| small-events | 7 | 72.2 | 104.3 | 91.8 | 43.1 | 114% | 79% |
| **small-events** | **4096** | 885.5 | 1636.4 | 1195.7 | 222.6 | **137%** | 74% |
| large-data | 1 | 16.0 | 30.3 | 18.0 | 0.1 | 168% | 89% |
| large-data | 7 | 102.4 | 133.6 | 123.4 | 1.1 | 108% | 83% |
| large-data | 4096 | 1727.9 | 2226.6 | 1456.5 | 245.1 | 153% | 119% |
| ends-crlf | 1 | 16.4 | 30.5 | 18.2 | 8.5 | 168% | 90% |
| ends-crlf | 7 | 71.4 | 90.8 | 88.7 | 36.1 | 102% | 80% |
| ends-crlf | 4096 | 735.6 | 1383.2 | 663.8 | 165.1 | 208% | 111% |
| ends-cr | 1 | 14.3 | 26.8 | 17.4 | 7.3 | 154% | 82% |
| ends-cr | 7 | 68.9 | 84.3 | 79.9 | 33.5 | 106% | 86% |
| ends-cr | 4096 | 797.4 | 1436.9 | 801.4 | 192.7 | 179% | 100% |
| ends-mixed | 1 | 16.4 | 30.9 | 17.5 | 6.3 | 177% | 94% |
| ends-mixed | 7 | 76.7 | 98.5 | 84.8 | 33.5 | 116% | 90% |
| ends-mixed | 4096 | 806.1 | 1305.6 | 616.7 | 218.6 | 212% | 131% |

## What is left, and the ceiling

Per event of `small-events` at 4096 (about 940 instructions now, 1630 before): the copies into the output (about 25%), the loop's own work (about 25%), the byte search (about 18%), the rest in allocation, the `id:` and `event:` lines (which still build their name and value arrays) and the report's last copy. The classes of cost found in vbm-json: checked `Nat` arithmetic on boxed positions is present (the loop's indices are `Nat`; moving them to `USize` through the machine and its proofs is the largest item left, put at under 10%); per-token options and pairs were on the hot path and are gone from it (the loop keeps its state in arguments, the event is bytes in the output); runtime copy calls per small run were present (three to four per event; now one for the header and one for the value); buffers grown by doubling were present in the output (now sized for the chunk). A realistic ceiling for this design is about 5 instructions per byte on this corpus at 4096 (the byte search, one copy of the value, a loop on unboxed state), against 7.8 now: another 1.3 to 1.5 times, for the cost of rewriting the loop on `USize` with its refinement proof and building the report in place.

## Round two

The first round ended at about 7.9 instructions per byte on `small-events` at 4096 and named two levers: the loop's positions on words instead of `Nat`, and the report built in place. Each lands as its own slice, with its refinement lemma, and a table of instructions per byte (deterministic) and of MB/s against the best scalar comparator in the same run.

### Slice 6: the event loop on word positions (`feedFastU`)

* every position of the loop (the read position, the line end, the value start, the end of the empty line after a line) is a `USize`: a byte is read by `ByteArray.uget`, a position is advanced by a machine add, the comparisons are word compares. `feedFastU` has the cases of `feedFast`, in the same order; `feedFastU_eq` says it is `feedFast` at the positions' values (the 14 cases, by the induction principle of `feedFast`), `feedF_eq` and with it `fast_eq_parse`, chunk invariance and `abi_feed_report` stand as theorems; no new axiom. Each helper is shown equal to its `Nat` model (`scanFastU_eq`, `dataLineU_eq`, `valStartU_eq`, `blankAfterU_eq`, `packEventTSU_eq`); the loop's additions cannot wrap because the chunk is checked to leave room for them (`c.size + 8` fits a word: the test is a round trip through a word, so no platform constant is needed; a chunk that fails it, never on a real platform, runs the `Nat` loop `feedFast`);
* the search is called with the word: `VbmSimd.hasAvx2` then `VbmSimd.findAvx2` (the AVX2 kernel), else `VbmSimd.hasNeon` then `VbmSimd.findNeon` (the NEON kernel, aarch64), or `VbmSimd.findSwar` (the proved portable search): the two halves of `VbmSimd.findFirstOf`, with no `Nat` boxing and two calls fewer for every line (`findEolU`). These are the shims that are already the carve-outs of the pinned vbm-simd (T13): no new trusted C; `LeanSse.Fast`'s C is now compiled with that package's header, as the package's own modules are (`lakefile.lean`, `scripts/build_native.sh`, `scripts/build_wasm.sh`). A rare line (a field that is not `data`, a comment, a line not whole in the chunk) uses the `Nat` functions at the positions' values.

Instructions per byte are in the first table (slice 6): small-events at 4096 7.86 to 6.38 (19% fewer), the other corpora 16 to 20% fewer at 4096; chunks 1 and 7 do not run this loop and are unchanged.

Against the scalar comparators (MB/s, best of three runs, the runs alternating: the library before the slice, after it, then the two comparators; host x, load printed). `eventsource-parser` is the best scalar comparator (JavaScript, JIT warmed up).

| corpus | chunk | before | now | eventsource-parser | eventsource-stream | before / best | now / best |
|---|---|---|---|---|---|---|---|
| **small-events** | **4096** | 1989.3 | 2321.3 | 1334.9 | 258.0 | 149% | **174%** |
| small-events | 7 | 116.5 | 119.9 | 106.2 | 50.3 | 110% | 113% |
| small-events | 1 | 31.2 | 30.5 | 18.3 | 8.9 | 170% | 167% |
| large-data | 4096 | 1771.0 | 2077.1 | 888.0 | 176.5 | 199% | 234% |
| large-data | 7 | 140.1 | 135.1 | 112.5 | 1.1 | 125% | 120% |
| large-data | 1 | 34.6 | 25.0 | 12.7 | 0.1 | 272% | 197% |
| ends-crlf | 4096 | 1567.2 | 1722.7 | 587.2 | 186.9 | 267% | 293% |
| ends-crlf | 7 | 86.6 | 74.5 | 72.6 | 31.6 | 119% | 103% |
| ends-crlf | 1 | 23.9 | 27.0 | 16.0 | 5.7 | 149% | 169% |
| ends-cr | 4096 | 1722.2 | 2033.6 | 966.5 | 247.0 | 178% | 210% |
| ends-cr | 7 | 123.4 | 100.5 | 97.7 | 38.2 | 126% | 103% |
| ends-cr | 1 | 32.4 | 33.4 | 19.9 | 8.1 | 163% | 168% |
| ends-mixed | 4096 | 1550.8 | 1923.9 | 831.8 | 280.2 | 186% | 231% |
| ends-mixed | 7 | 134.3 | 129.1 | 120.7 | 49.8 | 111% | 107% |
| ends-mixed | 1 | 39.6 | 41.4 | 26.9 | 10.8 | 147% | 154% |

Load 24 before the table, 17 after, on a host of 22 threads. At chunks 1 and 7 the library runs the same instructions as before the slice (the table of instructions per byte shows it); the differences in those rows, up to 20%, are the noise of a shared host (the same rows moved by the same amount in the other direction in other runs), not the slice.

### Slice 7: the report written in place (`finishEv`)

* a chunk of 64 bytes or more starts its output behind a copy of the cached report of the state it starts from (`startOut`: room for the chunk's events, with the header and the last event ID string already in the first `32 + idLen` bytes); the events are packed behind it by the loop as before; when the chunk has completed an event `finishEv` writes the header over those bytes (`reportIn`: one small header array copied over the room, in place) and the buffer **is** the report: `abiReport` hands it out, with no second buffer and no copy of the events. When the chunk changed the length of the last event ID (the room is the wrong size) the events are copied behind a header of the right size, once, as before. A chunk that completes no event (nearly every small chunk) is answered with the cached report and touches none of this;
* proved: `reportIn_L` (the report written over the room is the header, the last event ID string and the events that were there; both cases), `finishEv_rep`, `abiFeed_spec`: `abi_feed_report` still says the report read back is the reference's events, last event ID and reconnection time. `outBufOf` and `finishEv` are calls of their own (`@[noinline]`): inlined, the compiler hoisted reference-count updates of the state in front of the test for an event and the small chunks paid 6 to 8% more instructions (measured, tried, not kept: a flag in the reader for the report being in place, which made the compiled code allocate a reader per chunk instead of reusing it).

Instructions per byte: first table, slice 7: small-events at 4096 6.38 to 6.27 (2%), large-data 3.72 to 3.62 (3%); chunk 1 unchanged, chunk 7 0.5% more (a call to `finishEv` for the chunks that complete an event). The saving is what the first round estimated for the copy (about 0.1 instruction per byte: one buffer's allocation and one copy of the events).

MB/s against the scalar comparators (best of three, alternating: slice 6, slice 7, the two comparators; host x, load 16 before, 18 after):

| corpus | chunk | slice 6 | slice 7 | eventsource-parser | eventsource-stream | slice 6 / best | slice 7 / best |
|---|---|---|---|---|---|---|---|
| **small-events** | **4096** | 2206.5 | 2477.8 | 1386.2 | 234.1 | 159% | **179%** |
| small-events | 7 | 121.1 | 125.4 | 143.8 | 50.3 | 84% | 87% |
| small-events | 1 | 36.4 | 37.4 | 25.2 | 9.9 | 144% | 148% |
| large-data | 4096 | 3185.0 | 3331.6 | 2355.5 | 306.4 | 135% | 141% |
| large-data | 7 | 185.3 | 179.7 | 154.9 | 1.3 | 120% | 116% |
| large-data | 1 | 38.6 | 40.0 | 24.4 | 0.2 | 158% | 164% |
| ends-crlf | 4096 | 2401.7 | 2489.1 | 862.9 | 285.7 | 278% | 288% |
| ends-crlf | 7 | 90.1 | 95.8 | 81.9 | 30.4 | 110% | 117% |
| ends-crlf | 1 | 40.4 | 37.7 | 25.4 | 10.3 | 159% | 148% |
| ends-cr | 4096 | 2319.9 | 2461.4 | 1154.6 | 264.1 | 201% | 213% |
| ends-cr | 7 | 107.5 | 126.4 | 112.8 | 42.1 | 95% | 112% |
| ends-cr | 1 | 35.7 | 31.1 | 22.7 | 10.0 | 157% | 137% |
| ends-mixed | 4096 | 1255.0 | 1674.7 | 637.6 | 179.8 | 197% | 263% |
| ends-mixed | 7 | 135.2 | 136.2 | 106.2 | 42.4 | 127% | 128% |
| ends-mixed | 1 | 39.3 | 39.6 | 24.8 | 9.8 | 158% | 160% |

Rows at chunks 1 and 7 move by tens of percent between runs on this host (small-events at 7 bytes read 105% of the best comparator on a quiet host, 84 to 87% here, with the library running the same instructions): the call is dominated by the C interface's chunk copy, the allocation of the report and the reader, not by the parser.

### Round two, start and now

Same run, same host (x, load 14 before, 33 after; the runs alternating, best of three): the library at the start of the round (`e5cd1b6`, after slice 5) against the library after slice 7, and the two scalar comparators. Instructions per byte are the first table (slice 5 to slice 7, which is the main of that day: 7.86 to 6.27 on `small-events` at 4096; the main of the same day also moved the pinned vbm-simd, and the count on this host was 6.14 with it).

| corpus | chunk | start | now | eventsource-parser | eventsource-stream | start / best | now / best |
|---|---|---|---|---|---|---|---|
| **small-events** | **4096** | 2341.6 | 2658.2 | 1741.1 | 315.6 | 134% | **153%** |
| small-events | 7 | 136.6 | 117.9 | 131.3 | 51.1 | 104% | 90% |
| small-events | 1 | 37.8 | 36.8 | 23.8 | 10.1 | 159% | 155% |
| large-data | 4096 | 2970.2 | 3469.9 | 1739.4 | 327.9 | 171% | 199% |
| large-data | 7 | 195.2 | 191.8 | 129.0 | 1.4 | 151% | 149% |
| large-data | 1 | 43.8 | 45.6 | 23.1 | 0.2 | 190% | 197% |
| ends-crlf | 4096 | 1798.2 | 2254.1 | 1040.9 | 248.4 | 173% | 217% |
| ends-crlf | 7 | 122.4 | 121.4 | 114.9 | 50.5 | 107% | 106% |
| ends-crlf | 1 | 31.9 | 29.8 | 23.0 | 7.2 | 139% | 130% |
| ends-cr | 4096 | 1968.4 | 2303.0 | 1338.9 | 312.0 | 147% | 172% |
| ends-cr | 7 | 102.4 | 121.9 | 99.6 | 44.9 | 103% | 122% |
| ends-cr | 1 | 32.3 | 35.8 | 23.1 | 9.3 | 140% | 155% |
| ends-mixed | 4096 | 1524.0 | 1801.0 | 857.1 | 277.7 | 178% | 210% |
| ends-mixed | 7 | 131.0 | 105.7 | 99.8 | 34.2 | 131% | 106% |
| ends-mixed | 1 | 32.0 | 29.1 | 15.4 | 6.4 | 208% | 189% |

The 4096 rows, the network read, gained 13 to 25% in MB/s (the ratio to the best scalar comparator on the primary row 134% to 153%). The rows at chunks 1 and 7 run the same instructions as before (140.2 to 140.9 per byte at 7, 492.8 to 492.7 at 1) and moved by tens of percent in both directions between runs: a focused alternation of the two builds (minimum of seven runs, load 27 to 55) gave, in cycles per byte, small-events at 7 bytes 27.24 start / 27.53 now, at 1 byte 101.9 / 99.2; ends-mixed at 7 bytes 27.81 / 28.32, at 1 byte 157.8 / 158.1: within 2% either way, the noise of this host.

### What is left, and the ceiling, after round two

Profile of `small-events` at 4096 by instruction (6.14 instructions per byte, about 740 per event): `lean_byte_array_copy_slice` 29% (three calls an event: the event header, the value, the last event ID, each about 45 to 70 instructions with its own prologue, plus the copy of the chunk's events into the report buffer), `feedFastU` 25% (the loop itself), the AVX2 search 17% (one call an event), allocation and release 11% (the three small arrays of each `id:` line, the buffers of the chunk), the chunk's copy in the C interface 3.7%, `ByteArray.extract` 2.5%, and the field functions of the rare lines 4%.

The classes of cost found in vbm-json, in order of what they were here: checked `Nat` arithmetic and the layers around a native call (present, the largest single item: 19% of the instructions, more than the 10% estimated at the end of round one because the boxed positions also went through two wrapper functions of the search; gone from the hot loop); per-token records and options (gone in round one); runtime copy calls per small run (present: three an event, the biggest item left, 29%, and each costs its prologue more than its bytes: the event is 120 bytes); buffers grown by doubling (gone); an extra copy of the output (present, 2%, gone: the report is written in place). What is not paid any more: the report's second buffer and copy, the boxed positions, the search's wrapper layers.

The ceiling for this design on this corpus is about 4.5 to 5 instructions per byte (from 6.14: another 1.2 to 1.35 times), and every step towards it is smaller than the last: (a) the three copy calls of an event as inline stores (an inline primitive in the pinned vbm-simd header, a new carve-out with its model test: about 0.5 per byte); (b) a fast path for the `id:` and `event:` lines, no name or value arrays, no `applyField` (about 0.2 per byte on this corpus, which has an `id:` every tenth event, and nothing on a stream without them); (c) the chunk's copy in the C interface as vector stores (0.15). The cost of a call itself (the reader's record, the cached report, the C interface's input array) is about 500 instructions: it shows only at chunks of a few bytes, where every reader pays per call and this one is level with the best scalar comparator (90 to 155% on `small-events`, by chunk size and by run).
