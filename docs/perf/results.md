# Results of the speed slices

User instructions per input byte (hardware counter, deterministic; `docs/perf/run.sh`), an x86-64 host with AVX2, chunk sizes 1 / 7 / 4096. Core cycles per byte and MB/s move by tens of percent with the load of a shared host, so each slice was also timed against the one before it with the two builds run alternately (minimum of three), and none of the 15 rows got slower in cycles.

## Instructions per byte, by slice

| corpus | before: 1 / 7 / 4096 | slice 1 | slice 2 | slice 3 | slice 4 | slice 5 | slice 6 |
|---|---|---|---|---|---|---|---|
| small-events (primary at 4096) | 913.2 / 170.9 / 13.61 | 666.2 / 159.3 / 11.97 | 495.8 / 140.7 / 10.48 | 495.8 / 140.7 / 9.39 | 495.8 / 140.7 / 8.20 | 492.8 / 140.2 / 7.86 | 492.8 / 140.2 / 6.38 |
| large-data | 877.8 / 148.5 / 4.78 | 649.5 / 138.8 / 4.64 | 476.6 / 116.2 / 4.64 | 476.6 / 116.2 / 4.46 | 476.6 / 116.2 / 4.47 | 473.6 / 115.8 / 4.44 | 473.6 / 115.8 / 3.72 |
| ends-crlf | 911.0 / 172.5 / 15.46 | 665.4 / 159.8 / 12.72 | 495.0 / 141.1 / 11.27 | 495.0 / 141.1 / 10.25 | 495.0 / 141.2 / 8.78 | 492.0 / 140.7 / 8.42 | 492.0 / 140.7 / 6.60 |
| ends-cr | 913.2 / 170.8 / 13.65 | 666.2 / 159.3 / 12.02 | 495.9 / 140.7 / 10.53 | 495.9 / 140.7 / 9.45 | 495.9 / 140.7 / 8.26 | 492.9 / 140.3 / 7.90 | 492.9 / 140.3 / 6.40 |
| ends-mixed | 911.8 / 170.8 / 13.85 | 665.5 / 159.0 / 12.00 | 494.5 / 139.8 / 10.69 | 494.5 / 139.8 / 9.72 | 494.5 / 139.8 / 8.75 | 491.5 / 139.4 / 8.44 | 491.5 / 139.4 / 6.81 |

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
