# Results of the speed slices

User instructions per input byte (hardware counter, deterministic; `docs/perf/run.sh`), an x86-64 host with AVX2, chunk sizes 1 / 7 / 4096. Core cycles per byte and MB/s move by tens of percent with the load of a shared host, so each slice was also timed against the one before it with the two builds run alternately (minimum of three), and none of the 15 rows got slower in cycles.

## Instructions per byte, by slice

| corpus | before: 1 / 7 / 4096 | slice 1 | slice 2 | slice 3 | slice 4 | slice 5 |
|---|---|---|---|---|---|---|
| small-events (primary at 4096) | 913.2 / 170.9 / 13.61 | 666.2 / 159.3 / 11.97 | 495.8 / 140.7 / 10.48 | 495.8 / 140.7 / 9.39 | 495.8 / 140.7 / 8.20 | 492.8 / 140.2 / 7.86 |
| large-data | 877.8 / 148.5 / 4.78 | 649.5 / 138.8 / 4.64 | 476.6 / 116.2 / 4.64 | 476.6 / 116.2 / 4.46 | 476.6 / 116.2 / 4.47 | 473.6 / 115.8 / 4.44 |
| ends-crlf | 911.0 / 172.5 / 15.46 | 665.4 / 159.8 / 12.72 | 495.0 / 141.1 / 11.27 | 495.0 / 141.1 / 10.25 | 495.0 / 141.2 / 8.78 | 492.0 / 140.7 / 8.42 |
| ends-cr | 913.2 / 170.8 / 13.65 | 666.2 / 159.3 / 12.02 | 495.9 / 140.7 / 10.53 | 495.9 / 140.7 / 9.45 | 495.9 / 140.7 / 8.26 | 492.9 / 140.3 / 7.90 |
| ends-mixed | 911.8 / 170.8 / 13.85 | 665.5 / 159.0 / 12.00 | 494.5 / 139.8 / 10.69 | 494.5 / 139.8 / 9.72 | 494.5 / 139.8 / 8.75 | 491.5 / 139.4 / 8.44 |

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

Tried and not kept: a scalar loop instead of the byte search for lines in fewer than 16 bytes (slower: the search's own tail loop is better compiled than Lean's loop); a vector copy loop in the C interface's copy of the chunk (no measurable change at 4096, seven instructions more per call at 1).
