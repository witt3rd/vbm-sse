# Results of the speed slices

User instructions per input byte (hardware counter, deterministic; `docs/perf/run.sh`), an x86-64 host with AVX2, chunk sizes 1 / 7 / 4096. Core cycles per byte and MB/s move by tens of percent with the load of a shared host, so each slice was also timed against the one before it with the two builds run alternately (minimum of three), and none of the 15 rows got slower in cycles.

## Instructions per byte, by slice

| corpus | before: 1 / 7 / 4096 | slice 1 | slice 2 |
|---|---|---|---|
| small-events (primary at 4096) | 913.2 / 170.9 / 13.61 | 666.2 / 159.3 / 11.97 | 495.8 / 140.7 / 10.48 |
| large-data | 877.8 / 148.5 / 4.78 | 649.5 / 138.8 / 4.64 | 476.6 / 116.2 / 4.64 |
| ends-crlf | 911.0 / 172.5 / 15.46 | 665.4 / 159.8 / 12.72 | 495.0 / 141.1 / 11.27 |
| ends-cr | 913.2 / 170.8 / 13.65 | 666.2 / 159.3 / 12.02 | 495.9 / 140.7 / 10.53 |
| ends-mixed | 911.8 / 170.8 / 13.85 | 665.5 / 159.0 / 12.00 | 494.5 / 139.8 / 10.69 |

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
