# Results of the speed slices

Instructions per byte (user mode, deterministic) and core cycles per byte (best of the passes, host with other load: a figure with a spread of tens of percent), `docs/perf/run.sh`, host x86-64 with AVX2. Chunk sizes 1, 7, 4096. Each slice is a row of the table below it.

## Before (main at the start of the work)

| corpus | chunk 1 ins/B | chunk 7 ins/B | chunk 4096 ins/B | 4096 cyc/B |
|---|---|---|---|---|
| small-events | 913.2 | 170.9 | 13.61 | 3.35 to 4.2 |
| large-data | 877.8 | 148.5 | 4.78 | 1.86 |
| ends-crlf | 911.0 | 172.5 | 15.46 | 3.6 |
| ends-cr | 913.2 | 170.8 | 13.65 | 3.3 to 4.7 |
| ends-mixed | 911.8 | 170.8 | 13.85 | 4.8 to 5.2 |

Where the instructions went (small-events at 4096, sampled by instruction): `lean_byte_array_copy_slice` 23%, the byte search 17%, `feedFast` 11%, `malloc` 9%, `packEvent` 8%, `lean_dec_ref_cold` 7%, `ByteArray.extract` 5%, the rest in small helpers. At chunk 1 (a call per byte): the report (header appends and stores) about 40%, the machine step 30%, the C copy and call 15%.
