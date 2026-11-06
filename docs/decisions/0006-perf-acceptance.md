# 0006 A performance change is accepted by the full per-row table on a quiet machine, before it lands

Status: standing rule. Learned from the slice that moved the state records out of the per-line loop (`feedFast`, commit 167db51).

What happened. That slice was proved correct, cut the allocations per event from 6.8 to 2.8 (counted on the freestanding library) and sped up the primary row of the benchmark by a third on a loaded machine. It landed on those numbers.
Measured afterwards on an idle machine, over all fifteen rows (five corpora times chunks of 1, 7 and 4096 bytes), it made every row with a 1- or 7-byte chunk 19 to 26 percent slower, and some larger-chunk rows slower too: the unpacked loop pays to take
the state apart and put it back on every call, which a chunk of a few bytes cannot afford, and a CR LF took the general step every line. The primary row had hidden it.

The rule. A change whose purpose is speed is accepted only by this evidence, produced BEFORE it lands:
 1. the per-row table of the whole benchmark (every corpus and chunk size, not the primary row alone), baseline against the change, on a quiet machine (load below 2 and no other build running), interleaved runs, medians of five or more, with the load figures;
 2. no row below its baseline beyond the run-to-run spread of the baseline itself (the spread is printed in the table); a row that is bimodal run to run is judged on its maximum as well as its median;
 3. counts (allocations, calls) and CPU-time shares are for finding the next lever, never for accepting a change; a loaded-machine number is indicative and is not quoted as a result.
The scorecard's card is updated only from a table that passes this.
