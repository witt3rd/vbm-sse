# Profiling the compiled reader

The method of vbm-json's `docs/perf`, on this library: a sampler on the compiled freestanding library through its C interface, and counters of retired instructions. Not part of the library, built by no gate.

* `prof.c`: feeds a corpus file to the library in chunks of K bytes. `bench` prints MB/s, **core cycles per byte**, **user instructions per byte** (hardware counters through `perf_event_open`; a pass counts only if the counter ran for all of it) and the event count, best of the passes of two seconds. `sample` is a 1 kHz time sampler; `isample` takes a sample every 2003 retired user instructions, so the profile is by instructions and does not move with load.
* `resolve.py BINARY SAMPLES`: percent of samples per symbol.
* `run.sh OUT`: builds the library and `prof`, writes the five corpora, prints the 15-row table with the load beside it. Run from the repository root: `mise exec -- docs/perf/run.sh /tmp/o`.

Read the numbers so: **instructions per byte are deterministic** and are the figure a change is judged by; seconds and cycles move by tens of percent with the load of a shared host (the load is printed before and after the table), so a time comparison is made with the two builds run alternately and the minimum of each kept. Chunk 1 is a call per byte (the cost of a call and a report), chunk 7 puts line ends across cuts, chunk 4096 is a network read; the primary corpus of the scorecard is `small-events` at 4096.

`results.md` keeps the table of each slice that landed.
