# The throughput bench

What it measures, on which bytes, against what, and how to read it. The scorecard's efficiency metric is this bench (`scorecard.toml`, `[bench]`).

## The corpus (deterministic, generated)

`bench/gen_corpus.py DIR` writes five Server-Sent Events streams. It has no input but a fixed seed and its own integer generator (splitmix64), so the bytes depend on no Python version, no clock and no machine; the sha256 of each is pinned in `bench/run_bench.py`, which refuses any other bytes before measuring. All bytes are ASCII, so a cut at any byte is a cut at a character (the comparators that take text are fed the same cuts).

| name | bytes | what it is |
|---|---|---|
| `small-events` | 3,616,788 | **the primary corpus**: 30,000 small events of the shape of a chat-completion stream (a `data:` line of a short JSON object and a blank line; every 10th event has an `id:`, every 25th an `event:`, every 50th a `: keepalive` comment). LF line ends |
| `large-data` | 1,500,824 | events with long `data:` lines (2 KB to 16 KB) and events of 8 to 40 short `data:` lines the reader joins with LF (404 events). LF |
| `ends-crlf` | 3,681,588 | the events of `small-events`, every line ended by CR LF |
| `ends-cr` | 3,616,788 | the same, every line ended by a lone CR |
| `ends-mixed` | 3,638,365 | the same, each line ended by CR LF, CR or LF, chosen per line (a CR that meets the next line's LF becomes a CR LF: 26,606 events, as the standard says) |

Every stream is cut into chunks of **1**, **7** and **4096** bytes: one byte is the worst case for a reader that pays per call, seven puts line ends and CR LF pairs across cuts, 4096 is a network read. That is 15 rows. The events are not chosen by the bench: the Lean reference counts them, and the compiled library and the Lean array machine must find the same number on every row (a difference fails the bench).

## What is measured

| name | what | how |
|---|---|---|
| `subject` | the compiled **freestanding** library (`scripts/build_native.sh`: no libc) through its C interface, as a consumer calls it | `bench/bench.c`: feed the chunks, read each report's event count, best of five full passes |
| `lean-fast` | the array machine (`LeanSse.feedF`) in Lean, without the C interface | `bench/Bench.lean` (`vbm-sse-bench`) |
| `reference` | the whole-buffer reference `LeanSse.parse`, over a list of bytes: the specification itself, not a fast reader | `bench/Bench.lean`; independent of the chunk size, so one number per corpus |
| `eventsource-parser` | the npm package of that name, version in the card (JavaScript, scalar) | `scorecard/comparators/sse_js/bench.mjs`: text chunks, three warm-up passes for the JIT, the fastest of nine |
| `eventsource-stream` | the crate of that name, version in the card (Rust, scalar; the parser under `reqwest-eventsource`) | `scorecard/comparators/sse_rs`: `Bytes` chunks, a single-threaded executor, best of five |

MB/s is 10^6 bytes per second of the corpus. The corpus is read (and, for the comparators, cut) before the clock starts. The comparators are built once outside the sandbox (network only at build time, exact versions and lock files in the scorecard repository, `comparators/build-sse.sh`), mounted read-only, and their binaries are hash-checked against a manifest before each run; the card shows the versions and hashes.

The floor (scorecard `DECISIONS` 1) is on the primary corpus only: the subject's MB/s as a percent of the **best scalar comparator**, at least 50%. The other fourteen rows are reported, never floored and never averaged in.

## Known differences, stated

* A stream that ends in a lone CR: `eventsource-stream` waits for a possible LF and does not dispatch the last event (29,999 events on `ends-cr`, the standard and the other implementations say 30,000). The bench names this in a `note` line and does not hide it; the number is still reported.
* `eventsource-stream` rescans a held line on every chunk: with 1-byte chunks and long lines it is quadratic (`large-data` at chunk 1 runs at about 0.1 MB/s). That is its design at that cut; it is why `large-data` is 1.5 MB and its longest line 16 KB (the bench has a time limit).
* The comparators are not freestanding and not verified; the JIT-compiled one is measured in steady state (warmed up). A consumer that parses one short stream pays the warm-up.

## What it shows today

The numbers of a run are in the scorecard's card (`registry/scores` in the scorecard repository) and are not repeated here: a number in a document goes stale, a card is stamped with the commit. Read them honestly: the array machine takes **one byte at a time** (the bulk scan for line ends is the open claim `fast-machine-refines`, "partly", in the ledger), and the C interface builds a report per chunk, so at 4096 bytes it is far behind a parser that searches for line ends in bulk, and at 1 byte the cost of a call and a report dominates every reader. The bench exists to make that gap a number the next landing has to move.

## Run it

```
mise exec -- lake build vbm-sse-bench
mise exec -- scripts/build_native.sh /tmp/o --no-so
mise exec -- leanc -O2 -I include -o /tmp/bench_c bench/bench.c /tmp/o/libvbm_sse.a
VBM_COMPARATORS=<a build-sse.sh output> mise exec -- python3 bench/run_bench.py /tmp/bench_c .lake/build/bin/vbm-sse-bench
```

`bench/gen_corpus.py --sha256` prints the corpus hashes (it writes nothing).
