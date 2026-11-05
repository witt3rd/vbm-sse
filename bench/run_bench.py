#!/usr/bin/env python3
"""The throughput bench of vbm-sse, in the form the scorecard reads (docs/bench.md).
  run_bench.py C_BENCH LEAN_BENCH     C_BENCH: bench/bench.c built against the freestanding library; LEAN_BENCH: the vbm-sse-bench executable;
                                      env VBM_COMPARATORS: the prebuilt comparators (scorecard/comparators/build-sse.sh), mounted read-only.
Generates the five corpora (bench/gen_corpus.py), refuses any whose sha256 is not the pin below, and for each corpus and each chunk size (1, 7, 4096 bytes) measures
  subject        the compiled library through its C interface (bench/bench.c)
  lean-fast      the array machine in Lean (bench/Bench.lean)
  reference      the whole-buffer reference in Lean (bench/Bench.lean; independent of the chunk size, so the same number on a corpus's three rows)
  eventsource-parser, eventsource-stream   the comparators (run-sse.sh)
The PRIMARY corpus, the one the scorecard floors, is small-events cut at 4096 bytes. Every other (corpus, chunk) is a `corpusrow`: reported, never floored.
Every implementation must find the same number of events as the Lean reference: the subject and the Lean machine must (a difference exits 1: a bench that measures a wrong reader is no bench);
a comparator that differs is reported in a `note` line (never hidden, never fatal: the comparator is not ours)."""
import hashlib, os, re, subprocess, sys, tempfile

PIN = {"small-events": "490f3c117d2f5c347d15eb3833e0a77388e13ee11a50b6fd5a2eebce10e1cbcd", "large-data": "16c547a49632c7a6f5d92d4a8570b081e89fdc20e540dc0502bb36440bdc5ca2",
       "ends-crlf": "52f907184c0ff2acf10dc2b1fecc3d2c0ccd9015f40a967397eea8d5b0d6d101", "ends-cr": "69953a24a48edb929e1b15652ef97500b368071aba1fb303a522fddc08c41e12",
       "ends-mixed": "e0e6a1c024bc8a4b8e6e8698fb86eb08a7b0e522f56154efca64219bcd3726d5"}
CHUNKS = (1, 7, 4096)
PRIMARY = ("small-events", 4096)


def run(cmd):
    r = subprocess.run(cmd, capture_output=True, text=True, timeout=900)
    if r.returncode: sys.exit("bench: %s failed (exit %d): %s" % (cmd[0], r.returncode, r.stderr[-400:]))
    return r.stdout


def main():
    cbench, leanbench = sys.argv[1:3]
    comp_dir = os.environ.get("VBM_COMPARATORS") or sys.exit("bench: VBM_COMPARATORS (the prebuilt comparators) is not set")
    d = tempfile.mkdtemp()
    run([sys.executable, os.path.join(os.path.dirname(os.path.abspath(__file__)), "gen_corpus.py"), d])
    rows, prov, primary, corpus = [], {}, None, None
    for name in PIN:
        path = "%s/%s.sse" % (d, name); raw = open(path, "rb").read(); sha = hashlib.sha256(raw).hexdigest()
        if sha != PIN[name]: sys.exit("bench: corpus %s has sha256 %s, not the pinned %s" % (name, sha, PIN[name]))
        lean = {}
        for l in run([leanbench, path]).splitlines():
            f = l.split()
            lean[("reference", 0) if f[0] == "reference" else ("lean-fast", int(f[1]))] = (float(f[2]), int(f[4]))
        ref_mb, ref_ev = lean[("reference", 0)]
        for chunk in CHUNKS:
            f = run([cbench, path, str(chunk)]).split(); subj, subj_ev = float(f[0]), int(f[2])
            fast, fast_ev = lean[("lean-fast", chunk)]
            if not (subj_ev == fast_ev == ref_ev): sys.exit("bench: %s@%d: events differ: subject %d, lean-fast %d, reference %d" % (name, chunk, subj_ev, fast_ev, ref_ev))
            comp = {}
            for l in run([comp_dir + "/run-sse.sh", path, str(chunk)]).splitlines():
                f = l.split()
                if f[0] == "comparator": comp[f[1]] = float(f[2])
                elif f[0] == "events" and int(f[2]) != ref_ev: print("note %s@%d: %s found %s events, the reference %d" % (name, chunk, f[1], f[2], ref_ev))
                elif f[0] == "provenance": prov[f[1]] = l
            kv = dict(comp, subject=subj, **{"lean-fast": fast, "reference": ref_mb})
            rows.append((("%s@%d" % (name, chunk)), sha, len(raw), kv))
            if (name, chunk) == PRIMARY: primary = (sha, len(raw), subj, comp)
    sha, n, subj, comp = primary
    print("corpus %s %d" % (sha, n)); print("subject %.1f" % subj)
    for k in sorted(comp): print("comparator %s %.1f" % (k, comp[k]))
    for k in sorted(prov): print(prov[k])
    for name, sha, n, kv in rows: print("corpusrow %s %s %d %s" % (name, sha, n, " ".join("%s=%.1f" % x for x in sorted(kv.items()))))


main()
