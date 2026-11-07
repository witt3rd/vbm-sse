#!/usr/bin/env python3
"""Bin the instruction pointers written by `prof ... sample` into symbols. Usage: resolve.py BINARY SAMPLES [TOP]. Percent of samples per symbol (nm -n of the binary; the first line of SAMPLES is the address of main)."""
import bisect, subprocess, sys, collections
b, s = sys.argv[1], sys.argv[2]; top = int(sys.argv[3]) if len(sys.argv) > 3 else 25
syms = sorted((int(a, 16), n) for a, t, n in (l.split(None, 2) for l in subprocess.run(["nm", "-n", b], capture_output=True, text=True).stdout.splitlines() if len(l.split(None, 2)) == 3) if t in "tTwW")
addrs = [a for a, _ in syms]
rows = open(s).read().split()
base = int(rows[0], 16) - next(a for a, n in syms if n == "main")
c = collections.Counter(); tot = 0
for l in rows[1:]:
    ip = int(l, 16) - base; i = bisect.bisect_right(addrs, ip) - 1
    c[syms[i][1] if i >= 0 else "?"] += 1; tot += 1
print(f"{tot} samples")
for n, k in c.most_common(top): print(f"{100 * k / tot:6.2f}%  {n}")
