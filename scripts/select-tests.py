#!/usr/bin/env python3
"""Delta selection (docs/decisions/0004-tier1-speed.md): which Tier 1 test scripts can the delta since the merge base affect?
Usage: select-tests.py [--map FILE] [--files F...] [--check TEST...]   prints the selected test scripts, one per line, in map order.
Without --files the delta is `git diff --name-only --no-renames BASE` plus untracked files, BASE = $TIER1_BASE, else merge-base(origin/main, HEAD).
CONSERVATIVE: TIER1_ALL=1, no resolvable base, an empty delta, or ANY file the map does not place => every test. --check TEST...: the tests given all have a map line (exit 1 otherwise)."""
import os, subprocess, sys

def parse(path):
    allp, nonep, tests = [], [], {}
    for l in open(path):
        l = l.split("#", 1)[0].strip()
        if not l: continue
        k, v = l.split(":", 1); v = v.split()
        if k == "all": allp += v
        elif k == "none": nonep += v
        else: tests[k] = v + [k]   # a test is selected by a change to its own script
    return allp, nonep, tests

def hit(f, ps): return any(f == p or (p.endswith("/") and f.startswith(p)) for p in ps)

def select(files, allp, nonep, tests):
    """tests selected by `files`; every test when a file is in `all` or in nothing."""
    if not files: return list(tests)
    sel = set()
    for f in files:
        if hit(f, allp): return list(tests)
        ts = [t for t, ps in tests.items() if hit(f, ps)]
        if ts: sel.update(ts)
        elif not hit(f, nonep): return list(tests)
    return [t for t in tests if t in sel]

def delta():
    g = lambda *a: subprocess.run(["git", *a], capture_output=True, text=True)
    base = os.environ.get("TIER1_BASE") or g("merge-base", "origin/main", "HEAD").stdout.strip()
    if not base or g("rev-parse", "--verify", "-q", base + "^{commit}").returncode: return None
    d = g("diff", "--name-only", "--no-renames", base); u = g("ls-files", "-o", "--exclude-standard")
    if d.returncode or u.returncode: return None
    return sorted({x for x in (d.stdout + u.stdout).split("\n") if x})

def main(a):
    mp = "scripts/tests-map.txt"
    if a[:1] == ["--map"]: mp, a = a[1], a[2:]
    allp, nonep, tests = parse(mp)
    if a[:1] == ["--check"]:
        miss = [t for t in a[1:] if t not in tests]
        if miss: print("select-tests: no map line for: " + " ".join(miss), file=sys.stderr); return 1
        return 0
    if a[:1] == ["--files"]: files = a[1:]
    elif os.environ.get("TIER1_ALL"): files = None
    else: files = delta()
    out = list(tests) if files is None else select(files, allp, nonep, tests)
    if out: print("\n".join(out))
    return 0

if __name__ == "__main__": sys.exit(main(sys.argv[1:]))
