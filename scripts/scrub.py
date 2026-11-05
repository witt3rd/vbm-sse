#!/usr/bin/env python3
"""The scrub gate (Tier 1): the repository is public-ready from its first commit, so no file of the tree may carry an internal name, a path on a developer's machine, or a
secret-shaped string. Three checks over every tracked or not-yet-added, not-ignored text file:
  1. a TOKEN (letters and digits, case folded, split at every other character) whose sha256 is in scripts/scrub-banned.sha256 (the list holds hashes, so it names nothing);
  2. a path on a developer's machine (a home directory, a mount, a source tree under the home) or an agent-home dot directory;
  3. a secret-shaped string (a GitHub or cloud token prefix, a private key block).
`--selftest` also proves the gate can fail: files built at run time that carry each kind of finding must be flagged, a clean file must not, and the banned list must hold the six words it was written for.
usage: scripts/scrub.py [--selftest] [FILES...]  (default: the files git lists)"""
import hashlib, os, re, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
PATHS = [re.compile(p) for p in (r"/home/[A-Za-z0-9_.-]+", r"/Users/[A-Za-z0-9_.-]+", r"(?<![A-Za-z0-9_.])/mnt/[A-Za-z0-9_.-]+", r"~/" + "src/", r"\.[a-z]+-homes?/")]
SECRETS = [re.compile(p) for p in (r"gh[pousr]_[A-Za-z0-9]{20,}", r"github_pat_[A-Za-z0-9_]{20,}", r"\bsk-[A-Za-z0-9]{20,}", r"\bAKIA[0-9A-Z]{16}\b", r"\bxox[baprs]-[A-Za-z0-9-]{10,}",
                                       r"AIza[0-9A-Za-z_-]{30,}", r"-----BEGIN [A-Z ]*PRIVATE KEY-----")]
TOKEN = re.compile(r"[A-Za-z0-9]+")
SKIP_DIRS = ("scripts/land/", ".agents/skills/")   # the pinned copy of the landing tool: its own repository is public and drift-checked (scripts/land/bin/land-check)

def banned(path):
    out = set()
    for l in open(path, encoding="utf-8"):
        l = l.strip()
        if l and not l.startswith("#"): out.add(l)
    return out

def scan_text(text, bans):
    """-> a list of (kind, detail) findings in one file's text."""
    found = []
    for tok in set(TOKEN.findall(text)):
        if hashlib.sha256(tok.lower().encode()).hexdigest() in bans: found.append(("name", hashlib.sha256(tok.lower().encode()).hexdigest()[:12]))
    for rx in PATHS:
        m = rx.search(text)
        if m: found.append(("path", m.group(0)))
    for rx in SECRETS:
        if rx.search(text): found.append(("secret", rx.pattern[:20]))
    return found

def files():
    out = subprocess.run(["git", "ls-files", "-co", "--exclude-standard", "-z"], cwd=ROOT, capture_output=True, check=True).stdout.decode().split("\0")
    return [f for f in out if f and not f.startswith(SKIP_DIRS) and f != "scripts/scrub-banned.sha256"]

def scan_files(paths, bans, quiet=False):
    bad = 0
    for f in paths:
        full = f if os.path.isabs(f) else os.path.join(ROOT, f)
        try: text = open(full, encoding="utf-8").read()
        except (UnicodeDecodeError, IsADirectoryError, FileNotFoundError): continue   # binary or gone: not text
        for kind, detail in scan_text(text, bans):
            bad += 1
            if not quiet: print(f"scrub: {f}: {kind}: {detail}", file=sys.stderr)
    return bad

def selftest(bans):
    words = [("fir", "stmate"), ("ro", "ger"), ("mcfe", "ely"), ("sp", "ire"), ("lu", "ng"), ("jan", "us")]
    for a, b in words:
        if not scan_text(f"a line about {a}{b.upper()} in prose", bans): print(f"scrub: self-test: the banned list does not hold the word {a}…{b}", file=sys.stderr); sys.exit(1)
    cases = {"a path": "see " + "/ho" + "me/someone/x", "a mount": "at " + "/m" + "nt/share", "a token": "key " + "gh" + "p_" + "a" * 30, "a private key": "-----BEGIN " + "RSA PRIVATE KEY-----"}
    for what, text in cases.items():
        if not scan_text(text, bans): print(f"scrub: self-test: the gate does not flag {what}", file=sys.stderr); sys.exit(1)
    for text in ("Server-sent events, the lungs of a stream? no: just data.", "a public name: witt3rd, vbm-json, WHATWG; a url https://html.spec.whatwg.org/x; ~/.config is not ~/src"):
        if scan_text(text, bans): print("scrub: self-test: the gate flags a clean text: " + text, file=sys.stderr); sys.exit(1)
    # the gate reads files: a scratch file with a finding must make scan_files fail
    with tempfile.TemporaryDirectory() as d:
        p = os.path.join(d, "f.txt"); open(p, "w").write("x " + "ro" + "ger" + " y\n")
        if scan_files([p], bans, quiet=True) == 0: print("scrub: self-test: scan_files passes a file with a banned word", file=sys.stderr); sys.exit(1)
    print("scrub: negative self-tests ok (each banned word, a path, a mount, a token, a private key is flagged; a clean text is not)")

def main():
    args = sys.argv[1:]
    st = "--selftest" in args
    args = [a for a in args if a != "--selftest"]
    bans = banned(os.path.join(HERE, "scrub-banned.sha256"))
    if len(bans) < 6: print("scrub: the banned list is shorter than the six words it was written for", file=sys.stderr); sys.exit(1)
    paths = args or files()
    bad = scan_files(paths, bans)
    if bad: print(f"scrub: FAILS ({bad} finding(s))", file=sys.stderr); sys.exit(1)
    if st: selftest(bans)
    print(f"scrub: ok ({len(paths)} files, {len(bans)} banned words)")

if __name__ == "__main__": main()
