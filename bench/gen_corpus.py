#!/usr/bin/env python3
"""The benchmark corpus of vbm-sse (docs/bench.md): five deterministic Server-Sent Events streams, written to DIR as NAME.sse.

  small-events   the primary corpus: 30000 small events (about 120 bytes each) of the shape a chat-completion stream has: a `data:` line of a short JSON object,
                 a blank line; every 10th event also has an `id:` line, every 25th an `event:` line, every 50th a `: keepalive` comment line before it. LF line ends.
  large-data     events whose `data:` lines are long (2 KB to 16 KB) and events of many (8 to 40) short `data:` lines that the reader joins with LF. LF line ends.
  ends-crlf      the same events as small-events, every line ended by CR LF.
  ends-cr        the same events as small-events, every line ended by a lone CR.
  ends-mixed     the same events as small-events, each line ended by CR LF, CR or LF, chosen per line from the generator's own stream.

ASCII only (so a cut at any byte is a cut at a character: the comparators that take text are fed the same cuts). The generator has no input but the fixed seed below and its own
integer generator (splitmix64), so the bytes depend on nothing: not on a Python version, not on the clock, not on the machine. The sha256 of each file is pinned by the bench command in
scorecard.toml, and `gen_corpus.py --sha256` prints them. The events of a corpus are decided by the Lean reference (`vbm-sse-bench` counts them) and every implementation measured must agree.
Usage: gen_corpus.py DIR | gen_corpus.py --sha256 (print NAME SHA256 BYTES for each corpus; writes nothing)."""
import hashlib, sys

M = (1 << 64) - 1


class Rng:
    def __init__(self, seed): self.s = seed & M

    def next(self):
        self.s = (self.s + 0x9E3779B97F4A7C15) & M
        z = self.s
        z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & M
        z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & M
        return z ^ (z >> 31)

    def below(self, n): return self.next() % n


WORDS = ["the", "quick", "brown", "fox", "jumps", "over", "lazy", "dog", "stream", "token", "delta", "model", "hello", "world", "verified", "reader", "event", "chunk"]


def small_events(rng, n):
    """n events, as a list of lists of lines (no line ends); an empty line closes an event."""
    out = []
    for i in range(n):
        ev = []
        if i % 50 == 25: ev.append(": keepalive")
        if i % 25 == 3: ev.append("event: delta")
        if i % 10 == 7: ev.append("id: %d" % (1000 + i))
        w = WORDS[rng.below(len(WORDS))]
        ev.append('data: {"id":"chatcmpl-%08x","object":"chat.completion.chunk","choices":[{"index":0,"delta":{"content":"%s"}}]}' % (rng.below(1 << 32), w))
        ev.append("")
        out.append(ev)
    return out


def large_data(rng, total):
    out, size = [], 0
    while size < total:
        ev = []
        if rng.below(3) == 0:
            n = 2048 + rng.below(14337)   # one data line of 2 KB to 16 KB
            ev.append("data: " + "".join(WORDS[rng.below(len(WORDS))][0] for _ in range(n)))
        else:
            for _ in range(8 + rng.below(33)):   # many short data lines, joined with LF by the reader
                ev.append("data: " + " ".join(WORDS[rng.below(len(WORDS))] for _ in range(1 + rng.below(8))))
        ev.append("")
        size += sum(len(l) + 1 for l in ev)
        out.append(ev)
    return out


def render(events, end, rng=None):
    parts = []
    for ev in events:
        for line in ev:
            parts.append(line + (end if rng is None else ("\r\n", "\r", "\n")[rng.below(3)]))
    return "".join(parts).encode("ascii")


def corpora():
    base = small_events(Rng(1), 30000)
    return [
        ("small-events", render(base, "\n")),
        ("large-data", render(large_data(Rng(2), 1_500_000), "\n")),
        ("ends-crlf", render(base, "\r\n")),
        ("ends-cr", render(base, "\r")),
        ("ends-mixed", render(base, None, Rng(3))),
    ]


if __name__ == "__main__":
    if len(sys.argv) != 2: sys.exit(__doc__)
    for name, data in corpora():
        if sys.argv[1] == "--sha256": print(name, hashlib.sha256(data).hexdigest(), len(data))
        else:
            with open("%s/%s.sse" % (sys.argv[1], name), "wb") as f: f.write(data)
