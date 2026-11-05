#!/usr/bin/env python3
"""The Python binding against the Lean reference: every row of the shared vectors (vbm-sse-vectors-1), on every cut: the whole input as one chunk, one byte per chunk, and each two-way split.
Usage: test_python.py VECTORS.jsonl [PACKAGE_PARENT_DIR]. Needs VBM_SSE_LIB (scripts/build_shared.sh). The events collected from the reports, the last report's last event ID and the reconnection time must
equal the row's. A DRIVER: it holds no input of its own (the retry saturation, the BOM and the CR LF rows are rows of the generated set)."""
import json, re, sys
if len(sys.argv) > 2: sys.path.insert(0, sys.argv[2])
import vbm_sse
from vbm_sse import Reader, Event

def run(chunks):
    events, last = [], None
    with Reader() as r:
        for c in chunks:
            last = r.feed(c)
            events += last.events
    return events, last.last_event_id, last.retry

def main():
    rows = runs = 0
    for line in open(sys.argv[1]):
        # the reconnection time as text: JSON parsers may round integers above 2**53 (Python's does not, but a driver should not rely on it)
        r = json.loads(line)
        want_retry = None if r["retry"] is None else int(re.search(r'"retry":(\d+)\}$', line.strip()).group(1))
        data = bytes.fromhex(r["input"])
        want = [Event(bytes.fromhex(e["type"]), bytes.fromhex(e["data"]), bytes.fromhex(e["last_event_id"])) for e in r["events"]]
        wid = bytes.fromhex(r["last_event_id"])
        cuts = [[data]] + [[data[:k], data[k:]] for k in range(len(data) + 1)] + ([[bytes([b]) for b in data]] if data else [])
        for cs in cuts:
            evs, lid, retry = run(cs); runs += 1
            if evs != want or lid != wid or retry != want_retry:
                sys.exit("test_python: row %s, %d chunk(s): events %r last_event_id %r retry %r, expected %r %r %r" % (r["id"], len(cs), evs, lid, retry, want, wid, want_retry))
        rows += 1
    # the binding's own API: a closed reader refuses; the error classes carry the ABI code
    r = Reader(); r.close(); r.close()
    try: r.feed(data); sys.exit("test_python: a closed reader accepted a chunk")
    except ValueError: pass
    assert issubclass(vbm_sse.SSEArgError, vbm_sse.Error) and vbm_sse.ABI_VERSION == 1
    # the library refuses a NULL reader with the ABI's code (1, ARG), and the binding maps that code to its error class
    import ctypes
    from vbm_sse import _generated as g
    rep = g.vbm_sse_report()
    rc = g.vbm_sse_feed(None, None, 0, ctypes.byref(rep))
    assert rc == 1 and g.ARG == 1, "test_python: a NULL reader is not refused with code 1"
    try: g._raise(rc); sys.exit("test_python: _raise did not raise")
    except vbm_sse.SSEArgError as e: assert e.code == 1 and e.name == "ARG"
    assert rows > 100, "test_python: fewer than 100 rows"
    print("test_python: %d rows, %d cuts: events, last event ID and reconnection time equal the reference's" % (rows, runs))

main()
