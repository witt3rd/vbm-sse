#!/usr/bin/env python3
"""Tier 1: the ABI description (abi/vbm_sse.abi.json), the C header (include/vbm_sse.h) and the report layout in LeanSse/Abi.lean must agree: ABI version, the result codes, every struct field, every function
prototype, the opaque type, and the report's words (their names and order, in the header's text and in the Lean module's). Usage: check_abi.py [--selftest]. With --selftest it also shows the check can fail:
each of a set of drifted headers (and drifted descriptions and Lean texts) must be rejected. Exit 1 on any disagreement."""
import json, re, sys

def strip_comments(t):
    t = re.sub(r"/\*.*?\*/", "", t, flags=re.S)
    return "\n".join(l for l in t.splitlines() if not l.lstrip().startswith("#"))

def ws(s):  # whitespace removed: the comparison is of tokens, not of layout
    return re.sub(r"\s+", "", s)

def parse_header(raw):
    """-> dict(version, enums=[{NAME: value}], structs={name: [decl]}, opaque=[names], funcs={name: text})"""
    h = {"version": None, "enums": [], "structs": {}, "opaque": [], "funcs": {}}
    m = re.search(r"#define\s+VBM_SSE_ABI_VERSION\s+(\d+)u?", raw)
    h["version"] = int(m.group(1)) if m else None
    t = strip_comments(raw)
    for body in re.findall(r"enum\s*\{(.*?)\}\s*;", t, flags=re.S):
        d = {}
        for item in body.split(","):
            if item.strip():
                k, _, v = item.partition("=")
                d[k.strip()] = int(v.strip(), 0)
        h["enums"].append(d)
    t = re.sub(r"enum\s*\{.*?\}\s*;", "", t, flags=re.S)
    def struct(m):
        h["structs"][m.group(2)] = [ws(d) for d in m.group(1).split(";") if d.strip()]
        return ""
    t = re.sub(r"typedef\s+struct\s+\w+\s*\{(.*?)\}\s*(\w+)\s*;", lambda m: struct(m), t, flags=re.S)
    h["opaque"] = re.findall(r"typedef\s+struct\s+\w+\s+(\w+)\s*;", t)
    for st in t.split(";"):
        st = st.strip()
        m = re.match(r'^(?:extern\s*"C"\s*\{\s*)?(.*?\b(vbm_sse_\w+)\s*\(.*\))$', st, flags=re.S)
        if m and not st.startswith("typedef"):
            h["funcs"][m.group(2)] = ws(m.group(1))
    return h

def camel(n):
    parts = n.split("_")
    return parts[0] + "".join(p.capitalize() for p in parts[1:])

def check(header, desc, lean):
    """-> list of disagreements (empty: they agree)."""
    bad = []
    h = parse_header(header)
    if h["version"] != desc["abi_version"]:
        bad.append(f"ABI version: header {h['version']} vs description {desc['abi_version']}")
    want = [{"VBM_SSE_" + k["name"]: k["value"] for k in desc["errors"]}]
    if h["enums"] != want:
        bad.append(f"result codes: header {h['enums']} vs description {want}")
    if sorted(h["opaque"]) != sorted(desc["opaque"]):
        bad.append(f"opaque types: header {sorted(h['opaque'])} vs description {sorted(desc['opaque'])}")
    hs = h["structs"]
    if sorted(hs) != sorted(s["name"] for s in desc["structs"]):
        bad.append(f"structs: header {sorted(hs)} vs description {sorted(s['name'] for s in desc['structs'])}")
    for s in desc["structs"]:
        if hs.get(s["name"]) != [ws(f["c"]) for f in s["fields"]]:
            bad.append(f"struct {s['name']}: header {hs.get(s['name'])} vs description {[ws(f['c']) for f in s['fields']]}")
        for f in s["fields"]:
            if not re.search(r"\b%s\b" % re.escape(f["name"]), f["c"]):
                bad.append(f"struct {s['name']}: field name {f['name']} is not in its C text")
    hf = h["funcs"]
    if sorted(hf) != sorted(f["name"] for f in desc["functions"]):
        bad.append(f"functions: header {sorted(hf)} vs description {sorted(f['name'] for f in desc['functions'])}")
    for f in desc["functions"]:
        if hf.get(f["name"]) != ws(f["c"]):
            bad.append(f"function {f['name']}: header {hf.get(f['name'])} vs description {ws(f['c'])}")
        names = re.findall(r"(\w+)\s*(?:,|$)", f["c"].split("(", 1)[1].rstrip(")"))
        if names != [p["name"] for p in f["params"]]:
            bad.append(f"function {f['name']}: parameter names {names} vs {[p['name'] for p in f['params']]}")
    r = desc["report"]
    if "little-endian u64 words" not in header or r["word_bytes"] != 8 or r["endian"] != "little":
        bad.append("report words: the header does not say little-endian u64 words")
    # the header's REPORT block lists the words in order: "count", "retry_set", "retry", "id_len", then the events' "type_len, data_len, id_len"
    block = header.split("THE REPORT", 1)[-1].split("MEMORY:", 1)[0]
    pos = -1
    for w in r["header"]:
        m = re.search(r"^ \*   %s\b" % re.escape(w), block, flags=re.M)
        if not m or m.start() <= pos:
            bad.append(f"report: the header text does not list the word '{w}' in the description's order")
            break
        pos = m.start()
    if not re.search(r"each: %s" % ", ".join(r["event"]), block):
        bad.append("report: the header text does not give the event's words as 'each: %s'" % ", ".join(r["event"]))
    # the Lean module that builds the report documents the same words (camelCase there)
    doc = lean.split("namespace LeanSse", 1)[0]
    for w in r["header"] + r["event"]:
        if "`%s`" % camel(w) not in doc:
            bad.append(f"report: LeanSse/Abi.lean does not name the word `{camel(w)}`")
    return bad

def selftest(header, desc, lean):
    mutants = {
        "an enumerator value changed": lambda h, d, l: (h.replace("VBM_SSE_INTERNAL = 2", "VBM_SSE_INTERNAL = 7"), d, l),
        "a result code added": lambda h, d, l: (h.replace("VBM_SSE_INTERNAL = 2 }", "VBM_SSE_INTERNAL = 2, VBM_SSE_X = 3 }"), d, l),
        "the ABI version bumped": lambda h, d, l: (h.replace("VBM_SSE_ABI_VERSION 1u", "VBM_SSE_ABI_VERSION 2u"), d, l),
        "a parameter retyped": lambda h, d, l: (h.replace("size_t len,", "uint32_t len,"), d, l),
        "a parameter renamed": lambda h, d, l: (h.replace("const uint8_t *buf,", "const uint8_t *data,"), d, l),
        "a function added": lambda h, d, l: (h.replace("#ifdef __cplusplus\n}", "int vbm_sse_extra(int x);\n#ifdef __cplusplus\n}"), d, l),
        "a function removed": lambda h, d, l: (h.replace("void vbm_sse_free(vbm_sse *r);", ""), d, l),
        "a struct field retyped": lambda h, d, l: (h.replace("size_t nbytes;", "uint32_t nbytes;"), d, l),
        "a struct field reordered": lambda h, d, l: (h.replace("const uint8_t *bytes;\n  size_t nbytes;", "size_t nbytes;\n  const uint8_t *bytes;"), d, l),
        "the opaque type removed": lambda h, d, l: (h.replace("typedef struct vbm_sse vbm_sse;", ""), d, l),
        "the report's words reordered in the header": lambda h, d, l: (h.replace(" *   retry_set  1 if", " *   retry_zzz  1 if").replace(" *   retry      the", " *   retry_set  the"), d, l),
        "the report's event words changed in the header": lambda h, d, l: (h.replace("each: type_len, data_len, id_len", "each: data_len, type_len, id_len"), d, l),
        "the report is no longer little-endian in the header": lambda h, d, l: (h.replace("little-endian u64 words", "big-endian u64 words"), d, l),
        "the description drifted (a result code)": lambda h, d, l: (h, json.loads(json.dumps(d).replace('"ARG", "value": 1', '"ARG", "value": 9')), l),
        "the description drifted (a field type text)": lambda h, d, l: (h, json.loads(json.dumps(d).replace("size_t nbytes", "size_t nbytes2")), l),
        "the description drifted (a header word)": lambda h, d, l: (h, json.loads(json.dumps(d).replace('"retry_set"', '"retry_flag"')), l),
        "Abi.lean's documented words drifted": lambda h, d, l: (h, d, l.replace("`retrySet`", "`retryFlag`")),
    }
    for name, f in mutants.items():
        h2, d2, l2 = f(header, desc, lean)
        if (h2, d2, l2) == (header, desc, lean):
            sys.exit(f"check_abi: self-test: the mutation '{name}' changed nothing")
        if not check(h2, d2, l2):
            sys.exit(f"check_abi: self-test: '{name}' was NOT rejected (the check cannot fail)")
    return len(mutants)

def main():
    header = open("include/vbm_sse.h").read()
    desc = json.load(open("abi/vbm_sse.abi.json"))
    lean = open("LeanSse/Abi.lean").read()
    bad = check(header, desc, lean)
    if bad:
        print("check_abi: the header, the ABI description and Abi.lean disagree:", file=sys.stderr)
        for b in bad: print("  " + b, file=sys.stderr)
        sys.exit(1)
    n = selftest(header, desc, lean) if "--selftest" in sys.argv else 0
    print("check_abi: ok: header, description and Abi.lean agree (%d functions, %d structs, %d result codes, %d report words)%s" % (
        len(desc["functions"]), len(desc["structs"]), len(desc["errors"]), len(desc["report"]["header"]) + len(desc["report"]["event"]),
        "; %d drifted variants each rejected" % n if n else ""))

if __name__ == "__main__":
    main()
