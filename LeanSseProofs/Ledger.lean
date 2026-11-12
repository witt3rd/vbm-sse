import LeanSseProofs.Stream
import LeanSseProofs.Spec
import LeanSseProofs.Examples
import LeanSseProofs.Fast
import LeanSseProofs.Abi
import LandLedger
/-! # The obligation ledger

Every claim the library makes, keyed by a slug and tagged with the clauses of the standard it concerns (`docs/spec-clauses.txt`: the tags are checked against it, and a claim
with no tag fails the gate). A claim is `proved` only by naming theorems (double-backtick names are checked at elaboration, so a renamed or deleted theorem breaks this file),
`partly` when theorems cover only a part (the note says which part is open), `open_` when nothing is proved, or `limit` when no machine decides it (the note says who carries it).
`land-lean ledger` renders `docs/proof-ledger.md` from this list and ratchets it: proved may only rise, open may only fall. A report may not call anything verified
that is not `proved`. -/

open Land.Ledger

def ledger : List Obligation := [
  -- the reference reads the standard
  OC "reference-is-the-standard" ["whatwg-html:parsing-an-event-stream", "whatwg-html:event-stream-interpretation"]
    (.limit "the reference is written from the text of sections 9.2.5 and 9.2.6 at the snapshot pinned in docs/spec-pin.txt; fidelity to prose is checked by review and by the standard's own examples (the `ex_` theorems), and no machine decides it"),
  OC "standard-examples" ["whatwg-html:event-stream-interpretation/examples"]
    (.proved [``LeanSse.ex_stocks, ``LeanSse.ex_four_blocks, ``LeanSse.ex_empty_data, ``LeanSse.ex_space]),
  -- lines
  OC "line-terminators-interchangeable" ["whatwg-html:parsing-an-event-stream/end-of-line", "whatwg-html:event-stream-interpretation/lines"]
    (.proved [``LeanSse.crlf_is_lf, ``LeanSse.cr_is_lf, ``LeanSse.splitLines_line, ``LeanSse.ex_terminators]),
  OC "line-split-keeps-the-rest" ["whatwg-html:event-stream-interpretation/lines"]
    (.proved [``LeanSse.splitLines_noTerm, ``LeanSse.splitLines_lf, ``LeanSse.splitLines_cr]),
  -- fields
  OC "field-split-at-first-colon" ["whatwg-html:event-stream-interpretation/line-forms"]
    (.proved [``LeanSse.splitField_colon, ``LeanSse.splitField_noColon, ``LeanSse.dropSpace_one, ``LeanSse.procLine_blank, ``LeanSse.procLine_comment, ``LeanSse.procLine_field]),
  OC "field-table" ["whatwg-html:event-stream-interpretation/process-the-field"]
    (.proved [``LeanSse.field_event, ``LeanSse.field_data, ``LeanSse.field_id, ``LeanSse.field_id_nul, ``LeanSse.field_retry, ``LeanSse.field_unknown, ``LeanSse.data_lines_joined, ``LeanSse.ex_multiline_data, ``LeanSse.ex_id_nul]),
  OC "retry-needs-a-digit" ["whatwg-html:event-stream-interpretation/process-the-field", "vbm:policy-retry"]
    (.partly [``LeanSse.field_retry_ignored, ``LeanSse.ex_retry] "the standard's sentence 'consists of only ASCII digits' is silent on the empty string; the library ignores it (as the engines do). Proved: what is ignored and what is set. Carried by the policy note: that this is the standard's meaning"),
  OC "dispatch" ["whatwg-html:event-stream-interpretation/dispatch"]
    (.proved [``LeanSse.dispatch_lastEventId, ``LeanSse.dispatch_clears, ``LeanSse.dispatch_empty, ``LeanSse.dispatch_event, ``LeanSse.ex_event_type, ``LeanSse.ex_id_persists, ``LeanSse.ex_comment]),
  -- the byte order mark
  OC "bom-stripped-once" ["whatwg-html:event-stream-interpretation/bom"]
    (.proved [``LeanSse.bom_stripped, ``LeanSse.bom_once, ``LeanSse.ex_bom, ``LeanSse.ex_bom_twice]),
  -- the incremental machine
  OC "incremental-equals-reference" ["vbm:chunk-invariance"]
    (.proved [``LeanSse.feed_body, ``LeanSse.feed_bom, ``LeanSse.feed_eq_parse]),
  OC "chunk-invariance" ["vbm:chunk-invariance", "whatwg-html:event-stream-interpretation/lines", "whatwg-html:event-stream-interpretation/bom"]
    (.proved [``LeanSse.chunk_invariance, ``LeanSse.chunkings_agree, ``LeanSse.split_anywhere, ``LeanSse.byte_at_a_time, ``LeanSse.feed_append, ``LeanSse.feedChunks_eq]),
  OC "cr-lf-split-across-chunks" ["vbm:chunk-invariance", "whatwg-html:parsing-an-event-stream/end-of-line"]
    (.proved [``LeanSse.chunk_invariance, ``LeanSse.ex_cr_lf_across_chunks]),
  OC "end-of-stream-discards-pending-data" ["whatwg-html:event-stream-interpretation/end-of-file"]
    (.proved [``LeanSse.parse_append_noTerm, ``LeanSse.feed_noTerm, ``LeanSse.step_event_terminator]),
  -- text
  OC "values-are-decoded-as-utf-8" ["whatwg-html:event-stream-interpretation/utf-8"]
    (.open_ "values are byte strings; the UTF-8 decode algorithm's replacement of invalid sequences is a per-value step that commutes with the line and field cuts (they fall on ASCII bytes), to be specified and proved in LeanSse.Utf8"),
  OC "stream-production-agrees" ["whatwg-html:parsing-an-event-stream/abnf"]
    (.open_ "the ABNF `stream` production as a relation, and that the reference reads exactly the streams it derives as the standard describes them (every other byte string is read by the same algorithm, with no refusal)"),
  -- the compiled code
  OC "fast-machine-refines-reference" ["vbm:chunk-invariance"]
    (.partly [``LeanSse.stepF_sim, ``LeanSse.feedF_sim, ``LeanSse.feedChunksF_sim, ``LeanSse.fast_eq_parse, ``LeanSse.procLineF_abs, ``LeanSse.applyFieldF_abs, ``LeanSse.dispatchF_abs, ``LeanSse.splitFieldF_abs, ``LeanSse.digitsValF_eq, ``LeanSse.satStep]
      "the array machine (`feedF`, byte arrays, in-place line, events in `out`) yields the reference's events and final state on every chunking. Open: the bulk scan of a chunk for its terminators (the machine still takes one byte at a time)"),
  -- WHATWG leaves the overflow of a retry value unspecified; this library saturates it (a deliberate, documented deviation: docs/spec.md P-retry), theorem retry_saturates
  OC "retry-saturates" ["vbm:policy-retry"]
    (.proved [``LeanSse.retry_saturates, ``LeanSse.retry_le_cap, ``LeanSse.satStep, ``LeanSse.digitsValF_eq, ``LeanSse.digitsValF_digitsVal, ``LeanSse.applyFieldF_abs]),
  -- the C interface
  OC "report-says-what-the-machine-holds" ["vbm:abi-report"]
    (.proved [``LeanSse.pushWord_L, ``LeanSse.packEvent_L, ``LeanSse.report_L, ``LeanSse.rdReport_encReport, ``LeanSse.report_decodes, ``LeanSse.abi_feed_report]),
  OC "c-edge-moves-bytes" ["vbm:abi-report"]
    (.limit "abi/vbm_sse.c copies a chunk in and hands the report's bytes out; it decides nothing, but it is C and is not proved. It is checked by the compiled library running every row of vbm-sse-vectors-1 on every cut (scripts/test_native.sh) and by mutants of the shim and the runtime that each fail that run; listed as entries of the trust ledger"),
  OC "compiled-code-agrees-with-the-lean" ["vbm:chunk-invariance"]
    (.limit "the C that Lean emits, and the freestanding runtime that replaces libleanrt for it, are not proved to preserve the semantics of the Lean (trust ledger T01, T03, T04, T10); the shared vectors are the check, in the native build and in WebAssembly"),
  OC "bounded-state" ["vbm:policy-bounds"]
    (.open_ "the machine holds one line and the data buffer; neither is bounded by the standard, so a hostile stream grows them without limit. A named cap with a typed refusal is a policy to specify before the C interface"),
  OC "vectors-come-from-the-reference" ["vbm:chunk-invariance"]
    (.limit "the shared rows (vbm-sse-vectors-1) are written by LeanSse.Vectors from `parse` only, and the generator checks the compiled machine against the reference on every cut (whole, byte by byte, each two-way split) before it writes: a run of compiled code, not a proof; `chunk_invariance` is the theorem it exercises. The row set is pinned by size and sha256 (scripts/vectors-baseline.txt)"),
  OC "bindings-agree-with-the-reference" ["vbm:chunk-invariance"]
    (.limit "every binding will run the vectors the Lean reference generated; a second implementation per language is tested, not proved")]
