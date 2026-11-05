import LeanSseProofs.Stream
import LeanSseProofs.Spec
import LeanSseProofs.Examples
/-! # The obligation ledger

Every claim the library makes, keyed by a slug and tagged with the clauses of the standard it concerns (`docs/spec-clauses.txt`: the tags are checked against it, and a claim
with no tag fails the gate). A claim is `proved` only by naming theorems (double-backtick names are checked at elaboration, so a renamed or deleted theorem breaks this file),
`partly` when theorems cover only a part (the note says which part is open), `open_` when nothing is proved, or `limit` when no machine decides it (the note says who carries it).
`scripts/LedgerGate.lean` renders `docs/proof-ledger.md` from this list and ratchets it: proved may only rise, open may only fall. A report may not call anything verified
that is not `proved`. -/

inductive Status where
  | proved (thms : List Lean.Name)
  | partly (thms : List Lean.Name) (open_ : String)
  | open_ (note : String)
  | limit (carriedBy : String)

structure Obligation where
  slug    : String
  /-- The clauses of the standard (or the library's own policy) the claim is about: tags of `docs/spec-clauses.txt`. -/
  clauses : List String
  status  : Status

def O (slug : String) (clauses : List String) (s : Status) : Obligation := ⟨slug, clauses, s⟩

def ledger : List Obligation := [
  -- the reference reads the standard
  O "reference-is-the-standard" ["whatwg-html:parsing-an-event-stream", "whatwg-html:event-stream-interpretation"]
    (.limit "the reference is written from the text of sections 9.2.5 and 9.2.6 at the snapshot pinned in docs/spec-pin.txt; fidelity to prose is checked by review and by the standard's own examples (the `ex_` theorems), and no machine decides it"),
  O "standard-examples" ["whatwg-html:event-stream-interpretation/examples"]
    (.proved [``LeanSse.ex_stocks, ``LeanSse.ex_four_blocks, ``LeanSse.ex_empty_data, ``LeanSse.ex_space]),
  -- lines
  O "line-terminators-interchangeable" ["whatwg-html:parsing-an-event-stream/end-of-line", "whatwg-html:event-stream-interpretation/lines"]
    (.proved [``LeanSse.crlf_is_lf, ``LeanSse.cr_is_lf, ``LeanSse.splitLines_line, ``LeanSse.ex_terminators]),
  O "line-split-keeps-the-rest" ["whatwg-html:event-stream-interpretation/lines"]
    (.proved [``LeanSse.splitLines_noTerm, ``LeanSse.splitLines_lf, ``LeanSse.splitLines_cr]),
  -- fields
  O "field-split-at-first-colon" ["whatwg-html:event-stream-interpretation/line-forms"]
    (.proved [``LeanSse.splitField_colon, ``LeanSse.splitField_noColon, ``LeanSse.dropSpace_one, ``LeanSse.procLine_blank, ``LeanSse.procLine_comment, ``LeanSse.procLine_field]),
  O "field-table" ["whatwg-html:event-stream-interpretation/process-the-field"]
    (.proved [``LeanSse.field_event, ``LeanSse.field_data, ``LeanSse.field_id, ``LeanSse.field_id_nul, ``LeanSse.field_retry, ``LeanSse.field_unknown, ``LeanSse.data_lines_joined, ``LeanSse.ex_multiline_data, ``LeanSse.ex_id_nul]),
  O "retry-needs-a-digit" ["whatwg-html:event-stream-interpretation/process-the-field", "vbm:policy-retry"]
    (.partly [``LeanSse.field_retry_ignored, ``LeanSse.ex_retry] "the standard's sentence 'consists of only ASCII digits' is silent on the empty string; the library ignores it (as the engines do). Proved: what is ignored and what is set. Carried by the policy note: that this is the standard's meaning"),
  O "dispatch" ["whatwg-html:event-stream-interpretation/dispatch"]
    (.proved [``LeanSse.dispatch_lastEventId, ``LeanSse.dispatch_clears, ``LeanSse.dispatch_empty, ``LeanSse.dispatch_event, ``LeanSse.ex_event_type, ``LeanSse.ex_id_persists, ``LeanSse.ex_comment]),
  -- the byte order mark
  O "bom-stripped-once" ["whatwg-html:event-stream-interpretation/bom"]
    (.proved [``LeanSse.bom_stripped, ``LeanSse.bom_once, ``LeanSse.ex_bom, ``LeanSse.ex_bom_twice]),
  -- the incremental machine
  O "incremental-equals-reference" ["vbm:chunk-invariance"]
    (.proved [``LeanSse.feed_body, ``LeanSse.feed_bom, ``LeanSse.feed_eq_parse]),
  O "chunk-invariance" ["vbm:chunk-invariance", "whatwg-html:event-stream-interpretation/lines", "whatwg-html:event-stream-interpretation/bom"]
    (.proved [``LeanSse.chunk_invariance, ``LeanSse.chunkings_agree, ``LeanSse.split_anywhere, ``LeanSse.byte_at_a_time, ``LeanSse.feed_append, ``LeanSse.feedChunks_eq]),
  O "cr-lf-split-across-chunks" ["vbm:chunk-invariance", "whatwg-html:parsing-an-event-stream/end-of-line"]
    (.proved [``LeanSse.chunk_invariance, ``LeanSse.ex_cr_lf_across_chunks]),
  O "end-of-stream-discards-pending-data" ["whatwg-html:event-stream-interpretation/end-of-file"]
    (.proved [``LeanSse.parse_append_noTerm, ``LeanSse.feed_noTerm, ``LeanSse.step_event_terminator]),
  -- text
  O "values-are-decoded-as-utf-8" ["whatwg-html:event-stream-interpretation/utf-8"]
    (.open_ "values are byte strings; the UTF-8 decode algorithm's replacement of invalid sequences is a per-value step that commutes with the line and field cuts (they fall on ASCII bytes), to be specified and proved in LeanSse.Utf8"),
  O "stream-production-agrees" ["whatwg-html:parsing-an-event-stream/abnf"]
    (.open_ "the ABNF `stream` production as a relation, and that the reference reads exactly the streams it derives as the standard describes them (every other byte string is read by the same algorithm, with no refusal)"),
  -- the compiled code
  O "fast-machine-refines-reference" ["vbm:chunk-invariance"]
    (.open_ "an array-based machine that scans a chunk for its terminators in bulk, and its refinement to `feed`"),
  O "bounded-state" ["vbm:policy-bounds"]
    (.open_ "the machine holds one line and the data buffer; neither is bounded by the standard, so a hostile stream grows them without limit. A named cap with a typed refusal is a policy to specify before the C interface"),
  O "vectors-come-from-the-reference" ["vbm:chunk-invariance"]
    (.limit "the shared rows (vbm-sse-vectors-1) are written by LeanSse.Vectors from `parse` only, and the generator checks the compiled machine against the reference on every cut (whole, byte by byte, each two-way split) before it writes: a run of compiled code, not a proof; `chunk_invariance` is the theorem it exercises. The row set is pinned by size and sha256 (scripts/vectors-baseline.txt)"),
  O "bindings-agree-with-the-reference" ["vbm:chunk-invariance"]
    (.limit "every binding will run the vectors the Lean reference generated; a second implementation per language is tested, not proved")]
