import LeanSseProofs.Stream
import LeanSse.Ascii
/-! # The standard's own examples, and the cases people get wrong, as theorems about the reference

Each is `by decide` over the reference `parse`: the examples of HTML Standard 9.2.6 are the first obligations. -/

namespace LeanSse

def ev (type data id : String) : Event := ⟨ascii type, ascii data, ascii id⟩

/-- 9.2.6 example 1: three `data` lines make one event, joined by LF. -/
theorem ex_stocks :
    (parse (ascii "data: YHOO\ndata: +2\ndata: 10\n\n")).1 = [ev "message" "YHOO\n+2\n10" ""] := by decide

/-- 9.2.6 example 2: a comment, then events carrying an id; an `id` with no value resets it; the data keeps a second space. -/
theorem ex_four_blocks :
    (parse (ascii ": test stream\n\ndata: first event\nid: 1\n\ndata:second event\nid\n\ndata:  third event\n\n")).1 =
      [ev "message" "first event" "1", ev "message" "second event" "", ev "message" " third event" ""] := by decide

/-- 9.2.6 example 3: empty data lines still make events (an empty one, and one holding a single newline); the block with no blank line after it is discarded. -/
theorem ex_empty_data :
    (parse (ascii "data\n\ndata\ndata\n\ndata:")).1 = [ev "message" "" "", ev "message" "\n" ""] := by decide

/-- 9.2.6 example 4: the one space after the colon is dropped, if present. -/
theorem ex_space :
    (parse (ascii "data:test\n\ndata: test\n\n")).1 = [ev "message" "test" "", ev "message" "test" ""] := by decide

/-- The three line terminators mean the same thing, mixed in one stream. -/
theorem ex_terminators :
    parse (ascii "data: a\r\ndata: b\r\rdata: c\n\r\n") = parse (ascii "data: a\ndata: b\n\ndata: c\n\n") := by decide

/-- A multi-line `data` is one event (a reader that takes each `data` line as its own message gets this wrong). -/
theorem ex_multiline_data :
    (parse (ascii "data: {\"a\":\ndata: 1}\n\n")).1 = [ev "message" "{\"a\":\n1}" ""] := by decide

/-- A named event. -/
theorem ex_event_type :
    (parse (ascii "event: ping\ndata: x\n\n")).1 = [ev "ping" "x" ""] := by decide

/-- A comment line (a keep-alive) dispatches nothing and changes nothing. -/
theorem ex_comment :
    parse (ascii ": keep-alive\n\n") = ([], {}) := by decide

/-- A byte order mark at the very start is removed (once). -/
theorem ex_bom :
    (parse ([0xEF, 0xBB, 0xBF] ++ ascii "data: x\n\n")).1 = [ev "message" "x" ""] := by decide

/-- A second byte order mark is part of the first line (the field name `<BOM>data`, which no field has). -/
theorem ex_bom_twice :
    (parse ([0xEF, 0xBB, 0xBF, 0xEF, 0xBB, 0xBF] ++ ascii "data: x\n\n")).1 = [] := by decide

/-- A last event ID persists across events that set none. -/
theorem ex_id_persists :
    (parse (ascii "id: 7\ndata: a\n\ndata: b\n\n")).1 = [ev "message" "a" "7", ev "message" "b" "7"] := by decide

/-- A `retry` field sets the reconnection time, and is not an event. -/
theorem ex_retry :
    parse (ascii "retry: 200\n\n") = ([], { retry := some 200 }) := by decide

/-- A NUL in an `id` makes the field ignored: the earlier id stays. -/
theorem ex_id_nul :
    (parse (ascii "id: 1\ndata: a\n" ++ [105, 100, 58, 32, 120, 0, 10, 10])).1 = [ev "message" "a" "1"] := by decide

/-- A CR at the end of one chunk and its LF at the start of the next: one terminator, not two (no extra blank line, no extra event). -/
theorem ex_cr_lf_across_chunks :
    (feedChunks {} [ascii "data: a\r", ascii "\n\r", ascii "\ndata: b\n\n"]).2 = [ev "message" "a" "", ev "message" "b" ""] := by decide

end LeanSse
