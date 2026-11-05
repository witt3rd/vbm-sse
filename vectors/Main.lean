import LeanSse.Vectors
/-! The vector generator `vbm-sse-vectors-1`. Rows come from the Lean reference (`LeanSse.Vectors`); this executable only writes them.
  vbm-sse-vectors [--n N] [--out FILE]     write the rows (default N = 3) to FILE or stdout, after checking the machine against the reference on every cut
  vbm-sse-vectors --check FILE [--n N]     the file's lines are exactly the rows the reference gives (a tampered, dropped or added row fails)
  vbm-sse-vectors --selftest               the check can fail: a tampered row, a missing row and an extra row are each rejected -/
open LeanSse

def argOf (args : List String) (k : String) (d : String) : String :=
  match args.dropWhile (· != k) with | _ :: v :: _ => v | _ => d

def checkLines (want got : List String) : Bool := want == got

def main (args : List String) : IO UInt32 := do
  let n := (argOf args "--n" "3").toNat!
  if args.contains "--selftest" then
    let r := rows 2
    unless checkLines r r do IO.eprintln "vectors: the check rejects the rows themselves"; return 1
    let tampered := r.mapIdx fun i l => if i == 5 then l.replace "\"events\":[" "\"events\":[{\"type\":\"00\",\"data\":\"00\",\"last_event_id\":\"\"}," else l
    if checkLines r tampered then IO.eprintln "vectors: self-test: a tampered row was accepted"; return 1
    if checkLines r (r.drop 1) then IO.eprintln "vectors: self-test: a dropped row was accepted"; return 1
    if checkLines r (r ++ ["x"]) then IO.eprintln "vectors: self-test: an added row was accepted"; return 1
    unless consistent 2 do IO.eprintln "vectors: the machine disagrees with the reference"; return 1
    IO.println "vectors: the check rejects tampered, dropped and added rows"
    return 0
  unless consistent n do IO.eprintln "vectors: the machine disagrees with the reference on some cut"; return 1
  let rs := rows n
  if args.contains "--check" then
    let f := argOf args "--check" ""
    let got := (← IO.FS.readFile f).splitOn "\n" |>.filter (· != "")
    if checkLines rs got then IO.println s!"vectors: {rs.length} rows match the reference (vbm-sse-vectors-1, n = {n})"; return 0
    IO.eprintln s!"vectors: {f} is not the reference's rows (vbm-sse-vectors-1, n = {n})"; return 1
  let text := "\n".intercalate rs ++ "\n"
  if args.contains "--out" then IO.FS.writeFile (argOf args "--out" "") text else IO.print text
  IO.eprintln s!"vectors: {rs.length} rows, the machine agrees with the reference on every cut (vbm-sse-vectors-1, n = {n})"
  return 0
