import LeanSse
/-! `vbm-sse-bench FILE`: the Lean side of the throughput bench (docs/bench.md). For one corpus file it prints
      reference N MB/S events E        the whole-buffer reference `LeanSse.parse` (a list of bytes: the specification itself, not a fast reader)
      lean-fast CHUNK MB/S events E    the array machine `feedF` in Lean, the stream cut into chunks of CHUNK bytes (1, 7, 4096), the events taken out after each chunk as the C interface does
    The corpus is read and cut into chunks before the clock starts; each figure is the best of `reps` runs. The event counts are printed so that every implementation can be checked to agree.
    Not part of any export (it is not reachable from the library). -/
open LeanSse

def reps : Nat := 3

def secs (a b : Nat) : Float := (b - a).toFloat / 1.0e9

/-- Best of `reps` runs of `f i` (the run number goes in, so that no run can be shared with another). The result is looked at BEFORE the clock is read again: a pure value would otherwise be computed
after the clock (the compiler moves it to its use). -/
def best (f : Nat → Nat) : IO (Float × Nat) := do
  let mut t := 1.0e18
  let mut ev := 0
  for i in [0:reps] do
    let a ← IO.monoNanosNow
    ev := f i
    if ev == 0xFFFFFFFFFFFF then IO.eprintln "impossible"
    let b ← IO.monoNanosNow
    t := min t (secs a b)
  return (t, ev)

def cut (b : ByteArray) (c : Nat) : Array ByteArray := Id.run do
  let mut out := #[]
  let mut i := 0
  while i < b.size do
    out := out.push (b.extract i (min b.size (i + c)))
    i := i + c
  return out

@[noinline] def feedAll (cs : Array ByteArray) (i : Nat) : Nat := Id.run do
  let mut s : FSt := { p := { retry := some i.toUInt64 } }
  let mut n := 0
  for c in cs do
    s := feedF s c
    n := n + s.outN
    s := { s with outBuf := ByteArray.empty, outN := 0 }
  return n

def main (args : List String) : IO UInt32 := do
  let some f := args.head? | IO.eprintln "usage: vbm-sse-bench FILE"; return 2
  let b ← IO.FS.readBinFile f
  let mb := b.size.toFloat / 1.0e6
  let l : List UInt8 := b.toList
  let _ ← IO.lazyPure fun _ => l.length
  let (t, ev) ← best (fun i => (parse (if i == 0xFFFFFFFFFFFF then [] else l)).1.length)
  IO.println s!"reference N {mb / t} events {ev}"
  for c in [1, 7, 4096] do
    let cs := cut b c
    let (t, ev) ← best (feedAll cs)
    IO.println s!"lean-fast {c} {mb / t} events {ev}"
  return 0
