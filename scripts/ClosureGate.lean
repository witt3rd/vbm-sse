import Lean
import LeanSse
import LeanSseProofs
/-! Closure gate (adapted from the closure gate of the project these gates were first built in; docs/decisions/0001-vbm-sse.md): what the library's exports execute, classified.

Walks every definition reachable from the entry points (`scripts/closure-entries.txt`: one constant name per line, the Lean functions the C exports
`vbm_sse_*` call; none yet, they arrive with the ABI) and sorts it by where it comes from:
  spec        a `LeanSse` definition (specified; the code IS the specification, one Lean core)
  boundary    an `@[extern]` declaration of ours (a named trust-ledger item)
  toolchain   Lean's `Init` (trusted: docs/trust-ledger.md)
  pinned      a definition of a PINNED LIBRARY (`scripts/pinned-libs.lock`, docs/decisions/0005-pinned-library.md; today vbm-simd, root `VbmSimd`): counted as SPEC while the library on disk matches its lock
              line (the lake manifest's rev, the checkout's HEAD, the spec_hash of its spec files) and every module of its root was built from that very checkout; else UNVERIFIED. Its reached mass is
              printed apart and RATCHETED (`dep_mass` of the baseline may only fall: a new pin or more reached code is a reviewed edit). Its `@[extern]` shims count as boundary.
  carveout    an `@[extern]` declaration named in `scripts/carveouts.txt` (DECISIONS 20 of the scorecard: a documented, protected carve-out: its trust-ledger entry says what it is, why it cannot be proved and how it is checked instead; its files are in the protected set).
              It is OUTSIDE the specified share (numerator and denominator), printed apart (`carve-outs: N nodes`) and RATCHETED: `carveout_mass` of the baseline may only fall without approval. An extern NOT listed stays boundary and counts against the share.
  UNVERIFIED  a definition of ours outside `LeanSse` (the ABI shim and the like: none yet); its count per module may only fall
  FORBIDDEN   `LeanSseProofs` or `VbmSimdProofs` (never linked) or `Std`/`Lean` (Init only: a `Lean.*` import forces full runtime initialisation): any such definition
              reachable from an entry point FAILS the gate.
There is no handler class here: the boundary never decides (AGENTS.md); that project's handler mass and its target ratchet are not carried over.
DEFINITIONS (single source: this gate; other scripts quote its printed line, they never recompute):
  executed mass = the sum, over every definition reachable from the entry points (aux/theorems/constructors excluded), of the expression nodes
    (`sizeWithoutSharing` of its value), for every class of ours: spec + boundary + UNVERIFIED. Not in it: the toolchain (printed apart) and the C
    runtime (unmeasured in nodes).
  specified share = mass(spec) / executed mass. Every run prints the parts, never a bare percentage:
    `spec N | boundary N | unverified N | total N | deciding: n/a (...) | specified share P% (floor M%)`.
  The numerator is ONE class, whose membership no file we control decides: the module root `LeanSse`. The denominator is ALL executed mass of our
  own code, so moving a definition between non-spec classes cannot raise the share. The floor is the baseline line `specified_share S T` (an exact
  fraction); it may only rise: a fall fails, `--write` raises it on improvement and refuses to lower it, a baseline without the line fails.
NOT PORTED YET (upstream work in the originating gates): the deciding-code detector (the boundary / plumbing / deciding
  split of the non-spec mass, the `deciding` field printed below as n/a) and its hidden-code fix. Port them when they land.
Self-tests (`--selftest`, in this one process): the gate can fail, on synthetic measures and baselines, and the classifier and the walk are exercised on the real environment. -/
open Lean

/-- The class of a definition by the module it comes from. -/
def classifyModule (m : Name) : String :=
  let r := m.getRoot
  if r == `LeanSse then "spec"
  else if r == `LeanSseProofs || r == `VbmSimdProofs then "proofs"
  else if r == `Init then "toolchain"
  else if r == `Std || r == `Lean then "heavy"
  else "other"   -- a library root that is none of ours nor the toolchain's: a verified pinned library is spec, any other is UNVERIFIED (pinClass); it is never free

def classify (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | none => "local"
  | some idx => classifyModule env.header.moduleNames[idx.toNat]!

def isAux (env : Environment) (n : Name) : Bool :=
  isAuxRecursor env n || isNoConfusion env n || (Meta.isMatcherCore env n) ||
  (match env.find? n with
   | some (.ctorInfo _) | some (.recInfo _) | some (.inductInfo _) | some (.quotInfo _) | some (.thmInfo _) | some (.axiomInfo _) => true
   | _ => false) ||
  (n.isInternal && !(n.toString.endsWith "._unsafe_rec")) || (env.getProjectionFnInfo? n).isSome

partial def walk (env : Environment) (todo : List Name) (seen : NameSet) : NameSet :=
  match todo with
  | [] => seen
  | n :: rest =>
    if seen.contains n then walk env rest seen else
    let seen := seen.insert n
    match env.find? n with
    | none => walk env rest seen
    | some ci =>
      let used : Array Name := (match ci.value? true with | some v => v.getUsedConstants | none => #[])
      let impl := (match Compiler.getImplementedBy? env n with | some i => [i] | none => []) ++
        -- a `partial def` is an opaque constant; its body lives in `<name>._unsafe_rec`
        (if (env.find? (Name.str n "_unsafe_rec")).isSome then [Name.str n "_unsafe_rec"] else [])
      walk env (used.toList ++ impl ++ rest) seen

def readLines (p : String) : IO (List String) := do
  if !(← System.FilePath.pathExists p) then return []
  return (← IO.FS.readFile p).splitOn "\n" |>.map String.trimAscii |>.map (·.toString) |>.filter (fun l => l != "" && !l.startsWith "#")

/-- Mass of everything of ours that executes: every class except the toolchain. The specified share's denominator. -/
def execMass (mass : Std.HashMap String Nat) : Nat :=
  ["spec", "boundary", "UNVERIFIED"].foldl (fun a c => a + mass.getD c 0) 0

/-- The specified share as an exact fraction (spec mass, executed mass): the one definition the report, the ratchet and the relabel self-tests share. -/
def shareOf (mass : Std.HashMap String Nat) : Nat × Nat := (mass.getD "spec" 0, execMass mass)

/-- Percent with two decimals, in integers (exact floor). -/
def pct (a b : Nat) : String :=
  if b == 0 then "n/a" else
  let p := a * 10000 / b
  s!"{p / 100}.{if p % 100 < 10 then "0" else ""}{p % 100}%"

/-- The recorded floor `specified_share S T`: a share may only rise, compared exactly (S * T0 < S0 * T is a fall). -/
def shareFloor (base : List String) : Option (Nat × Nat) :=
  base.findSome? fun l => match l.splitOn " " with
    | ["specified_share", s, t] => do pure (← s.toNat?, ← t.toNat?)
    | _ => none

def argOf (args : List String) (k d : String) : String := match args.dropWhile (· != k) with | _ :: v :: _ => v | _ => d

/-! Pinned libraries (docs/decisions/0005-pinned-library.md). `scripts/pinned-lib.py verdict` judges the lock against the lake manifest and the checkout (rev, HEAD, spec_hash). A module root that is in neither
`LeanSse` nor the toolchain is "other": its mass counts as SPEC only when its root is a lock line whose verdict is `ok` AND every module of that root was built from that very checkout (an olean from anywhere
else is a fork: a local library that merely carries the name). Every other case is UNVERIFIED glue: a mismatch, an absent checkout, a library the lock does not name. -/
structure Pin where
  root : String
  status : String   -- ok | absent | bad
  dir : String
  why : String
deriving Inhabited

def pinVerdicts (args : List String) : IO (Std.HashMap String Pin) := do
  let a := argOf args
  let extra := (if a "--pin-lock" "" != "" then #["--lock", a "--pin-lock" ""] else #[]) ++ (if a "--pin-manifest" "" != "" then #["--manifest", a "--pin-manifest" ""] else #[]) ++
    (if a "--pin-pkgs" "" != "" then #["--pkgs", a "--pin-pkgs" ""] else #[])
  let o ← IO.Process.output { cmd := "python3", args := #["scripts/pinned-lib.py", "verdict"] ++ extra }
  if o.exitCode != 0 then throw (IO.userError s!"closure gate: scripts/pinned-lib.py verdict failed: {o.stderr}")
  let mut m : Std.HashMap String Pin := {}
  for l in o.stdout.splitOn "\n" do
    match l.splitOn " " with
    | r :: st :: dir :: rest => if !l.startsWith "pin " then m := m.insert r { root := r, status := st, dir, why := " ".intercalate rest }
    | _ => pure ()
  return m

/-- Is every loaded module of the pin's root an olean under the locked checkout's own build directory? (`none` = yes, else the first offender) -/
def pinOleans (env : Environment) (p : Pin) : IO (Option String) := do
  let base := (← IO.FS.realPath p.dir).toString ++ "/.lake/build/"
  for mn in env.header.moduleNames do
    if mn.getRoot.toString == p.root then
      let f ← (findOLean mn)
      let rp := (← IO.FS.realPath f).toString
      if !rp.startsWith base then return some s!"{mn} is {rp}, not built from {p.dir}"
  return none

/-- The class of an "other"-root definition: SPEC only for a verified pin (`ok` and its oleans from the locked checkout), else UNVERIFIED. Pure: the self-tests judge it. -/
def pinClass (pins : Std.HashMap String Pin) (bad : Std.HashMap String String) (root : String) : String :=
  match pins.get? root with
  | some p => if p.status == "ok" && !bad.contains root then "spec" else "UNVERIFIED"
  | none => "UNVERIFIED"

def rootOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with | some i => (env.header.moduleNames[i.toNat]!).getRoot | none => .anonymous

/-- What the walk measured: independent of any baseline, so one measurement serves the run and every self-test. -/
structure Measure where
  entries : Nat
  counts : Std.HashMap String Nat
  mass : Std.HashMap String Nat
  perModule : Std.HashMap String Nat
  perModuleMass : Std.HashMap String Nat
  uncovered : Array Name
  forbidden : Array Name
  /-- the reached mass of the verified pinned libraries (counted in `spec`; ratcheted as `dep_mass`) -/
  pinnedMass : Nat := 0
  /-- the carve-outs reached, with their node mass -/
  carved : Array (Name × Nat) := #[]
  /-- per pinned library: (root, status, why, reached mass, class) -/
  pinned : Array (String × String × String × Nat × String) := #[]

/-- Entry points: `--entry N` (repeatable via the file) or `scripts/closure-entries.txt`. An entry that is not in the environment is an error:
a typo must not measure nothing and pass. -/
def measureClosure (env : Environment) (args : List String) : IO Measure := do
  let arg := argOf args
  let entryNames ← readLines (arg "--entries-file" "scripts/closure-entries.txt")
  let entries := (entryNames ++ (if args.contains "--entry" then [arg "--entry" ""] else [])).map String.toName
  for e in entries do
    if (env.find? e).isNone then throw (IO.userError s!"closure gate: entry point {e} is not in the environment")
  let carveNames : List Name := (← readLines (arg "--carveouts-file" "scripts/carveouts.txt")).filterMap fun l => (l.splitOn "|").head?.map (fun x => x.trimAscii.toString.toName)
  let reach := walk env entries {}
  -- Which constants do the statements of LeanSseProofs theorems mention? A spec definition that no theorem mentions is "spec" in name only.
  let mut mentioned : NameSet := {}
  for (n, ci) in env.constants.map₁.toList do
    if let some idx := env.getModuleIdxFor? n then
      if (env.header.moduleNames[idx.toNat]!).getRoot == `LeanSseProofs then
        if let .thmInfo _ := ci then
          for u in ci.type.getUsedConstants do mentioned := mentioned.insert u
  let pins ← pinVerdicts args
  let mut pinBad : Std.HashMap String String := {}
  for (r, p) in pins.toList do
    if p.status == "ok" then if let some w ← pinOleans env p then pinBad := pinBad.insert r w
  let mut pinMass : Std.HashMap String Nat := {}
  let mut uncovered : Array Name := #[]
  let mut forbidden : Array Name := #[]
  let mut mass : Std.HashMap String Nat := {}
  let mut counts : Std.HashMap String Nat := {}
  let mut carved : Array (Name × Nat) := #[]
  let mut perModule : Std.HashMap String Nat := {}
  let mut perModuleMass : Std.HashMap String Nat := {}
  for n in reach.toList do
    if isAux env n then continue
    let some ci := env.find? n | continue
    if !(match ci with | .defnInfo _ | .opaqueInfo _ => true | _ => false) then continue
    let c := classify env n
    let c0 := if c == "local" then "UNVERIFIED" else if c == "other" then pinClass pins pinBad (rootOf env n).toString else c
    let cls := if (c0 == "spec" || c0 == "UNVERIFIED") && isExtern env n then (if carveNames.contains n then "carveout" else "boundary") else c0
    counts := counts.insert cls (counts.getD cls 0 + 1)
    let size := (ci.value?.map (·.sizeWithoutSharing)).getD 0
    if c == "other" && cls != "boundary" && cls != "carveout" then pinMass := pinMass.insert (rootOf env n).toString (pinMass.getD (rootOf env n).toString 0 + size)
    mass := mass.insert cls (mass.getD cls 0 + size)
    if cls == "carveout" then carved := carved.push (n, size)
    if cls == "proofs" || cls == "heavy" then forbidden := forbidden.push n
    if cls == "spec" && c == "spec" && !mentioned.contains n then uncovered := uncovered.push n   -- a pinned library's definitions are covered by ITS clauses, not by our theorems
    if args.contains "--emit" && cls != "spec" then
      IO.println s!"emit {cls} {match env.getModuleIdxFor? n with | some i => (if cls == "toolchain" then (env.header.moduleNames[i.toNat]!).getRoot else env.header.moduleNames[i.toNat]!).toString | none => "?"} {n}"
    if cls == "UNVERIFIED" then
      let m := match env.getModuleIdxFor? n with | some i => (env.header.moduleNames[i.toNat]!).toString | none => "?"
      perModule := perModule.insert m (perModule.getD m 0 + 1)
      perModuleMass := perModuleMass.insert m (perModuleMass.getD m 0 + size)
  let locked : Array (String × String × String × Nat × String) := pins.toArray.qsort (fun a b => a.1 < b.1) |>.map fun (r, p) =>
    let st := if p.status == "ok" && pinBad.contains r then "bad" else p.status
    (r, st, (pinBad.get? r).getD p.why, pinMass.getD r 0, pinClass pins pinBad r)
  let unlocked : Array (String × String × String × Nat × String) := (pinMass.toArray.filter fun (r, _) => !pins.contains r).qsort (fun a b => a.1 < b.1) |>.map fun (r, ms) =>
    (r, "unlocked", "its root is not a line of scripts/pinned-libs.lock", ms, "UNVERIFIED")
  let pinned := locked ++ unlocked
  let pinnedMass := pinned.foldl (fun a (_, _, _, ms, cl) => if cl == "spec" then a + ms else a) 0
  return { entries := entries.length, counts, mass, perModule, perModuleMass, uncovered, forbidden, pinnedMass, pinned, carved }

/-- The report and the ratchet checks of one run against one baseline file (stdout/stderr and the exit code). -/
def report (m : Measure) (args : List String) (baseFile : String) : IO UInt32 := do
  let { entries, counts, mass, perModule, perModuleMass, uncovered, forbidden, pinnedMass, pinned, carved } := m
  let base ← readLines baseFile
  if entries == 0 then IO.println "closure gate: no entry points yet (scripts/closure-entries.txt is empty: the exports arrive with the ABI); measured nothing"
  IO.println "closure gate: definitions reachable from the entry points, by class"
  for c in ["spec", "boundary", "carveout", "toolchain", "UNVERIFIED"] do
    IO.println s!"  {c}: {counts.getD c 0}"
  let mods := perModule.toList.toArray.qsort (fun a b => a.2 > b.2 || (a.2 == b.2 && a.1 < b.1))
  IO.println "code mass (expression nodes; a count of definitions can be moved by merging or splitting, mass cannot):"
  for c in ["spec", "boundary", "carveout", "toolchain", "UNVERIFIED"] do
    IO.println s!"  {c}: {mass.getD c 0}"
  let (sm, em) := shareOf mass
  let floor? := shareFloor base
  IO.println "closure gate: DEFINITIONS: executed mass = expression nodes of every definition reachable from the entry points, classes spec+boundary+UNVERIFIED (toolchain and the C runtime excluded); specified share = spec mass / executed mass"
  for (r, st, why, pm, cl) in pinned do
    IO.println s!"closure gate: pinned library {r}: {st}{if st == "ok" then " (rev and spec_hash match scripts/pinned-libs.lock)" else if st == "absent" then " (in the lock, not adopted)" else s!" ({why})"}; reached mass {pm}, counted as {if pm == 0 then "nothing" else cl}{if pm > 0 && cl != "spec" then " (unverified glue: the ratchets fail)" else ""}"
  IO.println s!"closure gate: carve-outs: {mass.getD "carveout" 0} nodes ({", ".intercalate (carved.toList.map fun (n, _) => n.toString)}); outside the share, ratcheted by carveout_mass"
  IO.println s!"closure gate: spec {sm} | boundary {mass.getD "boundary" 0} | unverified {mass.getD "UNVERIFIED" 0} | total {em} | deciding: n/a (the deciding-code detector is not yet ported) | specified share {pct sm em} (floor {match floor? with | some (s0, t0) => pct s0 t0 | none => "none"})"
  IO.println s!"  (of the spec mass, {pinnedMass} is a verified pinned library's, the rest is LeanSse's)"
  IO.println s!"  specified share = spec mass {sm} / executed mass {em} (spec+boundary+UNVERIFIED; the toolchain's {mass.getD "toolchain" 0} is outside it). Not counted at all: the C runtime (runtime/runtime.c) and the bindings."
  IO.println s!"spec definitions reachable from the entry points that no LeanSseProofs theorem statement mentions: {uncovered.size} of {counts.getD "spec" 0} (spec in name only until a theorem constrains them)"
  for n in uncovered.toList.take 8 do IO.println s!"    {n}"
  IO.println "unverified by module:"
  for (m, k) in mods do IO.println s!"  {m} {k}  (mass {perModuleMass.getD m 0})"
  let baseMap : Std.HashMap String Nat := base.foldl (init := {}) fun acc l =>
    match l.splitOn " " with | [m, k] => acc.insert m (k.toNat!) | _ => acc
  let mut bad := 0
  -- the library's closure is Init only and never reaches the proofs
  for n in forbidden.toList.take 8 do IO.eprintln s!"closure gate: {n} is reachable from an entry point but comes from LeanSseProofs, Std or Lean (only Init and LeanSse may be linked)"
  if !forbidden.isEmpty then bad := bad + 1
  for (m, k) in mods do
    match baseMap.get? m with
    | none => IO.eprintln s!"closure gate: {m} is new unverified code ({k} definitions); the unverified set may only shrink"; bad := bad + 1
    | some b => if k > b then IO.eprintln s!"closure gate: {m} grew from {b} to {k} unverified definitions"; bad := bad + 1
  -- the specified share ratchet: exact comparison, a fall fails; no floor = no ratchet = fail; a stale (low) floor is a notice
  match floor? with
  | none => IO.eprintln s!"closure gate: {baseFile} has no specified_share floor (a ratchet with no floor is no ratchet: run --write once)"; bad := bad + 1
  | some (s0, t0) =>
    if sm * t0 < s0 * em then IO.eprintln s!"closure gate: specified share fell from {pct s0 t0} ({s0}/{t0}) to {pct sm em} ({sm}/{em}); it may only rise (no relabel can raise it: only spec mass can)"; bad := bad + 1
    else if sm * t0 > s0 * em then IO.println s!"closure gate: the share floor {pct s0 t0} is below the measured {pct sm em}: run --write"
  match baseMap.get? "mass" with
  | some b => if mass.getD "UNVERIFIED" 0 > b then IO.eprintln s!"closure gate: unverified code mass grew from {b} to {mass.getD "UNVERIFIED" 0} expression nodes"; bad := bad + 1
  | none => IO.eprintln s!"closure gate: {baseFile} has no unverified mass line"; bad := bad + 1
  match baseMap.get? "dep_mass" with
  | some b => if pinnedMass > b then IO.eprintln s!"closure gate: the pinned libraries' reached mass grew from {b} to {pinnedMass} expression nodes (a new pin, or more of it reached, is a reviewed edit of the baseline)"; bad := bad + 1
  | none => IO.eprintln s!"closure gate: {baseFile} has no dep_mass line"; bad := bad + 1
  match baseMap.get? "carveout_mass" with
  | some b => if mass.getD "carveout" 0 > b then IO.eprintln s!"closure gate: the carve-outs grew from {b} to {mass.getD "carveout" 0} expression nodes (a carve-out may be neither added nor widened without approval)"; bad := bad + 1
  | none => if mass.getD "carveout" 0 > 0 then IO.eprintln s!"closure gate: {baseFile} has no carveout_mass line"; bad := bad + 1
  if args.contains "--write" then
    if bad != 0 then IO.eprintln "closure gate: --write refuses to write a baseline that fails the ratchets (a worsening is a deliberate, owner-approved edit of the file)"; return 1
    IO.FS.writeFile baseFile ("# unverified definitions reachable from the entry points, per module (scripts/ClosureGate.lean); may only fall\n" ++ String.intercalate "\n" (mods.toList.map fun (m, k) => s!"{m} {k}") ++ s!"{if mods.isEmpty then "" else "\n"}mass {mass.getD "UNVERIFIED" 0}\ndep_mass {pinnedMass}\ncarveout_mass {mass.getD "carveout" 0}\nspecified_share {sm} {em}\n")
    IO.println "closure gate: baseline written"
    return 0
  if bad == 0 then
    let total := mods.foldl (fun a (_, k) => a + k) 0
    IO.println s!"closure gate: ok ({total} unverified definitions; the baseline may be lowered by running with --write)"
  return if bad == 0 then 0 else 1

/-- The negative self-tests, on synthetic measures and baselines (never the committed baseline: the skeleton's closure is empty, and a self-test that
depends on the measured value would be vacuous), plus the classifier and the walk on the real environment, all in this one process. -/
def selfTests : IO UInt32 := do
  -- an environment that also has `Lean` loaded (the library's own closure never does), so the heavy-class detector can be shown to fire
  let env ← importModules #[{ module := `Lean }, { module := `LeanSse }, { module := `LeanSseProofs }] {}
  let (h, cb) ← IO.FS.createTempFile
  h.flush
  let cbs := cb.toString
  let mut bad := 0
  let mk (spec boundary unv : Nat) (mods : List (String × Nat)) (forb : Array Name := #[]) : Measure :=
    { entries := 1, counts := {}, perModule := Std.HashMap.ofList mods, perModuleMass := {}, uncovered := #[], forbidden := forb
      mass := Std.HashMap.ofList [("spec", spec), ("boundary", boundary), ("UNVERIFIED", unv), ("toolchain", 50), ("carveout", 36)], pinnedMass := 30 }
  let m := mk 100 10 5 [("Abi.Shim", 2)]
  let (sm, em) := shareOf m.mass
  let base (share : List String) (mass : Nat := 5) (mods : List String := ["Abi.Shim 2"]) (dep : List String := ["dep_mass 30"]) (carve : List String := ["carveout_mass 36"]) : IO Unit :=
    IO.FS.writeFile cb ("\n".intercalate (mods ++ [s!"mass {mass}"] ++ dep ++ carve ++ share) ++ "\n")
  let run (mm : Measure) (extra : List String := []) : IO (UInt32 × String) := do
    let (out, r) ← IO.FS.withIsolatedStreams (report mm (["--baseline", cbs] ++ extra) cbs)
    return (r, out)
  let has (out s : String) : Bool := (out.splitOn s).length > 1
  let mut expect : List (Bool × String) := []
  -- the gate can fail: against a missing baseline a module of unverified code is new, and there is no floor
  let (_, r) ← IO.FS.withIsolatedStreams (report m [] "/nonexistent")
  expect := expect ++ [(r != 0, "the closure gate cannot fail")]
  -- the ratchets on unverified code: a new module, a module that grew, a mass that grew
  base [s!"specified_share {sm} {em}"] (mods := []); let (r, _) ← run m
  expect := expect ++ [(r != 0, "the closure gate accepts new unverified code")]
  base [s!"specified_share {sm} {em}"] (mods := ["Abi.Shim 1"]); let (r, _) ← run m
  expect := expect ++ [(r != 0, "the closure gate accepts a module whose unverified definitions grew")]
  base [s!"specified_share {sm} {em}"] (mass := 4); let (r, _) ← run m
  expect := expect ++ [(r != 0, "the closure gate accepts a grown unverified mass")]
  base [s!"specified_share {sm} {em}"]; let (r, o) ← run m
  expect := expect ++ [(r == 0 && has o s!"specified share {pct sm em} (floor {pct sm em})", "the closure gate fails or does not print the share at its own floor")]
  expect := expect ++ [(has o s!"spec {sm} | boundary 10 | unverified 5 | total {em} | deciding: n/a", "the closure gate prints a bare percentage (the parts are required)")]
  -- the pinned libraries' reached mass is ratcheted (a grown mass fails; a baseline with no dep_mass line fails)
  base [s!"specified_share {sm} {em}"] (dep := ["dep_mass 29"]); let (r, o) ← run m
  expect := expect ++ [(r != 0 && has o "pinned libraries' reached mass grew", "the closure gate accepts a grown pinned-library mass")]
  base [s!"specified_share {sm} {em}"] (dep := []); let (r, _) ← run m
  expect := expect ++ [(r != 0, "the closure gate accepts a baseline with no dep_mass line")]
  -- the carve-outs: their mass is ratcheted (a grown mass fails; a baseline with no carveout_mass line fails while any carve-out is reached) and it is OUTSIDE the executed mass (the share's denominator)
  base [s!"specified_share {sm} {em}"] (carve := ["carveout_mass 35"]); let (r, o) ← run m
  expect := expect ++ [(r != 0 && has o "the carve-outs grew", "the closure gate accepts widened carve-outs")]
  base [s!"specified_share {sm} {em}"] (carve := []); let (r, _) ← run m
  expect := expect ++ [(r != 0, "the closure gate accepts carve-outs with no carveout_mass baseline line")]
  expect := expect ++ [(execMass m.mass == 115, "the carve-outs' mass leaked into the executed mass (the share's denominator)")]
  -- the specified share: a fall fails (a real fall of the spec mass, and a floor above the measure), a missing floor fails
  let (r, _) ← run (mk 99 10 5 [("Abi.Shim", 2)])
  expect := expect ++ [(r != 0, "the specified-share ratchet cannot fail on a synthetic fall of the spec mass")]
  base [s!"specified_share {sm + 1} {em}"]; let (r, o) ← run m
  expect := expect ++ [(r != 0 && has o "specified share fell", "the specified-share ratchet accepts a floor above the measured share")]
  base []; let (r, _) ← run m
  expect := expect ++ [(r != 0, "the closure gate accepts a baseline with no specified_share floor")]
  -- a floor of 0/0 (the skeleton's) accepts any share, and an empty closure prints n/a, not a division by zero
  base ["specified_share 0 0"]; let (r, _) ← run (mk 0 0 0 []); let (r', _) ← run m
  expect := expect ++ [(r == 0 && r' == 0, "the closure gate rejects the 0/0 floor of an empty closure or a share above it")]
  -- --write refuses to lower the floor (and writes nothing); on a rise it raises the floor to the measure
  base [s!"specified_share {sm + 1} {em}"]; let before ← IO.FS.readFile cb; let (r, _) ← run m ["--write"]
  expect := expect ++ [(r != 0 && (← IO.FS.readFile cb) == before, "the closure gate --write lowers the specified-share floor")]
  base [s!"specified_share {sm - 1} {em}"]; let (r, _) ← run m ["--write"]
  expect := expect ++ [(r == 0 && ((← IO.FS.readFile cb).splitOn s!"specified_share {sm} {em}").length > 1, "the closure gate --write does not raise the floor on an improvement")]
  -- a relabel cannot raise the share: moving all unverified mass to boundary (mass level) leaves spec and executed mass unchanged
  let relabeled := { m with mass := (m.mass.insert "UNVERIFIED" 0).insert "boundary" (m.mass.getD "boundary" 0 + m.mass.getD "UNVERIFIED" 0) }
  expect := expect ++ [(shareOf relabeled.mass == (sm, em) && relabeled.mass.getD "boundary" 0 == 15, "relabeling UNVERIFIED->boundary changed the specified share (or moved no mass)")]
  -- a reachable definition from LeanSseProofs, Std or Lean fails the gate
  base [s!"specified_share {sm} {em}"]; let (r, _) ← run (mk 100 10 5 [("Abi.Shim", 2)] #[`Lean.Json.compress])
  expect := expect ++ [(r != 0, "the closure gate accepts a reachable Std/Lean/LeanSseProofs definition")]
  IO.FS.removeFile cb
  -- the classifier, by module root
  for (mod, c) in [(`LeanSse.Value, "spec"), (`LeanSseProofs.Ledger, "proofs"), (`Init.Prelude, "toolchain"), (`Lean.Data.Json, "heavy"), (`Std.Data.HashMap, "heavy"), (`VbmSimd.Find, "other"), (`VbmSimdProofs.Find, "proofs"), (`Abi.Shim, "other")] do
    expect := expect ++ [(classifyModule mod == c, s!"classifyModule {mod} is not {c}")]
  -- pinned libraries: a root counts as spec ONLY for a lock line whose verdict is ok and whose oleans are the checkout's; a mismatch, an absent checkout and a library the lock does not name are UNVERIFIED
  let pin (st : String) : Pin := { root := "LibX", status := st, dir := "/x", why := "" }
  let pins : Std.HashMap String Pin := ({} : Std.HashMap String Pin).insert "LibX" (pin "ok") |>.insert "LibY" (pin "bad") |>.insert "LibZ" (pin "absent")
  expect := expect ++ [(pinClass pins {} "LibX" == "spec", "a verified pinned library is not counted as specified"),
                       (pinClass pins (({} : Std.HashMap String String).insert "LibX" "olean elsewhere") "LibX" == "UNVERIFIED", "a pinned library whose olean is not the locked checkout's counts as specified (a fork under the pinned name)"),
                       (pinClass pins {} "LibY" == "UNVERIFIED", "a pinned library whose rev or spec_hash does not match counts as specified"),
                       (pinClass pins {} "LibZ" == "UNVERIFIED", "an absent pinned library counts as specified"),
                       (pinClass pins {} "NotInTheLock" == "UNVERIFIED", "a library that is not in the lock counts as specified")]
  -- the olean check of a verified pin: every module of the root must be built under the locked checkout's own build directory (here the root `LeanSse` and this very tree: yes; the same root claimed by another directory: a fork)
  let here ← pinOleans env { root := "LeanSse", status := "ok", dir := ".", why := "" }
  let elsewhere ← pinOleans env { root := "LeanSse", status := "ok", dir := "/", why := "" }
  expect := expect ++ [(here.isNone, "pinOleans refuses the oleans that ARE under the locked checkout's build directory"),
                       (elsewhere.isSome, "pinOleans accepts oleans that are NOT under the locked checkout's build directory (a fork under the pinned name)")]
  -- the walk on the real environment: a toolchain function is measured (and is not heavy), a Lean.Json function IS heavy, a proof-library function is "proofs",
  -- an entry point that does not exist is an error (so the empty closure of the skeleton cannot hide a typo)
  let mT ← measureClosure env ["--entry", "List.map", "--entries-file", "/nonexistent"]
  expect := expect ++ [(mT.mass.getD "toolchain" 0 > 0 && mT.forbidden.isEmpty, "the walk measures no toolchain mass for List.map (vacuous), or calls it forbidden")]
  let mH ← measureClosure env ["--entry", "Lean.Json.compress", "--entries-file", "/nonexistent"]
  expect := expect ++ [(!mH.forbidden.isEmpty, "the walk does not find Lean.Json reachable from Lean.Json.compress")]
  let mP ← measureClosure env ["--entry", "ledger", "--entries-file", "/nonexistent"]
  expect := expect ++ [(!mP.forbidden.isEmpty, "the walk does not find LeanSseProofs reachable from the ledger")]
  let typo ← (measureClosure env ["--entry", "No.Such.Entry", "--entries-file", "/nonexistent"]).toBaseIO
  expect := expect ++ [(match typo with | .error _ => true | .ok _ => false, "an entry point that is not in the environment is accepted")]
  for (ok, msg) in expect do
    unless ok do IO.eprintln s!"tier1: {msg}"; bad := bad + 1
  if bad == 0 then IO.println s!"closure gate: {expect.length} negative self-tests ok (one process)"
  return if bad == 0 then 0 else 1

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  -- `--entry N` adds an entry point, `--baseline F` selects the ratchet file, `--selftest` also runs the negative self-tests, `--emit` prints machine lines for the trust-ledger check
  let arg := argOf args
  let env ← importModules #[{ module := `LeanSse }, { module := `LeanSseProofs }] {}
  let m ← measureClosure env args
  let r ← report m args (arg "--baseline" "scripts/closure-baseline.txt")
  if r != 0 || !args.contains "--selftest" then return r
  selfTests
