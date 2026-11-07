import Lake
open System Lake DSL

require «vbm-simd» from git "https://github.com/witt3rd/vbm-simd" @ "7bafe1efb64ce15e6bf338f8c4a45a802f31d1d9"

package «vbm-sse» where
  leanOptions := #[⟨`warningAsError, true⟩, ⟨`autoImplicit, false⟩]

/-- The library: specification and code, one Lean core. Imports `Init` only (checked by Tier 1): this is what is compiled to C, to WASM and into
every consumer, so nothing from `Std` or `Lean` may be in its closure (a `Lean.*` import forces full runtime initialisation). -/
@[default_target]
lean_lib LeanSse where
  -- every module under LeanSse/ is built, imported by the umbrella or not: a module cannot hide from the build
  globs := #[.andSubmodules `LeanSse]
  -- `LeanSse.Fast` calls the search and the CPU test of vbm-simd (trust ledger T13) by their C names: its C is compiled with that package's header, as the package's own modules are
  moreLeancArgs := #["-include", (__dir__ / ".lake" / "packages" / "vbm-simd" / "include" / "vbm_simd.h").toString]

/-- The proofs: may import `Std` and `Lean`; NEVER linked (nothing in `LeanSse` may import it, and no executable or export depends on it). -/
lean_lib LeanSseProofs where
  globs := #[.andSubmodules `LeanSseProofs]

/-- The vector generator (`vbm-sse-vectors-1`): rows come from the Lean REFERENCE only (`LeanSse.Vectors`); this executable only writes them. Not part of any export. -/
lean_exe «vbm-sse-vectors» where
  srcDir := "vectors"
  root := `Main

/-- The throughput bench (`docs/bench.md`): the Lean side, the reference and the array machine in Lean. Not part of any export. -/
lean_exe «vbm-sse-bench» where
  srcDir := "bench"
  root := `Bench
