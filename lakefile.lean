import Lake
open System Lake DSL

package «vbm-sse» where
  leanOptions := #[⟨`warningAsError, true⟩, ⟨`autoImplicit, false⟩]

/-- The library: specification and code, one Lean core. Imports `Init` only (checked by Tier 1): this is what is compiled to C, to WASM and into
every consumer, so nothing from `Std` or `Lean` may be in its closure (a `Lean.*` import forces full runtime initialisation). -/
@[default_target]
lean_lib LeanSse where
  -- every module under LeanSse/ is built, imported by the umbrella or not: a module cannot hide from the build
  globs := #[.andSubmodules `LeanSse]

/-- The proofs: may import `Std` and `Lean`; NEVER linked (nothing in `LeanSse` may import it, and no executable or export depends on it). -/
lean_lib LeanSseProofs where
  globs := #[.andSubmodules `LeanSseProofs]

/-- The vector generator (`vbm-sse-vectors-1`): rows come from the Lean REFERENCE only (`LeanSse.Vectors`); this executable only writes them. Not part of any export. -/
lean_exe «vbm-sse-vectors» where
  srcDir := "vectors"
  root := `Main
