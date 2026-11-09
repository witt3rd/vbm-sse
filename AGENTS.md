## Landing (direct to main, no PRs)
- Work in a worktree off a fresh origin/main. Diff ≤150 production lines, ≤45 min without a passing build; over either, stop and write a decomposition plan.
- Commit locally with Conventional Commits. Land only with `.land/land-direct`; never push main yourself, never force-push it, never open a PR.
- New behaviour lands behind a flag that defaults OFF. Interface changes: add beside the old, migrate callers, delete at zero references.
- Everything runs before the push, once (Tier 1 on the rebased tree); nothing runs after it. If main is ever red, whoever sees it reverts the offending commit with `git revert` and lands the revert; the author fixes forward in a new worktree. A landing must not add a failure.
- `.land/tool/` and `.land/land-direct` are a pinned copy of vbm-land: never edit them (`.land/tool/bin/land-check` fails the gate). Change the tool upstream, then `.land/tool/bin/land-update <tag>`.
- Decide anything reversible and log it. Escalate only money, data loss, secrets, publishing, or harm to a third party; say so in one line and stop.

## Principles (the VBM + HVTBD family)
- Everything runs before the push, once, on the commit rebased onto main. Nothing runs after the push.
- Proofs, not tests. A test exists only for what Lean does not prove (the C, WebAssembly and bindings boundary), never for the development tooling.
- A failure is a root-cause question, never a reason to add a check, gate, script or document. Nothing is added to the process without deleting something.
- The worker owns its change: when the lander refuses it, the worker fixes it and lands again until it converges.

# AGENTS.md: vbm-sse

A **verified Server-Sent Events reader written once in Lean**: the event-stream algorithm of the HTML Standard (9.2.5 and 9.2.6), as a whole-buffer reference and an incremental machine, with the proof that the events of a stream do not depend on how it is cut into chunks. C, WebAssembly and generated bindings sit around it (the same pattern as vbm-json). Agent-built, no human code review. Public-ready from the first commit; the repository is private until the owner flips it. The standard is VBM (verified bare metal); the libraries are `vbm-<name>`; the Lean namespace is `LeanSse`, the ABI prefix is `vbm_sse_`. `README.md` is the public face (for humans, kept short); `CONTRIBUTING.md` explains landing to outsiders; the design and the named policies are `docs/spec.md` and `docs/decisions/0001-vbm-sse.md` (read first).

## Status
Landed: the specification (`LeanSse/Spec.lean`: the algorithm over `List UInt8`), the incremental machine (`LeanSse/Stream.lean`), the proofs (`LeanSseProofs/`: the machine equals the reference, chunk invariance, the clauses, the standard's examples), the obligation ledger tagged with the clauses of the standard, and every Tier 1 gate. The vectors (`vbm-sse-vectors-1`, `lake exe vbm-sse-vectors`, rows from the reference, pinned by size and sha256) have landed. The array machine (`LeanSse/Fast.lean`, proved equal to the reference: `fast_eq_parse`), the C interface (`abi/`, `include/`, `runtime/`: freestanding, no libc), the WebAssembly module and the generated Python and Rust bindings (`bindings/`) have landed, each run on every vector. The throughput bench (`docs/bench.md`, `bench/`) has landed, and the speed work with its profile harness and a before/after table per change (`docs/perf/`). Next: a JavaScript package. `git log` says what has landed. Toolchain: Lean 4.35.0, pinned in `mise.toml` and `lean-toolchain` (no elan). Run everything as `mise exec -- ...`; the gate is `mise exec -- scripts/tier1.sh`.

## Hard rules
- **Forbidden anywhere in Lean:** `sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`, `csimp` (Tier 1 scans for them; a comment may mention one only on a line marked `tier1-allow`). A proof is hard? Decompose it; never weaken the statement.
- **Spec first.** Behaviour lands as a specification and its proofs before any optimised code; a fast machine exists only with its refinement proof to the reference. Vectors come from the reference, never from the fast code.
- **No unproved claim called verified.** Only `proved` in the obligation ledger (`LeanSseProofs/Ledger.lean`, rendered to `docs/proof-ledger.md`) may be called verified. Every claim carries a clause tag (`docs/spec-clauses.txt`).
- **The specified share is reported on every Tier 1 run** (`scripts/ClosureGate.lean`); the aim is that it only rises and the unverified set only shrinks, and nothing from `Std`, `Lean` or `LeanSseProofs` is reachable from an export.
- **The boundary never decides.** C, loaders and bindings move bytes; what an event is, is decided in Lean only.
- **Public-ready, always:** no internal project, host or person name, no machine path, no secret, in any file or commit message (the scrub gate, `scripts/scrub.py`, checks the tree; its banned list is hashes). No paid model calls from a test or a gate.
- **Land with `.land/land-direct`, never open a PR, never push a branch.** One lander at a time. Do not weaken a check to make it pass.
- Conventional Commits `type(scope): summary`. Heavy builds on a shared machine run under a memory cap, one at a time.

## Library rules
- **The standard is pinned** (`docs/spec-pin.txt`: url, date, sha256 of the fetched page). The reference is written from sections 9.2.5 and 9.2.6; a change of the standard is a reviewed change of the reference. The standard's own examples are theorems (`LeanSseProofs/Examples.lean`).
- **Bytes, not text.** The algorithm looks only at ASCII bytes (CR, LF, colon, space, NUL, digits, field-name letters), so values stay byte strings; the UTF-8 decode of a value is a separate step (to be written as `LeanSse.Utf8`; open in the ledger). A byte order mark is stripped once at the very start.
- **Named policies** (`docs/spec.md`): `retry` needs at least one digit; the unterminated end of a stream is discarded; no bound on a line or the data buffer yet (open claim `bounded-state`).
- **Module roots:** `LeanSse` imports only itself, `Init` and the pinned `VbmSimd` (Tier 1 scans the imports); `LeanSseProofs` also imports `Std`, `Lean` and `VbmSimdProofs`, and is never linked.
- **Chunk invariance is the pilot's result:** the pattern (one byte-step machine, a whole-buffer reference by a different recursion, a generalised invariant by induction on the chunk) is what vbm-http1, JSON-RPC over stdio and the stream decoder of vbm-llm reuse. Keep the statement `chunk_invariance` exactly as it is.
- **The trust ledger** (`docs/trust-ledger.md`) lists everything outside our control; a new boundary (extern, C file, loader, workflow, tool) with no entry fails Tier 1.
- **Pinned libraries:** one today, vbm-simd (the verified byte search for the line end: a lake dependency at a full commit sha, held by the lock `scripts/pinned-libs.lock` and checked by `scripts/pinned-lib.py`; trust ledger T13); the machine needs no JSON. A consumer pins this library by the same pinned-library gate; vbm-json is a pinned lake dependency only where JSON is needed, never in `LeanSse`.

## Gates (Tier 1, before landing; nothing runs after the push)
- **Tier 1** (`scripts/tier1.sh`): the forbidden-constructs scan, the `Init`-only import scan, the pinned library check, a zero-warning build of both libraries, the axiom gate, the trust ledger (a new boundary needs an entry), the scrub gate, and the real tests (vectors, ABI, native, WebAssembly, bindings). The specified share and closure counts are printed, never gated. Nothing else refuses a landing.

## Layout
`LeanSse/` spec and code (`Init` and the pinned `VbmSimd` only) · `LeanSseProofs/` proofs (never linked) · `scripts/` gates and process · `.land/tool/` the pinned lander (never edit) · `docs/` spec, decisions, trust ledger, proof ledger (generated), clause index, standard pin · `vectors/` the generator's `Main` · `bench/` the throughput bench · `abi/` `include/` `runtime/` the C interface and the freestanding runtime · `bindings/` generated bindings · `tests/` the C, WebAssembly and binding tests.
