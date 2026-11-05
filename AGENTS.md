## Landing (direct to main, no PRs)
- Work in a worktree off a fresh origin/main. Diff ≤150 production lines, ≤45 min without a passing build; over either, stop and write a decomposition plan.
- Commit locally with Conventional Commits. Land only with `scripts/land-direct`; never push main yourself, never force-push it, never open a PR.
- New behaviour lands behind a flag that defaults OFF. Interface changes: add beside the old, migrate callers, delete at zero references.
- Main is RED when the Tier 1 job of its latest push failed. While red or frozen, only a fix or revert lands. Never hotfix on main: pull the revert, reproduce in a new worktree, resubmit.
- `scripts/land/` and `scripts/land-direct` are a pinned copy of vbm-land: never edit them (`scripts/land/bin/land-check` fails the gate). Change the tool upstream, then `scripts/land/bin/land-update <tag>`.
- Decide anything reversible and log it. Escalate only money, data loss, secrets, publishing, or harm to a third party; say so in one line and stop.

# AGENTS.md: vbm-sse

A **verified Server-Sent Events reader written once in Lean**: the event-stream algorithm of the HTML Standard (9.2.5 and 9.2.6), as a whole-buffer reference and an incremental machine, with the proof that the events of a stream do not depend on how it is cut into chunks. C, WebAssembly and generated bindings follow (roadmap, the same pattern as vbm-json). Agent-built, no human code review. Public-ready from the first commit; the repository is private until the owner flips it. The standard is VBM (verified bare metal); the libraries are `vbm-<name>`; the Lean namespace is `LeanSse`, the ABI prefix will be `vbm_sse_`. `README.md` is the public face (for humans, kept short); `CONTRIBUTING.md` explains landing to outsiders; the design and the named policies are `docs/spec.md` and `docs/decisions/0001-vbm-sse.md` (read first).

## Status
Landed: the specification (`LeanSse/Spec.lean`: the algorithm over `List UInt8`), the incremental machine (`LeanSse/Stream.lean`), the proofs (`LeanSseProofs/`: the machine equals the reference, chunk invariance, the clauses, the standard's examples), the obligation ledger tagged with the clauses of the standard, and every Tier 1 gate. The vectors (`vbm-sse-vectors-1`, `lake exe vbm-sse-vectors`, rows from the reference, pinned by size and sha256) have landed. Next, in this order: the C interface and the freestanding runtime, the WebAssembly build, the bindings. `git log` says what has landed. Toolchain: Lean 4.35.0, pinned in `mise.toml` and `lean-toolchain` (no elan). Run everything as `mise exec -- ...`; the gate is `mise exec -- scripts/tier1.sh`.

## Hard rules
- **Forbidden anywhere in Lean:** `sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`, `csimp` (Tier 1 scans for them; a comment may mention one only on a line marked `tier1-allow`). A proof is hard? Decompose it; never weaken the statement.
- **Spec first.** Behaviour lands as a specification and its proofs before any optimised code; a fast machine exists only with its refinement proof to the reference. Vectors come from the reference, never from the fast code.
- **No unproved claim called verified.** Only `proved` in the obligation ledger (`LeanSseProofs/Ledger.lean`, rendered to `docs/proof-ledger.md`) may be called verified. Every claim carries a clause tag of the standard (`docs/spec-clauses.txt`); the gate refuses a claim with none.
- **The specified share may not fall** (`scripts/ClosureGate.lean`, printed on every Tier 1 run), the unverified set may only shrink, and nothing from `Std`, `Lean` or `LeanSseProofs` may be reachable from an export.
- **The boundary never decides.** C, loaders and bindings move bytes; what an event is, is decided in Lean only.
- **Every gate has a negative self-test** (it must be shown able to fail, in the same run). A new gate without one does not land.
- **Public-ready, always:** no internal project, host or person name, no machine path, no secret, in any file or commit message (the scrub gate, `scripts/scrub.py`, checks the tree; its banned list is hashes). No paid model calls from a test or a gate.
- **Land with `scripts/land-direct`, never open a PR, never push a branch.** One lander at a time. The protected set (`scripts/protected-paths.txt`) is what the owner reads on `main`: the spec, the ledger, the gates and baselines, the pins, the workflows, the governance files. Do not edit one to make a check pass.
- Conventional Commits `type(scope): summary`. Heavy builds on a shared machine run under a memory cap, one at a time.

## Library rules
- **The standard is pinned** (`docs/spec-pin.txt`: url, date, sha256 of the fetched page). The reference is written from sections 9.2.5 and 9.2.6; a change of the standard is a reviewed change of the reference. The standard's own examples are theorems (`LeanSseProofs/Examples.lean`).
- **Bytes, not text.** The algorithm looks only at ASCII bytes (CR, LF, colon, space, NUL, digits, field-name letters), so values stay byte strings; the UTF-8 decode of a value is a separate step (`LeanSse.Utf8`, open in the ledger). A byte order mark is stripped once at the very start.
- **Named policies** (`docs/spec.md`): `retry` needs at least one digit; the unterminated end of a stream is discarded; no bound on a line or the data buffer yet (open claim `bounded-state`).
- **Module roots:** `LeanSse` imports `Init` and other `LeanSse` modules only (Tier 1 scans the imports); `LeanSseProofs` may import `Std` and `Lean` and is never linked.
- **Chunk invariance is the pilot's result:** the pattern (one byte-step machine, a whole-buffer reference by a different recursion, a generalised invariant by induction on the chunk) is what vbm-http1, JSON-RPC over stdio and the stream decoder of vbm-llm reuse. Keep the statement `chunk_invariance` exactly as it is.
- **The trust ledger** (`docs/trust-ledger.md`) lists everything outside our control; a new boundary (extern, C file, loader, workflow, tool) with no entry fails Tier 1.
- **Pinned libraries:** none today (the machine needs no JSON). A consumer pins this library by the pinned-library gate; vbm-json is a pinned lake dependency only where JSON is needed, never in `LeanSse`.

## Gates (Tier 1 before landing; Tier 2 after merge)
- **Tier 1** (`scripts/tier1.sh`): forbidden-constructs scan, `Init`-only import scan, pipefail and proof-evaluation lints, zero-warning build of both libraries (the mechanism is checked), axiom gate, obligation ledger (with the clause tags), closure gate and specified share, trust ledger, scrub gate, workflow lint, the drift check of the pinned lander, and the offline self-tests of the protected set, `scripts/land-direct`, the commit-on-main hook, the parallel test runner, the gate-diff judge and the relabel-attack suite.
- **Tier 2** (`scripts/tier2.sh`, CI on main after merge): Tier 1 again, the whole relabel-attack suite, `leanchecker --fresh`, nanoda over the exported proof. A failure on main means revert, then fix in a worktree.

## Layout
`LeanSse/` spec and code (`Init` only; locked) · `LeanSseProofs/` proofs (never linked) · `scripts/` gates and process · `scripts/land/` the pinned lander (never edit) · `docs/` spec, decisions, trust ledger, proof ledger (generated), clause index, standard pin · `vectors/` the generator's `Main`; to come: `abi/`, `runtime/`, `include/`, `bindings/`.
