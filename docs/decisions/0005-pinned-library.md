# 0005 Pinned library: outside code counts as specified only on a hash match

Status: slice 1 (the gate class) and its first use (the line-end search of vbm-simd). Follows 0001 (the closure gate), 0002 (land direct). Same class as the pinned-library gate of the sibling libraries (vbm-llm and the project the gates were first built in): the lock format,
`scripts/pinned-lib.py` and its attacks 13a to 13j are copied from them, with the roots renamed; the closure gate's class is ported from the first one.

## The ruling
A library outside this repository that the machine executes is a **pinned-library class**: its reached code counts as specified only while its rev and its spec_hash match a protected lock. A library in no class counts for nothing; it must not be free.
Before this the closure gate sorted by module root and put every root that was neither `LeanSse` nor `Init` under UNVERIFIED (and `Std`/`Lean` under FORBIDDEN), so a library would have been unverified glue. Now such a root is **other**: spec when it is
a lock line whose verdict is ok and whose modules were built from the locked checkout, else UNVERIFIED. Its `@[extern]` shims are boundary mass (the trusted C), counted in the denominator and not in the numerator.

## The lock and what a match is
`scripts/pinned-libs.lock` (protected; one line `NAME REV SPEC_HASH ROOT SPEC_PATHS`). `scripts/pinned-lib.py` defines and checks it: **ok** = the lake manifest's `rev` is the lock's, the checkout `.lake/packages/NAME` is its own git checkout whose HEAD is that
rev, and the spec_hash of its working tree equals the lock's. The paths hashed for vbm-simd: its code (`VbmSimd/`, `VbmSimd.lean`), its trusted C (`include/`), its clause list and trust ledger (`docs/SPEC.md`, `docs/trust-ledger.md`), its lakefile, manifest and toolchain.
`fetch` clones a missing checkout at the LOCK's rev before the check (a cold runner, a scratch tree): the network is used only for the pinned source, then `verify` trusts nothing. Tier 1 runs fetch, verify and protected; `scripts/test_pinned_lib.sh` and the 13* attacks show each can fail.

## The ratchet
`dep_mass` of `scripts/closure-baseline.txt`: the reached mass of the verified pinned libraries (counted in the spec mass). It may only fall: a new pin, or more of the library reached, is a reviewed edit. The closure gate prints it apart on the `pinned library` line.

## Limits (said, not hidden)
Lake itself fetches and builds the checkout; the hash covers the sources, not the built oleans, so the olean check and the fresh CI build bind them. The proofs of the library are not re-checked here: `leanchecker` and nanoda recheck them in its own Tier 2. A deliberate bump is one
reviewed change: pin from a real checkout (`pinned-lib.py hash`), then the lock, the lakefile and the manifest. A sandbox with no network (the scorecard) must be given the pinned source before the network is cut, verified by the same lock (a separate proposal).
