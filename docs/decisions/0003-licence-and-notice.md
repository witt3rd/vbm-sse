# 0003. Licence and notice

Status: accepted (the repository is built public-ready; the owner publishes).

## Decision

* **Code, proofs, vectors, bindings and documents of this repository: Apache-2.0** (`LICENSE`), the default of the VBM family; copyright "Donald Thompson and the vbm-sse contributors" (`NOTICE`).
* **Nothing third-party is copied.** The HTML Standard's event-stream algorithm (CC BY 4.0; code snippets BSD 3-Clause) is implemented, and short clauses of it are quoted in `docs/` with attribution (`NOTICE`, `docs/spec-pin.txt`). The standard's four examples are theorems here, written out by hand from it. The vendored `vbm-land` lander (`scripts/land/`, Apache-2.0) is unchanged and checked by `scripts/land/bin/land-check`.
* **Measured against, not copied or shipped:** the throughput bench (`docs/bench.md`) compares the library with `eventsource-parser` (npm, MIT) and `eventsource-stream` (crates.io, MIT or Apache-2.0). Their code is not in this repository: the scorecard repository builds them from pinned versions and lock files outside the sandbox. This repository holds only the corpus generator and the drivers it wrote itself.
* **Pinned dependencies:** none (the library needs no JSON; `Init` only). The Lean toolchain (Apache-2.0) is downloaded at build time and is not part of the repository.

## Why

A library meant to be pinned by other projects must say, in one file, what it contains and under what terms. A change that copies a new third-party text or code lands with its `NOTICE` line in the same commit.
