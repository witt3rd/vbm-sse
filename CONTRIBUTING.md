# Contributing to vbm-sse

Thanks for looking. Short version: **fork, branch, open a pull request.** A maintainer lands it; you do not need to run the landing tool yourself.

## Why the process looks unusual

The maintainers' own work (mostly done by AI agents in parallel worktrees) lands **directly on `main`, with no pull requests**, through one script that runs the full gate locally first. Outside contributions use ordinary pull requests, and a maintainer carries them through the same gate and lands them (rebasing onto `main`, so history stays linear). Your PR may therefore show up as landed under a different commit hash.

## Before you open a PR

1. Install what the README lists (`mise`, `git`, `python3` with PyYAML, a C compiler, `node`, a recent `cargo`, `coredumpctl`; `VBM_ALLOW_SKIP=1` is the stated way past a missing optional tool).
2. Make your change on a branch of your fork.
3. Run the gate, **Tier 1**, and make sure it passes:

   ```sh
   mise install
   mise exec -- scripts/tier1.sh
   ```

   Tier 1 builds both Lean libraries with zero warnings, scans for forbidden constructs, checks the imports, the pinned library, the axioms, the trust ledger and the tree for secrets and internal names, and runs the real tests (vectors, C interface, WebAssembly, bindings).
4. Use Conventional Commit subjects: `type(scope): summary` (`feat`, `fix`, `docs`, `test`, `perf`, `refactor`, `build`, `ci`, `chore`).
5. Keep the change small and focused; a larger change needs a short plan in the PR description.

## The rules that matter

- **No `sorry`, `admit`, `axiom`, `unsafe`, `implemented_by` or `csimp`** anywhere in the Lean. If a proof is hard, break it into lemmas; never weaken the statement.
- **Spec first.** A behaviour change is a change to the specification (`LeanSse/`) together with its proofs; optimised code exists only with a proof that it agrees with the reference. Vectors come from the reference, never from the fast code.
- **Every claim names the clause of the standard it is about** (`docs/spec-clauses.txt`), and only a `proved` claim in the ledger may be called verified. The proved count and the specified share are reported on every run; they should only go up.
- **The boundary never decides.** C, loaders and bindings move bytes; what an event is, is decided in Lean.
- **A new boundary** (an `extern`, a C file, a loader, a workflow, a tool) needs an entry in `docs/trust-ledger.md`, or Tier 1 fails.
- **Gates and pins:** please do not edit a check, the pins or the workflows to make something pass; a maintainer reviews changes to them.
- **Nothing private in the tree:** the scrub gate (`scripts/scrub.py`) refuses internal names, machine paths and secret-shaped strings. No secrets in the repository; workflows run on GitHub-hosted runners only and never use `pull_request_target`.

## The maintainers' tools, in plain words

You do not need these to contribute; they are described so the repository makes sense.

- **`scripts/land-direct`**: lands the local commits of a worktree on `main`. Under one lock it checks that `main` is not red, rebases the commits onto `origin/main`, runs Tier 1 on exactly that result, and pushes as a plain fast-forward (never forced). The lander itself is a pinned, vendored copy of [vbm-land](https://github.com/witt3rd/vbm-land) (`scripts/land/`, checked by `scripts/land/bin/land-check`: never edit it); this repository's own rules are `scripts/land.conf` and `scripts/land.d/`. Design: `docs/decisions/0002-land-direct.md`.
- **Tier 1 / Tier 2**: Tier 1 is the quick gate described above, run before every landing and again by CI on every push. Tier 2 (`scripts/tier2.sh`) is slow, runs in CI on a schedule and on manual dispatch, and re-checks all proofs with independent kernel checkers; a Tier 2 failure on `main` means revert, then fix.

## Licence

By contributing you agree your contribution is licensed under Apache-2.0 (`LICENSE`).
