# 0002 Land direct to main: no pull requests, one coordinator (`scripts/land-direct`)

Status: accepted (the owner's decision).

## Decision
vbm-sse has **no pull requests**. Agents work in worktrees of one clone, so they share one git common dir: that is where the single coordinator lives. A worker commits locally (never pushes a branch), then runs `scripts/land-direct`, which lands the commits on `origin/main` itself. The lander is [vbm-land](https://github.com/witt3rd/vbm-land), vendored and pinned (`scripts/land/`, `scripts/land/PIN`, `scripts/land/MANIFEST.sha256`); it is read-only by contract: `scripts/land/bin/land-check` (Tier 1, and the lander itself on every rebased tree) fails on any difference, a stray file included. To change the tool, change vbm-land and update the pin (`scripts/land/bin/land-update <tag>`, one `chore(land)` commit).

## What it does
Under one `flock` in the git common dir: hold check, red-check (the latest push run of `core.yml`: its `tier1` job failed, or `gh` unreachable: only a fix or a revert lands), fetch, rebase onto `origin/main` in a scratch worktree, a conflict only in `scripts/generated-paths.txt` takes main's file and regenerates it with the gates' own `--write` (`scripts/regen-baselines.sh`: improvements only), **local Tier 1** on that exact combination, fetch again (main moved: rebase and run again, three tries), then a plain push of the commit to `refs/heads/main`, never forced. Each commit lands as itself (linear). The last stdout line is JSON (`sha`, `commits`, `tier1_seconds`, `specified_share`, `result`, `exit`).

## This repository's own rules (`scripts/land.conf`, `scripts/land.d/`)
Base `main`; red = the `tier1` job of `core.yml`; Tier 1 = `mise exec -- scripts/tier1.sh`; size budget: 150 production lines under `LeanSse/` per commit (a `Diff-Budget:` trailer waives it); Conventional subjects. Hooks: `prepare` copies the warm `.lake`; `post-rebase` reports the protected set and runs the gate-diff judge (a baseline may only improve, `tier1.sh` only gains plain steps, the protected list only grows); `post-tier1` runs the relabel-attack suite when a gate-defining file is touched; `json-fields` adds `specified_share`. The judges are taken from `origin/main`, not from the proposed tree: a change cannot weaken the judge that judges it. A gate-defining file needs no pull request: the suite replays every demonstrated way to relabel a gate against the proposed gates and refuses the change if one gets through.

## Consequences
After a landing the worker's branch still holds its pre-rebase commits: start the next task from a fresh worktree off `origin/main`. No GitHub-side review exists; the gates, the hold marker and the red-check are the whole review, and the protected set is reported (not blocked) at landing: the owner reads it on `main`. `main` is protected by a ruleset (no deletion, no non-fast-forward update, no required pull request, no bypass list). Tier 2 stays on `main` after the push.
