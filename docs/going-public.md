# Before going public

Do these in order; each is a checkable fact. The owner decides; publishing cannot be recalled (history and forks).

## The checklist

1. **Scans.** The scrub gate passes (Tier 1). The history scans are clean: gitleaks (`gitleaks detect --source . --log-opts=--all`), trufflehog (`trufflehog git file://$PWD --no-verification --fail`), and the scrub gate's own checks (hashed internal names, machine paths, secret shapes) over every blob and commit message of every commit. Commit metadata carries the author's name and e-mail, the same identity as the public `vbm-json`; publish the existing history, or a squashed one if the owner prefers, and scan what is published.
2. **README, licence, notice.** `README.md` says what the library is, what is proved and what is not, its speed (see `docs/bench.md`) and how to build it; `LICENSE` (Apache-2.0) and `NOTICE` list what is third-party (decision `docs/decisions/0003-licence-and-notice.md`).
3. **Container proof.** In a clean `ubuntu:24.04` container with no credentials and no network after the dependency fetch, clone and run `mise exec -- scripts/tier1.sh`: it passes from nothing (prerequisites in the README).
4. **The runner switch** (below): `runs-on` is a GitHub-hosted label in every workflow (no `self-hosted`), the repository's self-hosted runner is removed (`gh api repos/OWNER/REPO/actions/runners` lists none), `.github/visibility` says `public`, and `LAND_RED_MODE` in `scripts/land.conf` is unchanged (`push`).
5. **Settings.** Every item of `scripts/land/templates/PUBLIC-REPO-SETTINGS.md`, each read back: main protected from deletion and non-fast-forward (no required pull request, no bypass list), release tags protected, fork pull-request workflows need approval for all outside contributors, a read-only workflow token that cannot approve pull requests, private vulnerability reporting, secret scanning with push protection, delete head branches on merge. Then one real landing by `scripts/land-direct` proves landing still works under the ruleset.
6. **The scorecard side** (the scorecard repository, the owner's): add `witt3rd/vbm-sse` to `registry/allowlist.toml` only when the repository is public and an outside submission is wanted; the registry entry `registry/witt3rd__vbm-sse.toml` stays `planned` and unlinked until then, then goes `live` with its repository link; review `registry/scores` for the card of this repository (a card of a private repository is not linked or scored) and re-run the card at the published commit.
7. **The owner's word**, then the visibility change, then an anonymous clone and one hosted push run to green.

## The runner switch, exactly

While private, `.github/workflows/core.yml` runs both jobs on the owner's self-hosted runner (`runs-on: [self-hosted]`); a public repository must not (a pull request from a fork could run code on that machine). The single change that makes the repository publishable is one commit that:

1. replaces `runs-on: [self-hosted]` with `runs-on: ubuntu-latest` in both jobs, and the two trailing comments on those lines and the two `the self-hosted runner has mise` comments with nothing;
2. replaces the contents of `.github/visibility` with `public`;
3. leaves `scripts/land.conf` alone (the red check keeps reading the push run of `core.yml`, now a hosted one).

`core.yml` and `.github/visibility` are gate-defining: that commit lands by `scripts/land-direct` (the relabel-attack suite judges it) and is the owner's to approve. Then deregister the runner (the owner's runner host list; `gh api repos/OWNER/REPO/actions/runners` must list none), read one hosted push run to green (the hosted job installs the pinned Lean by `mise install` and has no cache beyond `actions/cache` on `.lake`; the build is cold on the first run), and only then change the visibility.

## What was checked before this checklist was written

Recorded outside this tree, under the lane's data directory: gitleaks and trufflehog over the full history with zero findings; the scrub checks over every blob and message of the history with zero findings; the grep of the tree and the history for internal host, project and person names, paths and addresses (none); a clean `ubuntu:24.04` container clone running Tier 1 from nothing (image digest and log). The numbers and digests are in the lane's report, not here: a number in a document goes stale.
