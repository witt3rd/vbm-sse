# Going public: the record

This repository starts private and is made public by its owner. This page records what was checked, what the published history carries, and the order of the flip, so that a reader can see what "public-ready" meant here. Publishing cannot be recalled (history and forks); the owner decides.

## History published as is

The history is **not** re-written or re-rooted: a rewrite would change every commit hash that a consumer's pin records. The following exposure is accepted by publishing it (the same class of decision as the public `vbm-json` and `vbm-land`):

- **The author identity.** The owner's name and e-mail appear as author and committer of 19 of the 20 commits on `main` (the first is a no-reply commit made by GitHub when the project was created). The same identity is already public in the owner's other repositories.
- **Two internal task identifiers.** Two commits carry a `Task` / `Task-ID` trailer naming a work item (a generic slug: no host, no private project).
- **Public keys and fixtures.** The release-signing public key of the vendored `vbm-land` (`scripts/land.signers`), a bot e-mail of its update workflow, and a test identity under the reserved `.invalid` domain.
- Nothing else: no secret, no host name, no address, no local path, no other person's data, no internal project name. There are no tags and one branch (`main`).

## What was checked

| Check | Result |
|---|---|
| gitleaks 8.30.1, every commit of every ref of a fresh mirror of the remote, and the working tree | 0 findings |
| trufflehog 3.99.8, same scope (verified and unverified) | 0 |
| the VBM public-readiness lint (hashed list of private names, path patterns) over the tree | clean after the fixes of the commit "the tree passes the VBM public-readiness lint" (before: a copyright line and three path-shaped strings) |
| the scrub gate of this repository (`scripts/scrub.py`, Tier 1) | clean, with its negative self-tests |
| a scan of every commit message, author line, path and changed line of all refs for the same hashes plus plain patterns (host names, home paths, e-mails, addresses, task trailers) | only the accepted items above |
| Tier 1 in a fresh `ubuntu:24.04` container, network disconnected after the dependency fetch, on the tip and on the flip-day tree | passes |
| Tier 2 in the same container (network up; the one `gh` call of the drift check goes through a `git clone` stand-in, because the token only exists on a hosted run) | passes |

The numbers, the image digest and the logs are in the preparing lane's data directory, not here: a number in a document goes stale.

## The flip, in order

While private, CI runs on the owner's self-hosted runner (hosted runners cannot start for this private repository), and `scripts/lint-workflows.py` allows a `self-hosted` label only while `.github/visibility` says `private`. So the change that returns CI to hosted runners is **prepared, not landed**, as one commit (`flip-day.patch` and its message, kept with the lane's data): in `.github/workflows/core.yml`, `runs-on: ubuntu-latest` in both jobs; the `mise install` step becomes the pinned `jdx/mise-action` (installs mise and the pinned Lean) after one `apt-get install` of `python3-yaml` and `systemd-coredump` (the gate fails, never skips, when PyYAML or `coredumpctl` is missing, and the hosted image is not promised to have them); the Tier 2 step gets the default read-only token as `GH_TOKEN` (a hosted job has no `gh` login, and the online drift check of the pinned lander clones its source with `gh`; no secret); and `.github/visibility` says `public`. `scripts/land.conf` is untouched (`LAND_RED_MODE` stays `push`; the red check keeps reading the push run of `core.yml`, now a hosted one). `core.yml` and `.github/visibility` are gate-defining: the commit lands by `scripts/land-direct` (the relabel-attack suite judges it) and the owner reads it.

1. Before the visibility change: everything that this repository's `main` carries is landed (the preparation commits), the scans above re-run on the tip, and `gh api repos/witt3rd/vbm-sse/actions/runners` still lists the runner (it keeps serving CI until step 5).
2. The owner changes the visibility to public and checks that an anonymous `git clone` works.
3. At once, the settings below (the API refuses the fork-pull-request policy on a private repository, so it can only be set now).
4. Land the flip-day commit with `scripts/land-direct` and read the push CI on a hosted runner: it must be green. This is the one step no rehearsal could prove (hosted runners cannot start while the repository is private; the clean-container run is the stand-in), so if it is red, main is red and only a fix lands: fix forward in the workflow.
5. Deregister the runner: the owner's runner configuration retires it (a patch to that configuration is prepared outside this repository); then `gh api repos/witt3rd/vbm-sse/actions/runners` lists none.
6. The scorecard side (the scorecard repository, the owner's): add `witt3rd/vbm-sse` to `registry/allowlist.toml` only when an outside submission is wanted. The registry entry stays `planned` and unlinked, and the card of this repository a private note, until now; then the entry goes `live` with its repository link and the card is re-run at the published commit. A private repository is never linked or scored in a public registry.
7. Tell the consumers, if any.

While the runner is still registered after the flip, an outside contributor's code cannot reach it: `core.yml` has no `pull_request` trigger (push to `main`, a schedule and a manual dispatch only), and the settings below require approval for fork workflows anyway.

## Settings at the flip (each has a read-back)

Already in place while private (read back on 2026-11-05): `main` protected from deletion and non-fast-forward by the ruleset `protect-main` (no required pull request, no bypass list, so landing still works); `v*` tags protected from deletion and update by `protect-release-tags` (no tag exists yet); the workflow token read-only and unable to approve pull requests; no Actions secret; no deploy key.

To do at the flip, as the repository admin:

1. Fork pull-request workflows need approval for **all outside collaborators**:
   `gh api -X PUT repos/witt3rd/vbm-sse/actions/permissions/fork-pr-contributor-approval -f approval_policy=all_external_contributors`
   Read back: `gh api repos/witt3rd/vbm-sse/actions/permissions/fork-pr-contributor-approval` prints `all_external_contributors`.
2. Read-only workflow token that cannot approve pull requests (re-assert):
   `gh api -X PUT repos/witt3rd/vbm-sse/actions/permissions/workflow -f default_workflow_permissions=read -F can_approve_pull_request_reviews=false`
   Read back: `gh api repos/witt3rd/vbm-sse/actions/permissions/workflow`.
3. Private vulnerability reporting (what `SECURITY.md` points to):
   `gh api -X PUT repos/witt3rd/vbm-sse/private-vulnerability-reporting`
   Read back: `gh api repos/witt3rd/vbm-sse/private-vulnerability-reporting` prints `{"enabled":true}`.
4. Secret scanning and push protection:
   `gh api -X PATCH repos/witt3rd/vbm-sse -F 'security_and_analysis[secret_scanning][status]=enabled' -F 'security_and_analysis[secret_scanning_push_protection][status]=enabled'`
   Read back: `gh api repos/witt3rd/vbm-sse --jq .security_and_analysis`.
5. Delete head branches on merge (the maintainers push none; this keeps contributors' fork flow tidy):
   `gh api -X PATCH repos/witt3rd/vbm-sse -F delete_branch_on_merge=true`
   Read back: `gh api repos/witt3rd/vbm-sse --jq .delete_branch_on_merge`.
6. `main` protection check: `gh api repos/witt3rd/vbm-sse/rules/branches/main --jq '.[].type'` prints `deletion` and `non_fast_forward`; then one real landing by `scripts/land-direct` proves landing still works under the ruleset (the flip-day commit is that landing).
7. Release tags: `gh api repos/witt3rd/vbm-sse/rulesets/26611305 --jq '.rules[].type'` prints `deletion` and `update` (the `v*` ruleset exists; nothing is released yet).
8. No workflow uses `pull_request_target`, every workflow declares read-only `permissions:`, and no secret is used: enforced by `scripts/lint-workflows.py` in Tier 1.
9. Optional: switch off the Projects tab (`-F has_projects=false`); Issues stay on (`SECURITY.md` falls back to an issue that carries no details).
