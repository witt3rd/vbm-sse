# Security policy

vbm-sse is a **pre-release** library. Nothing is published to a package registry and there are no supported versions yet; report problems against the latest `main`.

## What to report

- A stream whose events differ from what the HTML Standard's event-stream algorithm (section 9.2.5 and 9.2.6, pinned in `docs/spec-pin.txt`) yields, or events that depend on how the stream was cut into chunks.
- A crash, hang, out-of-bounds access, leak or unbounded memory use on any input, in the C interface, the runtime or a binding (when they exist).
- A disagreement between a binding and the Lean reference.
- A hole in the proofs: a way to make the ledger (`docs/proof-ledger.md`) claim more than is proved (a forbidden construct that evades the gates, an axiom, a theorem about code the exports do not run).
- Anything in the CI workflows that would expose a secret or run untrusted code with privileges.

The unverified parts, and what is assumed of them, are listed in `docs/trust-ledger.md`: findings there are expected and welcome. One known limit is stated, not hidden: the standard bounds neither a line nor the data buffer, so a hostile stream can make the reference grow both without limit (the ledger's `bounded-state` claim is open).

## How to report

Use GitHub's private vulnerability reporting for this repository (Security tab, "Report a vulnerability"). If that is not available, open an issue that says only that you have a security report and ask for a private channel; do not put exploit details in a public issue.

Please include the input (or a minimal one), the build you used (commit hash) and what you expected.

## What to expect

This is maintained on a best-effort basis. Expect an acknowledgement within about a week and a fix or a written assessment as soon as practical. A confirmed bug is fixed on `main` with a regression vector.
