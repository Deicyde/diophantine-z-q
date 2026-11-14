# Research review for contributors

Future pull requests are reviewed under [Protocol B, edition 2](https://github.com/elliotglazer/protocols/blob/main/Protocol_B.md).

- The public policy requires the computation checks and `Protocol B / review` from the designated GitHub App on the current PR revision. Astra read back that configuration through Elliot Glazer's authorized GitHub session on November 13, 2026, 18:57 PST; the [dated evidence and limits](reviews/activation-2026-11-13/README.md) distinguish that observation from independent anonymous verification. See also the [public ruleset](https://github.com/elliotglazer/diophantine-z-q/rules/26781429). A same-name Actions check does not satisfy the App requirement. The private repository has no ruleset.
- Mathematical and policy changes require both approved reviewers, Astra 6 and Fable 5.2, to finish and accept. A narrowly defined editorial path can pass without model calls; the [setup and test checklist](protocol-b-setup.md) gives its exact limits.
- A current collaborator can explicitly override a completed-review deadlock, one recorded finding at a time. The summary names the collaborator and reason, and marks the affected claims **not outside reviewed**. An override does not repair the mathematics.
- Passing CI shows that the recorded computations and builds reproduce. It does not establish that an argument is correct.
- An official new record needs a complete updated manuscript in TeX and PDF and the next integer version; see the [release policy](../release-policy.md).
- Objections and repairs follow the [audit-history protocol](../audit-history/PROTOCOL.md).
- Lean contributions follow the [Lean contribution policy](../lean-contributions.md).

## How review runs

Opening or updating a ready PR triggers the default-branch workflow. Contributors
do not need access to the API keys or a local review runner. Both models read the
changed sources and relevant history, and their reports appear on the PR.
Repair a finding by updating the branch. A current collaborator can also request
a review with `/protocol-b review`.

Only the designated App's review check satisfies this policy. The workflow
uses keys from the `protocol-b` Environment, whose `main`-only deployment rule
was present in the dated operator readback. That snapshot does not prove key
rotation, absence of copies elsewhere, or a live branch/tag access-denial test.
The App is used by this repository's workflow; there is no separate controller.
Unfinished reviews and unavailable required sources do not pass. The checklist
documents override commands, context limits and the remaining test limitations.
The [pre-activation review record](reviews/pre-activation-reviews.md) preserves
the review requirement and records how it was addressed, including the
owner-reported reviews and PR88's exceptional bootstrap merge.

This requirement applies to future changes. It does not retroactively certify
the repository's historical arguments under Protocol B.

## Earlier review policy

Releases through Version 17 were reviewed under the project's earlier review protocol. Its texts are retained here as historical policy: [version 1.4](PROTOCOL.md), [version 1.3](protocol-v1.3.md), [version 1.2](protocol-v1.2.md) and [version 1.1](protocol-v1.1.md), with the [Astra acceptance policy](ASTRA-REVIEW-POLICY.md) and the [version 1.4 adoption record](ADOPTION-V1.4.md). Those releases and their review records keep their original standard and scope.
