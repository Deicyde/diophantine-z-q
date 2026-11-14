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

## Archived review records

The complete historical records tracked in this repository before archiving are preserved at the [review-archive-v17 tag](https://github.com/elliotglazer/diophantine-z-q/tree/review-archive-v17), commit `005b17abfbefd8bee7b34f3bbe8f5aabf872eb1f`. The six original files in [distilled/](distilled/README.md), supplied by Elliot Glazer from his work with Claude Fable 5.2 and its reader agents, are preserved unchanged as their summary and recorded judgments. The internal findings previously recorded as open have now been checked against Version 17 in [open-findings-check.md](distilled/open-findings-check.md), preserved unchanged from the owner-supplied file. Fable 5.2 assembled that check from six reader agents: it examines 131 entries, identifies one real gap in the written proof (R2-F7) and one step needing a short proof or checked source (R3-F20), and lists additional citation, exposition and unresolved supplier checks. Its “Fixes for Version 18” section is the Version 18 work list. The file distinguishes locating a passage or citation from re-deriving its mathematics; it did not re-examine the 114 findings recorded as repaired and accepted. This archival addition does not declare the listed repairs complete, close the separate outside-audit findings below, or constitute new whole-proof acceptance.

The folder includes new same-family reader-agent checks of Version 17, not just extracts of old reviews. Their mathematical verdicts have not received cross-family acceptance under Protocol B and are not adopted as new proof acceptance by this transfer. In particular, the broad “none is a real gap” sentence in the original distilled README must not be applied to the outside objections or unread proof ranges; the owner-supplied follow-up records the contrary R2-F7 result. The outside objections recorded OPEN (E8, E34, E37, E38, E43), PARTIAL (E5, E7, E23, E28, E32, E35, E36, E42), or UNLOCATED (E24) have not been re-checked by this archival update and are not closed by archiving the internal-findings check. The earlier Atkin–Lehner verdict also remains a reported reader judgment, not an accepted resolution of the prime-to-level issue.

Erratum to the unchanged ledger: E32 and E43 incorrectly say Version 17 no longer contains the indices `4,6,2` sentence. It remains at line 5842 of `manuscripts/quartic_v17.tex`, in the height argument. E43 therefore concerns current text; its argument-level effect is unresolved here. Preserving the original files does not endorse this erroneous statement or close that objection.

The archive tag preserves the repository corpus, not every external source used to compile the summaries. Part 1 of the ledger also relies on nine locally held Fable audit PDFs and a task brief. The tag contains `research/version16/audits/fable-5-2-audit-4.pdf`, but not all the other local PDFs or that brief. In particular, the original out-of-tree sources for E1–E7, E23–E24 and E27–E29 are not supplied by the tag; E30, E32 and E33 include provisional objector attribution from the brief. These are source and provenance qualifications, not a fresh audit of the claims.
