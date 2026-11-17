# Project and review configuration

This repository studies Diophantine definitions of the ordinary integers in the
rationals. The current target statements, parameter qualifications and coefficient
representations are in the complete manuscript selected by
[`docs/current-manuscript.json`](docs/current-manuscript.json). The
[release policy](docs/release-policy.md) requires a complete TeX/PDF pair for an
official new record, with the next ordinary integer manuscript version.

## Approved reviewers for Protocol B

The owner selected these two reviewer models on November 13, 2026:

| Provider family | Exact API model ID |
|---|---|
| OpenAI | `gpt-6-astra` |
| Anthropic | `claude-fable-5-2` |

Both reviewers must complete their review and accept mathematical changes,
subject to the explicit exceptions below. An App-authenticated acceptance remains
valid for an unchanged head. Completed reviews can also carry across a rebase with an unchanged diff
and unchanged reviewed dependencies.

Editorial notes do not block. A completed review with only editorial notes meets
the review requirement even if its original decision is `changes_requested`;
the record preserves that decision and does not call it unanimous acceptance.
A source-access-only finding is nonblocking if the other reviewer actually
checked the same source passage and application without objection; its limitation
remains in the record. Substantive findings and named gaps otherwise require
resolution or an explicit admin override.

A current repository admin may explicitly accept a recorded finding or an
incomplete or absent review for one exact head, using the documented override
command and a reason. Each remaining substantive finding needs its own resolution
or override; a scope override does not cover it. The record identifies the affected
claims as not outside reviewed and discloses the unreviewed work. If no model review
completed, it says so, including when neither model ran. It never changes an
incomplete execution or rejecting model verdict into a model acceptance.
Write-access collaborators retain ordinary review commands and protected merge
access; only admins may override.

There is no fallback model. Changing this list is the owner's decision and takes
effect at the next release. The workflow records the requested and returned model
IDs; it does not claim cryptographic verification of a provider's internal model.

## Deployment state

Protocol B is the active review policy for future pull requests, as authorized
by Elliot Glazer on November 13, 2026, America/Los_Angeles. At 18:57 PST that day
(November 14, 02:57 UTC), Astra read back the settings through Elliot's authorized
GitHub session: live mode, repository auto-merge, the designated App's
`Protocol B / review` requirement, all 14 computation requirements and strict
up-to-date protection. This is a dated operator observation, not a claim that
anonymous readers independently verified those settings. The
[readback and limits](docs/research-review/reviews/activation-2026-11-13/README.md)
preserve the non-secret evidence. The [current contributor guide](docs/research-review/README.md) describes
the review requirement and the admin override path. Activation does not
retroactively certify the repository's historical claims.

The App key and two model API keys belong in the `protocol-b` GitHub Environment,
restricted to the default branch. They must not be repository-level secrets or
appear in files or PRs. The [setup and test checklist](docs/research-review/protocol-b-setup.md)
specifies the App identity, secret names, activation checks and deferred tests.
The retired controller and local runner are not used.

Non-author-family review of the implementation and repairs remains an activation
requirement. The [pre-activation review record](https://github.com/elliotglazer/diophantine-z-q/blob/005b17abfbefd8bee7b34f3bbe8f5aabf872eb1f/docs/research-review/reviews/pre-activation-reviews.md)
records Fable 5.2's original review files, the retrospective PR73 record, and
owner-reported in-session acceptances of later commits. It also records PR88's owner-bypass
merge on those reviews, not an App acceptance. Branch/tag key-isolation testing
and a successful live protected merge remain unverified in this snapshot.

Use the existing theorem-application inventory and findings history during the
transition. Their distillation and archival are separate work; this gate does
not rewrite historical reviews or bind acceptance to shared-file byte hashes.

Protocol reference: [Protocol B, edition 2](https://github.com/elliotglazer/protocols/blob/main/Protocol_B.md).

## Load-bearing steps

This is a review map, not a new acceptance of the historical arguments. Follow
the current-manuscript profile above before using the labels below. For Version
19, the following parts need outside review when changed, along with their
affected consumers:

| Step | Current manuscript labels | Why it is load-bearing |
|---|---|---|
| Selected 195 family | `v19:195-reduction`, `v19:195-rows`, `v19:195-fixed` | Both directions of the guarded coordinate changes, the primitive row basis and the coefficient specialization must agree with the retained 196 parent. |
| Explicit 250 polynomial | `v19:sum-height`, `v19:reflected-height`, `v19:250-soundness`, `v19:250-completeness`, `v19:250-maps`, `v19:250-rows` | Effective constants, the fixed parameter 10220, simultaneous witnesses and the full decimal expansion must agree. |
| Selected 196 family and elimination | `q196:fixed`, `q196:general`, `q196:family`, `q196:rows` | Both projection directions, nonzero rescaling factors, all retained guards and printed coefficients must agree with the parent and selected table. |
| Parent arithmetic and finite algebra | `q198:family`, `q198:finite-algebra`, `q198:soundness`, `q198:completeness` | The 198-coordinate parent must supply the integer characterization for the same parameter and simultaneous witness choices. |
| Busy Beaver parameter and coefficient bound | `q198bb:fixed`, `q198bb:threshold`, `q198bb:compiler`, `q198bb:coefficient` | The uniform threshold, halting-machine size, machine convention and strict coefficient comparison must justify the selected fixed parameter. |
| Retained 214 foundation | `q214:theorem`, `q214:certificates` | The inherited arithmetic interfaces and finite identities retain their separate proof scopes. |
| Arithmetic height input | `sec:height`, `thm:height`, `q214:height-supplier` | Soundness needs the height bound for the actual contact data, including exceptional cases and uniformity. |
| Modularity, evaluation and height comparison | `q214:modularity`, `q214:height-evaluation`, `q214:height-different`, `q214:height-metric`, `q214:height-averaging`, `q214:height-assembly` | These compare different models, metrics and normalizations; a citation must supply the object actually consumed. |
| Pole predicate and restricted converse | `sec:pole`, `sec:rc`, `q214:source-carry` | Completeness uses simultaneous realization and the analytic/arithmetic converse chain, including determinant, limit and local-condition arguments. |
| Prime patterns and analytic input | `prop:fixed-prime-pattern`, `thm:v5-simultaneous-primes`, `q214:source-carry` | The required simultaneous choices, large-prime tail, prime weights and transference must all hold for the same fixed data. |
| Current repairs and foundation transfer | `q214:foundation-transition` | Horizontal normalization, the corrected height citations and the Tao–Ziegler adaptation must occur at their actual points of use. |
| Final assembly | `q214:assembly`, `q214:existence`, `q214:uniform-existence`, `q214:geometry-carry` | Both projection directions and the parameter choices must use compatible hypotheses and objects. |
| Lean statements and assumptions | Current Lean contribution policy and each changed declaration's source | A kernel build is insufficient if the statement, quantifiers, definitions or remaining assumptions differ from the mathematical target. |

The reviewer adds any omitted deep application, new central argument,
exceptional case, limit interchange, simultaneous witness choice or substantive
repair discovered while reading. Existing source applications and findings are
in `docs/theorem-application-audit/` and `docs/audit-history/`; their historical
states remain intact. A Protocol B review records its changed scope rather than
retroactively relabeling this entire list as outside reviewed.
