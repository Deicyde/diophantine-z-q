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

Both must review every mathematical change and both must accept, except for an
explicit collaborator override of a recorded deadlock. An overridden step is
not outside reviewed. There is no
fallback model. Changing this list is the owner's decision and takes effect at
the next release. The workflow records the requested and returned model IDs;
it does not claim cryptographic verification of a provider's internal model.

## Deployment state

The Protocol B workflow is being prepared. It is inactive unless explicitly
enabled by the repository owner. Its presence does not establish that this
repository or its historical claims have completed Protocol B review. The
[current contributor guide](docs/research-review/README.md) remains authoritative.

Before activation, a reviewer outside the author's model family must review the
workflow and instructions, and a designated throwaway PR must pass an end-to-end
test with both model APIs. The owner then approves activation. The App key and
two API keys belong in the `protocol-b` GitHub Environment, restricted to the
default branch. They must not be repository-level secrets or appear in files or
PRs. The [setup and test checklist](docs/research-review/protocol-b-setup.md)
specifies the App identity, secret names and activation steps.

Use the existing theorem-application inventory and findings history during the
transition. Their distillation and archival are separate work; this gate does
not rewrite historical reviews or bind acceptance to shared-file byte hashes.

Protocol reference: [Protocol B, edition 2](https://github.com/elliotglazer/protocols/blob/main/Protocol_B.md).

## Load-bearing steps

This is a review map, not a new acceptance of the historical arguments. Follow
the current-manuscript profile above before using the labels below. For Version
17, the following parts need outside review when changed, along with their
affected consumers:

| Step | Current manuscript labels | Why it is load-bearing |
|---|---|---|
| Main family and its finite algebra | `q214:theorem`, `q214:certificates` | The equations, parameter range and coefficient representation must match the claimed projection and the regenerated artifacts. |
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
