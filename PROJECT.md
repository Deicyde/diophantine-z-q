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

Both must review every mathematical change and both must accept. There is no
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
test with both model APIs. The owner then approves activation. The two API keys
belong in repository secrets, never in a file or PR.

Use the existing theorem-application inventory and findings history during the
transition. Their distillation and archival are separate work; this gate does
not rewrite historical reviews or bind acceptance to shared-file byte hashes.

Protocol reference: [Protocol B, edition 2](https://github.com/elliotglazer/protocols/blob/main/Protocol_B.md).
