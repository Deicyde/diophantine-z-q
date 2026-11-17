# Conditional quartic research stack: November 8, 2026

This cumulative handoff responds to protocol v1.2, merged in upstream #10 at
`9c0b3aba60d90fdcac82115f0582a6f52f1054f7`. It describes research proposals,
their retained evidence and remaining work. It does not designate a new
current manuscript edition or certify the inherited arithmetic theorem.

| Proposal | Variables | Maximum decimal digits | Role |
| --- | ---: | ---: | --- |
| #8, delivered package | 389 | 757 | Frozen import, source comparison and full replay |
| #9, above #8 | 385 | 757 | Four factored pole conics |
| #11, above #9 | 385 | 682 | Order-31 scalar chain and smaller anchor |
| #12, above #11 | 383 | 682 | Scalar preparation zero with simultaneous real/finite choices |
| Separate higher-precision experiment | 386 | 646 | Order 46/47 coefficient tradeoff; not selected in these PRs |

All counts include the input. These are complete compiled counts, not sums
of estimated savings from Version 13. Version 13 remains the repository's
current manuscript and current polynomial release. An earlier PR in this
table contains only its own layer and its ancestors; later layers and
research alternatives are linked evidence, not files claimed to be present.

## Exact evidence and reproduction

`ARTIFACTS.json` identifies every layer by immutable source commit, source
directory, representation, reproduction command and measured summary.
`EVIDENCE_MANIFEST.json` hashes every tracked file in those research packets,
the retained negative-result investigations, the independent-review archive,
and the unchanged current release surfaces. The source locations are public
immutable GitHub URLs. `HANDOFF_MANIFEST.json` binds this handoff's own files;
its digest is stored separately in `HANDOFF_SHA256.txt` to avoid self-reference.

The supplied 389 package includes its selected full decimal expansion. The
385/383 layers and higher-precision alternatives supply deterministic
generators, exact expected table hashes and verification tools; their full
decimal expansions are produced by reproduction and are not checked into
those source directories. The words “decimal coefficients” describe the
resulting representation, not a claim that every generated table is committed.
The original package's proposal PDF is a frozen historical artifact, not a
new Version 13 PDF built from these later improvements.

The exact original source inventory, 32 transformations and 11 inherited
input groups are in the package's `PR_DEPENDENCIES.md` and associated JSON
inventory. The later layers have separate application contracts, proof notes,
source bindings and reproducible coefficient checks. Earlier reports and
author snapshots that say “pending” remain preserved as historical evidence;
later review decisions are linked separately, not written over them.

Python 3.12.3 and Node 18.19.1 were used for the local reproductions; the
standard library suffices. The parent 23-stage replay and all selected
subsequent layer replays passed. Per-layer receipts and independently
regenerated summaries are preserved at the exact review-archive locations in
`ARTIFACTS.json`. CI and finite checks establish their stated algebraic,
coefficient and integrity properties; they do not prove the inherited
arithmetic or authorize the designated protocol App's merge check.

## Research history and corrections

The source package was delivered from Cameron's ChatGPT research session,
with its own retained internal AI audits, `ATTRIBUTION.md` and `PROVENANCE.json`.
Codex performed the fresh import checks and authored the later focused
reductions and research experiments. A separately assigned model reviewer,
task `/root/independent_math_review`, reviewed #9/#11, #12 and the higher
precision alternatives with source manifests and fresh finite checks.
These are internal model reviews, not human peer review; correlated errors
remain possible. Model metadata not recorded in those reports is unknown.

The quoted earlier chart and rational-logarithm savings were estimates,
subsequently retracted. Actual full builds showed a direct chart port saves
zero variables (and 194 monomials), and the implemented rational-logarithm
port adds eight variables. The earlier preparation-zero experiment retained
the old norm tree and 757-digit bound; the selected #12 combines preparation
zero with #11's different order-31 chain and has 682-digit coefficients.
The exact derivations, implementations and results remain in the versioned
`research/quartic-followup` and `research/scalar-chain-investigation` packets.

The higher-precision packet proves the existing G12 truncation supports
uniform relative precision 51, with a depth-one obstruction to 52 at prime
53. Its implemented order-46/47 weights cost one additional coordinate per
detector. A cost-neutral higher-order weight circuit remains open; neither
the old bounded search nor these measurements establish general optimality.

## Findings and limits

`FINDINGS.json` records the received objections, corrections, scope limits
and remaining work with exact evidence locations. The live PR comments and
reviews for #8, #9, #11 and #12 were read on November 8, 2026; each was empty
at that observation cutoff. Later comments must be reconciled separately.
The supplied package's audit records remain included in its complete source
manifest; this handoff does not claim to have independently re-audited all
156 imported files or all published-source applications.

The mathematical interpretation remains conditional on the package's named
inherited inputs. Review coverage is a separate limitation: local source and
circuit reviews do not establish that every inherited application has been
checked against its authoritative publication. The historical Version 10
Kato route and Version 11 repair are recorded in the import source-comparison
note. Complete integration of the actual repaired source chain, inventories,
assembled proof and current manuscript remains pending. This is not a claim
that an unread theorem is false or an additional conjecture.

## Protocol applicability and publication

See `PROFILE.md` for each applicable duty and the reason current release
surfaces stay unchanged. This profile requires separate reviewer assessment;
it is not a self-authored exemption from the protocol. The scope decision
and final updated-head acknowledgment are published as distinct reviewer
evidence linked from the PR descriptions. No old acceptance hash is refreshed.

Authorized publication here is to Cameron's public fork and the existing
upstream research PRs. No private-mirror publication was requested or
performed. Readback records compare the pushed public heads and handoff
manifest to local bytes. Upstream merging remains a maintainer action.
The live rules require `Protocol / independent agent audit` from the
designated App on the exact revision. Contributor-written reports cannot
substitute for that check; its outstanding status is reported explicitly.

## Original delivery records outside the overlay

`delivery-history/` now preserves the original assembled-manifest, exact-patch-route, integration and final-fresh-build reviews, their checker sources, validation JSON and original bundle manifest byte for byte. `DELIVERY_SELECTION.json` records the original archive digest and every selected or omitted non-overlay file. Distribution patches, execution logs and delivery instructions remain archive-only and are not advertised as public artifacts or current reproduction inputs. This handoff does not claim to publish the entire original ZIP or independently rerun its historical patch routes. Source files, actual current reproduction and all original review verdicts remain available at the declared locations.
