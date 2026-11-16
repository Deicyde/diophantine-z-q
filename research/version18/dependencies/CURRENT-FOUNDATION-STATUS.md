# Current use of the historical H170 and H201 findings

This is a source-and-consumer comparison for the Version 18 source identified in `CURRENT-V18-LABELS.json`. It is not a new independent acceptance record. The original [cleanup status](../../../docs/research-review/version18-cleanup-status.md) describes the evidence checked by that cleanup and remains historical evidence of its stated scope. PR120's assembled-proof review is still required.

## H201: the selected invariant formula has a different derivation

The original [adverse record](../../version14/proofs/a001-moduli-current-v1/ADVERSE-CASE.md) correctly distinguishes the degree-four product map in Baba–Granath Proposition 3.7 from an assertion that no other product isomorphism exists. It also warns that citing the final invariant formula without examining its derivation can retain an ancestral dependency on that calculation.

For the selected current use, the repository contains a separate derivation in [the Lin–Yang normalization proof](../../version14/proofs/ly-d6-normalization-v1/PROOF.md). It uses the divisor identities and product-curve and `Y'_5` intersection data in Lin–Yang Examples 29–30, then evaluates the latter at the discriminant-24 eta-coordinate satisfying `x^2+12x+144=0`. It derives the constants and the weighted Igusa tuple. It does not use the later discriminant-19 value or assume Lin–Yang's final equation (2) as the formula to prove.

The original [Compiler review](../../version14/proofs/ly-d6-normalization-v1/reviews/INDEPENDENT-REVIEW.md) is by a different agent from the author. It accepts that connection under its retained published inputs, after reading the cited final-source pages. It explicitly excludes a recursive audit of all source ancestors, approval of the disputed product map and a whole-release decision. The [current-consumer review](../../version14/proofs/ly-d6-normalization-v1/reviews/CURRENT-INTERFACE-REVIEW.md) separately checks the normalized coordinate, weights, conjugate-object and theta-height uses. It discloses its author's earlier contribution to an unselected route.

The current manuscript incorporates that derivation immediately before `eq:qm-normalized-igusa`. It fixes the same three marked values, derives all four constants, converts with the same weights and expressly excludes the disputed product-isomorphism arguments. Its later theta-height calculation reuses that same equation and the weight-zero quotient. The [A001 review](../../version14/proofs/a001-moduli-current-v1/reviews/INDEPENDENT-REVIEW.md) covers the separate principal-datum/coarse-quotient application and does not pretend to prove the invariant formula merely from the quotient.

Thus **prior justification was found and the replacement is incorporated for this selected normalized-invariant use**. The historical cleanup's statement that it had not verified a later disposition must not be read as a finding that this proof is absent. This comparison neither repairs Baba–Granath's disputed argument nor retires every historical use of it. The old objection remains in the record; the selected consumer uses the separately reviewed Lin–Yang derivation. PR120's reviewers still decide whether this evidence and the current application suffice for their finding.

## H170: the old inverse-proof occurrences are superseded in this manuscript

The [original occurrence record](../../version14/proofs/local-gi-v1/proof/modules/09-gi-section12/RELATED-USE-AUDIT.json) concerns the old local inverse proof's larger-domain frequency, filtration and related assembly uses. Its [geometric-join review](../../version14/proofs/local-gi-v1/proof/reviews/section12-join-independent-arithmetic/REVIEW.md) has explicit conditional scope and is not a certificate that every old copy was corrected.

The adopted Version 18 route replaces those local inverse-proof sections with the Candela–Szegedy dependency and the retained ordinary-degree normalization and increment-group proof. The consumer and removal checks, old-material location and actual PR118 review decision are recorded in [the inverse-dependency record](../../../docs/research-review/version18-inverse-dependency.md). Current `v15:gi:ASSEMBLY` uses the replacement, with `v18:cs:witnesses`, `v18:cs:models-lemma`, `v18:cs:metric-lemma`, `v18:cs:interval-correlation` and `v15:gi:14:thm:linear` supplying its steps.

For this manuscript the removed local occurrences are **superseded by the adopted route**. This is not an assertion that all archived copies were repaired. The archive-wide propagation obligation and original conditional review remain unchanged. PR118's acceptance included owner source-access overrides; it must not be reported as unanimous model acceptance.

## Other inherited inputs

The [current inventory](CURRENT-V18-INVENTORY.md) locates the remaining arithmetic suppliers and their receiving assertions. A located proof or a byte-identical inherited passage is not automatically a new acceptance. The current PR120 findings on unfinished supplier coverage remain for the reviewers to disposition. The selected polynomial, its variable count and the frozen Version 16/17 files are unchanged by these records.
