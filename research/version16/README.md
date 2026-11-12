# Version 16

[Manuscript PDF](../../manuscripts/quartic_v16.pdf) · [TeX source](../../manuscripts/quartic_v16.tex)

Dated November 11, 2026. This edition incorporates three corrections from the [fourth Fable 5.2 audit](audits/fable-5-2-audit-4.pdf), whose new material is on pages 84–97. It retains Version 15's original large construction, 314-variable decimal quartic and 222-variable quartic family. The abstract, theorem statements and polynomial data are unchanged. No Busy Beaver specialization is included.

## Changes

1. Before deleting rational or small horizontal coordinates, normalize the actual polynomial orbit by a lattice-valued polynomial so its horizontal Taylor identities hold in the vector groups. Divide those fixed real lifts when passing to the finite covering lattice.
2. Cite Gaudron–Rémond's *Théorème des périodes et degrés minimaux d'isogénies*, Comment. Math. Helv. 89 (2014), 343–403, DOI 10.4171/CMH/322, for the two auxiliary Faltings-height statements. The Duke paper remains cited for its separate isogeny results.
3. Describe the fixed-extra-factor Tao–Ziegler use as an adaptation of the proofs. This edition does not substitute the alternative statement-only reduction sketched by Fable.

The [exact edits](EDITS.json) reconstruct the mathematically reviewed Version 16 source from the preserved Version 15 source. The subsequent [editorial amendment](EDITORIAL-AMENDMENT.json) restores the original AI usage statement, adds Fable 5.2 to the auditing credit, and moves the unchanged Conant credit immediately before that statement. The [precision amendment](TZ-PRECISION-AMENDMENT.json) clarifies that the divisor-sum local factors satisfy the same uniform estimates; it does not assert that their numerical values are identical. The [preceding source](snapshots/pre-precision/quartic_v16.tex) preserves the original review target. The independent reviews retain their original byte bindings. The [application inventory](APPLICATIONS.json), [findings](FINDINGS.json), [initial review](review/REVIEW.json), [current review](review/current/REVIEW.md), [build record](BUILD.json) and [artifact manifest](MANIFEST.json) separate mathematical review from finite validation and repository approval.

## Scope and remaining review limits

Fable withdrew the Bogolyubov-numbering objection after comparing the published version. The normalization device already appeared at another site in Version 15; this edition incorporates it at the earlier finite-cover application. This is not a claim that no earlier justification existed.

Fable's four-pass report leaves Kato 1999 and Ribet 1990 unread, the complete modified-modulus Tao–Ziegler proof outside its re-derived scope, and several source comparisons unfinished. These limits remain recorded in FINDINGS.json. The present changes do not represent a new whole-proof audit or completed Lean formalization. A local review report is not the public repository's required App check.

The subsequent [current review](review/current/REVIEW.md) checks the fixed-extra-factor adaptation against the published proofs and traces the affected arguments into their consumers. It also identifies the earlier independent Kato and Ribet reviews. This does not change the scope of Fable's own audit. The [current connection records](protocol/CONNECTIONS.json) preserve the old objections and record the additional dispositions.

## Reproduce and continue

Run `python -B research/version16/check.py` from the repository root. It checks the exact delta, hashes, unchanged abstract and theorem statements, citation split, PDF/source binding, and the scoped review record’s content and hashes. Reviewer identity and model eligibility are authenticated separately by the protected controller. The unchanged [Version 15 package](../version15/ARTIFACT-INDEX.md) supplies the polynomial data and its finite verifier.

The [cumulative handoff](CUMULATIVE-HANDOFF.md) preserves the previous research archive and this edition's evidence. Previous snapshots and their original review statuses remain unchanged.
