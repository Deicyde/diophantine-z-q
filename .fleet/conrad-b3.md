# conrad-b3 (2026-11-17): Tate 1967 off the C8 route; one Conrad App. B leaf

**Result.** `LocAlgExponentEqWeight` (diophantine_zq.tex L763-764, "removing its integral local Hodge–Tate weight") is
proved from Conrad's Prop. B.3 (App. B p. 33, the manuscript's own citation L760-762) for the base field `ℚ_p`, stated in
Conrad's conventions (arithmetic Artin map = Tau Ceti's; `χ_cyc` of weight `+1`): `C8ConradB.locAlgExponentEqWeight_of_conradPropB3`.
The exponent-sign and weight-sign translations are definitional and proved (`isLocallyAlgebraic_iff_conrad`,
`htMult_eq_conradHTMult_neg` = `rfl`). The two Conrad leaves are merged into one, `ConradAppB := ConradAppBQp ∧
ConradPropB3Qp` (App. B pp. 32-33, exactly the manuscript's citation); every consumer takes it. `TateTwistInvariantsInertia`
(a DEPARTURE) had no consumer outside the C8 files; it is removed from `C8Inputs` and `C8Leaves` (consumer statements
changed and named in the report) and from the fold spec.

**Count** (H strict LEAF/GLUE, `scratch/conrad-b3/count_out.txt`): main 5/24 on 29 before; joint fold (C8 + Poincaré +
ht-merge's (iii) swap) with PR #86's `poincareComplement_proof`: **5/24 on 29** after (ht-merge's spec: 5/25 on 30), so
GLUE one lower and the joint fold count-neutral. Without PR #86: 5/25 on 30 (ht-merge's spec: 5/26 on 31).

**Manuscript check.** L763-764 is supported by the cited source (Prop. B.3: the weight is the exponent). No known issue.

**What compiles** (merged tree: origin/wip/ht-merge 027f637cd merged): `lake build ZInQKernel.Contrib.OneProof.C8Printed`
(13414 jobs); joint dry run `scratch/conrad-b3/CBDryRun.lean` (`frozenTarget_cb`, `sixContactMin_of_open73CB`: standard
axioms); `#discharges` 30 open, 16 discharge one (none from C8, expected). New file `ZInQKernel/Contrib/OneProof/C8ConradB.lean`.

**New leaf rating.** `ConradPropB3Qp`: consequence of the print (bridge from `ℂ_p ⊗ V ≅ ⊕ ℂ_p(n)` to
`dim_{ℚ_p} H_n = [E:ℚ_p]` is linear algebra + Ax–Sen–Tate, proved in the tree, not formalized); merged row `conradAppB`
GLUE until reviewed (the p. 32 half keeps queue28's GLUE/GLUE bridges). Flag: AI page read 11-17; unrefereed preprint,
the manuscript's own citation.

**Remains.** Review of `conradAppB`; the joint fold (integrator), re-based onto main's current top (open76).
Report: docs/research/conrad-b3.md.
