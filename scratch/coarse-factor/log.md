# coarse-factor results log

## Step 1: reduction (Reduction.lean)
- Copied verbatim from scratch/qm-glue/ModuliCompare.lean: `CoarseFactor`, `CanonicalCoarseX6` (python substring check True, VERIFIED).
- New Props: `PairsLift` (every QM pair over Q̄ is iso to P.forget for some QML3 P), `FactorThroughSurj` (AG glue:
  proper smooth curves Y,X,X' over ℚ, f : Y→X onto X(Q̄), f' constant on Q̄-fibres of f ⇒ ∃ h, f ≫ h = f').
- COMPILED (lake env lean, 15 s, imports ZInQKernel.OneProof.H.LPrefix; standard axioms):
  `coarseFactor_of : PairsLift → FactorThroughSurj → CoarseFactor`,
  `pairsLift_of_canonical : CanonicalCoarseX6 → PairsLift`, `pairsLift_of_rep : R1R2fpRep → PairsLift`,
  `coarseFactor_of_canonical`, `coarseFactor_of_rep`.
- Finding: X6Props alone does not give surjectivity of fY on Q̄-points; it needs that every QM pair has a level-3
  structure (PairsLift). PairsLift is not a new leaf: it follows from the leaf-forms qm-glue already uses.
- Build note: lean/.lake/build copied from ~/dzq-wt/leaf-fold7 (lean/ZInQ sources identical, diff -rq).

## Step 2: FactorThroughSurj proved (Factor.lean; COMPILED, standard axioms, ~7 s)
- Lemmas (all COMPILED): `exists_lift_of_closed`, `exists_lift_of_surjective`, `exists_lift_at` (K-points lift along lft
  morphisms through closed sets of the fibre product; Mathlib `pointOfClosedPoint`); `exists_hom_ker_eq`, `exists_extend`;
  `bijective_of_points` (A Dedekind f.t. over ℚ, B reduced finite over A, Spec B → Spec A bijective on Ω-points ⇒ A ≅ B;
  B is shown a domain via Jacobson + unique maximal ideal over each maximal ideal, then curve-split's
  `bijective_of_unramifiedAt`, residue degree 1 by `AlgHom.card`); `isIso_affine`, `restrict_inj/surj`,
  `isIso_of_points` (finite p from reduced Z onto a compact smooth ℚ-curve, Ω-bijective ⇒ iso);
  `isReduced_image` (scheme-theoretic image of reduced is reduced); `isZariskiLocalAtTarget_isFinite`
  (instance not found by TC search: explicit term); `factorThroughSurj`.
- Proof of FactorThroughSurj: Z = image of (f,f') in X ×_ℚ X'; p = pr₁|_Z is proper, finite by Mathlib's
  `exists_finite_imageι_comp_morphismRestrict_of_finite_image_preimage` (Stacks 0AH8) at each closed point (fibres over
  closed points are single points: Ω-point injectivity + Jacobson), Ω-bijective (lifts along the surjective toImage).
- Copies from scratch/curve-split/CurveBij.lean: sections Topo, Curves, isIntegrallyClosed_of_normal,
  isLocalization_of_cofinal, bijective_of_unramifiedAt, bijective_of_finrank_eq_one, isDedekindDomain_sections (section
  variables [IsAlgClosed k] [CharZero k] dropped; unused in its proof).

## Step 3: combined file CoarseFactor.lean (COMPILED over import ZInQKernel.OneProof.H.LPrefix; standard axioms)
- `HDec.QMSplit.Moduli.coarseFactor_of_canonical' : CanonicalCoarseX6 → CoarseFactor`,
  `HDec.QMSplit.Moduli.coarseFactor_of_rep' : LeafAdopt.R1R2fpRep → CoarseFactor`.
- Verbatim checks: CoarseFactor, CanonicalCoarseX6 True; the two FactorThroughSurj texts identical.
- Note: under LPrefix the QM namespace is HDec.LeafQM.AV; Part 1's `open LeafQM.AV` changed to `open HDec.LeafQM.AV`.
