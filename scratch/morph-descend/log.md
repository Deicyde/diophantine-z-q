# morph-descend results log

- VERIFIED (read): Mathlib v4.35 `Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean` has
  `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation` (cofiltered limit of qcqs schemes with
  affine transition maps, X LFP over S: an S-morphism lim D_i → X factors through some D_j; Stacks 01ZC
  surjective part = EGA IV₃ 8.8.2(ii) form) and `Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType`
  (injective part), `Scheme.preservesColimit_yoneda`.
- Plan: MorphismsDescend is glue over that lemma: ℚ̄ = colim of finite L ⊇ E₀ (CommRingCat), Spec
  preserves limits, Over.forget reflects connected limits, Over.pullback (right adjoint) preserves
  limits, Over.forget preserves connected limits.
- 02:05 Colim.lean: `ringCoconeIsColimit` (ℚ̄ = filtered colimit of finite subextensions ⊇ E₀ in
  CommRingCat) COMPILED, no errors.
