# morph-descend results log

- VERIFIED (read): Mathlib v4.35 `Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean` has
  `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation` (cofiltered limit of qcqs schemes with
  affine transition maps, X LFP over S: an S-morphism lim D_i → X factors through some D_j; Stacks 01ZC
  surjective part = EGA IV₃ 8.8.2(ii) form) and `Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType`
  (injective part), `Scheme.preservesColimit_yoneda`.
- Plan: MorphismsDescend is glue over that lemma: ℚ̄ = colim of finite L ⊇ E₀ (CommRingCat), Spec
  preserves limits, Over.forget reflects connected limits, Over.pullback (right adjoint) preserves
  limits, Over.forget preserves connected limits.
- Colim.lean (now Descend.lean): `ringCoconeIsColimit` (ℚ̄ = filtered colimit of finite subextensions ⊇ E₀ in
  CommRingCat) COMPILED, no errors.
- Descend.lean: specConeIsLimit (Spec ℚ̄ = lim Spec L in Over (Spec K)), bcConeIsLimit (ℚ̄ ×_K X = lim L ×_K X in Scheme), bcDiag_map, bcCone_π_app (rfl) COMPILED.
- Descend.lean: `MorphDescend.exists_descend` COMPILED (general: X qc+qs over K, Y LFP over K, e₁ e₂ : K →+* ℚ̄ into number field E₀; every ℚ̄-morphism X×_{e₁}ℚ̄ → Y×_{e₂}ℚ̄ is the base change of ψ over a number field E₀ ⊆ L). Proof: Mathlib Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation on bcDiag.
- Descend.lean (404 lines): `MorphDescend.morphismsDescend : MorphDescend.MorphismsDescend` (statement
  copied verbatim from G4.lean) COMPILED, 0 errors, 0 warnings; `#print axioms` for exists_descend and
  morphismsDescend: [propext, Classical.choice, Quot.sound]. VERIFIED.
- G4Closed.lean (1903 lines = Descend block + G4.lean unchanged + tail): `G4WeilRes.morphismsDescend :
  G4WeilRes.MorphismsDescend` (proof term `MorphDescend.morphismsDescend`; the two Qbar abbreviations
  unify), `G4WeilRes.homDescends : HomDescends`, `G4WeilRes.homField_of_model_closed` (G4 headline
  without the hM argument) COMPILED; all printed axioms standard. Needed `lake build` of B3b,
  TorsionFree, Numerics, B3Assembly (succeeded).
