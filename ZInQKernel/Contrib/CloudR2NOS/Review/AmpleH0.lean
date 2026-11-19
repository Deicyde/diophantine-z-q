/-
Copyright (c) 2026 H5/NOS Round-2 Lane6 contributors.
Released under the Apache License, Version 2.0.

NOTICE OF MODIFICATION / PURPOSE (2026-11-14): new actual coherent-cohomology
specialization bridge, using W07 c425's universal finite-free model and its
PROVED minor-based `exists_finrank_homology_pullback_le`. No source file is edited.

This is upper semicontinuity on ACTUAL derived fibre cohomology of a proper
finitely presented family. It does NOT assume projectivity, ampleness, or that
cohomology is concentrated in degree zero. In particular the curve-only
PositiveFamilyCohomology result is NOT used for an arbitrary-dimensional AV.
The same original group-model/invertible-module interface is given below.
No NOS/model existence, CharZero, perfectness or henselianity is assumed.
-/
import ZInQKernel.Contrib.CloudR2NOS.Review.AmpleEuler

set_option autoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace ZInQ.Contrib.CloudR2NOS.Review.AmpleExtension

/-- ACTUAL fibre cohomology can only increase along specialization. The finite
free cohomology model is CONSTRUCTED from properness/finiteness/flatness, not
postulated as a new input or restricted to projective families. -/
theorem hFiber_le_of_specializes {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [LocallyOfFinitePresentation f]
    (M : X.Modules) [M.IsFinitePresentation] (hflat : M.IsFlatOver f)
    (q : ℕ) {x y : S} (hxy : x ⤳ y) : M.hFiber f q x ≤ M.hFiber f q y := by
  haveI : M.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData M).choose.isQuasicoherent
  obtain ⟨U, P, bound, hyU, hP, comparison⟩ :=
    exists_isFiniteFreeComplex_higherDirectImage f M hflat y
  let ry := S.fromSpecResidueField y
  have ryRange : Set.range ry ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι, Scheme.range_fromSpecResidueField]
    exact Set.singleton_subset_iff.mpr hyU
  let gy := IsOpenImmersion.lift U.ι ry ryRange
  have gyFactor : gy ≫ U.ι = ry := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨V, gyRange, upper⟩ := exists_finrank_homology_pullback_le hP.exists_iso_free
    (q : ℤ) (Field.toIsField (S.residueField y)) gy
  let W : S.Opens := U.ι ''ᵁ V
  let py : Spec (S.residueField y) := IsLocalRing.closedPoint _
  have gyImage : U.ι (gy py) = y := by
    rw [← Scheme.Hom.comp_apply, gyFactor]
    exact fromSpecResidueField_base_apply y py
  have hyW : y ∈ W := ⟨gy py, gyRange ⟨py, rfl⟩, gyImage⟩
  have hxW : x ∈ W := hxy.mem_open W.isOpen hyW
  have hxU : x ∈ U := by
    obtain ⟨z, _, hz⟩ := hxW
    exact hz ▸ z.2
  let rx := S.fromSpecResidueField x
  have rxRange : Set.range rx ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι, Scheme.range_fromSpecResidueField]
    exact Set.singleton_subset_iff.mpr hxU
  let gx := IsOpenImmersion.lift U.ι rx rxRange
  have gxFactor : gx ≫ U.ι = rx := IsOpenImmersion.lift_fac _ _ _
  have gxRange : Set.range gx.base ⊆ V := by
    rintro _ ⟨px, rfl⟩
    obtain ⟨z, hzV, hz⟩ := hxW
    have gxImage : U.ι (gx px) = x := by
      rw [← Scheme.Hom.comp_apply, gxFactor]
      exact fromSpecResidueField_base_apply x px
    have he : gx px = z := U.ι.isOpenEmbedding.injective (gxImage.trans hz.symm)
    rw [he]
    exact hzV
  have hxCoh := hFiber_eq_finrank_homology f M comparison gx gxFactor q
  have hyCoh := hFiber_eq_finrank_homology f M comparison gy gyFactor q
  rw [hxCoh, hyCoh]
  exact upper (Field.toIsField (S.residueField x)) gx gxRange

/-- Positivity of the ACTUAL generic H0 dimension implies a nonzero special
section dimension. No generic or special ampleness is inserted into the proof. -/
theorem h0_pos_of_specializes {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [LocallyOfFinitePresentation f]
    (M : X.Modules) [M.IsFinitePresentation] (hflat : M.IsFlatOver f)
    {x y : S} (hxy : x ⤳ y) (hx : 0 < M.hFiber f 0 x) :
    0 < M.hFiber f 0 y :=
  hx.trans_le (hFiber_le_of_specializes f M hflat 0 hxy)

/-- SAME arbitrary-DVR group-model/invertible-module specialization interface.
Smoothness supplies relative flatness. Generic and closed points remain ACTUAL
points of the ORIGINAL Spec O, with their specialization relation explicit. -/
theorem goodModel_h0_pos_of_specializes {K : Type u} [Field K]
    (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (G : Grp (Over (Spec (CommRingCat.of O)))) [PkgI2.IsAbelianScheme G]
    (M : G.X.left.Modules) [M.IsInvertible]
    {genericPoint closedPoint : Spec (CommRingCat.of O)}
    (hsp : genericPoint ⤳ closedPoint) (hx : 0 < M.hFiber G.X.hom 0 genericPoint) :
    0 < M.hFiber G.X.hom 0 closedPoint := by
  haveI : IsProper G.X.hom := PkgI2.IsAbelianScheme.proper
  haveI : Smooth G.X.hom := PkgI2.IsAbelianScheme.smooth
  haveI : M.IsFinitePresentation := isFinitePresentation_of_invertible M
  exact h0_pos_of_specializes G.X.hom M
    (isFlatOver_of_isInvertible G.X.hom M) hsp hx

#print axioms hFiber_le_of_specializes
#print axioms h0_pos_of_specializes
#print axioms goodModel_h0_pos_of_specializes

end ZInQ.Contrib.CloudR2NOS.Review.AmpleExtension
