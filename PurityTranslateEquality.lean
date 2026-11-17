/-
Copyright (c) 2026 H5 contributors. Apache-2.0.
EXACT C3 B2.d2 PurityTranslateEquality.{u}, native SOURCE ONLY / UNCOMPILED.
Actual A/D/phi/E/F stay unchanged. The theorem works for the GIVEN scheme
isomorphism, not only translations or reflections, and needs no group-
homomorphism claim about a translation. All point/ring maps are explicit.

Maximality in the closed support derives closedness and generic-point
minimality. Native Krull PIT on the actual nonzerodivisor local equation
makes both generic stalks codimension1. The phi-stalk RING ISOMORPHISM
preserves that dimension. A strict specialization of codimension-one
points contradicts the native affine prime-height inequality; no
catenarity, ampleness, finite-kernel/curve or multiplicity Fact is used.
-/
import ZInQKernel.Contrib.CloudR2NOS.Step2B2.PurityInterface
import NativeCartierCodimension

set_option autoImplicit false
noncomputable section
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace H5OriginalDVR.Lane5.I0Native

/-- EXACT C3 d2 consumer; all codimension/purity data are derived internally. -/
theorem purityTranslateEquality :
    ZInQ.Contrib.CloudR2NOS.Step2B2.PurityTranslateEquality.{u} := by
  intro K _ _ A _ D hD φ _ E F hE hF hsub
  letI : IsProper A.X.hom := PkgI2.IsAbelianVariety.proper
  letI : IsLocallyNoetherian A.X.left :=
    LocallyOfFiniteType.isLocallyNoetherian A.X.hom
  letI : CompactSpace A.X.left := QuasiCompact.compactSpace_of_compactSpace A.X.hom
  letI : IsNoetherian A.X.left := {}
  have hEclosed : IsClosed E :=
    maximal_irreducible_subset_closed (D.support : Set A.X.left) E D.support.isClosed hE
  have hFclosed : IsClosed F :=
    maximal_irreducible_subset_closed (D.support : Set A.X.left) F D.support.isClosed hF
  obtain ⟨x, hx⟩ := QuasiSober.sober hE.1.2 hEclosed
  obtain ⟨y, hy⟩ := QuasiSober.sober hF.1.2 hFclosed
  have hdx : ringKrullDim (A.X.left.presheaf.stalk x) = 1 :=
    cartier_stalk_dim_one_of_no_generization D hD x (hE.1.1 hx.mem)
      (fun z hz hzx => maximal_generic_no_generization
        (D.support : Set A.X.left) E D.support.isClosed hE x hx z hz hzx)
  have hdy : ringKrullDim (A.X.left.presheaf.stalk y) = 1 :=
    cartier_stalk_dim_one_of_no_generization D hD y (hF.1.1 hy.mem)
      (fun z hz hzy => maximal_generic_no_generization
        (D.support : Set A.X.left) F D.support.isClosed hF y hy z hz hzy)
  let e : A.X.left ≃ₜ A.X.left := TopCat.homeoOfIso (asIso φ.base)
  let x' : A.X.left := e.symm x
  have himage : e.symm '' E = φ ⁻¹' E := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      change e (e.symm w) ∈ E
      rwa [e.apply_symm_apply]
    · intro hz
      change e z ∈ E at hz
      exact ⟨e z, hz, e.symm_apply_apply z⟩
  have hGclosed : IsClosed (φ ⁻¹' E) := hEclosed.preimage φ.continuous
  have hxG : IsGenericPoint x' (φ ⁻¹' E) := by
    change IsGenericPoint (e.symm x) (φ ⁻¹' E)
    simpa only [himage, hGclosed.closure_eq] using hx.image e.symm.continuous
  have hφx : φ x' = x := e.apply_symm_apply x
  have hdphi := ringKrullDim_eq_of_ringEquiv
    (asIso (φ.stalkMap x')).commRingCatIsoToRingEquiv
  rw [hφx, hdx] at hdphi
  have hdx' : ringKrullDim (A.X.left.presheaf.stalk x') = 1 := hdphi.symm
  have hyx' : y ⤳ x' := hy.specializes (hsub hxG.mem)
  have heq : y = x' := stalk_dim_one_specialization_eq x' y hyx' hdx' hdy
  calc φ ⁻¹' E = closure ({x'} : Set A.X.left) := hxG.symm
    _ = closure ({y} : Set A.X.left) :=
      congrArg (fun z : A.X.left => closure ({z} : Set A.X.left)) heq.symm
    _ = F := hy

end H5OriginalDVR.Lane5.I0Native
