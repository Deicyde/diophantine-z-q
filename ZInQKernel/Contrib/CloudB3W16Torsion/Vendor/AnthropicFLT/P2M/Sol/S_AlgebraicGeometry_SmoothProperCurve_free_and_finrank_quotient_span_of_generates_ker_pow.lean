/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_SmoothProperCurve_free_and_finrank_quotient_span_of_generates_ker_pow. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_SmoothProperCurve_free_and_finrank_quotient_span_of_generates_ker_pow

set_option autoImplicit false

universe u

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ORDERRANK

theorem main
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c]
    (ε : NeronModelInfra.SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (m : ℕ) (hm : 1 ≤ m)
    (V : C.Opens) (hV : IsAffineOpen V) (hεV : ∀ x ∈ Set.range ε.1.base, x ∈ V) (g : Γ(C, V))
    (hg : ∀ W : C.affineOpens, ∀ hW : (W : C.Opens) ≤ V,
      (ε.1.ker ^ m).ideal W = Ideal.span {(C.presheaf.map (homOfLE hW).op).hom g}) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c V
    Module.Free R (Γ(C, V) ⧸ Ideal.span {g}) ∧ Module.finrank R (Γ(C, V) ⧸ Ideal.span {g}) = m := by
  letI algV := Scheme.TwoAffineOpenCover.algebraOfHom c V

  let I : C.IdealSheafData := ε.1.ker ^ m
  let Z := I.subscheme
  let ι : Z ⟶ C := I.subschemeι
  obtain ⟨hfin, hrank, hflat, -⟩ :=
    AlgebraicGeometry.Scheme.Hom.isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id (p := c) ε.1 ε.2 m
  change IsFinite (ι ≫ c) at hfin
  change ∀ t, (ι ≫ c).finrank t = m at hrank
  change Flat (ι ≫ c) at hflat
  haveI := hfin
  haveI := hflat

  haveI : IsClosedImmersion (ε.1 ≫ c) := by rw [ε.2]; infer_instance
  haveI : IsClosedImmersion ε.1 := IsClosedImmersion.of_comp ε.1 c
  have hsupp : (I.support : Set C) = Set.range ε.1.base := by
    show ((ε.1.ker ^ m).support : Set C) = _
    rw [Scheme.IdealSheafData.support_pow _ m (by omega), Scheme.Hom.support_ker,
      ε.1.isClosedEmbedding.isClosed_range.closure_eq]
  have hZV : (⊤ : Z.Opens) ≤ ι ⁻¹ᵁ V := by
    intro z _
    show ι.base z ∈ V
    apply hεV
    rw [← hsupp, ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨z, rfl⟩

  let W : C.affineOpens := ⟨V, hV⟩
  have hIV : I.ideal W = Ideal.span {g} := by
    have := hg W le_rfl
    have hid : (C.presheaf.map (homOfLE (le_rfl : (W : C.Opens) ≤ V)).op).hom g = g := by
      have : homOfLE (le_rfl : (W : C.Opens) ≤ V) = 𝟙 _ := Subsingleton.elim _ _
      rw [this, op_id, CategoryTheory.Functor.map_id]; rfl
    rw [hid] at this
    exact this

  haveI : IsAffine Z := isAffine_of_isAffineHom (ι ≫ c)
  have hcmp := IsAffineOpen.SpecMap_appLE_fromSpec (ι ≫ c) (isAffineOpen_top _) (isAffineOpen_top Z)
    (le_top : (⊤ : Z.Opens) ≤ (ι ≫ c) ⁻¹ᵁ ⊤)
  rw [IsAffineOpen.fromSpec_top, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at hcmp

  have happ : (ι ≫ c).appLE ⊤ ⊤ le_top = c.appLE ⊤ V le_top ≫ ι.appLE V ⊤ hZV :=
    (Scheme.Hom.appLE_comp_appLE ι c ⊤ V ⊤ le_top hZV).symm
  have happ2 : ι.appLE V ⊤ hZV = ι.app V ≫ Z.presheaf.map (homOfLE hZV).op := rfl

  have happ3 : ι.app V = CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal W)) ≫ (I.subschemeObjIso W).inv :=
    I.subschemeι_app W

  have htop : ι ⁻¹ᵁ V = ⊤ := le_antisymm le_top hZV
  haveI : IsIso (Z.presheaf.map (homOfLE hZV).op) := by
    have : homOfLE hZV = eqToHom htop.symm := Subsingleton.elim _ _
    rw [this, eqToHom_op]
    infer_instance

  let A' := Γ(C, V) ⧸ I.ideal W
  have halg : CommRingCat.ofHom (algebraMap R A') =
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ c.appLE ⊤ V le_top) ≫
        CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal W)) := by
    ext r
    rfl
  let ψ : CommRingCat.of A' ⟶ Γ(Z, ⊤) := (I.subschemeObjIso W).inv ≫ Z.presheaf.map (homOfLE hZV).op
  haveI : IsIso ψ := IsIso.comp_isIso
  have hkey : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (ι ≫ c).appLE ⊤ ⊤ le_top =
      CommRingCat.ofHom (algebraMap R A') ≫ ψ := by
    show _ = _ ≫ ((I.subschemeObjIso W).inv ≫ Z.presheaf.map (homOfLE hZV).op)
    rw [happ, happ2, happ3, halg]
    simp only [Category.assoc]
  have hιc : ι ≫ c = (Z.isoSpec.hom ≫ Spec.map ψ) ≫ Spec.map (CommRingCat.ofHom (algebraMap R A')) := by
    have h1 : Z.isoSpec.inv ≫ (ι ≫ c) =
        Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (ι ≫ c).appLE ⊤ ⊤ le_top) := by
      rw [Spec.map_comp, hcmp]
    rw [hkey, Spec.map_comp] at h1
    rw [Category.assoc, ← h1, Iso.hom_inv_id_assoc]

  haveI hfinA : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R A'))) := by
    have := hfin; rw [hιc] at this
    exact (MorphismProperty.cancel_left_of_respectsIso @IsFinite _ _).mp this
  haveI hflatA : Flat (Spec.map (CommRingCat.ofHom (algebraMap R A'))) := by
    have := hflat; rw [hιc] at this
    exact (MorphismProperty.cancel_left_of_respectsIso @Flat _ _).mp this
  haveI : Module.Finite R A' := by
    have := (IsFinite.SpecMap_iff _).mp hfinA
    exact (RingHom.finite_algebraMap).mp this
  haveI : Module.Flat R A' := by
    have := (Flat.SpecMap_iff).mp hflatA
    exact (RingHom.flat_algebraMap_iff).mp this
  haveI : Module.Free R A' := Module.free_of_flat_of_isLocalRing
  have hrankA : Module.finrank R A' = m := by
    have h := hrank (IsLocalRing.closedPoint R)
    rw [hιc, Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_SpecMap_algebraMap,
      Module.rankAtStalk_eq_finrank_of_free] at h
    exact h

  let e : A' ≃ₐ[R] Γ(C, V) ⧸ Ideal.span {g} := Ideal.quotientEquivAlgOfEq R hIV
  refine ⟨Module.Free.of_equiv e.toLinearEquiv, ?_⟩
  rw [← e.toLinearEquiv.finrank_eq, hrankA]

end ORDERRANK

open scoped TensorProduct in
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve NeronModelInfra in

theorem solution
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (m : ℕ) (hm : 1 ≤ m)
    (V : C.Opens) (hV : IsAffineOpen V) (hεV : ∀ x ∈ Set.range ε.1.base, x ∈ V) (g : Γ(C, V))
    (hg : ∀ W : C.affineOpens, ∀ hW : (W : C.Opens) ≤ V,
      (ε.1.ker ^ m).ideal W = Ideal.span {(C.presheaf.map (homOfLE hW).op).hom g}) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c V
    Module.Free R (Γ(C, V) ⧸ Ideal.span {g}) ∧ Module.finrank R (Γ(C, V) ⧸ Ideal.span {g}) = m :=
  ORDERRANK.main R c ε m hm V hV hεV g hg
