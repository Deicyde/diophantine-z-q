/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_bijective_kerBaseChangeHom_and_surjective_unit_app_of_subsingleton_H1. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_TwoChartCech_Mumford_projective_ker_of_fibre_surjective
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_projective_sections_of_locallyTrivial
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_ofModules_of_locallyTrivial
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_toOrderedAffineCover_iff
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_sectionsOf_baseChange_equiv_of_locallyTrivial
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_H0
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_bijective_kerBaseChangeHom_and_surjective_unit_app_of_subsingleton_H1

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Opposite

namespace BCH0

theorem flat_prod (R : Type u) [CommRing R] (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] [Module.Flat R M] [Module.Flat R N] : Module.Flat R (M × N) := by
  rw [Module.Flat.iff_rTensor_injectiveₛ]
  intro P _ _ Q
  have h1 : Function.Injective (Q.subtype.rTensor M) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ Q.subtype_injective
  have h2 : Function.Injective (Q.subtype.rTensor N) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ Q.subtype_injective
  have key : (TensorProduct.prodRight R R P M N).toLinearMap ∘ₗ Q.subtype.rTensor (M × N) =
      (LinearMap.prodMap (Q.subtype.rTensor M) (Q.subtype.rTensor N)) ∘ₗ
        (TensorProduct.prodRight R R Q M N).toLinearMap := by
    apply TensorProduct.ext'
    intro q mn
    simp [LinearMap.rTensor_tmul]
  intro x y hxy
  apply (TensorProduct.prodRight R R Q M N).injective
  have := congrArg (TensorProduct.prodRight R R P M N) hxy
  have hx := LinearMap.congr_fun key x
  have hy := LinearMap.congr_fun key y
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply] at hx hy
  rw [hx, hy] at this
  exact (h1.prodMap h2) this

theorem flat_sections {R : Type u} [CommRing R] {X : Scheme.{u}} (c : X ⟶ Spec (.of R)) [Flat c]
    (U : X.Opens) (hU : IsAffineOpen U) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    Module.Flat R Γ(X, U) := by
  have h1 : (c.appLE ⊤ U le_top).hom.Flat :=
    Flat.flat_appLE c (isAffineOpen_top (Spec (.of R))) hU le_top
  have h2 : ((Scheme.ΓSpecIso (.of R)).inv).hom.Flat :=
    RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv)
  exact RingHom.Flat.comp h2 h1

end BCH0

open BCH0 in
theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover)
    (c : X ⟶ Spec (.of R)) [IsProper c] [Flat c] (M : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (hfib : ∀ (K : Type u) [Field K] [Algebra R K],
      Subsingleton ((𝒱.pullback c K).sectionsOf (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K))
        ((Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R K))).obj M)).H1) :
    Module.Finite R (𝒱.sectionsOf c M).H0 ∧ Module.Projective R (𝒱.sectionsOf c M).H0 ∧
    (∀ (A : Type u) [CommRing A] [Algebra R A],
      Function.Bijective (TwoChartCech.kerBaseChangeHom (𝒱.sectionsOf c M).cechDiff A)) ∧
    (∀ (A : Type u) [CommRing A] [Algebra R A], Function.Surjective (algebraMap R A) →
      Function.Surjective
        (((Scheme.Modules.pullbackPushforwardAdjunction
          (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).unit.app M).app ⊤).hom) := by

  haveI hfl0 : Module.Flat R (𝒱.sectionsOf c M).M0 := by
    haveI : Module.Flat R (𝒱.cover c).A0 := flat_sections c 𝒱.U0 𝒱.isAffineOpen_U0
    haveI : Module.Projective (𝒱.cover c).A0 (𝒱.sectionsOf c M).M0 :=
      Scheme.Modules.projective_sections_of_locallyTrivial M htriv ⟨𝒱.U0, 𝒱.isAffineOpen_U0⟩
    exact Module.Flat.trans R (𝒱.cover c).A0 (𝒱.sectionsOf c M).M0
  haveI hfl1 : Module.Flat R (𝒱.sectionsOf c M).M1 := by
    haveI : Module.Flat R (𝒱.cover c).A1 := flat_sections c 𝒱.U1 𝒱.isAffineOpen_U1
    haveI : Module.Projective (𝒱.cover c).A1 (𝒱.sectionsOf c M).M1 :=
      Scheme.Modules.projective_sections_of_locallyTrivial M htriv ⟨𝒱.U1, 𝒱.isAffineOpen_U1⟩
    exact Module.Flat.trans R (𝒱.cover c).A1 (𝒱.sectionsOf c M).M1
  haveI hfl01 : Module.Flat R (𝒱.sectionsOf c M).M01 := by
    haveI : Module.Flat R (𝒱.cover c).A01 := flat_sections c (𝒱.U0 ⊓ 𝒱.U1) 𝒱.isAffineOpen_inf
    haveI : Module.Projective (𝒱.cover c).A01 (𝒱.sectionsOf c M).M01 :=
      Scheme.Modules.projective_sections_of_locallyTrivial M htriv ⟨𝒱.U0 ⊓ 𝒱.U1, 𝒱.isAffineOpen_inf⟩
    exact Module.Flat.trans R (𝒱.cover c).A01 (𝒱.sectionsOf c M).M01
  haveI : Module.Flat R ((𝒱.sectionsOf c M).M0 × (𝒱.sectionsOf c M).M1) := flat_prod R (𝒱.sectionsOf c M).M0 (𝒱.sectionsOf c M).M1

  have hfin := (OModulePresheaf.cechFinite_toOrderedAffineCover_iff (OModulePresheaf.ofModules c M) 𝒱).mp
    (OModulePresheaf.cechFinite_ofModules_of_locallyTrivial c M htriv 𝒱.toOrderedAffineCover)
  haveI : Module.Finite R (LinearMap.ker (𝒱.sectionsOf c M).cechDiff) := hfin.1
  haveI : Module.Finite R ((𝒱.sectionsOf c M).M01 ⧸ LinearMap.range (𝒱.sectionsOf c M).cechDiff) := hfin.2

  have hinl : (𝒱.sectionsOf c M).cechDiff ∘ₗ LinearMap.inl R (𝒱.sectionsOf c M).M0 (𝒱.sectionsOf c M).M1 = -(𝒱.sectionsOf c M).r0 := LinearMap.coprod_inl _ _
  have hinr : (𝒱.sectionsOf c M).cechDiff ∘ₗ LinearMap.inr R (𝒱.sectionsOf c M).M0 (𝒱.sectionsOf c M).M1 = (𝒱.sectionsOf c M).r1 := LinearMap.coprod_inr _ _

  have hcomp : ∀ (A : Type u) [CommRing A] [Algebra R A]
      (e0 : A ⊗[R] (𝒱.sectionsOf c M).M0 ≃ₗ[A] ((𝒱.pullback c A).sectionsOf (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))
            ((Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).M0)
      (e1 : A ⊗[R] (𝒱.sectionsOf c M).M1 ≃ₗ[A] ((𝒱.pullback c A).sectionsOf (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))
            ((Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).M1)
      (e01 : A ⊗[R] (𝒱.sectionsOf c M).M01 ≃ₗ[A] ((𝒱.pullback c A).sectionsOf (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))
            ((Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).M01),
      (∀ x, e01 (((𝒱.sectionsOf c M).r0.baseChange A) x) = ((𝒱.pullback c A).sectionsOf (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))
            ((Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).r0 (e0 x)) →
      (∀ x, e01 (((𝒱.sectionsOf c M).r1.baseChange A) x) = ((𝒱.pullback c A).sectionsOf (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))
            ((Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).r1 (e1 x)) →
      ∀ (a : A ⊗[R] (𝒱.sectionsOf c M).M0) (b : A ⊗[R] (𝒱.sectionsOf c M).M1),
        e01 ((𝒱.sectionsOf c M).cechDiff.baseChange A ((LinearMap.inl R (𝒱.sectionsOf c M).M0 (𝒱.sectionsOf c M).M1).baseChange A a +
          (LinearMap.inr R (𝒱.sectionsOf c M).M0 (𝒱.sectionsOf c M).M1).baseChange A b)) =
        ((𝒱.pullback c A).sectionsOf (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))
            ((Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).cechDiff
          (e0 a, e1 b) := by
    intro A _ _ e0 e1 e01 hr0 hr1 a b
    have h1 : (𝒱.sectionsOf c M).cechDiff.baseChange A ((LinearMap.inl R (𝒱.sectionsOf c M).M0 (𝒱.sectionsOf c M).M1).baseChange A a) = -((𝒱.sectionsOf c M).r0.baseChange A a) := by
      rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hinl, LinearMap.baseChange_neg, LinearMap.neg_apply]
    have h2 : (𝒱.sectionsOf c M).cechDiff.baseChange A ((LinearMap.inr R (𝒱.sectionsOf c M).M0 (𝒱.sectionsOf c M).M1).baseChange A b) = (𝒱.sectionsOf c M).r1.baseChange A b := by
      rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hinr]
    rw [map_add, h1, h2, map_add, map_neg, hr0, hr1, TwoChartCech.Sections.cechDiff_apply]
    abel

  have hH1 : ∀ (K : Type u) [Field K] [Algebra R K], Function.Surjective ((𝒱.sectionsOf c M).cechDiff.baseChange K) := by
    intro K _ _
    obtain ⟨e0, e1, e01, hr0, hr1, -, -, -⟩ :=
      Scheme.TwoAffineOpenCover.exists_sectionsOf_baseChange_equiv_of_locallyTrivial 𝒱 c M htriv K
    have hsurjK := (hfib K)
    rw [Submodule.Quotient.subsingleton_iff, LinearMap.range_eq_top] at hsurjK
    intro y
    obtain ⟨⟨a, b⟩, hab⟩ := hsurjK (e01 y)
    obtain ⟨a', rfl⟩ := e0.surjective a
    obtain ⟨b', rfl⟩ := e1.surjective b
    refine ⟨(LinearMap.inl R (𝒱.sectionsOf c M).M0 (𝒱.sectionsOf c M).M1).baseChange K a' + (LinearMap.inr R (𝒱.sectionsOf c M).M0 (𝒱.sectionsOf c M).M1).baseChange K b', ?_⟩
    apply e01.injective
    rw [hcomp K e0 e1 e01 hr0 hr1 a' b', hab]
  obtain ⟨hproj, hbij, -⟩ := TwoChartCech.Mumford.projective_ker_of_fibre_surjective (𝒱.sectionsOf c M).cechDiff hH1
  refine ⟨hfin.1, hproj, hbij, ?_⟩

  intro A _ _ hA
  obtain ⟨e0, e1, e01, hr0, hr1, hu0, hu1, -⟩ :=
    Scheme.TwoAffineOpenCover.exists_sectionsOf_baseChange_equiv_of_locallyTrivial 𝒱 c M htriv A
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c M ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))
    ((Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).obj M) ⊤
  obtain ⟨eX, heX⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 𝒱 c M
  obtain ⟨eXA, heXA⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 (𝒱.pullback c A)
    (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))
    ((Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).obj M)
  intro s'

  have hz0 : (𝒱.sectionsOf c M).cechDiff.baseChange A
      ((LinearMap.inl R (𝒱.sectionsOf c M).M0 (𝒱.sectionsOf c M).M1).baseChange A (e0.symm (eXA s' : ((𝒱.pullback c A).sectionsOf (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ((Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).M0 × ((𝒱.pullback c A).sectionsOf (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ((Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).M1).1) +
        (LinearMap.inr R (𝒱.sectionsOf c M).M0 (𝒱.sectionsOf c M).M1).baseChange A (e1.symm (eXA s' : ((𝒱.pullback c A).sectionsOf (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ((Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).M0 × ((𝒱.pullback c A).sectionsOf (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ((Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).M1).2)) = 0 := by
    apply e01.injective
    rw [hcomp A e0 e1 e01 hr0 hr1, map_zero, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
      Prod.mk.eta]
    exact (eXA s').2
  obtain ⟨w, hw⟩ := (hbij A).2 ⟨_, hz0⟩
  obtain ⟨h, rfl⟩ := TensorProduct.mk_surjective R (LinearMap.ker (𝒱.sectionsOf c M).cechDiff) A hA w
  obtain ⟨s, rfl⟩ := eX.surjective h
  refine ⟨s, ?_⟩

  have hz1 : (LinearMap.inl R (𝒱.sectionsOf c M).M0 (𝒱.sectionsOf c M).M1).baseChange A (e0.symm (eXA s' : ((𝒱.pullback c A).sectionsOf (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ((Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).M0 × ((𝒱.pullback c A).sectionsOf (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ((Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).M1).1) +
        (LinearMap.inr R (𝒱.sectionsOf c M).M0 (𝒱.sectionsOf c M).M1).baseChange A (e1.symm (eXA s' : ((𝒱.pullback c A).sectionsOf (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ((Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).M0 × ((𝒱.pullback c A).sectionsOf (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ((Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).M1).2) =
      (1 : A) ⊗ₜ[R] ((eX s : (𝒱.sectionsOf c M).H0) : (𝒱.sectionsOf c M).M0 × (𝒱.sectionsOf c M).M1) := by
    have := congrArg Subtype.val hw
    rw [TwoChartCech.kerBaseChangeHom_apply_coe] at this
    simpa using this.symm
  have hfst_inl : ∀ x, (LinearMap.fst R (𝒱.sectionsOf c M).M0 (𝒱.sectionsOf c M).M1).baseChange A ((LinearMap.inl R (𝒱.sectionsOf c M).M0 (𝒱.sectionsOf c M).M1).baseChange A x) = x := by
    intro x; rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, LinearMap.fst_comp_inl,
      LinearMap.baseChange_id, LinearMap.id_apply]
  have hfst_inr : ∀ x, (LinearMap.fst R (𝒱.sectionsOf c M).M0 (𝒱.sectionsOf c M).M1).baseChange A ((LinearMap.inr R (𝒱.sectionsOf c M).M0 (𝒱.sectionsOf c M).M1).baseChange A x) = 0 := by
    intro x; rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, LinearMap.fst_comp_inr,
      LinearMap.baseChange_zero, LinearMap.zero_apply]
  have hsnd_inl : ∀ x, (LinearMap.snd R (𝒱.sectionsOf c M).M0 (𝒱.sectionsOf c M).M1).baseChange A ((LinearMap.inl R (𝒱.sectionsOf c M).M0 (𝒱.sectionsOf c M).M1).baseChange A x) = 0 := by
    intro x; rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, LinearMap.snd_comp_inl,
      LinearMap.baseChange_zero, LinearMap.zero_apply]
  have hsnd_inr : ∀ x, (LinearMap.snd R (𝒱.sectionsOf c M).M0 (𝒱.sectionsOf c M).M1).baseChange A ((LinearMap.inr R (𝒱.sectionsOf c M).M0 (𝒱.sectionsOf c M).M1).baseChange A x) = x := by
    intro x; rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, LinearMap.snd_comp_inr,
      LinearMap.baseChange_id, LinearMap.id_apply]
  have ha1 : e0.symm (eXA s' : ((𝒱.pullback c A).sectionsOf (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ((Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).M0 × ((𝒱.pullback c A).sectionsOf (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ((Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).M1).1 = (1 : A) ⊗ₜ[R] ((eX s : (𝒱.sectionsOf c M).H0) : (𝒱.sectionsOf c M).M0 × (𝒱.sectionsOf c M).M1).1 := by
    have := congrArg ((LinearMap.fst R (𝒱.sectionsOf c M).M0 (𝒱.sectionsOf c M).M1).baseChange A) hz1
    rwa [map_add, hfst_inl, hfst_inr, add_zero, LinearMap.baseChange_tmul] at this
  have hb1 : e1.symm (eXA s' : ((𝒱.pullback c A).sectionsOf (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ((Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).M0 × ((𝒱.pullback c A).sectionsOf (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ((Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).M1).2 = (1 : A) ⊗ₜ[R] ((eX s : (𝒱.sectionsOf c M).H0) : (𝒱.sectionsOf c M).M0 × (𝒱.sectionsOf c M).M1).2 := by
    have := congrArg ((LinearMap.snd R (𝒱.sectionsOf c M).M0 (𝒱.sectionsOf c M).M1).baseChange A) hz1
    rwa [map_add, hsnd_inl, hsnd_inr, zero_add, LinearMap.baseChange_tmul] at this

  apply eXA.injective
  apply Subtype.ext
  apply Prod.ext
  · have e1' : (eXA s' : ((𝒱.pullback c A).sectionsOf (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ((Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).M0 × ((𝒱.pullback c A).sectionsOf (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ((Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).M1).1 = e0 ((1 : A) ⊗ₜ[R] ((eX s : (𝒱.sectionsOf c M).H0) : (𝒱.sectionsOf c M).M0 × (𝒱.sectionsOf c M).M1).1) := by
      rw [← ha1, LinearEquiv.apply_symm_apply]
    rw [e1', heX, hu0, heXA]

    have nat := ((Scheme.Modules.pullbackPushforwardAdjunction
      (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).unit.app M).mapPresheaf.naturality
      (homOfLE (le_top : 𝒱.U0 ≤ ⊤)).op
    have nat' := congrArg (fun φ => φ.hom s) nat
    simp only [Scheme.Modules.mapPresheaf_app, unop_op] at nat'
    exact nat'.symm
  · have e2' : (eXA s' : ((𝒱.pullback c A).sectionsOf (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ((Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).M0 × ((𝒱.pullback c A).sectionsOf (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ((Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).M1).2 = e1 ((1 : A) ⊗ₜ[R] ((eX s : (𝒱.sectionsOf c M).H0) : (𝒱.sectionsOf c M).M0 × (𝒱.sectionsOf c M).M1).2) := by
      rw [← hb1, LinearEquiv.apply_symm_apply]
    rw [e2', heX, hu1, heXA]
    have nat := ((Scheme.Modules.pullbackPushforwardAdjunction
      (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).unit.app M).mapPresheaf.naturality
      (homOfLE (le_top : 𝒱.U1 ≤ ⊤)).op
    have nat' := congrArg (fun φ => φ.hom s) nat
    simp only [Scheme.Modules.mapPresheaf_app, unop_op] at nat'
    exact nat'.symm
