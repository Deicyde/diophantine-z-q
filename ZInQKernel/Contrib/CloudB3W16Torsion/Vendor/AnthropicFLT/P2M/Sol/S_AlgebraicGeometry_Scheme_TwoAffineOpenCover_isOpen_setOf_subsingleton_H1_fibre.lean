/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_isOpen_setOf_subsingleton_H1_fibre. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_cech_sectionsOf_baseChange_equiv_of_locallyTrivial
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_ofModules_of_locallyTrivial
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_toOrderedAffineCover_iff
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_LinearMap_isOpen_setOf_surjective_baseChange_residueField
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_isOpen_setOf_subsingleton_H1_fibre

set_option autoImplicit false

open scoped TensorProduct

namespace K4Geom

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem nonempty_cokerBaseChangeEquiv {R : Type*} [CommRing R] {C0 C1 : Type*} [AddCommGroup C0] [Module R C0]
    [AddCommGroup C1] [Module R C1] (d : C0 →ₗ[R] C1) (K : Type*) [CommRing K] [Algebra R K] :
    Nonempty (((K ⊗[R] C1) ⧸ LinearMap.range (d.baseChange K)) ≃ₗ[K] K ⊗[R] (C1 ⧸ LinearMap.range d)) := by
  let q : C1 →ₗ[R] C1 ⧸ LinearMap.range d := (LinearMap.range d).mkQ
  let qK : K ⊗[R] C1 →ₗ[K] K ⊗[R] (C1 ⧸ LinearMap.range d) := q.baseChange K
  have hsurj : Function.Surjective qK := by
    rw [show (qK : K ⊗[R] C1 → K ⊗[R] (C1 ⧸ LinearMap.range d)) = LinearMap.lTensor K q from
      LinearMap.baseChange_eq_ltensor q]
    exact LinearMap.lTensor_surjective K (Submodule.mkQ_surjective _)
  have hker : LinearMap.ker qK = LinearMap.range (d.baseChange K) := by
    have h1 : LinearMap.ker (LinearMap.lTensor K q) = LinearMap.range (LinearMap.lTensor K d) := by
      rw [lTensor_mkQ]
      have hd : d = (LinearMap.range d).subtype ∘ₗ d.rangeRestrict := LinearMap.ext fun _ => rfl
      conv_rhs => rw [hd, LinearMap.lTensor_comp]
      rw [LinearMap.range_comp_of_range_eq_top]
      exact LinearMap.range_eq_top.mpr (LinearMap.lTensor_surjective K (LinearMap.surjective_rangeRestrict d))
    ext x
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    have hx : qK x = LinearMap.lTensor K q x := congrFun (LinearMap.baseChange_eq_ltensor q) x
    rw [hx, ← LinearMap.mem_ker, h1, LinearMap.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, (congrFun (LinearMap.baseChange_eq_ltensor d) y)⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, (congrFun (LinearMap.baseChange_eq_ltensor d) y).symm⟩
  exact ⟨(Submodule.quotEquivOfEq _ _ hker.symm).trans (qK.quotKerEquivOfSurjective hsurj)⟩

theorem surjective_baseChange_iff {R : Type*} [CommRing R] {C0 C1 : Type*} [AddCommGroup C0] [Module R C0]
    [AddCommGroup C1] [Module R C1] (d : C0 →ₗ[R] C1) (K : Type*) [CommRing K] [Algebra R K] :
    Function.Surjective (d.baseChange K) ↔ Subsingleton (K ⊗[R] (C1 ⧸ LinearMap.range d)) := by
  obtain ⟨e⟩ := nonempty_cokerBaseChangeEquiv d K
  rw [← e.toEquiv.subsingleton_congr, Submodule.Quotient.subsingleton_iff, LinearMap.range_eq_top]

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of A)) [IsProper c]
  (𝒱 : C.TwoAffineOpenCover) (M : C.Modules) (hM : Scheme.Modules.IsInvertible M)

include hM in

theorem finite_H1 : Module.Finite A (𝒱.sectionsOf c M).H1 := by
  have hcf := OModulePresheaf.cechFinite_ofModules_of_locallyTrivial c M hM.1 𝒱.toOrderedAffineCover
  exact ((OModulePresheaf.cechFinite_toOrderedAffineCover_iff _ _).mp hcf).2

include hM in
theorem iff_pair (𝔭 : PrimeSpectrum A) :
    (Subsingleton
        ((𝒱.pullback c 𝔭.asIdeal.ResidueField).sectionsOf (pullback.snd c (Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField)) ((Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField))).obj M)).H1 ↔
      Function.Surjective ((𝒱.sectionsOf c M).cechDiff.baseChange 𝔭.asIdeal.ResidueField)) ∧
    (Subsingleton
        ((𝒱.pullback c 𝔭.asIdeal.ResidueField).sectionsOf (pullback.snd c (Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField)) ((Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField))).obj M)).H1 ↔
      𝔭 ∉ Module.support A (𝒱.sectionsOf c M).H1) := by
  obtain ⟨⟨eH1⟩, -, -⟩ :=
    Scheme.TwoAffineOpenCover.exists_cech_sectionsOf_baseChange_equiv_of_locallyTrivial 𝒱 c M hM.1 𝔭.asIdeal.ResidueField
  have e1 : Subsingleton ((𝒱.pullback c 𝔭.asIdeal.ResidueField).sectionsOf (pullback.snd c (Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField)) ((Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField))).obj M)).H1 ↔ Subsingleton (𝔭.asIdeal.ResidueField ⊗[A] (𝒱.sectionsOf c M).H1) :=
    eH1.toEquiv.subsingleton_congr
  haveI := finite_H1 c 𝒱 M hM
  refine ⟨e1.trans (surjective_baseChange_iff _ _).symm, e1.trans ?_⟩
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct, not_nontrivial_iff_subsingleton]

include hM in
theorem isOpen :
    IsOpen {𝔭 : PrimeSpectrum A | Subsingleton
      ((𝒱.pullback c 𝔭.asIdeal.ResidueField).sectionsOf (pullback.snd c (Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField)) ((Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField))).obj M)).H1} := by
  haveI := finite_H1 c 𝒱 M hM
  have h : {𝔭 : PrimeSpectrum A | Subsingleton ((𝒱.pullback c 𝔭.asIdeal.ResidueField).sectionsOf (pullback.snd c (Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField)) ((Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField))).obj M)).H1} =
      {𝔭 : PrimeSpectrum A | Function.Surjective ((𝒱.sectionsOf c M).cechDiff.baseChange 𝔭.asIdeal.ResidueField)} := by
    ext 𝔭
    exact (iff_pair c 𝒱 M hM 𝔭).1
  rw [h]
  exact LinearMap.isOpen_setOf_surjective_baseChange_residueField _

end K4Geom

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct in

theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of A)) [IsProper c]
    (𝒱 : C.TwoAffineOpenCover) (M : C.Modules) (hM : Scheme.Modules.IsInvertible M) :
    IsOpen {𝔭 : PrimeSpectrum A | Subsingleton
      ((𝒱.pullback c 𝔭.asIdeal.ResidueField).sectionsOf (pullback.snd c (Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField)) ((Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField))).obj M)).H1} :=
  K4Geom.isOpen c 𝒱 M hM
