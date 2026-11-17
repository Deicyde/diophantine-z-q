/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_isLocallyConstant_finrank_ker_sub_finrank_coker_cechDiff_baseChange. Apache-2.0.
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
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_TwoChartCech_isLocallyConstant_fibreEulerChar
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_flat_sections_of_flat
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_projective_sections_of_locallyTrivial
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_ofModules_of_locallyTrivial
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_toOrderedAffineCover_iff
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_isLocallyConstant_finrank_ker_sub_finrank_coker_cechDiff_baseChange

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

namespace ChiLocallyConstant

theorem flat_prod {R : Type*} [CommRing R] (M N : Type*) [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] [Module.Flat R M] [Module.Flat R N] : Module.Flat R (M × N) := by
  rw [Module.Flat.iff_lTensor_injective']
  intro I
  have hM := (Module.Flat.iff_lTensor_injective'.mp (inferInstance : Module.Flat R M)) I
  have hN := (Module.Flat.iff_lTensor_injective'.mp (inferInstance : Module.Flat R N)) I
  have key' : ∀ (p : M × N) (i : I), TensorProduct.prodLeft R R M N R (LinearMap.lTensor (M × N) I.subtype (p ⊗ₜ i)) =
      ((LinearMap.lTensor M I.subtype).prodMap (LinearMap.lTensor N I.subtype)) (TensorProduct.prodLeft R R M N I (p ⊗ₜ i)) := by
    intro p i
    obtain ⟨m, n⟩ := p
    simp [TensorProduct.prodLeft_tmul, LinearMap.lTensor_tmul]
  have key : ∀ x, TensorProduct.prodLeft R R M N R (LinearMap.lTensor (M × N) I.subtype x) =
      ((LinearMap.lTensor M I.subtype).prodMap (LinearMap.lTensor N I.subtype)) (TensorProduct.prodLeft R R M N I x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul p i => exact key' p i
  intro x y hxy
  apply (TensorProduct.prodLeft R R M N I).injective
  have hxy' := congrArg (TensorProduct.prodLeft R R M N R) hxy
  rw [key, key] at hxy'
  have h1 := congrArg Prod.fst hxy'
  have h2 := congrArg Prod.snd hxy'
  simp only [LinearMap.prodMap_apply] at h1 h2
  exact Prod.ext (hM h1) (hN h2)

end ChiLocallyConstant

theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of A))
    [IsProper c] [Flat c] (𝒱 : C.TwoAffineOpenCover) (M : C.Modules) (hM : Scheme.Modules.IsInvertible M) :
    IsLocallyConstant fun 𝔭 : PrimeSpectrum A =>
      (Module.finrank 𝔭.asIdeal.ResidueField
          (LinearMap.ker ((𝒱.sectionsOf c M).cechDiff.baseChange 𝔭.asIdeal.ResidueField)) : ℤ) -
        Module.finrank 𝔭.asIdeal.ResidueField
          ((𝔭.asIdeal.ResidueField ⊗[A] (𝒱.sectionsOf c M).M01) ⧸
            LinearMap.range ((𝒱.sectionsOf c M).cechDiff.baseChange 𝔭.asIdeal.ResidueField)) := by

  have flatOf : ∀ (U : C.Opens) (hU : IsAffineOpen U),
      letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c M U
      Module.Flat A Γ(M, U) := by
    intro U hU
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c M U
    haveI := Scheme.TwoAffineOpenCover.isScalarTower_sections c M U
    haveI : Module.Flat A Γ(C, U) := Scheme.TwoAffineOpenCover.flat_sections_of_flat c U hU
    haveI : Module.Projective Γ(C, U) Γ(M, U) :=
      Scheme.Modules.projective_sections_of_locallyTrivial _ hM.1 ⟨U, hU⟩
    exact Module.Flat.trans A Γ(C, U) Γ(M, U)
  haveI : Module.Flat A (𝒱.sectionsOf c M).M0 := flatOf _ 𝒱.isAffineOpen_U0
  haveI : Module.Flat A (𝒱.sectionsOf c M).M1 := flatOf _ 𝒱.isAffineOpen_U1
  haveI : Module.Flat A (𝒱.sectionsOf c M).M01 := flatOf _ 𝒱.isAffineOpen_inf
  haveI : Module.Flat A ((𝒱.sectionsOf c M).M0 × (𝒱.sectionsOf c M).M1) := ChiLocallyConstant.flat_prod _ _

  have hcf := OModulePresheaf.cechFinite_ofModules_of_locallyTrivial c M hM.1 𝒱.toOrderedAffineCover
  obtain ⟨hfin0, hfin1⟩ := (OModulePresheaf.cechFinite_toOrderedAffineCover_iff _ _).mp hcf
  haveI : Module.Finite A (LinearMap.ker (𝒱.sectionsOf c M).cechDiff) := hfin0
  haveI : Module.Finite A ((𝒱.sectionsOf c M).M01 ⧸ LinearMap.range (𝒱.sectionsOf c M).cechDiff) := hfin1
  exact TwoChartCech.isLocallyConstant_fibreEulerChar (𝒱.sectionsOf c M).cechDiff
