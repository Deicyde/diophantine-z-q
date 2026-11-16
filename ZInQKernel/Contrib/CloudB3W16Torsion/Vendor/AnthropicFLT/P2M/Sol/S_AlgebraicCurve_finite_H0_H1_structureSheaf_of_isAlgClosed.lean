/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicCurve_finite_H0_H1_structureSheaf_of_isAlgClosed. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModel
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCech
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlacesOf
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_finite_H0_H1_structureSheaf_of_smoothProperCurve
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_placesOf_union_eq_univ_of_sup_eq_top
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_not_isAffine_of_isProper_of_smoothOfRelativeDimension_one
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_essFiniteType_functionField
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicCurve_finite_H0_H1_structureSheaf_of_isAlgClosed

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicCurve
export AlgebraicCurve (H1 genusFF IsCurveOver IsCurveOver.deg_eq_one_of_isAlgClosed ConstantsAreBase ell_zero_eq_one_of_constantsAreBase baseToFunctionField finite_H0_H1_structureSheaf_of_smoothProperCurve placesOf_union_eq_univ_of_sup_eq_top isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one essFiniteType_functionField constantsAreBase_of_deg_eq_one stichtenothGenusExists_of_isCurveOver)
open AlgebraicCurve
open CategoryTheory AlgebraicGeometry TopologicalSpace

theorem ne_top_of_isAffineOpen' {C : Scheme.{u}} (hC : ¬ IsAffine C) {U : C.Opens}
    (hU : IsAffineOpen U) : U ≠ ⊤ := by
  intro h
  apply hC
  have hT : IsAffineOpen (⊤ : C.Opens) := h ▸ hU
  haveI : IsAffine (⊤ : C.Opens) := hT
  exact IsAffine.of_isIso C.topIso.inv

theorem finite_H0_H1_structureSheaf_of_isAlgClosed' {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover)
    (c : C ⟶ Spec (CommRingCat.of K)) [IsIntegral C] [IsProper c] [SmoothOfRelativeDimension 1 c] :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    Module.Finite K (𝒱.structureSheafSections c).H0 ∧ Module.Finite K (𝒱.structureSheafSections c).H1 ∧
      Module.finrank K (𝒱.structureSheafSections c).H0 = 1 ∧
      Module.finrank K (𝒱.structureSheafSections c).H1 = AlgebraicCurve.genusFF K C.functionField := by
  letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra

  haveI hcurve : IsCurveOver K C.functionField :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one c (RingEquiv.refl _) (fun _ => rfl)
  haveI : Algebra.EssFiniteType K C.functionField := essFiniteType_functionField c

  have hNA := not_isAffine_of_isProper_of_smoothOfRelativeDimension_one c
  have hne0 : 𝒱.U0 ≠ ⊤ := ne_top_of_isAffineOpen' hNA 𝒱.isAffineOpen_U0
  have hne1 : 𝒱.U1 ≠ ⊤ := ne_top_of_isAffineOpen' hNA 𝒱.isAffineOpen_U1
  obtain ⟨-, ⟨v₀, -⟩, -⟩ :=
    placesOf_union_eq_univ_of_sup_eq_top c 𝒱.U0 𝒱.U1 𝒱.sup_eq_top hne0 hne1

  have hC : ConstantsAreBase K C.functionField :=
    constantsAreBase_of_deg_eq_one v₀ (IsCurveOver.deg_eq_one_of_isAlgClosed v₀)
  obtain ⟨-, hL0, γ, D₀, hγ⟩ := stichtenothGenusExists_of_isCurveOver hC
  obtain ⟨hf0, hf1, hrk0, hrk1⟩ :=
    finite_H0_H1_structureSheaf_of_smoothProperCurve 𝒱 c hcurve hL0 ⟨γ, D₀, hγ⟩
  exact ⟨hf0, hf1, hrk0.trans (ell_zero_eq_one_of_constantsAreBase hC), hrk1⟩

end AlgebraicCurve

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_finite_H0_H1_structureSheaf_of_isAlgClosed.AlgebraicCurve in
theorem solution {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover)
    (c : C ⟶ Spec (CommRingCat.of K)) [IsIntegral C] [IsProper c] [SmoothOfRelativeDimension 1 c] :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    Module.Finite K (𝒱.structureSheafSections c).H0 ∧ Module.Finite K (𝒱.structureSheafSections c).H1 ∧
      Module.finrank K (𝒱.structureSheafSections c).H0 = 1 ∧
      Module.finrank K (𝒱.structureSheafSections c).H1 = AlgebraicCurve.genusFF K C.functionField :=
  finite_H0_H1_structureSheaf_of_isAlgClosed' 𝒱 c
