/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_place_deg_eq_one_laurentBaseChange_qExpFunctionFieldC (git blob dc7eb9f3cfa5775e05c4599e74acf05a2cde337a, sha256 9d3a5ba665473fc3e376299fe0a263d6e44acacb063c429ff98825d4c34c070b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Correspondence
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0ModL
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_deg_ne_zero_of_finiteDimensional_adjoin
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_of_isAlgClosed
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace ModularCurve
end ModularCurve
namespace P2MW.S_ModularCurve_place_deg_eq_one_laurentBaseChange_qExpFunctionFieldC.ModularCurve
end P2MW.S_ModularCurve_place_deg_eq_one_laurentBaseChange_qExpFunctionFieldC.ModularCurve
namespace AlgebraicCurve
end AlgebraicCurve

namespace P2MW.S_ModularCurve_place_deg_eq_one_laurentBaseChange_qExpFunctionFieldC

set_option autoImplicit false

open _root_.ModularCurve
open _root_.P2MW.S_ModularCurve_place_deg_eq_one_laurentBaseChange_qExpFunctionFieldC.ModularCurve
open _root_.AlgebraicCurve
open scoped MatrixGroups

namespace ModularCurve
export _root_.ModularCurve (qExpFunctionFieldC intFormRatiosC_subset coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange coeffMap_jqModC jqModC transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC jqModC_mem_intFormRatiosC)
namespace PlaceDegOne
open _root_.ModularCurve

theorem jqModC_mem_laurentBaseChange (L : Type*) [Field L] [Algebra ℚ L]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) :
    jqModC L ∈ laurentBaseChange L (qExpFunctionFieldC ℚ Γ) := by
  have h := intFormRatiosC_subset ℚ Γ (ModularCurve.jqModC_mem_intFormRatiosC ℚ Γ)
  have e : coeffEmb L (jqModC ℚ) = jqModC L := coeffMap_jqModC _
  exact e ▸ coeffEmb_mem_laurentBaseChange L h

end ModularCurve.PlaceDegOne

theorem solution
    (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (hF : F₀ = ModularCurve.qExpFunctionFieldC ℚ Γ)
    (W : AlgebraicCurve.Place L ↥(ModularCurve.laurentBaseChange L F₀)) :
    W.deg = 1 := by
  subst hF
  obtain ⟨htr, hfin⟩ :=
    ModularCurve.transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
      L Γ hT ⟨jqModC L, ModularCurve.PlaceDegOne.jqModC_mem_laurentBaseChange L Γ⟩ rfl
  haveI := hfin
  exact AlgebraicCurve.Place.deg_eq_one_of_isAlgClosed W
    (AlgebraicCurve.Place.deg_ne_zero_of_finiteDimensional_adjoin _ htr W)
