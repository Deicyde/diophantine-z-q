/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_jqModC_eq_qExpansion_E4_cube_div_discriminant
Modification notice (2026-11-15, Cloud Worker 14): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2); mathematical definitions,
theorem statements, and proof bodies are unchanged.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_JqCoeff
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_jqModC_eq_qExpansion_E4_cube_div_discriminant
attribute [-simp] ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single

open UpperHalfPlane
theorem ModularCurve.jqModC_eq_qExpansion_E4_cube_div_discriminant : ModularCurve.jqModC ℂ = (((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 / ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_jqModC_eq_qExpansion_E4_cube_div_discriminant.solution
