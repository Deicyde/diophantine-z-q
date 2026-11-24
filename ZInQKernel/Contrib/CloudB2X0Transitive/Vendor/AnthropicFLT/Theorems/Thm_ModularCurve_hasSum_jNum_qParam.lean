/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_hasSum_jNum_qParam
Modification notice (2026-11-15, Cloud Worker 14): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2); mathematical definitions,
theorem statements, and proof bodies are unchanged.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_hasSum_jNum_qParam

theorem ModularCurve.hasSum_jNum_qParam (τ : UpperHalfPlane) : HasSum (fun m : ℕ => ((PowerSeries.coeff m ModularCurve.jNum : ℤ) : ℂ) * Function.Periodic.qParam 1 (τ : ℂ) ^ m) (Function.Periodic.qParam 1 (τ : ℂ) * (ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_hasSum_jNum_qParam.solution
