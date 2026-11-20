/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
Modification notice (2026-11-15, Cloud Worker 14): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2); mathematical definitions,
theorem statements, and proof bodies are unchanged.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0
import Mathlib.NumberTheory.ModularForms.Discriminant
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit

theorem ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit : UpperHalfPlane.qExpansion 1 ModularForm.discriminant = PowerSeries.map (Int.castRingHom ℂ) (PowerSeries.X * ModularCurve.dedekindEtaUnit) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit.solution
