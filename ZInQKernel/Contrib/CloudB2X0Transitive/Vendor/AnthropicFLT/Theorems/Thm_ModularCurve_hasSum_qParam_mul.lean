/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_hasSum_qParam_mul
Modification notice (2026-11-15, Cloud Worker 14): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2); mathematical definitions,
theorem statements, and proof bodies are unchanged.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
import Mathlib.RingTheory.PowerSeries.Basic
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_hasSum_qParam_mul

theorem ModularCurve.hasSum_qParam_mul (h : ℝ) (hh : 0 < h) (A B : PowerSeries ℂ) (F G : UpperHalfPlane → ℂ) (hA : ∀ τ : UpperHalfPlane, HasSum (fun m : ℕ => PowerSeries.coeff m A * Function.Periodic.qParam h (τ : ℂ) ^ m) (F τ)) (hB : ∀ τ : UpperHalfPlane, HasSum (fun m : ℕ => PowerSeries.coeff m B * Function.Periodic.qParam h (τ : ℂ) ^ m) (G τ)) (τ : UpperHalfPlane) : HasSum (fun m : ℕ => PowerSeries.coeff m (A * B) * Function.Periodic.qParam h (τ : ℂ) ^ m) (F τ * G τ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_hasSum_qParam_mul.solution
