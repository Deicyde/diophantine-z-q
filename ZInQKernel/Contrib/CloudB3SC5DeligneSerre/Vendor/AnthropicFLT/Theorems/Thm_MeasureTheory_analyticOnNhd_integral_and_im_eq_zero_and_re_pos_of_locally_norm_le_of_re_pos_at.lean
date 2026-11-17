/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_MeasureTheory_analyticOnNhd_integral_and_im_eq_zero_and_re_pos_of_locally_norm_le_of_re_pos_at (git blob c64dff84d8cfdaed3880feb4efb4fd834a8398d4, sha256 58b28b8fce7753a3b73ca0e08b088f2e1f5e4ee1fb756fe4f1e8385608ba0e31).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_MeasureTheory_analyticOnNhd_integral_and_im_eq_zero_and_re_pos_of_locally_norm_le_of_re_pos_at

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.analyticOnNhd_integral_and_im_eq_zero_and_re_pos_of_locally_norm_le_of_re_pos_at
    {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] (μ : Measure Y)
    (a : ℝ) (F : ℂ → Y → ℂ)
    (hmeas : ∀ s : ℂ, AEStronglyMeasurable (F s) μ)
    (hhol : ∀ y : Y, Differentiable ℂ (fun s => F s y))
    (hdom : ∀ s₀ : ℂ, a < s₀.re → ∃ ε : ℝ, 0 < ε ∧ ∃ M : Y → ℝ, Integrable M μ ∧
      ∀ s ∈ Metric.ball s₀ ε, ∀ y : Y, ‖F s y‖ ≤ M y)
    (hreal : ∀ σ : ℝ, a < σ → ∀ y : Y, (F σ y).im = 0 ∧ 0 ≤ (F σ y).re)
    (hcont : ∀ σ : ℝ, a < σ → Continuous (F σ))
    (y₀ : Y) (hpt : ∀ σ : ℝ, a < σ → 0 < (F σ y₀).re)
    (hopen : ∀ U : Set Y, IsOpen U → y₀ ∈ U → 0 < μ U) :
    (∀ s : ℂ, a < s.re → Integrable (F s) μ) ∧
      AnalyticOnNhd ℂ (fun s : ℂ => ∫ y, F s y ∂μ) {s : ℂ | a < s.re} ∧
      (∀ σ : ℝ, a < σ → (∫ y, F σ y ∂μ).im = 0 ∧ 0 < (∫ y, F σ y ∂μ).re) := by
  revert Y μ a F hmeas hhol hdom hreal hcont y₀ hpt hopen
  exact @_root_.P2MW.S_MeasureTheory_analyticOnNhd_integral_and_im_eq_zero_and_re_pos_of_locally_norm_le_of_re_pos_at.solution
