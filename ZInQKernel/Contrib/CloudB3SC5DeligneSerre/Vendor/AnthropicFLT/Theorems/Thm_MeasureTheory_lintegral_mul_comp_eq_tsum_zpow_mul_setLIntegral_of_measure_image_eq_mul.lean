/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_MeasureTheory_lintegral_mul_comp_eq_tsum_zpow_mul_setLIntegral_of_measure_image_eq_mul (git blob 158e59f2de98f7378ca84d1b6e011d274ad27217, sha256 3f965b7bba41ffd35cbb9a06c900a4dff37d3acd8eec13fa89e99dbfcdb74367).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_MeasureTheory_lintegral_mul_comp_eq_tsum_zpow_mul_setLIntegral_of_measure_image_eq_mul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

theorem MeasureTheory.lintegral_mul_comp_eq_tsum_zpow_mul_setLIntegral_of_measure_image_eq_mul
    {Q : Type*} [MeasurableSpace Q] (ν : Measure Q) (T : Q ≃ᵐ Q)
    (κ : ℝ≥0∞) (hκ₀ : κ ≠ 0) (hκ : κ ≠ ∞)
    (hT : ∀ s : Set Q, MeasurableSet s → ν (T '' s) = κ * ν s)
    (m : Q → ℤ) (hm : Measurable m) (hmT : ∀ q, m (T q) = m q + 1)
    (h : Q → ℝ≥0∞) (hh : Measurable h) (hhT : ∀ q, h (T q) = h q)
    (Φ : ℤ → ℝ≥0∞) :
    ∫⁻ q, h q * Φ (m q) ∂ν = (∑' n : ℤ, κ ^ n * Φ n) * ∫⁻ q in {q | m q = 0}, h q ∂ν := by
  revert Q ν T κ hκ₀ hκ hT m hm hmT h hh hhT Φ
  exact @_root_.P2MW.S_MeasureTheory_lintegral_mul_comp_eq_tsum_zpow_mul_setLIntegral_of_measure_image_eq_mul.solution
