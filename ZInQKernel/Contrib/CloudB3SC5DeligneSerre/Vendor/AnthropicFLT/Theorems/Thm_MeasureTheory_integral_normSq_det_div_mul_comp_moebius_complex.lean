/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_MeasureTheory_integral_normSq_det_div_mul_comp_moebius_complex (git blob 87e06444b1edf62b7b1b21f921a479d759bf8764, sha256 8272b961dee65d18f5a4b839c0bceb99b104dbecf02b549f80a3a666333d01e8).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_MeasureTheory_integral_normSq_det_div_mul_comp_moebius_complex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.integral_normSq_det_div_mul_comp_moebius_complex
    (a b c d : ℂ) (_hdet : a * d - b * c ≠ 0) (G : ℂ → ℂ) :
    ∫ z : ℂ, ((‖a * d - b * c‖ ^ 2 / ‖a + z * c‖ ^ 4 : ℝ) : ℂ) * G ((b + z * d) / (a + z * c))
      = ∫ u : ℂ, G u := by
  revert a b c d _hdet G
  exact @_root_.P2MW.S_MeasureTheory_integral_normSq_det_div_mul_comp_moebius_complex.solution
