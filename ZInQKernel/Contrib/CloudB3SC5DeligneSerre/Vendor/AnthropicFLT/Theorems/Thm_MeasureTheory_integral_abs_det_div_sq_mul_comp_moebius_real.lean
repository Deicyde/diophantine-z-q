/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_MeasureTheory_integral_abs_det_div_sq_mul_comp_moebius_real (git blob c77aaee76c68e7ea380bbaba69d3e8d867dcc751, sha256 a6179ddfa895fd2a5af7e1f66e808faa75dcf8e60d1b57d26db87b081a971a02).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_MeasureTheory_integral_abs_det_div_sq_mul_comp_moebius_real

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.integral_abs_det_div_sq_mul_comp_moebius_real
    (a b c d : ℝ) (_hdet : a * d - b * c ≠ 0) (G : ℝ → ℂ) :
    ∫ x : ℝ, ((|a * d - b * c| / (a + x * c) ^ 2 : ℝ) : ℂ) * G ((b + x * d) / (a + x * c))
      = ∫ u : ℝ, G u := by
  revert a b c d _hdet G
  exact @_root_.P2MW.S_MeasureTheory_integral_abs_det_div_sq_mul_comp_moebius_real.solution
