/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_LocalIntertwining_tendsto_integral_normSq_rpow_sub_one_mul_complexAtom_nhdsGT_one_half (git blob bf5771bc59b2f4c0afdf41d44821521ef580aa2d, sha256 d70169fedc4b4f9ab6ec763508361dfb57fad6b430117b183300189f0a6fbd24).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_LocalIntertwining_tendsto_integral_normSq_rpow_sub_one_mul_complexAtom_nhdsGT_one_half

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open MeasureTheory Filter Topology

theorem AutomorphicForm.LocalIntertwining.tendsto_integral_normSq_rpow_sub_one_mul_complexAtom_nhdsGT_one_half
    (c' d' : ℂ) (_h : c' ≠ 0 ∨ d' ≠ 0) (a b m : ℕ) (_habm : a + b ≤ m) :
    Tendsto (fun σ : ℝ =>
        ∫ z : ℂ, ((((‖c' * z + d'‖ ^ 2) ^ (2 * σ - 1) - 1 : ℝ)) : ℂ)
          * (z ^ a * (starRingEnd ℂ) z ^ b
              * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * (σ : ℂ) + 1) - ((m : ℂ)) / 2)))
      (𝓝[>] (1 / 2 : ℝ)) (𝓝 0) := by
  revert c' d' _h a b m _habm
  exact @_root_.P2MW.S_AutomorphicForm_LocalIntertwining_tendsto_integral_normSq_rpow_sub_one_mul_complexAtom_nhdsGT_one_half.solution
