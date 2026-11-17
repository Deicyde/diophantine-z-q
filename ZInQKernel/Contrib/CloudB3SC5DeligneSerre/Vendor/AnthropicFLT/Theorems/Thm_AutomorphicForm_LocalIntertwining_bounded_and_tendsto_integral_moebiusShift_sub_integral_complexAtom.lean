/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_LocalIntertwining_bounded_and_tendsto_integral_moebiusShift_sub_integral_complexAtom (git blob 651382f6b7883093559f8b88406cadc8d68a80dd, sha256 7f2483df4d98719b3dafe3f864094de36ed99e54ec67b3dfc3bccdd737efd252).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_LocalIntertwining_bounded_and_tendsto_integral_moebiusShift_sub_integral_complexAtom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open MeasureTheory Filter Topology

theorem AutomorphicForm.LocalIntertwining.bounded_and_tendsto_integral_moebiusShift_sub_integral_complexAtom
    (a b c d : ℂ) (_hdet : a * d - b * c ≠ 0) (a₀ b₀ m : ℕ) (_habm : a₀ + b₀ ≤ m) :
    let atom : ℝ → ℂ → ℂ := fun σ z =>
      z ^ a₀ * (starRingEnd ℂ) z ^ b₀ * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * (σ : ℂ) + 1) - ((m : ℂ)) / 2)
    (∃ C : ℝ, ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 → ‖∫ z, atom σ z‖ ≤ C) ∧
    Tendsto (fun σ : ℝ =>
        (∫ z : ℂ, (((‖a * d - b * c‖ ^ 2 : ℝ) : ℂ) ^ ((σ : ℂ) + 1 / 2) * ((‖a + z * c‖ ^ 2 : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1)))
            * atom σ ((b + z * d) / (a + z * c)))
          - ∫ z : ℂ, atom σ z)
      (𝓝[>] (1 / 2 : ℝ)) (𝓝 0) := by
  revert a b c d _hdet a₀ b₀ m _habm
  exact @_root_.P2MW.S_AutomorphicForm_LocalIntertwining_bounded_and_tendsto_integral_moebiusShift_sub_integral_complexAtom.solution
