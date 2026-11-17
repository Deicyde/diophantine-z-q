/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_LocalIntertwining_integrable_complexAtom_and_integrable_moebiusShift (git blob 68f2ebcc0c5e6c08cd3b6c379d51f43655ab23ce, sha256 7d158c2a6e21f689568c14d435151c0d2d42d34b762d484f0d7b1d784e212c5c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_LocalIntertwining_integrable_complexAtom_and_integrable_moebiusShift

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open MeasureTheory

theorem AutomorphicForm.LocalIntertwining.integrable_complexAtom_and_integrable_moebiusShift
    (a b c d : ℂ) (_hdet : a * d - b * c ≠ 0) (a₀ b₀ m : ℕ) (_habm : a₀ + b₀ ≤ m) (σ : ℝ) (_hσ : 0 < σ) :
    let atom : ℝ → ℂ → ℂ := fun σ z =>
      z ^ a₀ * (starRingEnd ℂ) z ^ b₀ * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * (σ : ℂ) + 1) - ((m : ℂ)) / 2)
    Integrable (atom σ) ∧
    Integrable (fun z : ℂ =>
      (((‖a * d - b * c‖ ^ 2 : ℝ) : ℂ) ^ ((σ : ℂ) + 1 / 2) * ((‖a + z * c‖ ^ 2 : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1)))
        * atom σ ((b + z * d) / (a + z * c))) := by
  revert a b c d _hdet a₀ b₀ m _habm σ _hσ
  exact @_root_.P2MW.S_AutomorphicForm_LocalIntertwining_integrable_complexAtom_and_integrable_moebiusShift.solution
