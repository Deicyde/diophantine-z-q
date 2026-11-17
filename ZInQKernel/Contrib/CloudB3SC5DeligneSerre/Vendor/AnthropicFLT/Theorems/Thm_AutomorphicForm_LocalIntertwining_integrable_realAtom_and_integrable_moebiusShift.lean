/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_LocalIntertwining_integrable_realAtom_and_integrable_moebiusShift (git blob c89713542dbb2dc28162b699f84345bfa997b2a9, sha256 934f229c58185cab62a7f74ef7cd604d929d94dc37bbb4b44692bd50714d5bd3).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_LocalIntertwining_integrable_realAtom_and_integrable_moebiusShift

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open MeasureTheory

theorem AutomorphicForm.LocalIntertwining.integrable_realAtom_and_integrable_moebiusShift
    (a b c d : ℝ) (_hdet : a * d - b * c ≠ 0) (k : ℤ) (σ : ℝ) (_hσ : 0 < σ) :
    let atom : ℝ → ℝ → ℂ := fun σ x =>
      ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-((σ : ℂ) + 1 / 2))
    Integrable (atom σ) ∧
    Integrable (fun x : ℝ =>
      (((|a * d - b * c| : ℝ) : ℂ) ^ ((σ : ℂ) + 1 / 2) * ((|a + x * c| : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1)))
        * atom σ ((b + x * d) / (a + x * c))) := by
  revert a b c d _hdet k σ _hσ
  exact @_root_.P2MW.S_AutomorphicForm_LocalIntertwining_integrable_realAtom_and_integrable_moebiusShift.solution
