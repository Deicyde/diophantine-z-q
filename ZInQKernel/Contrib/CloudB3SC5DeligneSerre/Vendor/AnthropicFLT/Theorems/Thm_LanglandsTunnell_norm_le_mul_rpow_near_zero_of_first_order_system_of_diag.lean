/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_LanglandsTunnell_norm_le_mul_rpow_near_zero_of_first_order_system_of_diag (git blob 7c639206b92a381bb88ad9e56d82a029f490e77c, sha256 dd78c404b1ec3ea310afb71698e6c31d6f96cdbd8718f7e7d16e57f9db50cf1f).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_LanglandsTunnell_norm_le_mul_rpow_near_zero_of_first_order_system_of_diag

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped Real

theorem LanglandsTunnell.norm_le_mul_rpow_near_zero_of_first_order_system_of_diag
    (m : ℕ) (a : Fin m → ℂ) (r₀ c τ : ℝ) (hτ : 0 < τ) (ha : ∀ i, r₀ ≤ (a i).re)
    (B : ℝ → Matrix (Fin m) (Fin m) ℂ) (hB : ∀ y : ℝ, 0 < y → y ≤ 1 → ∀ i j, ‖B y i j‖ ≤ c * y ^ τ)
    (F : Fin m → ℝ → ℂ) (hF : ∀ i, DifferentiableOn ℝ (F i) (Set.Ioi 0))
    (hFeq : ∀ y : ℝ, 0 < y → y ≤ 1 → ∀ i,
      (y : ℂ) * deriv (F i) y = a i * F i y + ∑ j, B y i j * F j y) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ∀ i, ‖F i y‖ ≤ C * y ^ (r₀ - ε) := by
  revert m a r₀ c τ hτ ha B hB F hF hFeq
  exact @_root_.P2MW.S_LanglandsTunnell_norm_le_mul_rpow_near_zero_of_first_order_system_of_diag.solution
