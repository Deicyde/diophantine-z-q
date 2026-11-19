/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_addMonoidHom_exp_eq_of_norm_eq_one_of_trace_sq_le_four_of_finiteIndex (git blob 161f3aff227b4683e5d81e7f5f5b7c368bfff608, sha256 2ab68ccbee19f1ae91fde2551d286c7cb8b3223a9d6541fd19fc64b85701ea57).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_addMonoidHom_exp_eq_of_norm_eq_one_of_trace_sq_le_four_of_finiteIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.exists_addMonoidHom_exp_eq_of_norm_eq_one_of_trace_sq_le_four_of_finiteIndex
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (χ : Γ → ℂ)
    (hmul : ∀ γ δ, χ (γ * δ) = χ γ * χ δ) (hunit : ∀ γ, ‖χ γ‖ = 1)
    (htriv : ∀ γ : Γ,
      ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 ≤ 4 → χ γ = 1) :
    ∃ φ : Additive Γ →+ ℝ,
      (∀ γ : Γ,
        ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 ≤ 4 → φ (Additive.ofMul γ) = 0) ∧
      ∀ γ, χ γ = Complex.exp (2 * Real.pi * Complex.I * (φ (Additive.ofMul γ) : ℂ)) := by
  revert Γ χ hmul hunit htriv
  exact @_root_.P2MW.S_ModularCurve_exists_addMonoidHom_exp_eq_of_norm_eq_one_of_trace_sq_le_four_of_finiteIndex.solution
