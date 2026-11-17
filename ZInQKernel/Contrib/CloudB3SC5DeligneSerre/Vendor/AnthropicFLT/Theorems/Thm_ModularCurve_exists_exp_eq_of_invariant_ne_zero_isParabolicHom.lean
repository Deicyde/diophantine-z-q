/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_exp_eq_of_invariant_ne_zero_isParabolicHom (git blob ad9e84d2dc0473a2117fdb3ac6dc00ac50208edb, sha256 a4a72fc085c470170a48da281f567a70c398d61005685edeb60a5281f1579243).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodMap
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_exp_eq_of_invariant_ne_zero_isParabolicHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open UpperHalfPlane Filter
open scoped MatrixGroups Topology Real

theorem ModularCurve.exists_exp_eq_of_invariant_ne_zero_isParabolicHom
    (Γ : Subgroup SL(2, ℤ)) (Φ : ℂ → ℂ)
    (hΦ : ∀ τ : ℍ, ContDiffAt ℝ 1 Φ τ) (hne : ∀ τ : ℍ, Φ τ ≠ 0)
    (hinv : ∀ γ ∈ Γ, ∀ τ : ℍ, Φ ((γ • τ : ℍ) : ℂ) = Φ τ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ c : ℂ, c ≠ 0 ∧
      Tendsto (fun τ : ℍ => Φ ((σ • τ : ℍ) : ℂ)) atImInfty (𝓝 c)) :
    ∃ (L : ℂ → ℂ) (m : Additive Γ →+ ℤ),
      ModularCurve.Period.IsParabolicHom Γ m ∧
      (∀ τ : ℍ, ContDiffAt ℝ 1 L τ) ∧
      (∀ τ : ℍ, HasFDerivAt L ((Φ τ)⁻¹ • fderiv ℝ Φ τ) τ) ∧
      (∀ τ : ℍ, Complex.exp (L τ) = Φ τ) ∧
      (∀ (γ : Γ) (τ : ℍ), L (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ) =
        L τ + 2 * π * Complex.I * (m (Additive.ofMul γ) : ℂ)) ∧
      (∀ σ : SL(2, ℤ), ∃ c : ℂ, Tendsto (fun τ : ℍ => L ((σ • τ : ℍ) : ℂ)) atImInfty (𝓝 c)) := by
  revert Γ Φ hΦ hne hinv hcusp
  exact @_root_.P2MW.S_ModularCurve_exists_exp_eq_of_invariant_ne_zero_isParabolicHom.solution
