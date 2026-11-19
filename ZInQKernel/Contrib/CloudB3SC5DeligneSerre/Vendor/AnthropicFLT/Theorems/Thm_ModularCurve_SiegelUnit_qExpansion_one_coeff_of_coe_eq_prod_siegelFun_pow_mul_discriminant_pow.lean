/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_SiegelUnit_qExpansion_one_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow (git blob 6e4014ff7afecc43a8cca210b402879c65816e14, sha256 87bb9a07181a2f8ea97c161914cf423d017f266a927f3d050068a1339771c0e6).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_SiegelFunction
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_SiegelUnit_qExpansion_one_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false
open scoped MatrixGroups ModularForm in

theorem ModularCurve.SiegelUnit.qExpansion_one_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow
    (N : ℕ) [NeZero N] (m : ZMod N → ZMod N → ℕ) (hm0 : m 0 0 = 0) (t : ℕ)
    (ϑ : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) (12 * (t : ℤ)))
    (hϑ : ∀ τ : UpperHalfPlane, ϑ τ =
      (∏ r : ZMod N, ∏ s : ZMod N,
          ModularCurve.siegelFun N (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * N * m r s)) *
        ModularForm.discriminant τ ^ t)
    (m₀ : ℕ)
    (hm₀ : (N : ℤ) * m₀ =
      (∑ r : ZMod N, ∑ s : ZMod N, (m r s : ℤ) *
        (6 * (r.val : ℤ) ^ 2
          - 6 * (N : ℤ) * (r.val : ℤ) + (N : ℤ) ^ 2)) + (N : ℤ) * t) :
    ∃ a : ℕ,
      (∀ n : ℕ, n < m₀ → (UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff n = 0) ∧
      (UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff m₀ ≠ 0 ∧
      IsIntegral ℤ ((N : ℂ) ^ a *
        ((UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff m₀)⁻¹) ∧
      ∀ n : ℕ, IsIntegral ℤ ((N : ℂ) ^ a *
        (UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff n) := by
  revert N m hm0 t ϑ hϑ m₀ hm₀
  exact @_root_.P2MW.S_ModularCurve_SiegelUnit_qExpansion_one_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow.solution
