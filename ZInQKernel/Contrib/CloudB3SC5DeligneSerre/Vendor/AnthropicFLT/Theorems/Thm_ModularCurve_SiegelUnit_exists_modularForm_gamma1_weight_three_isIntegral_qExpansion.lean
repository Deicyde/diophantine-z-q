/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_SiegelUnit_exists_modularForm_gamma1_weight_three_isIntegral_qExpansion (git blob 70aa5a78944a548f60cd04a582b927813b879802, sha256 240519f8a23f70e110b53099d03c70ef49c6aaba39e4212ce352829cb38da42a).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_SiegelUnit_exists_modularForm_gamma1_weight_three_isIntegral_qExpansion

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false
open scoped MatrixGroups ModularForm in

theorem ModularCurve.SiegelUnit.exists_modularForm_gamma1_weight_three_isIntegral_qExpansion
    (N : ℕ) (hN : 3 ≤ N) :
    ∃ (E : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) 3) (a : ℕ),
      (∀ n : ℕ, IsIntegral ℤ ((N : ℂ) ^ a *
        (UpperHalfPlane.qExpansion 1 (⇑E : UpperHalfPlane → ℂ)).coeff n)) ∧
      (UpperHalfPlane.qExpansion 1 (⇑E : UpperHalfPlane → ℂ)).coeff 0 ≠ 0 ∧
      IsIntegral ℤ ((N : ℂ) ^ a *
        ((UpperHalfPlane.qExpansion 1 (⇑E : UpperHalfPlane → ℂ)).coeff 0)⁻¹) ∧
      ∀ n : ℕ, IsIntegral ℤ ((N : ℂ) ^ a * (UpperHalfPlane.qExpansion (N : ℝ)
        ((⇑E : UpperHalfPlane → ℂ) ∣[(3 : ℤ)] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))).coeff n) := by
  revert N hN
  exact @_root_.P2MW.S_ModularCurve_SiegelUnit_exists_modularForm_gamma1_weight_three_isIntegral_qExpansion.solution
