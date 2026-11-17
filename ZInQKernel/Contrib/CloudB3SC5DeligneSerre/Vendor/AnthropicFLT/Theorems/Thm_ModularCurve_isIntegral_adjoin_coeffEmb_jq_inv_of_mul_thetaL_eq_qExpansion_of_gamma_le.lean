/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_isIntegral_adjoin_coeffEmb_jq_inv_of_mul_thetaL_eq_qExpansion_of_gamma_le (git blob 2abf4034bda739a7621e65b992b97f40a75fa227, sha256 a1f48c3708b653700a2f3fac7681b95d861766d2202f2009b6b2c58b67f15636).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_LaurentCoeff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_QExpansionDiff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_isIntegral_adjoin_coeffEmb_jq_inv_of_mul_thetaL_eq_qExpansion_of_gamma_le

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open UpperHalfPlane ModularCurve
open scoped MatrixGroups

theorem ModularCurve.isIntegral_adjoin_coeffEmb_jq_inv_of_mul_thetaL_eq_qExpansion_of_gamma_le
    (M : ℕ) [NeZero M] (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (hΓ : CongruenceSubgroup.Gamma M ≤ Γ)
    (h1 : (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods)
    (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) 2) (Y : LaurentSeries ℂ)
    (hY : Y * thetaL ℂ (coeffEmb ℂ jq) =
      ((qExpansion 1 (f : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) :
    IsIntegral (Algebra.adjoin ℂ ({(coeffEmb ℂ jq)⁻¹} : Set (LaurentSeries ℂ)))
      (Y ^ (2 * M) * coeffEmb ℂ jq ^ (M + 1) * (coeffEmb ℂ jq - 1728) ^ M) := by
  revert M Γ hΓ h1 f Y hY
  exact @_root_.P2MW.S_ModularCurve_isIntegral_adjoin_coeffEmb_jq_inv_of_mul_thetaL_eq_qExpansion_of_gamma_le.solution
