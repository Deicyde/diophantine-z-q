/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_cuspForm_qExpansion_eq_mul_thetaL_pow_of_isIntegral_qExpFunctionFieldC (git blob a6c666f564d1c9ffa36b72e39f3ab81aeb7ce5f3, sha256 78d9bfabd09950cb66ee2f45ac69bb831a45bdea9a32905780b39b8b52de87ba).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_LaurentCoeff
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_JqCoeff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_QExpansionDiff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_cuspForm_qExpansion_eq_mul_thetaL_pow_of_isIntegral_qExpFunctionFieldC

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open ModularCurve
open scoped MatrixGroups

theorem ModularCurve.exists_cuspForm_qExpansion_eq_mul_thetaL_pow_of_isIntegral_qExpFunctionFieldC
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ) (m : ℕ) (hm : 1 ≤ m)
    (X : LaurentSeries ℂ)
    (hX : X ∈ ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ Γ)) (M : ℕ)
    (h₁ : IsIntegral (Algebra.adjoin ℂ ({ModularCurve.jqModC ℂ} : Set (LaurentSeries ℂ)))
      (X ^ 6 * ModularCurve.jqModC ℂ ^ (4 * m) * (ModularCurve.jqModC ℂ - algebraMap ℂ (LaurentSeries ℂ) 1728) ^ (3 * m)))
    (h₂ : IsIntegral (Algebra.adjoin ℂ ({(ModularCurve.jqModC ℂ)⁻¹} : Set (LaurentSeries ℂ)))
      (X ^ (2 * M) * ModularCurve.jqModC ℂ ^ (m * M + 1) * (ModularCurve.jqModC ℂ - algebraMap ℂ (LaurentSeries ℂ) 1728) ^ (m * M))) :
    ∃ f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) (2 * (m : ℤ)),
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) =
        X * ModularCurve.thetaL ℂ (ModularCurve.jqModC ℂ) ^ m := by
  revert Γ hT m hm X hX M h₁ h₂
  exact @_root_.P2MW.S_ModularCurve_exists_cuspForm_qExpansion_eq_mul_thetaL_pow_of_isIntegral_qExpFunctionFieldC.solution
