/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_eventually_norm_slash_le_of_isIntegral_adjoin_jqModC_inv_pow (git blob 716e9e21e9e556cfd11df8facbdd4f830dd737a0, sha256 c3e88fe414bd7fd823d5bead31f332f250825b7a3c1b0748db9d1878bc78f8a5).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_JqCoeff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_eventually_norm_slash_le_of_isIntegral_adjoin_jqModC_inv_pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace ModularCurve
end ModularCurve


open _root_.ModularCurve hiding coeffEmb
open scoped MatrixGroups ModularForm

theorem ModularCurve.eventually_norm_slash_le_of_isIntegral_adjoin_jqModC_inv_pow
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (hT : ModularGroup.T ∈ Γ) {k : ℤ} (m : ℕ) (hm : 1 ≤ m)
    (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (hh : h ≠ 0) (X : LaurentSeries ℂ)
    (hX : X * ((UpperHalfPlane.qExpansion 1 (h : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
      ((UpperHalfPlane.qExpansion 1 (g : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) (M : ℕ)
    (h₂ : IsIntegral (Algebra.adjoin ℂ ({(ModularCurve.jqModC ℂ)⁻¹} : Set (LaurentSeries ℂ)))
      (X ^ (2 * M) * ModularCurve.jqModC ℂ ^ (m * M + 1) * (ModularCurve.jqModC ℂ - algebraMap ℂ (LaurentSeries ℂ) 1728) ^ (m * M)))
    (A : Matrix.SpecialLinearGroup (Fin 2) ℤ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ τ : UpperHalfPlane in UpperHalfPlane.atImInfty,
      ‖((fun z : UpperHalfPlane => g z * (ModularForm.E₄ z ^ 2 * ModularForm.E₆ z) ^ m) ∣[k + 14 * (m : ℤ)] (A : GL (Fin 2) ℝ)) τ‖ ≤
        ε * ‖((fun z : UpperHalfPlane => h z * ModularForm.discriminant z ^ m) ∣[k + 12 * (m : ℤ)] (A : GL (Fin 2) ℝ)) τ‖ := by
  revert Γ hT k m hm g h hh X hX M h₂ A ε hε
  exact @_root_.P2MW.S_ModularCurve_eventually_norm_slash_le_of_isIntegral_adjoin_jqModC_inv_pow.solution
