/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_analyticOrderAt_le_of_isIntegral_adjoin_jqModC_pow (git blob 90f246bfeef98c645d6e1d26e1073a5c3cfa1fe8, sha256 e02cff2136e6fbdb58d7288ac12b8df2627d669cdd24d039fdca92bb41ae8310).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_JqCoeff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_analyticOrderAt_le_of_isIntegral_adjoin_jqModC_pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open ModularCurve
open scoped MatrixGroups ModularForm

theorem ModularCurve.analyticOrderAt_le_of_isIntegral_adjoin_jqModC_pow
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ) {k : ℤ} (m : ℕ) (hm : 1 ≤ m)
    (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (X : LaurentSeries ℂ)
    (hX : X * ((UpperHalfPlane.qExpansion 1 (h : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) = ((UpperHalfPlane.qExpansion 1 (g : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ))
    (h₁ : IsIntegral (Algebra.adjoin ℂ ({ModularCurve.jqModC ℂ} : Set (LaurentSeries ℂ)))
      (X ^ 6 * ModularCurve.jqModC ℂ ^ (4 * m) * (ModularCurve.jqModC ℂ - algebraMap ℂ (LaurentSeries ℂ) 1728) ^ (3 * m)))
    (τ : UpperHalfPlane) :
    analyticOrderAt ((fun z : UpperHalfPlane => h z * ModularForm.discriminant z ^ m) ∘ UpperHalfPlane.ofComplex) (τ : ℂ) ≤
      analyticOrderAt ((fun z : UpperHalfPlane => g z * (ModularForm.E₄ z ^ 2 * ModularForm.E₆ z) ^ m) ∘ UpperHalfPlane.ofComplex) (τ : ℂ) := by
  revert Γ hT k m hm g h X hX h₁ τ
  exact @_root_.P2MW.S_ModularCurve_analyticOrderAt_le_of_isIntegral_adjoin_jqModC_pow.solution
