/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_eq_const_of_norm_multiplier_eq_one_of_finiteIndex (git blob 5faf43023eb29e716583ff51315d49f2f8209341, sha256 6aaa3dd54ccc3cec92551eeed025ef2e7a278b784ab359ac6f003f473377f7b3).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_eq_const_of_norm_multiplier_eq_one_of_finiteIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open UpperHalfPlane
open scoped MatrixGroups Topology

theorem ModularCurve.exists_eq_const_of_norm_multiplier_eq_one_of_finiteIndex
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (F : ℍ → ℂ) (χ : Γ → ℂ)
    (hF : DifferentiableOn ℂ (fun z : ℂ => F (ofComplex z)) {z : ℂ | 0 < z.im})
    (hχ : ∀ (γ : Γ) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) = χ γ * F τ)
    (hunit : ∀ γ : Γ, ‖χ γ‖ = 1)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) :
    ∃ C : ℂ, ∀ τ : ℍ, F τ = C := by
  revert Γ F χ hF hχ hunit hcusp
  exact @_root_.P2MW.S_ModularCurve_exists_eq_const_of_norm_multiplier_eq_one_of_finiteIndex.solution
