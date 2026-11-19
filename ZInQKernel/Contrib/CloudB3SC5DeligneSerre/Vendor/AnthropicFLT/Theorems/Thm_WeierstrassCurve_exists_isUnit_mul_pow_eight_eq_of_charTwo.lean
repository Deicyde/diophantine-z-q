/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_WeierstrassCurve_exists_isUnit_mul_pow_eight_eq_of_charTwo (git blob 904b0c4d54b84f4fbbb67403a87e9859684a11da, sha256 6c6f9e9e39c12a3d0735c502c3eee07e28f2a602d632aa68cec5873950051550).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_WeierstrassCurve_exists_isUnit_mul_pow_eight_eq_of_charTwo

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

universe u in

theorem WeierstrassCurve.exists_isUnit_mul_pow_eight_eq_of_charTwo
    {M : Type u} [Field M] [CharP M 2] [DecidableEq M] (A : ValuationSubring M)
    {t : M} (ht : t ∈ A) (htu : ¬ IsUnit (⟨t, ht⟩ : A)) (ht0 : t ≠ 0)
    {x₀ y₀ : M} (hP : (⟨t, 0, 0, 0, t ^ 5⟩ : WeierstrassCurve M).toAffine.Nonsingular x₀ y₀)
    (h3P : (3 : ℕ) • Point.some x₀ y₀ hP = 0) :
    ∃ (μ : M) (u : A), IsUnit u ∧ t = u * μ ^ 8 := by
  revert M A t ht htu ht0 x₀ y₀ hP h3P
  exact @_root_.P2MW.S_WeierstrassCurve_exists_isUnit_mul_pow_eight_eq_of_charTwo.solution
