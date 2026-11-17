/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_contDiff_and_finsum_smoothedFundamental_eq_one (git blob 5d42467765b2481e3728bef022174e06a60b4b28, sha256 bec7b54c1f77668a7acae37ef462574cba20fe7923294de269535e1f7edcf64d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_SmoothedFundamental
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_contDiff_and_finsum_smoothedFundamental_eq_one

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open UpperHalfPlane
open scoped MatrixGroups Topology ContDiff

theorem ModularCurve.contDiff_and_finsum_smoothedFundamental_eq_one
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (T : ℝ) :
    (∀ n : ℕ∞, ContDiff ℝ n (ModularCurve.smoothedFundamental Γ T)) ∧
    HasCompactSupport (ModularCurve.smoothedFundamental Γ T) ∧
    tsupport (ModularCurve.smoothedFundamental Γ T) ⊆ {z : ℂ | 0 < z.im} ∧
    (∀ z : ℂ, 0 ≤ ModularCurve.smoothedFundamental Γ T z) ∧
    (∀ τ : ℍ, (Function.support fun γ : Γ =>
        ModularCurve.smoothedFundamental Γ T (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ)).Finite) ∧
    (∀ τ : ℍ,
      ∑ᶠ γ : Γ, ModularCurve.smoothedFundamental Γ T (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ) ≤ 1) ∧
    (∀ τ : ℍ, max τ.im τ.im⁻¹ ≤ T →
      ∑ᶠ γ : Γ, ModularCurve.smoothedFundamental Γ T (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ) = 1) ∧
    (∃ G : Finset SL(2, ℤ), ∀ δ : SL(2, ℤ), δ ∉ G → ∀ τ : ℍ,
      ModularCurve.smoothedFundamental Γ T τ ≠ 0 →
        ModularCurve.smoothedFundamental Γ T ((δ • τ : ℍ) : ℂ) = 0) := by
  revert Γ T
  exact @_root_.P2MW.S_ModularCurve_contDiff_and_finsum_smoothedFundamental_eq_one.solution
