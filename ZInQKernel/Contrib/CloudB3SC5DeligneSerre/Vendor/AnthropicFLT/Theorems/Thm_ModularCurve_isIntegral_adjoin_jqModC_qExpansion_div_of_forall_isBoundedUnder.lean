/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_isIntegral_adjoin_jqModC_qExpansion_div_of_forall_isBoundedUnder (git blob 4e83191922cb73fc7c88231de46abf776b57842b, sha256 ffe9eeaf597e7752f98b1b9904668cb5f9957425ca3c840693902312e5eec4c9).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_JqCoeff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_isIntegral_adjoin_jqModC_qExpansion_div_of_forall_isBoundedUnder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open scoped Topology in

theorem ModularCurve.isIntegral_adjoin_jqModC_qExpansion_div_of_forall_isBoundedUnder
    (M : ℕ) [NeZero M] (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hΓ : CongruenceSubgroup.Gamma1 M ≤ Γ) {k : ℤ}
    (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (hh : h ≠ 0)
    (hb : ∀ τ : UpperHalfPlane, Filter.IsBoundedUnder (· ≤ ·) (𝓝[≠] τ)
      (fun z : UpperHalfPlane => ‖g z / h z‖)) :
    IsIntegral (Algebra.adjoin ℂ ({ModularCurve.jqModC ℂ} : Set (LaurentSeries ℂ)))
      (HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) /
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑h)) := by
  revert M Γ hΓ k g h hh hb
  exact @_root_.P2MW.S_ModularCurve_isIntegral_adjoin_jqModC_qExpansion_div_of_forall_isBoundedUnder.solution
