/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_isIntegral_adjoin_jqModC_qExpansion_div_of_forall_isBoundedUnder_of_finiteIndex (git blob 4788c311d20af690ddb1d630f84b38f49a9695ce, sha256 97ac595a14dfcbbfe8a3e050d8b36acb7174ef05a56e1960304bfb290f53a27d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_JqCoeff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_isIntegral_adjoin_jqModC_qExpansion_div_of_forall_isBoundedUnder_of_finiteIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open scoped MatrixGroups Topology

theorem ModularCurve.isIntegral_adjoin_jqModC_qExpansion_div_of_forall_isBoundedUnder_of_finiteIndex
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ) {k : ℤ}
    (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (hh : h ≠ 0)
    (hb : ∀ τ : UpperHalfPlane, Filter.IsBoundedUnder (· ≤ ·) (𝓝[≠] τ)
      (fun z : UpperHalfPlane => ‖g z / h z‖)) :
    IsIntegral (Algebra.adjoin ℂ ({ModularCurve.jqModC ℂ} : Set (LaurentSeries ℂ)))
      (HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) /
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑h)) := by
  revert Γ hT k g h hh hb
  exact @_root_.P2MW.S_ModularCurve_isIntegral_adjoin_jqModC_qExpansion_div_of_forall_isBoundedUnder_of_finiteIndex.solution
