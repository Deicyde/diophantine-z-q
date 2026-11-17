/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_periodOf_apply_eq_sub_of_hasEquivariantPrimitiveOf (git blob ade1754323587fd2a64069d4649121ab48a15335, sha256 26b803927f0ac41f9cf4a9973c8960013acf3a798066eb3f68cc2d9cd5b1065d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_periodOf_apply_eq_sub_of_hasEquivariantPrimitiveOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.periodOf_apply_eq_sub_of_hasEquivariantPrimitiveOf (Γ : Subgroup SL(2, ℤ))
    (f : CuspForm Γ 2) {F : UpperHalfPlane → ℂ}
    (hF : ModularCurve.HasEquivariantPrimitiveOf Γ f F) (γ : Γ) :
    ModularCurve.periodOf Γ γ f =
      F ((γ : SL(2, ℤ)) • UpperHalfPlane.I) - F UpperHalfPlane.I := by
  revert Γ f F hF γ
  exact @_root_.P2MW.S_ModularCurve_periodOf_apply_eq_sub_of_hasEquivariantPrimitiveOf.solution
