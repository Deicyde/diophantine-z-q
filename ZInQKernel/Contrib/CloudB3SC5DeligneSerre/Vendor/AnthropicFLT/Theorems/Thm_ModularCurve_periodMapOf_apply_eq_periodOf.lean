/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_periodMapOf_apply_eq_periodOf (git blob 0e2b616e986732f1f702cd509ef71d912ac5c9b8, sha256 2d66ca4563ae4d1bccf47bba594892d972f7c0d53f8ef4f2ebf6cd97dc247d14).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_periodMapOf_apply_eq_periodOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.periodMapOf_apply_eq_periodOf (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (f : CuspForm Γ 2) (γ : Γ) :
    ModularCurve.periodMapOf Γ f (Additive.ofMul γ) = ModularCurve.periodOf Γ γ f := by
  revert Γ f γ
  exact @_root_.P2MW.S_ModularCurve_periodMapOf_apply_eq_periodOf.solution
