/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_eq_zero_of_forall_re_periodOf_eq_zero (git blob 6e296fbadaed9248bd4ba1f1211ef11d9b848b3c, sha256 6310a75876e285ab84ef3f888f444fd95bcbb9a948fe052a27c2acef6eeb6163).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_eq_zero_of_forall_re_periodOf_eq_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.eq_zero_of_forall_re_periodOf_eq_zero (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (f : CuspForm Γ 2)
    (h : ∀ γ : Γ, (ModularCurve.periodOf Γ γ f).re = 0) : f = 0 := by
  revert Γ f h
  exact @_root_.P2MW.S_ModularCurve_eq_zero_of_forall_re_periodOf_eq_zero.solution
