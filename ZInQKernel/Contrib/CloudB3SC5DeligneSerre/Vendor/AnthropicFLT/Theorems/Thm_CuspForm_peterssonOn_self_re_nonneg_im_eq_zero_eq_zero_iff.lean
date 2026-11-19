/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CuspForm_peterssonOn_self_re_nonneg_im_eq_zero_eq_zero_iff (git blob 55613e4fbd78a24e29985419d34e9a2ad372e1df, sha256 772bdd3c8abae67edb7bbfbe63a2929d474727750e6d2306712668658770ce58).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PeterssonOn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CuspForm_peterssonOn_self_re_nonneg_im_eq_zero_eq_zero_iff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open scoped MatrixGroups

theorem CuspForm.peterssonOn_self_re_nonneg_im_eq_zero_eq_zero_iff (Γ : Subgroup SL(2, ℤ))
    [Γ.FiniteIndex] (k : ℤ) (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) :
    0 ≤ (CuspForm.peterssonOn Γ k f f).re ∧ (CuspForm.peterssonOn Γ k f f).im = 0 ∧
    (CuspForm.peterssonOn Γ k f f = 0 ↔ f = 0) := by
  revert Γ k f
  exact @_root_.P2MW.S_CuspForm_peterssonOn_self_re_nonneg_im_eq_zero_eq_zero_iff.solution
