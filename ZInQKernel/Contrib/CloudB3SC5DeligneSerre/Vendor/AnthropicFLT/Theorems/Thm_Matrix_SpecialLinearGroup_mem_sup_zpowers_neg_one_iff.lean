/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Matrix_SpecialLinearGroup_mem_sup_zpowers_neg_one_iff (git blob edda2f2ea65f20d2a67172ce9df938c11bdccace, sha256 a0c57da02fc799b9922f557f60295cb2d9713a08c1fecef634f2c04de6241e2a).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Matrix_SpecialLinearGroup_mem_sup_zpowers_neg_one_iff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped MatrixGroups

theorem Matrix.SpecialLinearGroup.mem_sup_zpowers_neg_one_iff
    (Γ : Subgroup SL(2, ℤ)) (g : SL(2, ℤ)) :
    g ∈ Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) ↔ g ∈ Γ ∨ -g ∈ Γ := by
  revert Γ g
  exact @_root_.P2MW.S_Matrix_SpecialLinearGroup_mem_sup_zpowers_neg_one_iff.solution
