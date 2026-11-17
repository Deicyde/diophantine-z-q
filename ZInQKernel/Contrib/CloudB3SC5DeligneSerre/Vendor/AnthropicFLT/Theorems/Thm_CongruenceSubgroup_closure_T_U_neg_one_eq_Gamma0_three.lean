/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CongruenceSubgroup_closure_T_U_neg_one_eq_Gamma0_three (git blob c60b6d71b0ebf9e55826a23b3999d4daac222463, sha256 cc2171effaa4ef84596cba1ef8fcbd002db1ce8c0bdab8700bbd058e85054cba).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CongruenceSubgroup_closure_T_U_neg_one_eq_Gamma0_three

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open scoped MatrixGroups in

theorem CongruenceSubgroup.closure_T_U_neg_one_eq_Gamma0_three (U : SL(2, ℤ))
    (hU : (U : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; -3, 1]) :
    Subgroup.closure ({ModularGroup.T, U, -1} : Set SL(2, ℤ)) = CongruenceSubgroup.Gamma0 3 := by
  revert U hU
  exact @_root_.P2MW.S_CongruenceSubgroup_closure_T_U_neg_one_eq_Gamma0_three.solution
