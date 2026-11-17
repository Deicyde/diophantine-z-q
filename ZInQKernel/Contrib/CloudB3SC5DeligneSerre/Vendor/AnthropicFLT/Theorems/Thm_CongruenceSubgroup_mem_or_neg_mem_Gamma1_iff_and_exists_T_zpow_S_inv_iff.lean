/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CongruenceSubgroup_mem_or_neg_mem_Gamma1_iff_and_exists_T_zpow_S_inv_iff (git blob 41851823caab92a1f25e147698831aee96a423f4, sha256 1b412af50b712d2d736ebf81d1b86e9525a1383bc4b3b354f041249ac8da4bee).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CongruenceSubgroup_mem_or_neg_mem_Gamma1_iff_and_exists_T_zpow_S_inv_iff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false
open scoped MatrixGroups in

theorem CongruenceSubgroup.mem_or_neg_mem_Gamma1_iff_and_exists_T_zpow_S_inv_iff
    (N : ℕ) (β : SL(2, ℤ)) :
    ((β ∈ CongruenceSubgroup.Gamma1 N ∨ -β ∈ CongruenceSubgroup.Gamma1 N) ↔
        (((β 1 0 : ℤ) : ZMod N) = 0 ∧
          (((β 0 0 : ℤ) : ZMod N) = 1 ∨ ((β 0 0 : ℤ) : ZMod N) = -1))) ∧
    ((∃ j : ℤ, β * ModularGroup.T ^ j * ModularGroup.S⁻¹ ∈ CongruenceSubgroup.Gamma1 N ∨
        -(β * ModularGroup.T ^ j * ModularGroup.S⁻¹) ∈ CongruenceSubgroup.Gamma1 N) ↔
        (((β 1 0 : ℤ) : ZMod N) = 1 ∨ ((β 1 0 : ℤ) : ZMod N) = -1)) ∧
    (∃ a b : ZMod N, a * ((β 0 0 : ℤ) : ZMod N) + b * ((β 1 0 : ℤ) : ZMod N) = 1) := by
  revert N β
  exact @_root_.P2MW.S_CongruenceSubgroup_mem_or_neg_mem_Gamma1_iff_and_exists_T_zpow_S_inv_iff.solution
