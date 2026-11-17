/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CongruenceSubgroup_Gamma_div_le_gamma1_inf_Gamma_sup_zpowers (git blob 1a65d7fe29ad4f50acee23ff368cadc8b9d9804b, sha256 0416ace75224f649b24177a4fe52b6a17822049689bcba8d809f077687326d73).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CongruenceSubgroup_Gamma_div_le_gamma1_inf_Gamma_sup_zpowers

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CongruenceSubgroup.Gamma_div_le_gamma1_inf_Gamma_sup_zpowers
    (N p : ℕ) [NeZero N] (hp : p.Prime) (hpN : p ∣ N) :
    Gamma (N / p) ≤ (Gamma1 N ⊓ Gamma (N / p ^ N.factorization p)) ⊔
      Subgroup.zpowers (ModularGroup.S * ModularGroup.T ^ ((N / p : ℕ) : ℤ) * ModularGroup.S⁻¹) := by
  revert N p hp hpN
  exact @_root_.P2MW.S_CongruenceSubgroup_Gamma_div_le_gamma1_inf_Gamma_sup_zpowers.solution
