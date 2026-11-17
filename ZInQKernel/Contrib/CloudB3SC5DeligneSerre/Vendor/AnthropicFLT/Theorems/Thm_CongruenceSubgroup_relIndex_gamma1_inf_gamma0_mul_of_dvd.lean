/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CongruenceSubgroup_relIndex_gamma1_inf_gamma0_mul_of_dvd (git blob 184d544f2de21af8aebde238d4261915b839bcc9, sha256 0cb093081f56e29fcd05d2050e255a393795f1a1ff0aaf09d7ddd9d4c774219e).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CongruenceSubgroup_relIndex_gamma1_inf_gamma0_mul_of_dvd

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem CongruenceSubgroup.relIndex_gamma1_inf_gamma0_mul_of_dvd (M q : ℕ) [NeZero M] (hq : q ∣ M) :
    (CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 (M * q)).relIndex (CongruenceSubgroup.Gamma1 M) = q := by
  revert M q hq
  exact @_root_.P2MW.S_CongruenceSubgroup_relIndex_gamma1_inf_gamma0_mul_of_dvd.solution
