/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AddAut_exists_mem_apply_eq_of_addOrderOf_eq_of_transvection_mem (git blob a7f5cc2ef9b353e9087d7820349876b31ccaecf8, sha256 ef37a93cb4ed5442a009d0d0a950763cfb8016dd9cee43d17137436601286d3f).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AddAut_exists_mem_apply_eq_of_addOrderOf_eq_of_transvection_mem
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem AddAut.exists_mem_apply_eq_of_addOrderOf_eq_of_transvection_mem
    (M : ℕ) [NeZero M] (H : Subgroup (AddAut (ZMod M × ZMod M)))
    (htrans : ∀ v w : ZMod M × ZMod M, addOrderOf v = M → addOrderOf w = M →
      ∃ h ∈ H, ∃ n : ℤ, h v = n • w)
    (ht : ∃ t ∈ H, ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      t (1, 0) = ε • ((1, 0) : ZMod M × ZMod M) ∧ t (0, 1) = ε • ((1, 1) : ZMod M × ZMod M))
    (v w : ZMod M × ZMod M) (hv : addOrderOf v = M) (hw : addOrderOf w = M) :
    ∃ h ∈ H, h v = w := by
  revert M H htrans ht v w hv hw
  exact @_root_.P2MW.S_AddAut_exists_mem_apply_eq_of_addOrderOf_eq_of_transvection_mem.solution
