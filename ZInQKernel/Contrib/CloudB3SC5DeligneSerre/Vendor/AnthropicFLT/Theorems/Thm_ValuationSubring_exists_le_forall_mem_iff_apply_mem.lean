/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ValuationSubring_exists_le_forall_mem_iff_apply_mem (git blob 8e2095dedc06dcbefae6c856886178da55d86f9f, sha256 e39c9be5e0bc5ad2f646627a257454b8440ce4f76a475a0aaeb0c1ac0a85e4de).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ValuationSubring_exists_le_forall_mem_iff_apply_mem

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem ValuationSubring.exists_le_forall_mem_iff_apply_mem
    {F : Type*} [Field F] (O : ValuationSubring F)
    {Kbar : Type*} [Field Kbar] (res : O →+* Kbar)
    (hker : IsLocalRing.maximalIdeal O ≤ RingHom.ker res)
    (W : ValuationSubring Kbar) :
    ∃ O' : ValuationSubring F, O' ≤ O ∧
      (∀ x : O, (x : F) ∈ O' ↔ res x ∈ W) ∧
      (∀ x : O, (x : F) ∈ O'.nonunits ↔ res x ∈ W.nonunits) := by
  revert F O Kbar res hker W
  exact @_root_.P2MW.S_ValuationSubring_exists_le_forall_mem_iff_apply_mem.solution
