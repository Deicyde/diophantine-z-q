/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ValuationSubring_mem_of_forall_mem_iff_of_subset (git blob 2dadd0bde3536ecff03cd504ba697b57d07779b3, sha256 17ccfe112d29c08b92e2fa8309d07b5bb609fb233c5b710855fff208913e87ad).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ValuationSubring_mem_of_forall_mem_iff_of_subset

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem ValuationSubring.mem_of_forall_mem_iff_of_subset
    {F : Type*} [Field F] (K : Subfield F) (O V : ValuationSubring F)
    (hKV : ∀ e ∈ K, e ∈ O → e ∈ V) (g : F)
    (hg : ∀ V' : ValuationSubring F, (∀ e ∈ K, e ∈ V' ↔ e ∈ O) → g ∈ V') :
    g ∈ V := by
  revert F K O V hKV g hg
  exact @_root_.P2MW.S_ValuationSubring_mem_of_forall_mem_iff_of_subset.solution
