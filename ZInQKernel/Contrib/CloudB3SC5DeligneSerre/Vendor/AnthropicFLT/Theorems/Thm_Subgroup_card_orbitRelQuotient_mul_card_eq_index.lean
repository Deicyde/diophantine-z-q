/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Subgroup_card_orbitRelQuotient_mul_card_eq_index (git blob 8b806179bea1909d09ad89e65ac35f01bd679bae, sha256 78b63488f696510bbc0bbc7a1d969c31728964f386d351d27e60220a776a1cec).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Subgroup_card_orbitRelQuotient_mul_card_eq_index

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false
theorem Subgroup.card_orbitRelQuotient_mul_card_eq_index {M : Type*} [Group M] (H K : Subgroup M)
    (hKH : ∀ g x : M, x ∈ K → g⁻¹ * x * g ∈ H → x = 1) :
    Nat.card (MulAction.orbitRel.Quotient H (M ⧸ K)) * Nat.card K = H.index := by
  revert M H K hKH
  exact @_root_.P2MW.S_Subgroup_card_orbitRelQuotient_mul_card_eq_index.solution
