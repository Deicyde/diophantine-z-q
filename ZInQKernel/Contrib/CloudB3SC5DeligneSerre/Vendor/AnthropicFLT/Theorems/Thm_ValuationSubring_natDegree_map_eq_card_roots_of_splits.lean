/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ValuationSubring_natDegree_map_eq_card_roots_of_splits (git blob 0976f42d25f96e5c802de6e5f5cc811c6670f815, sha256 0cbccfa3de9075a6d6d1ad5027a722632b7dca88ea6419fe8193663b3ef206cb).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ValuationSubring_natDegree_map_eq_card_roots_of_splits

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open scoped Polynomial

theorem ValuationSubring.natDegree_map_eq_card_roots_of_splits
    {E k : Type*} [Field E] [Field k] (A : ValuationSubring E) (σ : A →+* k)
    (hσ : RingHom.ker σ = IsLocalRing.maximalIdeal A)
    (p : A[X]) (hp : p.map σ ≠ 0)
    (hsplit : Multiset.card (p.map (algebraMap A E)).roots = p.natDegree) :
    (p.map σ).natDegree = Multiset.card p.roots := by
  revert E k A σ hσ p hp hsplit
  exact @_root_.P2MW.S_ValuationSubring_natDegree_map_eq_card_roots_of_splits.solution
