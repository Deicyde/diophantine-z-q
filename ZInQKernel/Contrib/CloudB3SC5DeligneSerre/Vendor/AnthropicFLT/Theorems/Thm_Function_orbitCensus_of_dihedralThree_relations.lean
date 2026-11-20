/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Function_orbitCensus_of_dihedralThree_relations (git blob 539d4b8d080fdd54e027bdff54de3d8526cc503c, sha256 20dc673f1675646b5100b6f2f50a61393a125d19c1101f4384c9f3af3400015b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Function_orbitCensus_of_dihedralThree_relations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem Function.orbitCensus_of_dihedralThree_relations
    {X : Type*} [Fintype X] [DecidableEq X] (a b : X → X)
    (ha : ∀ x, a (a x) = x) (hb : ∀ x, b (b (b x)) = x) (hab : ∀ x, a (b x) = b (b (a x)))
    {ι : Type*} [DecidableEq ι] (c : X → ι)
    (hc : ∀ x y, c x = c y ↔
      (y = x ∨ y = a x ∨ y = b x ∨ y = b (b x) ∨ y = a (b x) ∨ y = a (b (b x))))
    (S : Finset ι) (hS : ∀ p, p ∈ S ↔ ∃ x, c x = p) :
    (∀ x, (Finset.univ.filter fun y => c y = c x).card = 1 ∨
        (Finset.univ.filter fun y => c y = c x).card = 2 ∨
        (Finset.univ.filter fun y => c y = c x).card = 3 ∨
        (Finset.univ.filter fun y => c y = c x).card = 6) ∧
    (S.filter fun p => (Finset.univ.filter fun y => c y = p).card = 1 ∨
        (Finset.univ.filter fun y => c y = p).card = 3).card =
      (Finset.univ.filter fun x => a x = x).card ∧
    (S.filter fun p => (Finset.univ.filter fun y => c y = p).card = 1).card +
        2 * (S.filter fun p => (Finset.univ.filter fun y => c y = p).card = 2).card =
      (Finset.univ.filter fun x => b x = x).card := by
  revert X a b ha hb hab ι c hc S hS
  exact @_root_.P2MW.S_Function_orbitCensus_of_dihedralThree_relations.solution
