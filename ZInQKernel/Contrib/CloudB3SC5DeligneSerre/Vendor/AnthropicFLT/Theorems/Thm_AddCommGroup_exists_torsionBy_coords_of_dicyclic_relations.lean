/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AddCommGroup_exists_torsionBy_coords_of_dicyclic_relations (git blob 23a5ab8ae7c9542d9b1eef33aaf9f0be17d338cd, sha256 61deee6549c54e9cc2da2cd52ad3ec216aaee460b7e6294c45f3cfcf4d8ce6b1).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AddCommGroup_exists_torsionBy_coords_of_dicyclic_relations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem AddCommGroup.exists_torsionBy_coords_of_dicyclic_relations
    (M : ℕ) [NeZero M] (hM : ¬ 3 ∣ M) {A : Type*} [AddCommGroup A]
    (e : ZMod M × ZMod M ≃+ Submodule.torsionBy ℤ A M)
    (α β : A →+ A) (hα : ∀ T, α (α T) = -T) (hβ : ∀ T, β (β T) + β T + T = 0)
    (hαβ : ∀ T, α (β T) = β (β (α T))) :
    (∃ P : A, (M : ℤ) • P = 0 ∧ ∀ T : A, (M : ℤ) • T = 0 →
      ∃! c : ZMod M × ZMod M, c.1.val • P + c.2.val • β P = T) ∧
    (∃ P : A, (M : ℤ) • P = 0 ∧ ∀ T : A, (M : ℤ) • T = 0 →
      ∃! c : ZMod M × ZMod M, c.1.val • P + c.2.val • α P = T) := by
  revert M hM A e α β hα hβ hαβ
  exact @_root_.P2MW.S_AddCommGroup_exists_torsionBy_coords_of_dicyclic_relations.solution
