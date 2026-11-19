/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AddCommGroup_exists_addEquiv_prod_torsionBy_apply_eq_of_forall_exists_ne_smul (git blob 20b36eea41f75506761ec53d58e2494147de7d34, sha256 f5b6df843018c34596e9acc3783ec6ad8230ff2b1fef24e5ada737f000b155be).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AddCommGroup_exists_addEquiv_prod_torsionBy_apply_eq_of_forall_exists_ne_smul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem AddCommGroup.exists_addEquiv_prod_torsionBy_apply_eq_of_forall_exists_ne_smul
    {A : Type*} [AddCommGroup A] (n : ℕ) [NeZero n]
    (e : ZMod n × ZMod n ≃+ Submodule.torsionBy ℤ A n) (σ : A →+ A)
    (hns : ∀ p : ℕ, p.Prime → p ∣ n → ∃ a : A, addOrderOf a = p ∧ ∀ k : ℕ, σ a ≠ k • a) :
    ∃ e' : ZMod n × ZMod n ≃+ Submodule.torsionBy ℤ A n,
      ((e' (0, 1) : Submodule.torsionBy ℤ A n) : A) =
        σ ((e' (1, 0) : Submodule.torsionBy ℤ A n) : A) := by
  revert A n e σ hns
  exact @_root_.P2MW.S_AddCommGroup_exists_addEquiv_prod_torsionBy_apply_eq_of_forall_exists_ne_smul.solution
