/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AddCommGroup_nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq
Modified for the Z-in-Q kernel (2026-11-15, task flt-cqj2): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.P2M.Sol.S_AddCommGroup_nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem AddCommGroup.nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq
    {A : Type*} [AddCommGroup A] {n : ℕ} (hn : n ≠ 0)
    (hcard : ∀ d : ℕ, d ∣ n → Nat.card (Submodule.torsionBy ℤ A d) = d ^ 2) :
    Nonempty (ZMod n × ZMod n ≃+ Submodule.torsionBy ℤ A n) := by p2m_exact_reverting @_root_.P2MW.S_AddCommGroup_nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq.solution
