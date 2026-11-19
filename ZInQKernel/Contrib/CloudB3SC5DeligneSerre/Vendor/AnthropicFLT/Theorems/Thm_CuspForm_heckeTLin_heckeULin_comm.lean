/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CuspForm_heckeTLin_heckeULin_comm (git blob 387cfd2444f5525b369d24a51fe9595461944fc2, sha256 53e80f99ce1a231431a8118acfa30926c1c2f938077ad9aca6207284d0a11fa5).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularForm_HeckeOperatorForms
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CuspForm_heckeTLin_heckeULin_comm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem CuspForm.heckeTLin_heckeULin_comm {N : ℕ} [NeZero N] (k : ℤ) {p q : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) (hqN : q ∣ N) :
    Commute (CuspForm.heckeTLin k hp hpN) (CuspForm.heckeULin k hqN) := by
  revert N k p q hp hpN hqN
  exact @_root_.P2MW.S_CuspForm_heckeTLin_heckeULin_comm.solution
