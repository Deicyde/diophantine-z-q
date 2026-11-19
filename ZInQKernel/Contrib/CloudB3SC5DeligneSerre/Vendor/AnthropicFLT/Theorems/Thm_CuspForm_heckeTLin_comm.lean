/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CuspForm_heckeTLin_comm (git blob 58b7b19ec30c30f0bf7d6a8e30d7ce712a56f7e5, sha256 7af464679eac0e7846b7db55cfb35631555ad7ac51198373ccc6c9c48497a621).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularForm_HeckeOperatorForms
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CuspForm_heckeTLin_comm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem CuspForm.heckeTLin_comm {N : ℕ} (k : ℤ) {p q : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N)
    (hq : q.Prime) (hqN : ¬ q ∣ N) :
    Commute (CuspForm.heckeTLin k hp hpN) (CuspForm.heckeTLin k hq hqN) := by
  revert N k p q hp hpN hq hqN
  exact @_root_.P2MW.S_CuspForm_heckeTLin_comm.solution
