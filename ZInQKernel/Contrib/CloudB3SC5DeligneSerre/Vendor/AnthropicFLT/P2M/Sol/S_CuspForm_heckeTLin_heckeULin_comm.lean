/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_CuspForm_heckeTLin_heckeULin_comm (git blob e2a39fc02ac64e126bb774ed1ac273926f989757, sha256 35da2984867428c0f34b94291f4163e1cfbfc7bb722c805e59035284d40c8dd8).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularForm_HeckeOperatorForms
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularFormClass_heckeT_heckeU_comm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_CuspForm_heckeTLin_heckeULin_comm

theorem solution {N : ℕ} [NeZero N] (k : ℤ) {p q : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) (hqN : q ∣ N) :
    Commute (CuspForm.heckeTLin k hp hpN) (CuspForm.heckeULin k hqN) := by
  rw [commute_iff_eq]; ext f τ
  simpa using congrFun (ModularFormClass.heckeT_heckeU_comm f (by simp)
    ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => hpN (h.trans hqN))) τ
