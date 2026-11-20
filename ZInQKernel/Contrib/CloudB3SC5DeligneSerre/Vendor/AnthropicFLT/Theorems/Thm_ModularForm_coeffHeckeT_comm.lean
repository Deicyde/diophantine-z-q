/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularForm_coeffHeckeT_comm (git blob ab59ad3546bb8a285b352097ebe0b6bf99236fe8, sha256 22b1b771b39e6922e4be48e63fd78eb3c8881fdfb0ca3c2b3695e31eb34d552b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularForm_HeckeOperator
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularForm_coeffHeckeT_comm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem ModularForm.coeffHeckeT_comm (k : ℤ) {p q : ℕ} (hpq : Nat.Coprime p q) (a : ℕ → ℂ) : ModularForm.coeffHeckeT k p (ModularForm.coeffHeckeT k q a) = ModularForm.coeffHeckeT k q (ModularForm.coeffHeckeT k p a) := by
  revert k p q hpq a
  exact @_root_.P2MW.S_ModularForm_coeffHeckeT_comm.solution
