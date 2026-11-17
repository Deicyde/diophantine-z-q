/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_StandardAddChar_isGlobalAddChar_stdAddChar (git blob dd5fa73336ccc077ebafa8a567770a78f2c3afbf, sha256 934dff47db887f511b96c612f0f5a2d08af35277dfbb180457c0b8762679b335).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicTraceFin
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_StandardAddChar_isGlobalAddChar_stdAddChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField NumberField.StandardAddChar AutomorphicForm
theorem NumberField.StandardAddChar.isGlobalAddChar_stdAddChar
    (F : Type) [Field F] [NumberField F] :
    IsGlobalAddChar F (stdAddChar F) := by
  revert F
  exact @_root_.P2MW.S_NumberField_StandardAddChar_isGlobalAddChar_stdAddChar.solution
