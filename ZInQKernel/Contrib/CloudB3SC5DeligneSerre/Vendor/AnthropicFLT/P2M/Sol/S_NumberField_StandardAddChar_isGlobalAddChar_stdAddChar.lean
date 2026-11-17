/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_NumberField_StandardAddChar_isGlobalAddChar_stdAddChar (git blob 0e9a107b1e153c516e6ad9b1b4659adc2844aa6a, sha256 b75f823dc5be87c9f980bfad72fb64d5979ab3d7fbcdc063aa68af7ec15c87b6).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicTraceFin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_NumberField_StandardAddChar_isGlobalAddChar_stdAddChar

open NumberField NumberField.StandardAddChar AutomorphicForm

theorem solution
    (F : Type) [Field F] [NumberField F] :
    IsGlobalAddChar F (stdAddChar F) :=
  (adelicTraceData F).isGlobalAddChar_psiK
