/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_TateGlobal_compactSpace_normOneIdeleClass (git blob 709d58b3ccdd4dfcb29adc64cb29b02191a128ca, sha256 bade061d8f40b140d63e7f7ac2d78d4a5fff512e4f142034c2c66cdac6cd838b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_TateGlobalZeta
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_M4aHerbrand_IdeleClassVocab
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open NumberField M4aHerbrand

theorem NumberField.TateGlobal.compactSpace_normOneIdeleClass (F : Type) [Field F] [NumberField F] :
    CompactSpace (↥(NumberField.TateGlobal.normOneIdeles F) ⧸
      (principalIdeles (𝓞 F) F).subgroupOf (NumberField.TateGlobal.normOneIdeles F)) := by
  revert F
  exact @_root_.P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.solution
