/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar (git blob 93f88bc43a5120a9fc69299b9744413e1f7ccc35, sha256 02c85dfcf92cb62cca1770b98a1b6e6df5a15ced389c73174ed351893812689e).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicHaar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped NumberField

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar (F : Type) [Field F] [NumberField F] :
    (adelicGLHaar (Fin 2) (𝓞 F) F).IsMulRightInvariant := by
  revert F
  exact @_root_.P2MW.S_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar.solution
