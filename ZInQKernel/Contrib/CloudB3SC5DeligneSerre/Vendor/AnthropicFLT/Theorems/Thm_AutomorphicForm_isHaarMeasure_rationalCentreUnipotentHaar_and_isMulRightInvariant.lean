/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_isHaarMeasure_rationalCentreUnipotentHaar_and_isMulRightInvariant (git blob d1df5250ed86e1503d66f1f5e931c93e4f50308e, sha256 1a61faae28a234c0e25fd02d898657d649b1dcc522a1b3e4e394322c90101fa9).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RationalCentreUnipotentQuotient
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_isHaarMeasure_rationalCentreUnipotentHaar_and_isMulRightInvariant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open MeasureTheory NumberField AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem AutomorphicForm.isHaarMeasure_rationalCentreUnipotentHaar_and_isMulRightInvariant
    (K : Type) [Field K] [NumberField K] :
    (rationalCentreUnipotentHaar K).IsHaarMeasure ∧ (rationalCentreUnipotentHaar K).IsMulRightInvariant := by
  revert K
  exact @_root_.P2MW.S_AutomorphicForm_isHaarMeasure_rationalCentreUnipotentHaar_and_isMulRightInvariant.solution
