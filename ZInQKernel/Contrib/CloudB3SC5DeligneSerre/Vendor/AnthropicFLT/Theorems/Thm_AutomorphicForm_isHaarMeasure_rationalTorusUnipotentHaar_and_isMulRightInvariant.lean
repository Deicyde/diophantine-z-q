/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant (git blob 0737aa996b28ea67b2d571d08ff7562265df1f93, sha256 7b636a71fe6c3a347b1483c95b7ed93d3e88528d6f0215a02ef36edbcfce3728).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_BorelSubgroup
import Mathlib.MeasureTheory.Group.FundamentalDomain
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel AutomorphicForm
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem AutomorphicForm.isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant
    (K : Type) [Field K] [NumberField K] :
    (rationalTorusUnipotentHaar K).IsHaarMeasure ∧ (rationalTorusUnipotentHaar K).IsMulRightInvariant := by
  revert K
  exact @_root_.P2MW.S_AutomorphicForm_isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant.solution
