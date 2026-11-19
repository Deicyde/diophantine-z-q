/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_isLocallyConstant_iwasawaShellIndex_and_measurable (git blob 36257d2ddb3b344ff113c53e510d7f8affac3ced, sha256 78c331d6129dd2d97dcbab68262d446f643846b1a48066c35af872d81fbe1208).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_IwasawaShellIndex
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicHaar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_isLocallyConstant_iwasawaShellIndex_and_measurable

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.isLocallyConstant_iwasawaShellIndex_and_measurable
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    IsLocallyConstant (iwasawaShellIndex K v) ∧ Measurable (iwasawaShellIndex K v) := by
  revert K v
  exact @_root_.P2MW.S_AutomorphicForm_isLocallyConstant_iwasawaShellIndex_and_measurable.solution
