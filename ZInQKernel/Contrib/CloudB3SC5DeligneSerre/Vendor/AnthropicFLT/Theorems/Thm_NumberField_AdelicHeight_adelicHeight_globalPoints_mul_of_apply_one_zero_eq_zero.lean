/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_AdelicHeight_adelicHeight_globalPoints_mul_of_apply_one_zero_eq_zero (git blob 20b9bf65097984d5adff44c35dad0f3df5186123, sha256 12af71d5c477180cb4d76ea69845efb8b6235c492fb9713061335bd05059d3fb).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RightConvolution
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_FactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_TateGlobalZeta
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicFourier
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicHeight
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_AdelicHeight_adelicHeight_globalPoints_mul_of_apply_one_zero_eq_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain NumberField.TateGlobal NumberField.AdelicHeight

theorem NumberField.AdelicHeight.adelicHeight_globalPoints_mul_of_apply_one_zero_eq_zero
    (F : Type) [Field F] [NumberField F]
    (γ : GL (Fin 2) F) (hγ : (γ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) (h : AdelicGL2 (𝓞 F) F) :
    adelicHeight F (globalPoints (𝓞 F) F γ * h) = adelicHeight F h := by
  revert F γ hγ h
  exact @_root_.P2MW.S_NumberField_AdelicHeight_adelicHeight_globalPoints_mul_of_apply_one_zero_eq_zero.solution
