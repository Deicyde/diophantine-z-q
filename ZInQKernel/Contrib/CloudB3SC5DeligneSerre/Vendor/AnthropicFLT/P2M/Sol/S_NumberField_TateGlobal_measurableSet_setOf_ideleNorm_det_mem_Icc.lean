/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc (git blob 10f58f0d847ab3c52ceae10e2116386060c33668, sha256 034292fe82d8d92502bf56f5a32964d524186c83ba9645a7b3ee1b2652fb728b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_TateGlobalZeta
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc

set_option autoImplicit false

open NumberField AutomorphicForm

open NumberField.TateGlobal in

theorem solution (F : Type) [Field F] [NumberField F]
    (d₁ d₂ : ℝ) :
    @MeasurableSet (AdelicGL2 (𝓞 F) F) (NumberField.AdelicHaar.glBorel (Fin 2) (𝓞 F) F)
      {g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂} := by
  letI := NumberField.AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  exact (isClosed_Icc.preimage (NumberField.TateGlobal.continuous_ideleNorm_det F)).measurableSet
