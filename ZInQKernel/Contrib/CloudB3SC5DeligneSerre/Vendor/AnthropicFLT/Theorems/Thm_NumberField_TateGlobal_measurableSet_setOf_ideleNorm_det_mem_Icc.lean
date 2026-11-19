/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc (git blob 9923c50346f2f9cde33a6fbef2fe1e62fd757c4c, sha256 5c4f5090151a4aa06514fd699776c2cc87545d08d495389fa70a8292aa87f25a).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_TateGlobalZeta
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open NumberField AutomorphicForm

theorem NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc (F : Type) [Field F] [NumberField F]
    (d₁ d₂ : ℝ) :
    @MeasurableSet (AdelicGL2 (𝓞 F) F) (NumberField.AdelicHaar.glBorel (Fin 2) (𝓞 F) F)
      {g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂} := by
  revert F d₁ d₂
  exact @_root_.P2MW.S_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc.solution
