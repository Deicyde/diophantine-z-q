/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_ideleNorm_det_globalPoints (git blob bceee83efc869fbe45b8ce6133f805fc875b8073, sha256 103be6cfb3f0a55e86752133a87311af4401ac2633065efa5e02f36eba984bbe).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_AdelicLsXi
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_TateGlobalZeta
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_ideleNorm_det_globalPoints

set_option autoImplicit false

open scoped NumberField

theorem solution
    {F : Type} [Field F] [NumberField F] (γ : Matrix.GeneralLinearGroup (Fin 2) F) :
    NumberField.TateGlobal.ideleNorm F
        (Matrix.GeneralLinearGroup.det (AutomorphicForm.globalPoints (𝓞 F) F γ)) = 1 := by
  have hdet : Matrix.GeneralLinearGroup.det (AutomorphicForm.globalPoints (𝓞 F) F γ)
      = Units.map (algebraMap F (NumberField.AdeleRing (𝓞 F) F)).toMonoidHom
          (Matrix.GeneralLinearGroup.det γ) := by
    refine Units.ext ?_
    rw [Units.coe_map, Matrix.GeneralLinearGroup.val_det_apply,
      Matrix.GeneralLinearGroup.val_det_apply, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      RingHom.map_det]
    rfl
  letI := NumberField.AdelicHaar.adeleBorel (𝓞 F) F
  haveI := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 F) F
  unfold NumberField.TateGlobal.ideleNorm
  rw [hdet, NumberField.AdeleRing.distribHaarChar_algebraMap F (Matrix.GeneralLinearGroup.det γ)]
  rfl
