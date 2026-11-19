/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_eq_one_of_isCompact_of_mem (git blob 6ba3dd18a86e3bc82d792f43886829e4305796a1, sha256 83f5146c341c2d5b7e626943a5606c62ea9e606750979de480219b42c77cc015).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_TateGlobalZeta
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_TateGlobal_ideleNorm_det_eq_one_of_isCompact_of_mem

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open NumberField AutomorphicForm

theorem NumberField.TateGlobal.ideleNorm_det_eq_one_of_isCompact_of_mem
    (F : Type) [Field F] [NumberField F]
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (u : AdelicGL2 (𝓞 F) F) (hu : u ∈ U) :
    ideleNorm F (Matrix.GeneralLinearGroup.det u) = 1 := by
  revert F U hU u hu
  exact @_root_.P2MW.S_NumberField_TateGlobal_ideleNorm_det_eq_one_of_isCompact_of_mem.solution
