/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult (git blob a658b624d730696f6986509e981361d225b91ae2, sha256 582ff19eedbdcec87cdc22037df9aebfe95204f201b2240955facdea630439cf).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_TateGlobalZeta
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicVolume AutomorphicForm

theorem NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult (F : Type) [Field F] [NumberField F]
    (X : AdelicGL2 (𝓞 F) F) (hX : glFin (𝓞 F) F X ∈ finiteIntegralGL2 (𝓞 F) F) :
    ideleNorm F (Matrix.GeneralLinearGroup.det X) = ∏ w : InfinitePlace F, archDetNorm w X ^ w.mult := by
  revert F X hX
  exact @_root_.P2MW.S_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult.solution
