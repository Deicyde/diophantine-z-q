/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_AdelicHaar_adelicAddHaar_setOf_snd_apply_eq_zero (git blob 145a3f7d8fea7ab9d4b041b7c31a187cb91d7738, sha256 e61596519fa22734b81f18282f4854046c36636a74f954acc8ed0fd57eecdd81).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicHaar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_AdelicHaar_adelicAddHaar_setOf_snd_apply_eq_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain

theorem NumberField.AdelicHaar.adelicAddHaar_setOf_snd_apply_eq_zero
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    adelicAddHaar (𝓞 F) F {x : AdeleRing (𝓞 F) F | x.2 v = 0} = 0 := by
  revert F v
  exact @_root_.P2MW.S_NumberField_AdelicHaar_adelicAddHaar_setOf_snd_apply_eq_zero.solution
