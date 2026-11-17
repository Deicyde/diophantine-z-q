/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_AdelicHaar_adelicAddHaar_setOf_fst_apply_eq_eq_zero (git blob c8d8038a562a9f2d2360e0e2727be2fc134e00c7, sha256 f833d316a39f4826971a8467e28a2eb8ec44c6c1bdd5781973ae036241414ea0).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicHaar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_AdelicHaar_adelicAddHaar_setOf_fst_apply_eq_eq_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain

theorem NumberField.AdelicHaar.adelicAddHaar_setOf_fst_apply_eq_eq_zero
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) (c : w.Completion) :
    adelicAddHaar (𝓞 F) F {x : AdeleRing (𝓞 F) F | x.1 w = c} = 0 := by
  revert F w c
  exact @_root_.P2MW.S_NumberField_AdelicHaar_adelicAddHaar_setOf_fst_apply_eq_eq_zero.solution
