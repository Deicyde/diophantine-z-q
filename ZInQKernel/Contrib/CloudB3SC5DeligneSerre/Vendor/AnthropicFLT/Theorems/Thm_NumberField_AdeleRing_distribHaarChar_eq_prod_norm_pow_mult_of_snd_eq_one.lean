/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one (git blob 8c7e15b0264209783302d5304d7ed79f671805ab, sha256 f417c4ca83cdf01ab5993c949bda8df63f993b54ae0b9d29a826a898d63f7e90).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicHaar
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one
    (F : Type) [Field F] [NumberField F]
    (a : (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)ˣ)
    (ha : (a : NumberField.AdeleRing (NumberField.RingOfIntegers F) F).2 = 1) :
    (MeasureTheory.distribHaarChar (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) a : ℝ)
      = ∏ w : NumberField.InfinitePlace F,
          ‖(a : NumberField.AdeleRing (NumberField.RingOfIntegers F) F).1 w‖ ^ w.mult := by
  revert F a ha
  exact @_root_.P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one.solution
