/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm (git blob d9fcc41b0d5621081fd13d187df1bbc2fa82ecdc, sha256 69473db79d34145aec3eecca6541a8a1f11905c4d43c247c82e680d187804e17).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicHaar
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
    (F : Type) [Field F] [NumberField F]
    (a : (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)ˣ) :
    (MeasureTheory.distribHaarChar (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) a : ℝ)
      = (∏ w : NumberField.InfinitePlace F,
            ‖(a : NumberField.AdeleRing (NumberField.RingOfIntegers F) F).1 w‖ ^ w.mult)
        * ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
            ‖(a : NumberField.AdeleRing (NumberField.RingOfIntegers F) F).2 v‖ := by
  revert F a
  exact @_root_.P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.solution
