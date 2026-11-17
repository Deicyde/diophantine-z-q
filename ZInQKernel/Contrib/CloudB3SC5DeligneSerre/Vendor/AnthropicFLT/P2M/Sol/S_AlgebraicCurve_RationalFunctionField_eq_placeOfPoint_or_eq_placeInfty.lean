/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_RationalFunctionField_eq_placeOfPoint_or_eq_placeInfty (git blob dcdc4a6ae6c4dfd4ae6bc3a779ca513a21bcf691, sha256 8ff8106af16f8efcd36faa5e99d6a3c12a21093a17e29a17d602cd2f357359c1).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.IsAlgClosed.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RatFuncPlaces
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_RationalFunctionField_eq_ofHeightOneSpectrum_or_eq_placeInfty

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace Polynomial
end Polynomial
namespace IsDedekindDomain
end IsDedekindDomain
namespace AlgebraicCurve
end AlgebraicCurve
namespace P2MW.S_AlgebraicCurve_RationalFunctionField_eq_placeOfPoint_or_eq_placeInfty.AlgebraicCurve
end P2MW.S_AlgebraicCurve_RationalFunctionField_eq_placeOfPoint_or_eq_placeInfty.AlgebraicCurve
namespace AlgebraicCurve.RationalFunctionField
end AlgebraicCurve.RationalFunctionField
namespace P2MW.S_AlgebraicCurve_RationalFunctionField_eq_placeOfPoint_or_eq_placeInfty.AlgebraicCurve.RationalFunctionField
end P2MW.S_AlgebraicCurve_RationalFunctionField_eq_placeOfPoint_or_eq_placeInfty.AlgebraicCurve.RationalFunctionField

namespace P2MW.S_AlgebraicCurve_RationalFunctionField_eq_placeOfPoint_or_eq_placeInfty

open _root_.Polynomial
open _root_.IsDedekindDomain
open _root_.AlgebraicCurve hiding RationalFunctionField.exists_eq_placeOfPoint
open _root_.P2MW.S_AlgebraicCurve_RationalFunctionField_eq_placeOfPoint_or_eq_placeInfty.AlgebraicCurve
open _root_.AlgebraicCurve.RationalFunctionField hiding exists_eq_placeOfPoint
open _root_.P2MW.S_AlgebraicCurve_RationalFunctionField_eq_placeOfPoint_or_eq_placeInfty.AlgebraicCurve.RationalFunctionField

open scoped Polynomial

namespace AlgebraicCurve
export _root_.AlgebraicCurve (Place Place.ofHeightOneSpectrum RationalFunctionField.eq_ofHeightOneSpectrum_or_eq_placeInfty)
namespace RationalFunctionField
export _root_.AlgebraicCurve.RationalFunctionField (placeInfty heightOneSpectrumOfIrreducible heightOneSpectrumOfIrreducible_asIdeal exists_irreducible_span placeOfPoint placeOfPoint_eq_ofHeightOneSpectrum eq_ofHeightOneSpectrum_or_eq_placeInfty)
open _root_.AlgebraicCurve.RationalFunctionField hiding exists_eq_placeOfPoint
open _root_.AlgebraicCurve hiding RationalFunctionField.exists_eq_placeOfPoint

variable (K : Type*) [Field K]

theorem exists_eq_placeOfPoint [IsAlgClosed K] (w : HeightOneSpectrum K[X]) :
    ∃ a : K, Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w = placeOfPoint K a := by
  obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w

  have hdeg : p.degree ≠ 0 := by
    rw [IsAlgClosed.degree_eq_one_of_irreducible K hp]
    exact one_ne_zero
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root p hdeg
  refine ⟨a, ?_⟩

  have hassoc : Associated ((X : K[X]) - C a) p :=
    (irreducible_X_sub_C a).associated_of_dvd hp (dvd_iff_isRoot.mpr ha)
  have hideal : w = heightOneSpectrumOfIrreducible K (irreducible_X_sub_C a) :=
    HeightOneSpectrum.ext (by
      rw [hwp, heightOneSpectrumOfIrreducible_asIdeal]
      exact (Ideal.span_singleton_eq_span_singleton.mpr hassoc).symm)
  rw [hideal, placeOfPoint_eq_ofHeightOneSpectrum]

end AlgebraicCurve.RationalFunctionField

open _root_.AlgebraicCurve hiding RationalFunctionField.exists_eq_placeOfPoint in open _root_.AlgebraicCurve.RationalFunctionField hiding exists_eq_placeOfPoint in open _root_.P2MW.S_AlgebraicCurve_RationalFunctionField_eq_placeOfPoint_or_eq_placeInfty.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_RationalFunctionField_eq_placeOfPoint_or_eq_placeInfty.AlgebraicCurve.RationalFunctionField in
theorem solution (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)] (v : Place K (RatFunc K)) : (∃ a : K, v = placeOfPoint K a) ∨ v = placeInfty K := by
  rcases AlgebraicCurve.RationalFunctionField.eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, hw⟩ | hw
  · obtain ⟨a, ha⟩ := exists_eq_placeOfPoint K w
    exact Or.inl ⟨a, hw.trans ha⟩
  · exact Or.inr hw
