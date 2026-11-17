/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_Place_ramificationIndexAlong_eq_ord_sub_of_restrictAlong_eq_placeOfPoint (git blob 1d568149d11a62e5ee5e1826cc3040b1fd7183c3, sha256 7b6a7449aed75f3a2cce9656153fd3c35f978014596d955aa1e803a9ce8ca69d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Correspondence
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RatFuncPlaces
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeOfPoint_algebraMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace AlgebraicCurve
end AlgebraicCurve
namespace P2MW.S_AlgebraicCurve_Place_ramificationIndexAlong_eq_ord_sub_of_restrictAlong_eq_placeOfPoint.AlgebraicCurve
end P2MW.S_AlgebraicCurve_Place_ramificationIndexAlong_eq_ord_sub_of_restrictAlong_eq_placeOfPoint.AlgebraicCurve
namespace AlgebraicCurve.RationalFunctionField
end AlgebraicCurve.RationalFunctionField
namespace AlgebraicCurve.Place
end AlgebraicCurve.Place

namespace P2MW.S_AlgebraicCurve_Place_ramificationIndexAlong_eq_ord_sub_of_restrictAlong_eq_placeOfPoint
set_option autoImplicit false
open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_Place_ramificationIndexAlong_eq_ord_sub_of_restrictAlong_eq_placeOfPoint.AlgebraicCurve
open _root_.AlgebraicCurve.RationalFunctionField

namespace AlgebraicCurve export _root_.AlgebraicCurve (Place.ramificationIndexAlong Place.ord_restrictAlong Place RationalFunctionField.placeOfPoint) namespace Place export _root_.AlgebraicCurve.Place (restrictAlong ramificationIndexAlong ord_restrictAlong ord) end AlgebraicCurve.Place
open scoped _root_.AlgebraicCurve _root_.AlgebraicCurve.Place in

private theorem AlgebraicCurve.Place.solution_impl
    {K F : Type*} [Field K] [Field F] [Algebra K F] [DecidableEq (RatFunc K)]
    (φ : RatFunc K →ₐ[K] F) (hφ : φ.toRingHom.IsIntegral)
    (w : AlgebraicCurve.Place K F) (a : K)
    (hwa : w.restrictAlong φ hφ = AlgebraicCurve.RationalFunctionField.placeOfPoint K a) :
    (AlgebraicCurve.Place.ramificationIndexAlong φ w : ℤ) =
      w.ord (φ (RatFunc.X : RatFunc K) - algebraMap K F a) := by

  have key := AlgebraicCurve.Place.ord_restrictAlong φ hφ w
    ((RatFunc.X : RatFunc K) - algebraMap K (RatFunc K) a)

  rw [map_sub, AlgHom.commutes] at key

  rw [hwa] at key

  have hpoly : (RatFunc.X : RatFunc K) - algebraMap K (RatFunc K) a =
      algebraMap (Polynomial K) (RatFunc K) (Polynomial.X - Polynomial.C a) := by
    simp [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  rw [hpoly, ord_placeOfPoint_algebraMap a (Polynomial.X_sub_C_ne_zero a)] at key

  simp only [Polynomial.rootMultiplicity_X_sub_C_self, Nat.cast_one, mul_one] at key
  exact key.symm

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] [DecidableEq (RatFunc K)] (φ : RatFunc K →ₐ[K] F) (hφ : φ.toRingHom.IsIntegral) (w : AlgebraicCurve.Place K F) (a : K) (hwa : w.restrictAlong φ hφ = AlgebraicCurve.RationalFunctionField.placeOfPoint K a) :
    (AlgebraicCurve.Place.ramificationIndexAlong φ w : ℤ) =
      w.ord (φ (RatFunc.X : RatFunc K) - algebraMap K F a) :=
  AlgebraicCurve.Place.solution_impl φ hφ w a hwa
