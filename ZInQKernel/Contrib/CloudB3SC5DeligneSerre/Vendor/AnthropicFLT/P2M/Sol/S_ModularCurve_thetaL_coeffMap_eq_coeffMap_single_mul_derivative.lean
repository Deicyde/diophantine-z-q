/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_thetaL_coeffMap_eq_coeffMap_single_mul_derivative (git blob dfb9b3b523a18ea7ff920966657317df0db8350a, sha256 d6e165614722317161e624ccf80c1d18f87464369bd7ab998539697fa72586be).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_QExpansionDiff
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace ModularCurve
end ModularCurve

namespace P2MW.S_ModularCurve_thetaL_coeffMap_eq_coeffMap_single_mul_derivative

namespace ModularCurve
export _root_.ModularCurve (thetaL thetaL_apply coeffMap coeffMap_coeff)
open _root_.ModularCurve

section

variable {R K : Type*} [CommRing R] [Field K]

private theorem coeffMap_single_one (φ : R →+* K) :
    coeffMap φ (HahnSeries.single (1 : ℤ) (1 : R)) = HahnSeries.single (1 : ℤ) (1 : K) := by
  ext n
  rw [coeffMap_coeff, HahnSeries.coeff_single, HahnSeries.coeff_single]
  split_ifs <;> simp

private theorem derivative_coeffMap (φ : R →+* K) (w : LaurentSeries R) :
    LaurentSeries.derivative K (coeffMap φ w) = coeffMap φ (LaurentSeries.derivative R w) := by
  ext n
  rw [LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff, coeffMap_coeff,
    coeffMap_coeff, LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff, map_zsmul]

private theorem thetaL_coeffMap_impl (φ : R →+* K) (w : LaurentSeries R) :
    thetaL K (coeffMap φ w) =
      coeffMap φ (HahnSeries.single (1 : ℤ) (1 : R) * LaurentSeries.derivative R w) := by
  rw [thetaL_apply, derivative_coeffMap, map_mul, coeffMap_single_one]

end

end ModularCurve

theorem solution {R : Type*} [CommRing R]
    {K : Type*} [Field K] (φ : R →+* K) (w : LaurentSeries R) :
    ModularCurve.thetaL K (ModularCurve.coeffMap φ w) =
      ModularCurve.coeffMap φ (HahnSeries.single (1 : ℤ) (1 : R) * LaurentSeries.derivative R w) :=
  ModularCurve.thetaL_coeffMap_impl φ w
