import ZInQKernel.Contrib.OneProof.RC.ModelGeneric2.AffineComparison

/-! # Regularity of the descended quotient coordinate -/

namespace WeierstrassCurve.ModelLevels.ModelGeneric2

open LeafModCurves ModelGeneric ModularCurve
open private genericJ_isFractionRing rationalAlgebra_isIntegrallyClosed from
  ZInQKernel.Contrib.OneProof.RC.ModelGeneric2.AffineComparison

attribute [local instance] Algebra.TensorProduct.rightAlgebra

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

variable {N : ℕ} [NeZero N] (h₂ : 2 ≤ N)

/-- The descended Vélu invariant is regular on the pinned rational open.
The monic modular equation makes it integral over the affine j-line, and
integral closedness gives its unique lift to the pinned rational ring. -/
noncomputable def rationalQuotientCoordinate :
    {a : Y0RationalAlgebra h₂ //
      Y0RationalGenericJInclusion h₂ a = Y0RationalGenericQuotientJ h₂} := by
  let B : Type := Y0RationalAlgebra h₂
  let E := Y0RationalGenericJ h₂
  letI := (Y0RationalJMap h₂).toRingHom.toAlgebra
  letI : Field E := genericJField h₂
  letI : IsFractionRing B E := genericJ_isFractionRing h₂
  letI : IsIntegralClosure B B E :=
    (isIntegrallyClosed_iff_isIntegralClosure E).mp (rationalAlgebra_isIntegrallyClosed h₂)
  let data := Classical.choice (nonempty_modularPolynomialData N)
  let p := data.Φ.map (Polynomial.mapRingHom (Int.castRingHom ℚ))
  let a := Y0RationalGenericQuotientJ h₂
  have h : _root_.IsIntegral (Polynomial ℚ) a := by
    refine ⟨p, data.monic.map _, ?_⟩
    change Polynomial.aeval a p = 0
    rw [← Polynomial.aeval_map_algebraMap Qj]
    exact genericQuotientJ_aeval h₂ data
  have hb : _root_.IsIntegral B a := h.tower_top
  exact ⟨IsIntegralClosure.mk' B a hb, IsIntegralClosure.algebraMap_mk' B a hb⟩

#print axioms rationalQuotientCoordinate

end WeierstrassCurve.ModelLevels.ModelGeneric2
