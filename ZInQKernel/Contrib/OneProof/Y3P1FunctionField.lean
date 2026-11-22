import ZInQKernel.Contrib.OneProof.Y3ToP1jDescent
import ZInQKernel.Contrib.RC53Assist.S2aNumberField.BirationalComparison
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Curve.Dimension
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Algebra.Algebra.Rat

/-! # The function field and valuation stalks of the target projective line -/

noncomputable section

set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory
open scoped Polynomial
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.ProjectiveLine
open ZInQ.Contrib.RC53Assist.AbelianCurve (functionFieldAlgebra fromFunctionField)

namespace Y3P1j.P1

instance integral_PQ : IsIntegral PQ.left := relative_isIntegral ℚ

/-- Properness of the fixed projective-line target over ℚ. -/
theorem proper_PQ : IsProper PQ.hom := proper_L

/-- Each local ring of the fixed projective-line target is a valuation ring. -/
theorem valuationStalk_PQ (x : PQ.left) : ValuationRing (PQ.left.presheaf.stalk x) := by
  haveI : SmoothOfRelativeDimension 1 PQ.hom := smooth_L
  exact Scheme.valuationRing_stalk PQ.hom x

/-- The standard affine chart identifies the function field of the fixed projective-line target
with the rational function field over ℚ. -/
def functionFieldEquivRatFunc :
    letI := functionFieldAlgebra PQ.hom
    PQ.left.functionField ≃ₐ[ℚ] RatFunc ℚ := by
  letI := functionFieldAlgebra PQ.hom
  let U := std i0
  haveI : Nonempty U := ⟨relativeChartPoint (𝟙 SQ) i0 0 (IsLocalRing.closedPoint ℚ)⟩
  have hU : IsAffineOpen U := isAffineOpen_standardOpen I SQ i0
  haveI := functionField_isFractionRing_of_isAffineOpen PQ.left U hU
  let c : ℚ[X] ≃+* Γ(PQ.left, U) := RingEquiv.ofBijective (chartPoly i0) (chartPoly_bijective i0)
  let e : RatFunc ℚ ≃+* PQ.left.functionField := IsFractionRing.ringEquivOfRingEquiv c
  exact { e.symm with commutes' := RingHom.map_rat_algebraMap e.symm.toRingHom }

/-- A proper integral rational curve with valuation local rings is isomorphic over ℚ to the
fixed target in `Y3ToP1j`. -/
theorem nonempty_iso_PQ_of_functionField (C : Over SQ) [IsIntegral C.left] [IsProper C.hom]
    (hC : ∀ x : C.left, ValuationRing (C.left.presheaf.stalk x))
    (e : letI := functionFieldAlgebra C.hom; C.left.functionField ≃ₐ[ℚ] RatFunc ℚ) :
    Nonempty (C ≅ PQ) := by
  letI := functionFieldAlgebra C.hom
  letI := functionFieldAlgebra PQ.hom
  haveI : IsProper PQ.hom := proper_PQ
  let F := functionFieldEquivRatFunc.trans e.symm
  obtain ⟨i, hi, _⟩ := ZInQ.Contrib.RC53Assist.S2aNumberField.isomorphism_of_functionField_equiv
    C.hom PQ.hom hC valuationStalk_PQ F.toRingEquiv F.commutes
  exact ⟨Over.isoMk i hi⟩

end Y3P1j.P1

#print axioms Y3P1j.P1.functionFieldEquivRatFunc
#print axioms Y3P1j.P1.valuationStalk_PQ
#print axioms Y3P1j.P1.nonempty_iso_PQ_of_functionField
