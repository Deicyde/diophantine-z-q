import ZInQKernel.Contrib.OneProof.RC.ModelTorsion.UniversalShort
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms

/-! # Reading the universal short curve at a coefficient point -/

namespace WeierstrassCurve.ModelLevels

open ModelTorsion

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
  (W : WeierstrassCurve B) [W.IsElliptic] [W.IsShortNF]

private noncomputable def shortCoefficientEval : MvPolynomial (Fin 2) R →ₐ[R] B :=
  MvPolynomial.aeval (fun i => if i = 0 then W.a₄ else W.a₆)

private theorem shortEquation_map :
    (shortEquation R).map (shortCoefficientEval (R := R) W).toRingHom = W := by
  ext <;>
    simp [shortEquation, shortCoefficientEval, a₁_of_isShortNF, a₂_of_isShortNF, a₃_of_isShortNF]

private theorem shortCoefficientEval_discriminant_isUnit :
    IsUnit (shortCoefficientEval (R := R) W (shortEquation R).Δ) := by
  change IsUnit ((shortCoefficientEval (R := R) W).toRingHom (shortEquation R).Δ)
  rw [← WeierstrassCurve.map_Δ, shortEquation_map W]
  exact W.isUnit_Δ

/-- The coefficient point classifying the indicated short equation with
invertible discriminant, over any algebra of the base ring. -/
noncomputable def shortCoefficientPoint : ShortBase R →ₐ[R] B :=
  IsLocalization.Away.liftAlgHom _ (shortCoefficientEval_discriminant_isUnit (R := R) W)

/-- The short family specializes along its classifying coefficient point
to the given short equation. -/
theorem shortFamily_map_coefficientPoint :
    (shortFamily R).map (shortCoefficientPoint (R := R) W).toRingHom = W := by
  rw [shortFamily, WeierstrassCurve.map_map, shortCoefficientPoint,
    IsLocalization.Away.liftAlgHom_toRingHom, IsLocalization.Away.lift_comp]
  exact shortEquation_map W

#print axioms shortCoefficientEval
#print axioms shortEquation_map
#print axioms shortCoefficientEval_discriminant_isUnit
#print axioms shortCoefficientPoint
#print axioms shortFamily_map_coefficientPoint

end WeierstrassCurve.ModelLevels
