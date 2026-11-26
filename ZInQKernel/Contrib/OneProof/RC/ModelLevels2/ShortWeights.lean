import ZInQKernel.Contrib.OneProof.RC.ModelTorsion.UniversalShort
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-! # Weights for the short Weierstrass presentation -/

namespace WeierstrassCurve.ModelLevels

open MvPolynomial ModelTorsion

/-- The coefficient weights of the short Weierstrass equation. -/
def shortCoefficientWeight (i : Fin 2) : ℤ :=
  if i = 0 then 4 else 6

/-- The short discriminant is homogeneous of degree twelve, so inverting
it calls for a generator of degree minus twelve. -/
theorem shortDiscriminant_weight (R : Type*) [CommRing R] :
    IsWeightedHomogeneous shortCoefficientWeight (shortEquation R).Δ 12 := by
  let : (shortEquation R).IsShortNF := ⟨rfl, rfl, rfl⟩
  rw [Δ_of_isShortNF]
  change IsWeightedHomogeneous shortCoefficientWeight
    (-16 * (4 * X 0 ^ 3 + 27 * X 1 ^ 2) : MvPolynomial (Fin 2) R) 12
  have h₄ : IsWeightedHomogeneous shortCoefficientWeight (X 0 : MvPolynomial (Fin 2) R) 4 :=
    isWeightedHomogeneous_X R shortCoefficientWeight 0
  have h₆ : IsWeightedHomogeneous shortCoefficientWeight (X 1 : MvPolynomial (Fin 2) R) 6 :=
    isWeightedHomogeneous_X R shortCoefficientWeight 1
  have h₄' : IsWeightedHomogeneous shortCoefficientWeight (4 * X 0 ^ 3 : MvPolynomial (Fin 2) R) 12 := by
    simpa [map_ofNat] using (h₄.pow 3).C_mul (4 : R)
  have h₆' : IsWeightedHomogeneous shortCoefficientWeight (27 * X 1 ^ 2 : MvPolynomial (Fin 2) R) 12 := by
    simpa [map_ofNat] using (h₆.pow 2).C_mul (27 : R)
  simpa [map_ofNat] using (h₄'.add h₆').C_mul (-16 : R)

/-- Weights for `a₄, a₆, x, y, Δ⁻¹`, in that order, in the polynomial
presentation before imposing the level and inverse relations. -/
def shortCoordinateWeight (i : Fin 5) : ℤ :=
  match i.val with
  | 0 => 4
  | 1 => 6
  | 2 => 2
  | 3 => 3
  | _ => -12

/-- The short curve equation is homogeneous of degree six in the
weighted polynomial presentation. -/
theorem shortCurveEquation_weight (R : Type*) [CommRing R] :
    IsWeightedHomogeneous shortCoordinateWeight
      (X 3 ^ 2 - (X 2 ^ 3 + X 0 * X 2 + X 1) : MvPolynomial (Fin 5) R) 6 := by
  have h₀ : IsWeightedHomogeneous shortCoordinateWeight (X 0 : MvPolynomial (Fin 5) R) 4 :=
    isWeightedHomogeneous_X R shortCoordinateWeight 0
  have h₁ : IsWeightedHomogeneous shortCoordinateWeight (X 1 : MvPolynomial (Fin 5) R) 6 :=
    isWeightedHomogeneous_X R shortCoordinateWeight 1
  have h₂ : IsWeightedHomogeneous shortCoordinateWeight (X 2 : MvPolynomial (Fin 5) R) 2 :=
    isWeightedHomogeneous_X R shortCoordinateWeight 2
  have h₃ : IsWeightedHomogeneous shortCoordinateWeight (X 3 : MvPolynomial (Fin 5) R) 3 :=
    isWeightedHomogeneous_X R shortCoordinateWeight 3
  have hx : IsWeightedHomogeneous shortCoordinateWeight (X 2 ^ 3 : MvPolynomial (Fin 5) R) 6 :=
    h₂.pow 3
  have hy : IsWeightedHomogeneous shortCoordinateWeight (X 3 ^ 2 : MvPolynomial (Fin 5) R) 6 :=
    h₃.pow 2
  exact hy.sub ((hx.add (h₀.mul h₂)).add h₁)

#print axioms shortCoefficientWeight
#print axioms shortDiscriminant_weight
#print axioms shortCoordinateWeight
#print axioms shortCurveEquation_weight

end WeierstrassCurve.ModelLevels
