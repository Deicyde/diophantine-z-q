import ZInQKernel.Contrib.OneProof.RC.ModelTorsion.UniversalShort
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-! # Rational scalar extension of the universal short locus -/

namespace WeierstrassCurve.ModelLevels.ModelGeneric

open ModelTorsion IsLocalization

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable (ell : ℕ) [Fact ell.Prime]

/-- The canonical inclusion of the detector ring in the rationals. -/
noncomputable instance : Algebra (LocalIntegers ell) ℚ :=
  localizationAlgebraOfSubmonoidLe _ _ (integerPrimeIdeal ell).primeCompl
    (nonZeroDivisors ℤ) (integerPrimeIdeal ell).primeCompl_le_nonZeroDivisors

/-- The rational scalar extension is taken at the fraction field of the detector. -/
theorem rational_isFractionRing : IsFractionRing (LocalIntegers ell) ℚ := by
  letI := localization_isScalarTower_of_submonoid_le (LocalIntegers ell) ℚ
    (integerPrimeIdeal ell).primeCompl (nonZeroDivisors ℤ)
    (integerPrimeIdeal ell).primeCompl_le_nonZeroDivisors
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (integerPrimeIdeal ell).primeCompl (LocalIntegers ell) ℚ

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]

private theorem shortEquation_map_coefficients :
    (shortEquation R).map (algebraMap (MvPolynomial (Fin 2) R) (MvPolynomial (Fin 2) B)) =
      shortEquation B := by
  change (shortEquation R).map (MvPolynomial.map (algebraMap R B)) = shortEquation B
  ext : 1 <;> simp [shortEquation]

private theorem shortDiscriminant_map_coefficients :
    algebraMap (MvPolynomial (Fin 2) R) (MvPolynomial (Fin 2) B) (shortEquation R).Δ =
      (shortEquation B).Δ := by
  rw [← WeierstrassCurve.map_Δ, shortEquation_map_coefficients]

private theorem shortDiscriminant_localization : IsLocalization.Away
    (algebraMap (MvPolynomial (Fin 2) R) (MvPolynomial (Fin 2) B) (shortEquation R).Δ)
    (ShortBase B) := by
  rw [shortDiscriminant_map_coefficients]
  infer_instance

/-- The coefficient extension of the universal short locus. -/
noncomputable def shortBaseMap : ShortBase R →+* ShortBase B :=
  letI := shortDiscriminant_localization (R := R) (B := B)
  IsLocalization.Away.map (ShortBase R) (ShortBase B)
    (algebraMap (MvPolynomial (Fin 2) R) (MvPolynomial (Fin 2) B)) (shortEquation R).Δ

noncomputable instance : Algebra (ShortBase R) (ShortBase B) :=
  (shortBaseMap (R := R) (B := B)).toAlgebra

theorem shortBaseMap_polynomial (x : MvPolynomial (Fin 2) R) :
    algebraMap (ShortBase R) (ShortBase B) (algebraMap _ (ShortBase R) x) =
      algebraMap (MvPolynomial (Fin 2) B) (ShortBase B) (algebraMap _ _ x) := by
  letI := shortDiscriminant_localization (R := R) (B := B)
  change shortBaseMap (algebraMap _ (ShortBase R) x) = _
  unfold shortBaseMap IsLocalization.Away.map
  exact IsLocalization.map_eq _ x

instance : IsScalarTower (MvPolynomial (Fin 2) R) (ShortBase R) (ShortBase B) :=
  IsScalarTower.of_algebraMap_eq (R := MvPolynomial (Fin 2) R) (S := ShortBase R)
    (A := ShortBase B) fun x => by
      rw [shortBaseMap_polynomial]
      exact IsScalarTower.algebraMap_apply (MvPolynomial (Fin 2) R)
        (MvPolynomial (Fin 2) B) (ShortBase B) x

instance : IsScalarTower R (ShortBase R) (ShortBase B) :=
  IsScalarTower.of_algebraMap_eq (R := R) (S := ShortBase R) (A := ShortBase B) fun r => by
    rw [IsScalarTower.algebraMap_apply R (MvPolynomial (Fin 2) R) (ShortBase R),
      ← IsScalarTower.algebraMap_apply (MvPolynomial (Fin 2) R) (ShortBase R) (ShortBase B),
      IsScalarTower.algebraMap_apply R (MvPolynomial (Fin 2) R) (ShortBase B)]

/-- The short coefficient ring commutes with scalar extension. The polynomial ring
is a pushout and localization inverts the image of its discriminant. -/
theorem shortBase_isPushout : Algebra.IsPushout R B (ShortBase R) (ShortBase B) := by
  let hloc : IsLocalization
      (Algebra.algebraMapSubmonoid (MvPolynomial (Fin 2) B)
        (Submonoid.powers (shortEquation R).Δ)) (ShortBase B) := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers, shortDiscriminant_map_coefficients]
    infer_instance
  have hs : Algebra.IsPushout (MvPolynomial (Fin 2) R) (MvPolynomial (Fin 2) B)
      (ShortBase R) (ShortBase B) := Algebra.isPushout_of_isLocalization
        (Submonoid.powers (shortEquation R).Δ) (ShortBase R) (MvPolynomial (Fin 2) B) (ShortBase B)
  exact ((Algebra.IsPushout.comp_iff (T := ShortBase R) (T' := ShortBase B)
    R (MvPolynomial (Fin 2) R) B (MvPolynomial (Fin 2) B)).2 hs.symm).symm

/-- The universal short equation itself is preserved by extension of coefficients. -/
theorem shortFamily_map_shortBaseMap :
    (shortFamily R).map (algebraMap (ShortBase R) (ShortBase B)) = shortFamily B := by
  unfold shortFamily
  rw [WeierstrassCurve.map_map]
  rw [show (algebraMap (ShortBase R) (ShortBase B)).comp
      (algebraMap (MvPolynomial (Fin 2) R) (ShortBase R)) =
    (algebraMap (MvPolynomial (Fin 2) B) (ShortBase B)).comp
      (algebraMap (MvPolynomial (Fin 2) R) (MvPolynomial (Fin 2) B)) from
    RingHom.ext (shortBaseMap_polynomial (R := R) (B := B))]
  rw [← WeierstrassCurve.map_map, shortEquation_map_coefficients]

#print axioms rational_isFractionRing
#print axioms shortEquation_map_coefficients
#print axioms shortDiscriminant_map_coefficients
#print axioms shortDiscriminant_localization
#print axioms shortBaseMap_polynomial
#print axioms shortBase_isPushout
#print axioms shortFamily_map_shortBaseMap

end WeierstrassCurve.ModelLevels.ModelGeneric
