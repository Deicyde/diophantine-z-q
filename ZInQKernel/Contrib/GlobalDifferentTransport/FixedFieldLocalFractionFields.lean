/-
# Fraction-field and integral-closure structure of the actual localized F/U/E tower

All finiteness, normality and faithful-map properties are supplied by the
constructed localized number-field rings. Canonical FractionRing.liftAlgebra
maps are used, with no additional fraction-field or different comparison premise.
-/
module

public import ZInQKernel.Contrib.GlobalDifferentTransport.FixedFieldLocalTower
public import ZInQKernel.Contrib.GlobalDifferentTransport.FiniteNormalFractionField

/-!
# Actual fraction fields for the given-factor DVR arithmetic

These discharge the structural finite/separable field and integral-closure
inputs on A/U0/B. Generation by a uniformizer, its degree and the derivative
estimate remain the arithmetic authors' scope.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open NumberField
open scoped NumberField GlobalDifferentTransportFixedFieldTower
  GlobalDifferentTransportLocalizedFixedFieldTower

namespace GlobalDifferentTransport.FixedFieldLocalTower

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable (M : Type*) [Field M] [NumberField M] [IsGalois ℚ M]
  (P : Ideal (𝓞 M)) [P.IsPrime] (H : Subgroup Gal(M/ℚ))

/-- The actual localized base has characteristic zero by its injective affine-model embedding. -/
theorem baseRing_charZero : CharZero (baseRing M P) :=
  CharZero.of_addMonoidHom
    (algebraMap (𝓞 (decompositionFixedField M P)) (baseRing M P)).toAddMonoidHom
    (algebraMap (𝓞 (decompositionFixedField M P)) (baseRing M P)).map_one
    (IsLocalization.injective (baseRing M P) (basePrime M P).primeCompl_le_nonZeroDivisors)
/-- The actual localized factor has characteristic zero by its injective affine-model embedding. -/
theorem factorRing_charZero : CharZero (factorRing M P H) :=
  CharZero.of_addMonoidHom
    (algebraMap (𝓞 (unramifiedFactorFixedField M P H)) (factorRing M P H)).toAddMonoidHom
    (algebraMap (𝓞 (unramifiedFactorFixedField M P H)) (factorRing M P H)).map_one
    (IsLocalization.injective (factorRing M P H) (factorPrime M P H).primeCompl_le_nonZeroDivisors)
/-- The actual localized upper ring has characteristic zero by its injective affine-model embedding. -/
theorem extensionRing_charZero : CharZero (extensionRing M P H) :=
  CharZero.of_addMonoidHom
    (algebraMap (𝓞 (transportedFixedField M P H)) (extensionRing M P H)).toAddMonoidHom
    (algebraMap (𝓞 (transportedFixedField M P H)) (extensionRing M P H)).map_one
    (IsLocalization.injective (extensionRing M P H) (extensionPrime M P H).primeCompl_le_nonZeroDivisors)

scoped[GlobalDifferentTransportLocalizedFixedFieldTower] attribute [instance]
  GlobalDifferentTransport.FixedFieldLocalTower.baseRing_charZero
  GlobalDifferentTransport.FixedFieldLocalTower.factorRing_charZero
  GlobalDifferentTransport.FixedFieldLocalTower.extensionRing_charZero

/-- The actual localized F/U extension induces a finite canonical fraction-field extension. -/
theorem fractionFields_baseFactor_finite :
    Module.Finite (FractionRing (baseRing M P)) (FractionRing (factorRing M P H)) :=
  finite_fractionField_extension (baseRing M P) (factorRing M P H)
/-- The actual localized U/E extension induces a finite canonical fraction-field extension. -/
theorem fractionFields_factorExtension_finite :
    Module.Finite (FractionRing (factorRing M P H)) (FractionRing (extensionRing M P H)) :=
  finite_fractionField_extension (factorRing M P H) (extensionRing M P H)
/-- The actual localized F/E extension induces a finite canonical fraction-field extension. -/
theorem fractionFields_baseExtension_finite :
    Module.Finite (FractionRing (baseRing M P)) (FractionRing (extensionRing M P H)) :=
  finite_fractionField_extension (baseRing M P) (extensionRing M P H)

/-- The actual canonical base/factor fraction-field extension is separable. -/
theorem fractionFields_baseFactor_separable :
    Algebra.IsSeparable (FractionRing (baseRing M P)) (FractionRing (factorRing M P H)) :=
  isSeparable_fractionField_extension (baseRing M P) (factorRing M P H)
/-- The actual canonical factor/upper fraction-field extension is separable. -/
theorem fractionFields_factorExtension_separable :
    Algebra.IsSeparable (FractionRing (factorRing M P H)) (FractionRing (extensionRing M P H)) :=
  isSeparable_fractionField_extension (factorRing M P H) (extensionRing M P H)
/-- The actual canonical base/upper fraction-field extension is separable. -/
theorem fractionFields_baseExtension_separable :
    Algebra.IsSeparable (FractionRing (baseRing M P)) (FractionRing (extensionRing M P H)) :=
  isSeparable_fractionField_extension (baseRing M P) (extensionRing M P H)

/-- The actual factor is the integral closure of the actual base in its canonical fraction field. -/
theorem factorRing_isIntegralClosure :
    IsIntegralClosure (factorRing M P H) (baseRing M P) (FractionRing (factorRing M P H)) :=
  isIntegralClosure_finite_normal_fractionField (baseRing M P) (factorRing M P H)
/-- The actual upper ring is the integral closure of the actual factor in its canonical fraction field. -/
theorem extensionRing_isIntegralClosure_factor :
    IsIntegralClosure (extensionRing M P H) (factorRing M P H) (FractionRing (extensionRing M P H)) :=
  isIntegralClosure_finite_normal_fractionField (factorRing M P H) (extensionRing M P H)
/-- The actual upper ring is the integral closure of the actual base in its canonical fraction field. -/
theorem extensionRing_isIntegralClosure_base :
    IsIntegralClosure (extensionRing M P H) (baseRing M P) (FractionRing (extensionRing M P H)) :=
  isIntegralClosure_finite_normal_fractionField (baseRing M P) (extensionRing M P H)

/-- The canonical fraction-field maps of the whole actual localized tower commute. -/
theorem fractionFields_isScalarTower :
    IsScalarTower (FractionRing (baseRing M P)) (FractionRing (factorRing M P H))
      (FractionRing (extensionRing M P H)) := by
  infer_instance

end GlobalDifferentTransport.FixedFieldLocalTower
