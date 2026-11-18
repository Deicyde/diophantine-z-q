import DirectHeckeCharacterV001
import DirectTorsionSeparatorV004
import DirectWeightedDeterminantV007
import DirectTorsionOrbitV001
import DirectOrbitAlgebraV003
import DirectOrbitInterpolationV001
import DirectLevelOneInterpolationV004
import DirectLocalizedTorsionGenerationV002
import DirectLevelOneArithmeticV004
import DirectLevelOneGaloisModelV002
import DirectCoefficientSaturationV004
import DirectCharacterObstructionV002
import BridgeDenominatorV002
import BridgeLambdaV002
import BridgeSeriesV002
import BridgeAxisFrameV002
import BridgeFrameConjugationV001
import BridgeDiamondRationalityV002
import BridgeHeckeClosureV001

set_option autoImplicit false
set_option pp.maxSteps 1000000
#check @DirectHeckeCharacter.character_eq_inverse_of_real
#print axioms DirectHeckeCharacter.character_eq_inverse_of_real
#check @DirectHeckeCharacter.character_value_sign_of_real
#print axioms DirectHeckeCharacter.character_value_sign_of_real
#check @DirectHeckeCharacter.diamond_integral_of_mem_character
#print axioms DirectHeckeCharacter.diamond_integral_of_mem_character
#check @DirectHeckeCharacter.prime_hecke_integral_of_mem_character
#print axioms DirectHeckeCharacter.prime_hecke_integral_of_mem_character
#check @DirectHeckeCharacter.prime_hecke_rational_of_mem_character
#print axioms DirectHeckeCharacter.prime_hecke_rational_of_mem_character
#check @DirectTorsionSeparator.axisMobius
#print axioms DirectTorsionSeparator.axisMobius
#check @DirectTorsionSeparator.axisMobius_injective
#print axioms DirectTorsionSeparator.axisMobius_injective
#check @DirectTorsionSeparator.axisMobius_conj_neg
#print axioms DirectTorsionSeparator.axisMobius_conj_neg
#check @DirectTorsionSeparator.axisMobius_not_conj_fixed
#print axioms DirectTorsionSeparator.axisMobius_not_conj_fixed
#check @DirectTorsionSeparator.torsion_coeff_zero_normalized
#print axioms DirectTorsionSeparator.torsion_coeff_zero_normalized
#check @DirectTorsionSeparator.primitive_axis_not_sign
#print axioms DirectTorsionSeparator.primitive_axis_not_sign
#check @DirectTorsionSeparator.torsion_slash_eq_self_iff
#print axioms DirectTorsionSeparator.torsion_slash_eq_self_iff
#check @DirectTorsionSeparator.torsion_slash_eq_iff
#print axioms DirectTorsionSeparator.torsion_slash_eq_iff
#check @DirectWeightedDeterminant.determinantForm
#print axioms DirectWeightedDeterminant.determinantForm
#check @DirectWeightedDeterminant.determinantForm_apply
#print axioms DirectWeightedDeterminant.determinantForm_apply
#check @DirectWeightedDeterminant.determinantForm_row_permute
#print axioms DirectWeightedDeterminant.determinantForm_row_permute
#check @DirectWeightedDeterminant.qExpansion_weighted_product
#print axioms DirectWeightedDeterminant.qExpansion_weighted_product
#check @DirectWeightedDeterminant.qExpansion_determinantForm
#print axioms DirectWeightedDeterminant.qExpansion_determinantForm
#check @DirectWeightedDeterminant.vandermondeForm
#print axioms DirectWeightedDeterminant.vandermondeForm
#check @DirectWeightedDeterminant.vandermondeForm_apply
#print axioms DirectWeightedDeterminant.vandermondeForm_apply
#check @DirectWeightedDeterminant.qExpansion_vandermondeForm
#print axioms DirectWeightedDeterminant.qExpansion_vandermondeForm
#check @DirectWeightedDeterminant.vandermondeForm_ne_zero
#print axioms DirectWeightedDeterminant.vandermondeForm_ne_zero
#check @DirectTorsionOrbit.cosetFintype
#print axioms DirectTorsionOrbit.cosetFintype
#check @DirectTorsionOrbit.orbitLength
#print axioms DirectTorsionOrbit.orbitLength
#check @DirectTorsionOrbit.orbitEquiv
#print axioms DirectTorsionOrbit.orbitEquiv
#check @DirectTorsionOrbit.representative
#print axioms DirectTorsionOrbit.representative
#check @DirectTorsionOrbit.base_good
#print axioms DirectTorsionOrbit.base_good
#check @DirectTorsionOrbit.torsionOrbit
#print axioms DirectTorsionOrbit.torsionOrbit
#check @DirectTorsionOrbit.torsionOrbit_coe
#print axioms DirectTorsionOrbit.torsionOrbit_coe
#check @DirectTorsionOrbit.principal_period
#print axioms DirectTorsionOrbit.principal_period
#check @DirectTorsionOrbit.torsionOrbit_qExpansion_injective
#print axioms DirectTorsionOrbit.torsionOrbit_qExpansion_injective
#check @DirectTorsionOrbit.orbitDenominator
#print axioms DirectTorsionOrbit.orbitDenominator
#check @DirectTorsionOrbit.orbitDenominator_ne_zero
#print axioms DirectTorsionOrbit.orbitDenominator_ne_zero
#check @DirectOrbitAlgebra.principal_le_inv_conjugate
#print axioms DirectOrbitAlgebra.principal_le_inv_conjugate
#check @DirectOrbitAlgebra.principal_le_gamma_one
#print axioms DirectOrbitAlgebra.principal_le_gamma_one
#check @DirectOrbitAlgebra.principalSlash
#print axioms DirectOrbitAlgebra.principalSlash
#check @DirectOrbitAlgebra.principalSlash_coe
#print axioms DirectOrbitAlgebra.principalSlash_coe
#check @DirectOrbitAlgebra.formOrbit
#print axioms DirectOrbitAlgebra.formOrbit
#check @DirectOrbitAlgebra.formOrbit_coe
#print axioms DirectOrbitAlgebra.formOrbit_coe
#check @DirectOrbitAlgebra.cosetPermutation
#print axioms DirectOrbitAlgebra.cosetPermutation
#check @DirectOrbitAlgebra.cosetPermutation_coset
#print axioms DirectOrbitAlgebra.cosetPermutation_coset
#check @DirectOrbitAlgebra.cosetPermutation_relation
#print axioms DirectOrbitAlgebra.cosetPermutation_relation
#check @DirectOrbitAlgebra.formOrbit_slash
#print axioms DirectOrbitAlgebra.formOrbit_slash
#check @DirectOrbitAlgebra.torsionOrbit_slash
#print axioms DirectOrbitAlgebra.torsionOrbit_slash
#check @DirectOrbitInterpolation.orbitWeight
#print axioms DirectOrbitInterpolation.orbitWeight
#check @DirectOrbitInterpolation.replacedWeight
#print axioms DirectOrbitInterpolation.replacedWeight
#check @DirectOrbitInterpolation.replacedEntry
#print axioms DirectOrbitInterpolation.replacedEntry
#check @DirectOrbitInterpolation.cofactorForm
#print axioms DirectOrbitInterpolation.cofactorForm
#check @DirectOrbitInterpolation.cofactorForm_apply
#print axioms DirectOrbitInterpolation.cofactorForm_apply
#check @DirectOrbitInterpolation.coefficientForm
#print axioms DirectOrbitInterpolation.coefficientForm
#check @DirectOrbitInterpolation.coefficientForm_apply
#print axioms DirectOrbitInterpolation.coefficientForm_apply
#check @DirectOrbitInterpolation.squared_denominator_interpolation
#print axioms DirectOrbitInterpolation.squared_denominator_interpolation
#check @DirectOrbitInterpolation.identityIndex
#print axioms DirectOrbitInterpolation.identityIndex
#check @DirectOrbitInterpolation.formOrbit_identity_coe
#print axioms DirectOrbitInterpolation.formOrbit_identity_coe
#check @DirectLevelOneInterpolation.determinant_scale_columns
#print axioms DirectLevelOneInterpolation.determinant_scale_columns
#check @DirectLevelOneInterpolation.product_zpow
#print axioms DirectLevelOneInterpolation.product_zpow
#check @DirectLevelOneInterpolation.determinant_slash_value
#print axioms DirectLevelOneInterpolation.determinant_slash_value
#check @DirectLevelOneInterpolation.weight_one_power_slash
#print axioms DirectLevelOneInterpolation.weight_one_power_slash
#check @DirectLevelOneInterpolation.replacedEntry_slash
#print axioms DirectLevelOneInterpolation.replacedEntry_slash
#check @DirectLevelOneInterpolation.denominator_slash
#print axioms DirectLevelOneInterpolation.denominator_slash
#check @DirectLevelOneInterpolation.cofactor_slash
#print axioms DirectLevelOneInterpolation.cofactor_slash
#check @DirectLevelOneInterpolation.coefficient_slash_invariant
#print axioms DirectLevelOneInterpolation.coefficient_slash_invariant
#check @DirectLevelOneInterpolation.squared_denominator_slash_invariant
#print axioms DirectLevelOneInterpolation.squared_denominator_slash_invariant
#check @DirectLevelOneInterpolation.toLevelOne
#print axioms DirectLevelOneInterpolation.toLevelOne
#check @DirectLevelOneInterpolation.toLevelOne_coe
#print axioms DirectLevelOneInterpolation.toLevelOne_coe
#check @DirectLevelOneInterpolation.levelOneCoefficient
#print axioms DirectLevelOneInterpolation.levelOneCoefficient
#check @DirectLevelOneInterpolation.levelOneCoefficient_coe
#print axioms DirectLevelOneInterpolation.levelOneCoefficient_coe
#check @DirectLocalizedTorsionGeneration.squaredDenominator
#print axioms DirectLocalizedTorsionGeneration.squaredDenominator
#check @DirectLocalizedTorsionGeneration.squaredDenominator_apply
#print axioms DirectLocalizedTorsionGeneration.squaredDenominator_apply
#check @DirectLocalizedTorsionGeneration.denominator
#print axioms DirectLocalizedTorsionGeneration.denominator
#check @DirectLocalizedTorsionGeneration.denominator_coe
#print axioms DirectLocalizedTorsionGeneration.denominator_coe
#check @DirectLocalizedTorsionGeneration.denominator_ne_zero
#print axioms DirectLocalizedTorsionGeneration.denominator_ne_zero
#check @DirectLocalizedTorsionGeneration.torsionOrbit_identity_coe
#print axioms DirectLocalizedTorsionGeneration.torsionOrbit_identity_coe
#check @DirectLocalizedTorsionGeneration.localized_generation
#print axioms DirectLocalizedTorsionGeneration.localized_generation
#check @DirectLocalizedTorsionGeneration.localized_cusp_generation
#print axioms DirectLocalizedTorsionGeneration.localized_cusp_generation
#check @DirectLevelOneArithmetic.IsRat
#print axioms DirectLevelOneArithmetic.IsRat
#check @DirectLevelOneArithmetic.rationalSpan
#print axioms DirectLevelOneArithmetic.rationalSpan
#check @DirectLevelOneArithmetic.series_lift
#print axioms DirectLevelOneArithmetic.series_lift
#check @DirectLevelOneArithmetic.isRat_mul
#print axioms DirectLevelOneArithmetic.isRat_mul
#check @DirectLevelOneArithmetic.isRat_pow
#print axioms DirectLevelOneArithmetic.isRat_pow
#check @DirectLevelOneArithmetic.isRat_sub
#print axioms DirectLevelOneArithmetic.isRat_sub
#check @DirectLevelOneArithmetic.isRat_smul
#print axioms DirectLevelOneArithmetic.isRat_smul
#check @DirectLevelOneArithmetic.isRat_mcast
#print axioms DirectLevelOneArithmetic.isRat_mcast
#check @DirectLevelOneArithmetic.eisenstein_rational
#print axioms DirectLevelOneArithmetic.eisenstein_rational
#check @DirectLevelOneArithmetic.discriminant_rational
#print axioms DirectLevelOneArithmetic.discriminant_rational
#check @DirectLevelOneArithmetic.deltaMul
#print axioms DirectLevelOneArithmetic.deltaMul
#check @DirectLevelOneArithmetic.deltaMul_apply
#print axioms DirectLevelOneArithmetic.deltaMul_apply
#check @DirectLevelOneArithmetic.deltaMul_rational
#print axioms DirectLevelOneArithmetic.deltaMul_rational
#check @DirectLevelOneArithmetic.deltaMul_span
#print axioms DirectLevelOneArithmetic.deltaMul_span
#check @DirectLevelOneArithmetic.rationalSpan_nat
#print axioms DirectLevelOneArithmetic.rationalSpan_nat
#check @DirectLevelOneArithmetic.rationalSpan_all
#print axioms DirectLevelOneArithmetic.rationalSpan_all
#check @DirectLevelOneGaloisModel.FiniteRationalRepresentation
#print axioms DirectLevelOneGaloisModel.FiniteRationalRepresentation
#check @DirectLevelOneGaloisModel.finite_rational_representation
#print axioms DirectLevelOneGaloisModel.finite_rational_representation
#check @DirectLevelOneGaloisModel.exists_unique_coefficient_conjugate
#print axioms DirectLevelOneGaloisModel.exists_unique_coefficient_conjugate
#check @DirectCoefficientSaturation.coefficients_mem_of_nonzero_mul
#print axioms DirectCoefficientSaturation.coefficients_mem_of_nonzero_mul
#check @DirectCharacterObstruction.unit_two_square
#print axioms DirectCharacterObstruction.unit_two_square
#check @DirectCharacterObstruction.real_weight_thirteen_not_character
#print axioms DirectCharacterObstruction.real_weight_thirteen_not_character
#check @DirectCharacterObstruction.deltaFive
#print axioms DirectCharacterObstruction.deltaFive
#check @DirectCharacterObstruction.mixedCusp
#print axioms DirectCharacterObstruction.mixedCusp
#check @DirectCharacterObstruction.mixedCusp_coe
#print axioms DirectCharacterObstruction.mixedCusp_coe
#check @DirectCharacterObstruction.mixedCusp_qExpansion
#print axioms DirectCharacterObstruction.mixedCusp_qExpansion
#check @DirectCharacterObstruction.mixedCusp_coeff_one
#print axioms DirectCharacterObstruction.mixedCusp_coeff_one
#check @DirectCharacterObstruction.mixedCusp_rational
#print axioms DirectCharacterObstruction.mixedCusp_rational
#check @DirectCharacterObstruction.mixedCusp_not_character
#print axioms DirectCharacterObstruction.mixedCusp_not_character
#check @BridgeDenominator.coefficientLift
#print axioms BridgeDenominator.coefficientLift
#check @BridgeDenominator.coefficientLift_map
#print axioms BridgeDenominator.coefficientLift_map
#check @BridgeDenominator.coefficients_mem_mul
#print axioms BridgeDenominator.coefficients_mem_mul
#check @BridgeDenominator.orbit_coefficients_mem
#print axioms BridgeDenominator.orbit_coefficients_mem
#check @BridgeDenominator.orbit_denominator_coefficients_mem
#print axioms BridgeDenominator.orbit_denominator_coefficients_mem
#check @BridgeDenominator.denominator_coefficients_mem_period
#print axioms BridgeDenominator.denominator_coefficients_mem_period
#check @BridgeDenominator.restrictLevelOne
#print axioms BridgeDenominator.restrictLevelOne
#check @BridgeDenominator.restrictLevelOne_coe
#print axioms BridgeDenominator.restrictLevelOne_coe
#check @BridgeDenominator.denominator_coefficients_mem
#print axioms BridgeDenominator.denominator_coefficients_mem
#check @BridgeDenominator.denominator_qExpansion_ne_zero
#print axioms BridgeDenominator.denominator_qExpansion_ne_zero
#check @BridgeDenominator.denominatorSeries
#print axioms BridgeDenominator.denominatorSeries
#check @BridgeDenominator.conjugateDenominator
#print axioms BridgeDenominator.conjugateDenominator
#check @BridgeDenominator.conjugateDenominator_coeff
#print axioms BridgeDenominator.conjugateDenominator_coeff
#check @BridgeDenominator.conjugateDenominator_coefficients_mem
#print axioms BridgeDenominator.conjugateDenominator_coefficients_mem
#check @BridgeDenominator.conjugateDenominator_qExpansion_ne_zero
#print axioms BridgeDenominator.conjugateDenominator_qExpansion_ne_zero
#check @BridgeLambda.base_admissible
#print axioms BridgeLambda.base_admissible
#check @BridgeLambda.baseLambda
#print axioms BridgeLambda.baseLambda
#check @BridgeLambda.baseLambda_coe
#print axioms BridgeLambda.baseLambda_coe
#check @BridgeLambda.lambdaForm
#print axioms BridgeLambda.lambdaForm
#check @BridgeLambda.lambdaForm_one
#print axioms BridgeLambda.lambdaForm_one
#check @BridgeLambda.diamond_lambdaForm
#print axioms BridgeLambda.diamond_lambdaForm
#check @BridgeLambda.real_slash_eq_integral
#print axioms BridgeLambda.real_slash_eq_integral
#check @BridgeLambda.diamond_restrictLevelOne
#print axioms BridgeLambda.diamond_restrictLevelOne
#check @BridgeLambda.diamond_mul
#print axioms BridgeLambda.diamond_mul
#check @BridgeLambda.unitPower
#print axioms BridgeLambda.unitPower
#check @BridgeLambda.unitPower_qExpansion
#print axioms BridgeLambda.unitPower_qExpansion
#check @BridgeLambda.diamond_unitPower
#print axioms BridgeLambda.diamond_unitPower
#check @BridgeLambda.lambdaForm_coefficients_mem
#print axioms BridgeLambda.lambdaForm_coefficients_mem
#check @BridgeLambda.exists_galois_unit
#print axioms BridgeLambda.exists_galois_unit
#check @BridgeSeries.fieldMap_injective
#print axioms BridgeSeries.fieldMap_injective
#check @BridgeSeries.coefficients_mem_pow
#print axioms BridgeSeries.coefficients_mem_pow
#check @BridgeSeries.coefficientLift_mul
#print axioms BridgeSeries.coefficientLift_mul
#check @BridgeSeries.coefficientLift_pow
#print axioms BridgeSeries.coefficientLift_pow
#check @BridgeSeries.conjugateSeries
#print axioms BridgeSeries.conjugateSeries
#check @BridgeSeries.conjugateSeries_coeff
#print axioms BridgeSeries.conjugateSeries_coeff
#check @BridgeSeries.conjugateSeries_mul
#print axioms BridgeSeries.conjugateSeries_mul
#check @BridgeSeries.conjugateSeries_pow
#print axioms BridgeSeries.conjugateSeries_pow
#check @BridgeSeries.conjugateSeries_eq_of_rational
#print axioms BridgeSeries.conjugateSeries_eq_of_rational
#check @BridgeSeries.conjugateSeries_coefficients_mem
#print axioms BridgeSeries.conjugateSeries_coefficients_mem
#check @BridgeAxisFrame.finite_span_representation
#print axioms BridgeAxisFrame.finite_span_representation
#check @BridgeAxisFrame.axisTerm
#print axioms BridgeAxisFrame.axisTerm
#check @BridgeAxisFrame.axisTerm_apply
#print axioms BridgeAxisFrame.axisTerm_apply
#check @BridgeAxisFrame.axisTerm_qExpansion
#print axioms BridgeAxisFrame.axisTerm_qExpansion
#check @BridgeAxisFrame.diamond_mcast
#print axioms BridgeAxisFrame.diamond_mcast
#check @BridgeAxisFrame.diamond_axisTerm
#print axioms BridgeAxisFrame.diamond_axisTerm
#check @BridgeAxisFrame.axisTermMap
#print axioms BridgeAxisFrame.axisTermMap
#check @BridgeAxisFrame.frameSet
#print axioms BridgeAxisFrame.frameSet
#check @BridgeAxisFrame.axisTermMap_mem_span
#print axioms BridgeAxisFrame.axisTermMap_mem_span
#check @BridgeAxisFrame.denominatorProduct
#print axioms BridgeAxisFrame.denominatorProduct
#check @BridgeAxisFrame.denominatorProduct_apply
#print axioms BridgeAxisFrame.denominatorProduct_apply
#check @BridgeAxisFrame.denominatorProduct_qExpansion
#print axioms BridgeAxisFrame.denominatorProduct_qExpansion
#check @BridgeAxisFrame.denominatorProduct_mem_span
#print axioms BridgeAxisFrame.denominatorProduct_mem_span
#check @BridgeAxisFrame.axisTerm_coefficients_mem
#print axioms BridgeAxisFrame.axisTerm_coefficients_mem
#check @BridgeAxisFrame.frame_coefficients_mem
#print axioms BridgeAxisFrame.frame_coefficients_mem
#check @BridgeAxisFrame.denominatorProduct_coefficients_mem
#print axioms BridgeAxisFrame.denominatorProduct_coefficients_mem
#check @BridgeAxisFrame.exists_field_frame_coordinates
#print axioms BridgeAxisFrame.exists_field_frame_coordinates
#check @BridgeFrameConjugation.conjugateSeries_congr
#print axioms BridgeFrameConjugation.conjugateSeries_congr
#check @BridgeFrameConjugation.galoisUnit
#print axioms BridgeFrameConjugation.galoisUnit
#check @BridgeFrameConjugation.lambdaForm_series_conjugate
#print axioms BridgeFrameConjugation.lambdaForm_series_conjugate
#check @BridgeFrameConjugation.denominator_series_conjugate
#print axioms BridgeFrameConjugation.denominator_series_conjugate
#check @BridgeFrameConjugation.axisTerm_series_conjugate
#print axioms BridgeFrameConjugation.axisTerm_series_conjugate
#check @BridgeFrameConjugation.conjugateProduct
#print axioms BridgeFrameConjugation.conjugateProduct
#check @BridgeFrameConjugation.conjugateProduct_qExpansion
#print axioms BridgeFrameConjugation.conjugateProduct_qExpansion
#check @BridgeFrameConjugation.diamond_denominatorProduct
#print axioms BridgeFrameConjugation.diamond_denominatorProduct
#check @BridgeFrameConjugation.diamond_conjugateProduct
#print axioms BridgeFrameConjugation.diamond_conjugateProduct
#check @BridgeFrameConjugation.denominatorProduct_series_conjugate
#print axioms BridgeFrameConjugation.denominatorProduct_series_conjugate
#check @BridgeFrameConjugation.exists_actual_axis_coordinates
#print axioms BridgeFrameConjugation.exists_actual_axis_coordinates
#check @BridgeDiamondRationality.diamond_coefficients_rational
#print axioms BridgeDiamondRationality.diamond_coefficients_rational
#check @BridgeDiamondRationality.cusp_diamond_coefficients_rational
#print axioms BridgeDiamondRationality.cusp_diamond_coefficients_rational
#check @BridgeHeckeClosure.heckePrimeIntegralToRational
#print axioms BridgeHeckeClosure.heckePrimeIntegralToRational
#check @BridgeHeckeClosure.actual_integral_input_hecke_rational
#print axioms BridgeHeckeClosure.actual_integral_input_hecke_rational

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup HeckeRing.GL2
open scoped MatrixGroups ModularForm BigOperators

example : _root_.CoeffRational.HeckePrimeIntegralToRational =
    (∀ (N : Nat) [NeZero N] (k : Int) (p : Nat)
      (g : _root_.CuspForm
        ((_root_.CongruenceSubgroup.Gamma1 N).map (_root_.Matrix.SpecialLinearGroup.mapGL Real)) k),
      2 ≤ k → p.Prime → ¬ p ∣ N →
      (∀ n : Nat, ∃ z : Int, (_root_.UpperHalfPlane.qExpansion 1 g).coeff n = (z : Complex)) →
      ∀ n : Nat, ∃ q : Rat,
        (_root_.UpperHalfPlane.qExpansion 1
          (_root_.HeckeRing.GL2.heckeSlashGamma1CuspFormEnd k
            (_root_.HeckeRing.GL2.diagCosetGamma1 N p) g)).coeff n = (q : Complex)) := rfl

example : _root_.CoeffRational.HeckePrimeIntegralToRational :=
  BridgeHeckeClosure.heckePrimeIntegralToRational

example (N : Nat) [NeZero N] (k : Int) (p : Nat)
    (g : _root_.CuspForm
      ((_root_.CongruenceSubgroup.Gamma1 N).map (_root_.Matrix.SpecialLinearGroup.mapGL Real)) k)
    (hk : 2 ≤ k) (hp : p.Prime) (hgood : ¬ p ∣ N)
    (hg : ∀ n : Nat, ∃ z : Int, (_root_.UpperHalfPlane.qExpansion 1 g).coeff n = (z : Complex)) :
    ∀ n : Nat, ∃ q : Rat,
      (_root_.UpperHalfPlane.qExpansion 1
        (_root_.HeckeRing.GL2.heckeSlashGamma1CuspFormEnd k
          (_root_.HeckeRing.GL2.diagCosetGamma1 N p) g)).coeff n = (q : Complex) :=
  BridgeHeckeClosure.actual_integral_input_hecke_rational N k p g hk hp hgood hg

example : ∀ (N : Nat) [NeZero N] (k : Int) (p : Nat)
    (g : _root_.CuspForm
      ((_root_.CongruenceSubgroup.Gamma1 N).map (_root_.Matrix.SpecialLinearGroup.mapGL Real)) k),
    2 ≤ k → p.Prime → ¬ p ∣ N →
    (∀ n : Nat, ∃ z : Int, (_root_.UpperHalfPlane.qExpansion 1 g).coeff n = (z : Complex)) →
    ∀ n : Nat, ∃ q : Rat,
      (_root_.UpperHalfPlane.qExpansion 1
        (_root_.HeckeRing.GL2.heckeSlashGamma1CuspFormEnd k
          (_root_.HeckeRing.GL2.diagCosetGamma1 N p) g)).coeff n = (q : Complex) :=
  BridgeHeckeClosure.heckePrimeIntegralToRational

example (N : Nat) [NeZero N] (hN : 3 ≤ N) (k : Int)
    (g : _root_.ModularForm
      ((_root_.CongruenceSubgroup.Gamma1 N).map (_root_.Matrix.SpecialLinearGroup.mapGL Real)) k)
    (hg : ∀ n : Nat, ∃ q : Rat, (_root_.UpperHalfPlane.qExpansion 1 g).coeff n = (q : Complex)) :
    ∀ (u : (ZMod N)ˣ) (n : Nat), ∃ q : Rat,
      (_root_.UpperHalfPlane.qExpansion 1 (_root_.diamondOp k u g)).coeff n = (q : Complex) :=
  BridgeDiamondRationality.diamond_coefficients_rational N hN k g hg

example (N : Nat) [NeZero N] (hN : 3 ≤ N) (k : Int)
    (g : _root_.CuspForm
      ((_root_.CongruenceSubgroup.Gamma1 N).map (_root_.Matrix.SpecialLinearGroup.mapGL Real)) k)
    (hg : ∀ n : Nat, ∃ q : Rat, (_root_.UpperHalfPlane.qExpansion 1 g).coeff n = (q : Complex)) :
    ∀ (u : (ZMod N)ˣ) (n : Nat), ∃ q : Rat,
      (_root_.UpperHalfPlane.qExpansion 1 (_root_.diamondOpCusp k u g)).coeff n = (q : Complex) :=
  BridgeDiamondRationality.cusp_diamond_coefficients_rational N hN k g hg

example (N : Nat) [NeZero N] (hN : 3 ≤ N) (k : Int)
    (g : _root_.ModularForm
      ((_root_.CongruenceSubgroup.Gamma1 N).map (_root_.Matrix.SpecialLinearGroup.mapGL Real)) k)
    (hg : ∀ n : Nat, ∃ q : Rat, (_root_.UpperHalfPlane.qExpansion 1 g).coeff n = (q : Complex)) :
    ∃ J : Type, ∃ hJ : Fintype J,
      letI := hJ
      ∃ e : J → Fin (DirectTorsionOrbit.orbitLength N),
      ∃ R : (i : J) → _root_.ModularForm 𝒮ℒ
        (k + 2 * DirectOrbitInterpolation.orbitWeight N - (e i : Int)),
      ∃ c : J → _root_.ZInQ.Contrib.HeckePrimeRationality.Torsion.coefficientField N,
        (∀ i, DirectLevelOneArithmetic.IsRat (R i)) ∧
          BridgeAxisFrame.denominatorProduct N hN k g =
            ∑ i, (c i : Complex) • BridgeAxisFrame.axisTerm N hN
              (k + 2 * DirectOrbitInterpolation.orbitWeight N) (e i : Nat) (R i) 1 :=
  BridgeFrameConjugation.exists_actual_axis_coordinates N hN k g hg

example (N : Nat) [NeZero N] (hN : 3 ≤ N) (k : Int)
    (g : _root_.ModularForm
      ((_root_.CongruenceSubgroup.Gamma1 N).map (_root_.Matrix.SpecialLinearGroup.mapGL Real)) k)
    (hg : ∀ n : Nat, ∃ q : Rat, (_root_.UpperHalfPlane.qExpansion 1 g).coeff n = (q : Complex))
    (σ : _root_.ZInQ.Contrib.HeckePrimeRationality.Torsion.coefficientField N ≃ₐ[Rat]
      _root_.ZInQ.Contrib.HeckePrimeRationality.Torsion.coefficientField N) :
    BridgeSeries.conjugateSeries
      (_root_.ZInQ.Contrib.HeckePrimeRationality.Torsion.coefficientField N) σ
      (_root_.UpperHalfPlane.qExpansion 1 (BridgeAxisFrame.denominatorProduct N hN k g))
      (BridgeAxisFrame.denominatorProduct_coefficients_mem N hN k g hg) =
        _root_.UpperHalfPlane.qExpansion 1 (BridgeFrameConjugation.conjugateProduct N hN k σ g) :=
  BridgeFrameConjugation.denominatorProduct_series_conjugate N hN k g hg σ

#print CoeffRational.HeckePrimeIntegralToRational
