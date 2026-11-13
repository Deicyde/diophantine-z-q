import ZInQKernel.Contrib.DifferentBound.SerreLocal
import ZInQKernel.Contrib.DifferentBound.Global
import ZInQKernel.Contrib.DifferentBound.Transport
import ZInQKernel.Contrib.GlobalDifferentTransport.FixedFieldLocalDifferentPowers

/-!
# Serre's bound on the actual localized fixed-field presentation

The supplied global transport is consumed at its actual canonical localized
rings A=(O F)_qF, U0=(O U)_qU and B=(O E)_qE. The ambient number field M/Q is
Galois, but the original fixed field L=M^H need not be Galois. No completeness,
perfectness, assumed model equality, Hilbert formula or Serre bound is an input.

This is the first global arithmetic closure step. The arbitrary-number-field
presentation wrapper is separate; this module does not redefine the baseline.
-/

namespace ZInQ.Contrib.DifferentBound

open NumberField IsLocalRing Module
open GlobalDifferentTransport
open GlobalDifferentTransport.FixedFieldLocalTower
open scoped NumberField GlobalDifferentTransportFixedFieldTower
  GlobalDifferentTransportLocalizedFixedFieldTower nonZeroDivisors

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable (M : Type*) [Field M] [NumberField M] [IsGalois ℚ M]
  (P : Ideal (𝓞 M)) [P.IsPrime] (H : Subgroup Gal(M/ℚ)) (hP : P ≠ ⊥)

include hP

/-- The actual localized tower's different satisfies the proved raw Serre inequality.
All structure and residue inputs are supplied by the proved F/U/E construction. -/
theorem fixedFieldLocalDifferentBound :
    differentIdeal (baseRing M P) (extensionRing M P H) ∣
      maximalIdeal (extensionRing M P H) ^
          ((maximalIdeal (extensionRing M P H)).ramificationIdx (baseRing M P) - 1) *
        Ideal.span {((maximalIdeal (extensionRing M P H)).ramificationIdx
          (baseRing M P) : extensionRing M P H)} := by
  let A := baseRing M P
  let U0 := factorRing M P H
  let B := extensionRing M P H
  have hDVR := localizations_areDVR M P H hP
  let : IsDiscreteValuationRing A := hDVR.1
  let : IsDiscreteValuationRing U0 := hDVR.2.1
  let : IsDiscreteValuationRing B := hDVR.2.2
  let : Algebra A U0 := baseFactorAlgebra M P H
  let : Algebra U0 B := factorExtensionAlgebra M P H
  let : Algebra A B := baseExtensionAlgebra M P H
  let : Module.Finite A U0 := factorRing_moduleFinite M P H
  let : Module.Finite U0 B := extensionRing_moduleFinite_factor M P H
  let : Module.Finite A B := extensionRing_moduleFinite_base M P H
  let : FaithfulSMul A U0 := factorRing_faithfulSMul M P H
  let : FaithfulSMul U0 B := extensionRing_faithfulSMul_factor M P H
  let : FaithfulSMul A B := extensionRing_faithfulSMul_base M P H
  let : Module.IsTorsionFree A U0 := isTorsionFree_iff_algebraMap_injective.mpr
    (FaithfulSMul.algebraMap_injective A U0)
  let : Module.IsTorsionFree U0 B := isTorsionFree_iff_algebraMap_injective.mpr
    (FaithfulSMul.algebraMap_injective U0 B)
  let : Module.IsTorsionFree A B := isTorsionFree_iff_algebraMap_injective.mpr
    (FaithfulSMul.algebraMap_injective A B)
  let : IsScalarTower A U0 B := localizations_isScalarTower M P H
  let : Algebra A (FractionRing B) := OreLocalization.instAlgebra
  let : Algebra (FractionRing A) (FractionRing B) := FractionRing.liftAlgebra A (FractionRing B)
  let : Algebra.IsSeparable (FractionRing A) (FractionRing B) :=
    fractionFields_baseExtension_separable M P H
  let : Algebra.IsUnramifiedAt A (maximalIdeal U0) := factorRing_isUnramifiedAt M P H
  exact differentIdeal_bound_of_residue_surjective_unramified_tower A U0 B
    (residue_factorExtension_surjective M P H)

/-- All nonzero natural integers have the same normalized prime-ideal multiplicity in the
actual localized upper ring and in the original absolute fixed field. The unramified E/L
factor and the prime localization are actual suppliers, not assumed valuation comparisons. -/
theorem fixedFieldLocal_multiplicity_natCast {n : ℕ} (hn : n ≠ 0) :
    multiplicity (maximalIdeal (extensionRing M P H))
        (Ideal.span {(n : extensionRing M P H)}) =
      multiplicity (P.under (𝓞 (originalFixedField M H)))
        (Ideal.span {(n : 𝓞 (originalFixedField M H))}) := by
  let L := originalFixedField M H
  let E := transportedFixedField M P H
  let qL := P.under (𝓞 L)
  let qE := P.under (𝓞 E)
  let : Algebra L E := originalToTransportedAlgebra M P H
  let : FaithfulSMul (𝓞 L) (𝓞 E) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (NumberField.RingOfIntegers.algebraMap.injective L E)
  have hqL : qL ≠ ⊥ := numberField_under_prime_ne_bot L M P hP
  have hqE : qE ≠ ⊥ := numberField_under_prime_ne_bot E M P hP
  have : qE.LiesOver qL := Ideal.LiesOver.tower_bot P qE qL
  have hI : (Ideal.span {(n : 𝓞 L)} : Ideal (𝓞 L)) ≠ ⊥ := by
    simpa only [ne_eq, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero] using hn
  have hmapI : (Ideal.span {(n : 𝓞 L)}).map (algebraMap (𝓞 L) (𝓞 E)) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hI
  have h := Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx'_mul hI
    (Ideal.prime_of_isPrime hqL inferInstance).irreducible
    (Ideal.prime_of_isPrime hqE inferInstance).irreducible hqE
  rw [Ideal.ramificationIdx'_eq_ramificationIdx qL qE hqL,
    transportedPrime_ramificationIdx_original_eq_one M P H, Nat.cast_one, one_mul,
    (FiniteMultiplicity.of_prime_left (Ideal.prime_of_isPrime hqE inferInstance)
      hmapI).emultiplicity_eq_multiplicity,
    (FiniteMultiplicity.of_prime_left (Ideal.prime_of_isPrime hqL inferInstance)
      hI).emultiplicity_eq_multiplicity,
    Ideal.map_span, Set.image_singleton, map_natCast] at h
  have hglobal : multiplicity qE (Ideal.span {(n : 𝓞 E)}) =
      multiplicity qL (Ideal.span {(n : 𝓞 L)}) := by exact_mod_cast h
  have hIE : (Ideal.span {(n : 𝓞 E)} : Ideal (𝓞 E)) ≠ ⊥ := by
    simpa only [ne_eq, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero] using hn
  have hloc := GlobalDifferentTransport.multiplicity_map_numberField_atPrime_eq
    E qE hqE (Ideal.span {(n : 𝓞 E)}) hIE
  rw [Ideal.map_span, Set.image_singleton, map_natCast] at hloc
  exact hloc.trans hglobal

/-- The original nongalois fixed field satisfies the absolute different-exponent bound.
No rational prime or normalized-valuation wrapper is needed in this integral formulation. -/
theorem fixedFieldDifferentMultiplicityBound :
    multiplicity (P.under (𝓞 (originalFixedField M H)))
        (differentIdeal ℤ (𝓞 (originalFixedField M H))) ≤
      (P.under (𝓞 (originalFixedField M H))).ramificationIdx ℤ - 1 +
        multiplicity (P.under (𝓞 (originalFixedField M H)))
          (Ideal.span {((P.under (𝓞 (originalFixedField M H))).ramificationIdx ℤ :
            𝓞 (originalFixedField M H))}) := by
  let A := baseRing M P
  let B := extensionRing M P H
  let : IsDiscreteValuationRing A := (localizations_areDVR M P H hP).1
  let : IsDiscreteValuationRing B := (localizations_areDVR M P H hP).2.2
  let : Algebra A B := baseExtensionAlgebra M P H
  let : Module.Finite A B := extensionRing_moduleFinite_base M P H
  let : FaithfulSMul A B := extensionRing_faithfulSMul_base M P H
  let : Module.IsTorsionFree A B := isTorsionFree_iff_algebraMap_injective.mpr
    (FaithfulSMul.algebraMap_injective A B)
  let : Algebra A (FractionRing B) := OreLocalization.instAlgebra
  let : Algebra (FractionRing A) (FractionRing B) := FractionRing.liftAlgebra A (FractionRing B)
  let : Algebra.IsSeparable (FractionRing A) (FractionRing B) :=
    fractionFields_baseExtension_separable M P H
  have hD : differentIdeal A B ≠ ⊥ := differentIdeal_ne_bot
  have hepos : 0 < (maximalIdeal B).ramificationIdx A :=
    (maximalIdeal B).ramificationIdx_pos A
  have heB : ((maximalIdeal B).ramificationIdx A : B) ≠ 0 := by exact_mod_cast hepos.ne'
  have hb := multiplicity_le_of_dvd_maximalIdeal_pow_mul_span (differentIdeal A B) hD
    ((maximalIdeal B).ramificationIdx A - 1) heB (fixedFieldLocalDifferentBound M P H hP)
  rw [extensionRing_differentMultiplicity_eq_original M P H hP,
    extensionRing_ramificationIdx_eq_original M P H hP] at hb
  have he0 : (P.under (𝓞 (originalFixedField M H))).ramificationIdx ℤ ≠ 0 :=
    ((P.under (𝓞 (originalFixedField M H))).ramificationIdx_pos ℤ).ne'
  rw [fixedFieldLocal_multiplicity_natCast M P H hP he0] at hb
  exact hb

/-- The exact global nondivisibility conclusion for the actual original fixed field, including
nongalois subfields. The only prime-above input is the one in the original global contract. -/
theorem fixedFieldSerreDifferentBound (p : ℕ) (hp : p.Prime)
    [(P.under (𝓞 (originalFixedField M H))).LiesOver (Ideal.span {(p : ℤ)})] :
    ¬ (P.under (𝓞 (originalFixedField M H))) ^
        ((P.under (𝓞 (originalFixedField M H))).ramificationIdx ℤ - 1 +
          (P.under (𝓞 (originalFixedField M H))).ramificationIdx ℤ *
            padicValNat p ((P.under (𝓞 (originalFixedField M H))).ramificationIdx ℤ) + 1)
      ∣ differentIdeal ℤ (𝓞 (originalFixedField M H)) := by
  have hb := fixedFieldDifferentMultiplicityBound M P H hP
  have he0 : (P.under (𝓞 (originalFixedField M H))).ramificationIdx ℤ ≠ 0 :=
    ((P.under (𝓞 (originalFixedField M H))).ramificationIdx_pos ℤ).ne'
  rw [primeAbove_multiplicity_natCast (originalFixedField M H) p hp
    (P.under (𝓞 (originalFixedField M H))) he0] at hb
  exact (not_pow_dvd_global_different_iff (originalFixedField M H)
    (P.under (𝓞 (originalFixedField M H))) _).mpr hb

#check @fixedFieldLocalDifferentBound
#check @fixedFieldDifferentMultiplicityBound
#check @fixedFieldSerreDifferentBound
#print axioms fixedFieldLocalDifferentBound
#print axioms fixedFieldDifferentMultiplicityBound
#print axioms fixedFieldSerreDifferentBound

end ZInQ.Contrib.DifferentBound
