/-
# All powers of the actual localized different and the original global different

The proved coefficient identity, with nonzeroness and finite multiplicity
established for both actual differents, supplies every prime-power comparison.
This module does not take a desired local/global comparison as a premise.
-/
module

public import ZInQKernel.Contrib.GlobalDifferentTransport.FixedFieldLocalFractionFields

/-!
# Exact all-exponent different transport for the actual F/E localized route

The target ideal is the genuine different of A/B, not merely a mapped ideal.
The global ideal is the original absolute different of L=M^H over `ℤ`.
All natural exponents, including zero, are covered.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open NumberField IsLocalRing
open scoped NumberField GlobalDifferentTransportFixedFieldTower
  GlobalDifferentTransportLocalizedFixedFieldTower

namespace GlobalDifferentTransport.FixedFieldLocalTower

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable (M : Type*) [Field M] [NumberField M] [IsGalois ℚ M]
  (P : Ideal (𝓞 M)) [P.IsPrime] (H : Subgroup Gal(M/ℚ)) (hP : P ≠ ⊥)

include hP

/-- Every prime-power divisibility test of the actual local relative different agrees with the
same test of the original absolute global different. The zero exponent is included. -/
theorem pow_dvd_actualDifferent_iff_original (n : ℕ) :
    maximalIdeal (extensionRing M P H) ^ n ∣ differentIdeal (baseRing M P) (extensionRing M P H) ↔
      (P.under (𝓞 (originalFixedField M H))) ^ n ∣ differentIdeal ℤ (𝓞 (originalFixedField M H)) := by
  let B := extensionRing M P H
  let A := baseRing M P
  let L := originalFixedField M H
  let qL := P.under (𝓞 L)
  let : IsDiscreteValuationRing B := (localizations_areDVR M P H hP).2.2
  let : Algebra.IsSeparable (FractionRing A) (FractionRing B) := fractionFields_baseExtension_separable M P H
  have hlocalD : differentIdeal A B ≠ ⊥ := differentIdeal_ne_bot
  have hglobalD : differentIdeal ℤ (𝓞 L) ≠ ⊥ := differentIdeal_ne_bot
  have hqL : qL ≠ ⊥ := numberField_under_prime_ne_bot L M P hP
  have hlocal := FiniteMultiplicity.of_prime_left
    (Ideal.prime_of_isPrime (IsDiscreteValuationRing.not_a_field B) inferInstance) hlocalD
  have hglobal := FiniteMultiplicity.of_prime_left (Ideal.prime_of_isPrime hqL inferInstance) hglobalD
  rw [hlocal.pow_dvd_iff_le_multiplicity, hglobal.pow_dvd_iff_le_multiplicity,
    extensionRing_differentMultiplicity_eq_original M P H hP]

/-- The exact upper-bound nondivisibility test is preserved, with the same `n+1` endpoint. -/
theorem not_pow_succ_dvd_actualDifferent_iff_original (n : ℕ) :
    (¬ maximalIdeal (extensionRing M P H) ^ (n + 1) ∣ differentIdeal (baseRing M P) (extensionRing M P H)) ↔
      ¬ (P.under (𝓞 (originalFixedField M H))) ^ (n + 1) ∣
        differentIdeal ℤ (𝓞 (originalFixedField M H)) :=
  (pow_dvd_actualDifferent_iff_original M P H hP (n + 1)).not

end GlobalDifferentTransport.FixedFieldLocalTower
