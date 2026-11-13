/-
# The genuine different at the actual decomposition fixed field

The fixed field, its contracted prime, unique-prime property and base indices
are the proved constructions in FixedFieldLocalization.lean. This file
instantiates the canonical number-field localization comparison without a new
uniqueness premise, and uses global different transitivity at the actual prime.
-/
module

public import ZInQKernel.Contrib.GlobalDifferentTransport.NumberFieldPrimeLocalizationDifferent
public import ZInQKernel.Contrib.GlobalDifferentTransport.FixedFieldLocalization

/-!
# Actual decomposition-field different transport

For a finite Galois number field `M/ℚ`, its selected nonzero prime `P`, and the
actual decomposition fixed field `F`, this gives the genuine relative different
at `(𝓞 F)_Q ⊆ (𝓞 M)_P`. The absolute global different is compared using global
transitivity and the proved unramifiedness at `Q`, not completion identities.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped NumberField nonZeroDivisors Pointwise

namespace GlobalDifferentTransport

variable (M : Type*) [Field M] [NumberField M] [IsGalois ℚ M]
  (P : Ideal (𝓞 M)) [P.IsPrime]

/-- The genuine relative different of the actual decomposition fixed field maps to the actual
relative different of its single-prime localization. No new uniqueness assumption is added. -/
theorem map_differentIdeal_decompositionField_atPrime_eq :
    let F := decompositionFixedField M P
    let Q := P.under (𝓞 F)
    let _ := Localization.AtPrime.algebraOfLiesOver Q P
    (differentIdeal (𝓞 F) (𝓞 M)).map (algebraMap (𝓞 M) (Localization.AtPrime P)) =
      differentIdeal (Localization.AtPrime Q) (Localization.AtPrime P) := by
  let F := decompositionFixedField M P
  let Q := P.under (𝓞 F)
  let _ := Localization.AtPrime.algebraOfLiesOver Q P
  exact NumberFieldLocalization.map_differentIdeal_atPrime_eq F M Q P
    (decompositionFixedField_primesOver M P)

/-- The full coefficient-localization identity at the actual decomposition fixed field. -/
theorem multiplicity_differentIdeal_decompositionField_atPrime_eq (hP : P ≠ ⊥) :
    let F := decompositionFixedField M P
    let Q := P.under (𝓞 F)
    let _ := Localization.AtPrime.algebraOfLiesOver Q P
    multiplicity (IsLocalRing.maximalIdeal (Localization.AtPrime P))
        (differentIdeal (Localization.AtPrime Q) (Localization.AtPrime P)) =
      multiplicity P (differentIdeal (𝓞 F) (𝓞 M)) := by
  let F := decompositionFixedField M P
  let Q := P.under (𝓞 F)
  let _ := Localization.AtPrime.algebraOfLiesOver Q P
  exact NumberFieldLocalization.multiplicity_differentIdeal_atPrime_eq F M Q P hP
    (decompositionFixedField_primesOver M P)

/-- The all-exponent version of the actual localized relative different comparison. -/
theorem pow_dvd_differentIdeal_decompositionField_atPrime_iff (hP : P ≠ ⊥) (n : ℕ) :
    let F := decompositionFixedField M P
    let Q := P.under (𝓞 F)
    let _ := Localization.AtPrime.algebraOfLiesOver Q P
    IsLocalRing.maximalIdeal (Localization.AtPrime P) ^ n ∣
        differentIdeal (Localization.AtPrime Q) (Localization.AtPrime P) ↔
      P ^ n ∣ differentIdeal (𝓞 F) (𝓞 M) := by
  let F := decompositionFixedField M P
  let Q := P.under (𝓞 F)
  let _ := Localization.AtPrime.algebraOfLiesOver Q P
  exact NumberFieldLocalization.pow_dvd_differentIdeal_atPrime_iff F M Q P hP
    (decompositionFixedField_primesOver M P) n

/-- The actual decomposition-field prime is unramified over `ℤ`; finite residue separability
comes from the number-field integer rings, not an assumed vanishing different. -/
theorem decompositionFixedField_isUnramifiedAt (hP : P ≠ ⊥) :
    Algebra.IsUnramifiedAt ℤ (P.under (𝓞 (decompositionFixedField M P))) :=
  Ideal.ramificationIdx_eq_one_iff.mp (decompositionFixedField_base_indices_eq_one M P hP).1

/-- The global ramification index of the selected prime is unchanged on passing to the actual
decomposition fixed field, by tower multiplicativity and the proved base index one. -/
theorem ramificationIdx_decompositionField_eq (hP : P ≠ ⊥) :
    P.ramificationIdx (𝓞 (decompositionFixedField M P)) = P.ramificationIdx ℤ := by
  let F := decompositionFixedField M P
  let Q := P.under (𝓞 F)
  have he : Q.ramificationIdx ℤ = 1 := (decompositionFixedField_base_indices_eq_one M P hP).1
  rw [Ideal.ramificationIdx_tower (R := ℤ) Q P, he, one_mul]

/-- Global different transitivity and local unramifiedness identify the genuine absolute and
relative different coefficients at the selected prime. No completed-different equality is used. -/
theorem multiplicity_absoluteDifferent_eq_decompositionRelative (hP : P ≠ ⊥) :
    multiplicity P (differentIdeal ℤ (𝓞 M)) =
      multiplicity P (differentIdeal (𝓞 (decompositionFixedField M P)) (𝓞 M)) := by
  let F := decompositionFixedField M P
  let Q := P.under (𝓞 F)
  let : Module.Finite (𝓞 F) (𝓞 M) := finite_decompositionFixedField_integers M P
  have hunram : Algebra.IsUnramifiedAt ℤ Q := decompositionFixedField_isUnramifiedAt M P hP
  have hnot : ¬ Q ∣ differentIdeal ℤ (𝓞 F) := not_dvd_differentIdeal_iff.mpr hunram
  have hnotmap : ¬ P ∣ (differentIdeal ℤ (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 M)) := by
    simpa only [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, ← Ideal.under_def] using hnot
  have htrans : differentIdeal ℤ (𝓞 M) = differentIdeal (𝓞 F) (𝓞 M) *
      (differentIdeal ℤ (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 M)) :=
    differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 F) (𝓞 M)
  have hprime : Prime P := Ideal.prime_of_isPrime hP inferInstance
  have hmul : emultiplicity P (differentIdeal ℤ (𝓞 M)) =
      emultiplicity P (differentIdeal (𝓞 F) (𝓞 M)) := by
    rw [htrans, emultiplicity_mul hprime, emultiplicity_eq_zero.mpr hnotmap, add_zero]
  have hglobal := FiniteMultiplicity.of_prime_left hprime
    (show differentIdeal ℤ (𝓞 M) ≠ ⊥ from differentIdeal_ne_bot)
  have hrelative := FiniteMultiplicity.of_prime_left hprime
    (show differentIdeal (𝓞 F) (𝓞 M) ≠ ⊥ from differentIdeal_ne_bot)
  rw [hglobal.emultiplicity_eq_multiplicity, hrelative.emultiplicity_eq_multiplicity] at hmul
  exact_mod_cast hmul

/-- The actual local relative different at the decomposition field has the coefficient of the
original absolute global different. This is a concrete global/localized-DVR transport statement. -/
theorem multiplicity_absoluteDifferent_decompositionField_atPrime_eq (hP : P ≠ ⊥) :
    let F := decompositionFixedField M P
    let Q := P.under (𝓞 F)
    let _ := Localization.AtPrime.algebraOfLiesOver Q P
    multiplicity (IsLocalRing.maximalIdeal (Localization.AtPrime P))
        (differentIdeal (Localization.AtPrime Q) (Localization.AtPrime P)) =
      multiplicity P (differentIdeal ℤ (𝓞 M)) := by
  let F := decompositionFixedField M P
  let Q := P.under (𝓞 F)
  let _ := Localization.AtPrime.algebraOfLiesOver Q P
  exact (multiplicity_differentIdeal_decompositionField_atPrime_eq M P hP).trans
    (multiplicity_absoluteDifferent_eq_decompositionRelative M P hP).symm

end GlobalDifferentTransport
