/-
# Genuine global different transport through the actual fixed-field scaffold

These are global different-transitivity arguments on the actual number-field
rings of integers. They use unramifiedness proved in FixedFieldTransport and
FixedFieldLocalization, not the desired different equality as a premise.
-/
module

public import ZInQKernel.Contrib.GlobalDifferentTransport.FixedFieldTransport
public import ZInQKernel.Contrib.GlobalDifferentTransport.NumberFieldPrimeLocalizationDifferent

/-!
# The original global different equals the transported local coefficient

`L=M^H` may be nongalois over `ℚ`. The actual transported field is
`E=M^(D∩H)` and the base is `F=M^D`. At the selected primes, the genuine local
relative different of `(𝓞 E)_P/(𝓞 F)_Q` has the coefficient of the original
absolute different of `L/ℚ`. No completed-different comparison is used.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped NumberField Pointwise GlobalDifferentTransportFixedFieldTower

namespace GlobalDifferentTransport

section GlobalComparison

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (P : Ideal (𝓞 L)) [P.IsPrime] (hP : P ≠ ⊥)

include hP

/-- A nonzero integer prime contracts nontrivially through any actual number-field inclusion. -/
theorem numberField_under_prime_ne_bot : P.under (𝓞 K) ≠ ⊥ := by
  intro h
  exact hP (Ideal.eq_bot_of_under_eq_bot h)

/-- If the actual base prime is unramified over `ℤ`, global different transitivity identifies
relative and absolute different coefficients at the upper prime. -/
theorem multiplicity_relativeDifferent_eq_absolute_of_unramifiedBase
    [Algebra.IsUnramifiedAt ℤ (P.under (𝓞 K))] :
    multiplicity P (differentIdeal (𝓞 K) (𝓞 L)) = multiplicity P (differentIdeal ℤ (𝓞 L)) := by
  let : Module.Finite (𝓞 K) (𝓞 L) := Module.Finite.right ℤ (𝓞 K) (𝓞 L)
  have hnot : ¬ P.under (𝓞 K) ∣ differentIdeal ℤ (𝓞 K) :=
    not_dvd_differentIdeal_iff.mpr inferInstance
  have hnotmap : ¬ P ∣ (differentIdeal ℤ (𝓞 K)).map (algebraMap (𝓞 K) (𝓞 L)) := by
    simpa only [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, ← Ideal.under_def] using hnot
  have hprime : Prime P := Ideal.prime_of_isPrime hP inferInstance
  have he : emultiplicity P (differentIdeal ℤ (𝓞 L)) =
      emultiplicity P (differentIdeal (𝓞 K) (𝓞 L)) := by
    rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 K) (𝓞 L),
      emultiplicity_mul hprime, emultiplicity_eq_zero.mpr hnotmap, add_zero]
  have hrelative := FiniteMultiplicity.of_prime_left hprime
    (show differentIdeal (𝓞 K) (𝓞 L) ≠ ⊥ from differentIdeal_ne_bot)
  have habsolute := FiniteMultiplicity.of_prime_left hprime
    (show differentIdeal ℤ (𝓞 L) ≠ ⊥ from differentIdeal_ne_bot)
  rw [hrelative.emultiplicity_eq_multiplicity, habsolute.emultiplicity_eq_multiplicity] at he
  have hn : multiplicity P (differentIdeal ℤ (𝓞 L)) =
      multiplicity P (differentIdeal (𝓞 K) (𝓞 L)) := by exact_mod_cast he
  exact hn.symm

/-- If the actual upper prime is unramified over `𝓞 K`, global transitivity and ramification
multiplicity transport preserve the original absolute different coefficient. -/
theorem multiplicity_absoluteDifferent_eq_under_of_isUnramifiedAt
    [Algebra.IsUnramifiedAt (𝓞 K) P] :
    multiplicity P (differentIdeal ℤ (𝓞 L)) =
      multiplicity (P.under (𝓞 K)) (differentIdeal ℤ (𝓞 K)) := by
  let : Module.Finite (𝓞 K) (𝓞 L) := Module.Finite.right ℤ (𝓞 K) (𝓞 L)
  let q := P.under (𝓞 K)
  have hq : q ≠ ⊥ := numberField_under_prime_ne_bot K L P hP
  have hqprime : Prime q := Ideal.prime_of_isPrime hq inferInstance
  have hPprime : Prime P := Ideal.prime_of_isPrime hP inferInstance
  have hD : differentIdeal ℤ (𝓞 K) ≠ ⊥ := differentIdeal_ne_bot
  have hnot : ¬ P ∣ differentIdeal (𝓞 K) (𝓞 L) := not_dvd_differentIdeal_iff.mpr inferInstance
  have hmap := Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx'_mul hD
    hqprime.irreducible hPprime.irreducible hP
  rw [Ideal.ramificationIdx'_eq_ramificationIdx q P hq,
    Ideal.ramificationIdx_eq_one P (𝓞 K), Nat.cast_one, one_mul] at hmap
  have he : emultiplicity P (differentIdeal ℤ (𝓞 L)) =
      emultiplicity q (differentIdeal ℤ (𝓞 K)) := by
    rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 K) (𝓞 L),
      emultiplicity_mul hPprime, emultiplicity_eq_zero.mpr hnot, zero_add]
    exact hmap
  have hglobal := FiniteMultiplicity.of_prime_left hPprime
    (show differentIdeal ℤ (𝓞 L) ≠ ⊥ from differentIdeal_ne_bot)
  have hbase := FiniteMultiplicity.of_prime_left hqprime hD
  rw [hglobal.emultiplicity_eq_multiplicity, hbase.emultiplicity_eq_multiplicity] at he
  exact_mod_cast he

end GlobalComparison

section ActualFixedFields

variable (M : Type*) [Field M] [NumberField M] [IsGalois ℚ M]
  (P : Ideal (𝓞 M)) [P.IsPrime] (H : Subgroup Gal(M/ℚ)) (hP : P ≠ ⊥)

include hP

/-- The genuine transported relative different has the coefficient of the original absolute
global different, for every original fixed subfield, including nongalois ones. -/
theorem multiplicity_transportedRelativeDifferent_eq_originalAbsolute :
    multiplicity (P.under (𝓞 (transportedFixedField M P H)))
        (differentIdeal (𝓞 (decompositionFixedField M P)) (𝓞 (transportedFixedField M P H))) =
      multiplicity (P.under (𝓞 (originalFixedField M H)))
        (differentIdeal ℤ (𝓞 (originalFixedField M H))) := by
  let F := decompositionFixedField M P
  let E := transportedFixedField M P H
  let L := originalFixedField M H
  let qF := P.under (𝓞 F)
  let qE := P.under (𝓞 E)
  let qL := P.under (𝓞 L)
  have hqE : qE ≠ ⊥ := numberField_under_prime_ne_bot E M P hP
  have hEF : qE.under (𝓞 F) = qF := Ideal.under_under (A := 𝓞 F) (B := 𝓞 E) (𝔓 := P)
  have hEL : qE.under (𝓞 L) = qL := Ideal.under_under (A := 𝓞 L) (B := 𝓞 E) (𝔓 := P)
  let : Algebra.IsUnramifiedAt ℤ (qE.under (𝓞 F)) :=
    Ideal.ramificationIdx_eq_one_iff.mp (by
      rw [hEF]
      exact (decompositionFixedField_base_indices_eq_one M P hP).1)
  let : Algebra.IsUnramifiedAt (𝓞 L) qE := transportedPrime_isUnramifiedAt_original M P H
  calc
    multiplicity qE (differentIdeal (𝓞 F) (𝓞 E)) = multiplicity qE (differentIdeal ℤ (𝓞 E)) :=
      multiplicity_relativeDifferent_eq_absolute_of_unramifiedBase F E qE hqE
    _ = multiplicity (qE.under (𝓞 L)) (differentIdeal ℤ (𝓞 L)) :=
      multiplicity_absoluteDifferent_eq_under_of_isUnramifiedAt L E qE hqE
    _ = multiplicity qL (differentIdeal ℤ (𝓞 L)) := by rw [hEL]

/-- Concrete coefficient localization at the actual F/E primes, with no additional uniqueness
or desired different comparison premise. -/
theorem multiplicity_localizedTransportedDifferent_eq_originalAbsolute :
    let F := decompositionFixedField M P
    let E := transportedFixedField M P H
    let qF := P.under (𝓞 F)
    let qE := P.under (𝓞 E)
    let _ := Localization.AtPrime.algebraOfLiesOver qF qE
    multiplicity (IsLocalRing.maximalIdeal (Localization.AtPrime qE))
        (differentIdeal (Localization.AtPrime qF) (Localization.AtPrime qE)) =
      multiplicity (P.under (𝓞 (originalFixedField M H)))
        (differentIdeal ℤ (𝓞 (originalFixedField M H))) := by
  let F := decompositionFixedField M P
  let E := transportedFixedField M P H
  let qF := P.under (𝓞 F)
  let qE := P.under (𝓞 E)
  let _ := Localization.AtPrime.algebraOfLiesOver qF qE
  exact (NumberFieldLocalization.multiplicity_differentIdeal_atPrime_eq F E qF qE
    (numberField_under_prime_ne_bot E M P hP) (transportedFixedField_primesOver M P H)).trans
      (multiplicity_transportedRelativeDifferent_eq_originalAbsolute M P H hP)

/-- The genuine global ramification of E/F is that of the original prime of L/ℚ. The two
unramified tower factors are proved, and the base is explicitly `ℤ`. -/
theorem ramificationIdx_transportedRelative_eq_originalAbsolute :
    (P.under (𝓞 (transportedFixedField M P H))).ramificationIdx
        (𝓞 (decompositionFixedField M P)) =
      (P.under (𝓞 (originalFixedField M H))).ramificationIdx ℤ := by
  let F := decompositionFixedField M P
  let E := transportedFixedField M P H
  let L := originalFixedField M H
  let qF := P.under (𝓞 F)
  let qE := P.under (𝓞 E)
  let qL := P.under (𝓞 L)
  let : qE.LiesOver qF := Ideal.LiesOver.tower_bot P qE qF
  let : qE.LiesOver qL := Ideal.LiesOver.tower_bot P qE qL
  have hF : qF.ramificationIdx ℤ = 1 := (decompositionFixedField_base_indices_eq_one M P hP).1
  have hL : qE.ramificationIdx (𝓞 L) = 1 := transportedPrime_ramificationIdx_original_eq_one M P H
  have hFE := Ideal.ramificationIdx_tower (R := ℤ) qF qE
  have hLE := Ideal.ramificationIdx_tower (R := ℤ) qL qE
  rw [hF, one_mul] at hFE
  rw [hL, mul_one] at hLE
  exact hFE.symm.trans hLE

end ActualFixedFields

end GlobalDifferentTransport
