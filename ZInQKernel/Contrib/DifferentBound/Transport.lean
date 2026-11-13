import ZInQKernel.Contrib.DifferentBound.Global
import ZInQKernel.Contrib.DifferentBound.Local

/-!
# Pointwise transport to the exact global target

These are conditional **model comparison** lemmas, not a closed T21 provider.
The completed model must actually be constructed, with the global different,
selected prime, and ramification index identified as stated. The construction of
that completion/different comparison is owned by the separate shared-foundation
work; this file does not assert or assume its existence globally.
-/

namespace ZInQ.Contrib.DifferentBound

open NumberField IsLocalRing

/-- Extending a prime to a DVR's maximal ideal preserves its multiplicity in every nonzero
ideal. The ramification of the prime itself is one because its image is exactly maximal. -/
theorem multiplicity_map_eq_of_prime_maps_to_maximal
    (R B : Type*) [CommRing R] [IsDedekindDomain R] [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] [Algebra R B] [FaithfulSMul R B]
    (P : Ideal R) [P.IsMaximal] (hP0 : P ≠ ⊥)
    (hmap : P.map (algebraMap R B) = maximalIdeal B)
    (I : Ideal R) (hI : I ≠ ⊥) :
    multiplicity (maximalIdeal B) (I.map (algebraMap R B)) = multiplicity P I := by
  have hm0 : maximalIdeal B ≠ ⊥ := IsDiscreteValuationRing.not_a_field B
  have : (maximalIdeal B).LiesOver P :=
    (Ideal.liesOver_iff_dvd_map (Ideal.IsPrime.ne_top
      (inferInstance : (maximalIdeal B).IsPrime))).mpr (by rw [hmap])
  have he : P.ramificationIdx' (maximalIdeal B) = 1 := by
    rw [← hmap]
    exact Ideal.ramificationIdx'_map_self_eq_one
      (by rw [hmap]; exact (maximalIdeal.isMaximal B).ne_top)
      (by rw [hmap]; exact hm0)
  have hmapI : I.map (algebraMap R B) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hI
  have h := Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx'_mul hI
    (Ideal.prime_of_isPrime hP0 inferInstance).irreducible
    (Ideal.prime_of_isPrime hm0 inferInstance).irreducible hm0
  rw [he, Nat.cast_one, one_mul,
    (FiniteMultiplicity.of_prime_left (Ideal.prime_of_isPrime hm0 inferInstance)
      hmapI).emultiplicity_eq_multiplicity,
    (FiniteMultiplicity.of_prime_left (Ideal.prime_of_isPrime hP0 inferInstance)
      hI).emultiplicity_eq_multiplicity] at h
  exact_mod_cast h

/-- A DVR ideal dividing `m^b (x)` has exponent at most `b + v(x)`, with zero excluded only
for the element whose valuation must be finite. The ideal is the actual input ideal. -/
theorem multiplicity_le_of_dvd_maximalIdeal_pow_mul_span
    {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    (D : Ideal B) (hD : D ≠ ⊥) (b : ℕ) {x : B} (hx : x ≠ 0)
    (hbound : D ∣ maximalIdeal B ^ b * Ideal.span {x}) :
    multiplicity (maximalIdeal B) D ≤ b + multiplicity (maximalIdeal B) (Ideal.span {x}) := by
  have hfin := FiniteMultiplicity.of_prime_left
    (Ideal.prime_of_isPrime (IsDiscreteValuationRing.not_a_field B) inferInstance) hD
  have hdvd : maximalIdeal B ^ multiplicity (maximalIdeal B) D ∣ D :=
    hfin.pow_dvd_iff_le_multiplicity.mpr le_rfl
  have h := dvd_trans hdvd hbound
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible B
  have hpow : maximalIdeal B ^ b = Ideal.span {π ^ b} := by
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
  rw [hpow, Ideal.span_singleton_mul_span_singleton, Ideal.dvd_span_singleton,
    mem_maximalIdeal_pow_iff_le_addVal, IsDiscreteValuationRing.addVal_mul,
    hπ.addVal_pow, addVal_eq_multiplicity_span_singleton hx] at h
  exact_mod_cast h

/-- **Conditional pointwise global transport.** A genuine local ideal bound implies the exact
T21 conclusion at `P`, after matching the mapped different, mapped prime, and ramification
index. This theorem supplies none of those model-construction hypotheses itself. -/
theorem serreDifferentBound_atPrime_of_local_ideal_model
    (L : Type*) [Field L] [NumberField L] (p : ℕ) (hp : p.Prime)
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (A B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
    [Module.IsTorsionFree A B] [Algebra (𝓞 L) B] [FaithfulSMul (𝓞 L) B]
    (hmapP : P.map (algebraMap (𝓞 L) B) = maximalIdeal B)
    (hmapD : (differentIdeal ℤ (𝓞 L)).map (algebraMap (𝓞 L) B) = differentIdeal A B)
    (he : (maximalIdeal B).ramificationIdx A = P.ramificationIdx ℤ)
    (hbound : differentIdeal A B ∣
      maximalIdeal B ^ ((maximalIdeal B).ramificationIdx A - 1) *
        Ideal.span {((maximalIdeal B).ramificationIdx A : B)}) :
    ¬ P ^ (P.ramificationIdx ℤ - 1 +
        P.ramificationIdx ℤ * padicValNat p (P.ramificationIdx ℤ) + 1)
      ∣ differentIdeal ℤ (𝓞 L) := by
  have hP0 : P ≠ ⊥ := primeAbove_ne_bot L hp P
  have : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP0
  have hD0 := global_different_ne_bot L
  have hDL0 : differentIdeal A B ≠ ⊥ := by
    rw [← hmapD]
    exact Ideal.map_ne_bot_of_ne_bot hD0
  have he0 : P.ramificationIdx ℤ ≠ 0 := (global_ramificationIdx_pos L P).ne'
  have heO : (P.ramificationIdx ℤ : 𝓞 L) ≠ 0 := by exact_mod_cast he0
  have heB : (P.ramificationIdx ℤ : B) ≠ 0 := by
    simpa only [map_natCast, map_zero] using
      (FaithfulSMul.algebraMap_injective (𝓞 L) B).ne_iff.mpr heO
  have hlocal := multiplicity_le_of_dvd_maximalIdeal_pow_mul_span
    (differentIdeal A B) hDL0 ((maximalIdeal B).ramificationIdx A - 1)
    (by simpa only [he] using heB) hbound
  have hDmult := multiplicity_map_eq_of_prime_maps_to_maximal (𝓞 L) B P hP0 hmapP
    (differentIdeal ℤ (𝓞 L)) hD0
  rw [hmapD] at hDmult
  have hI0 : (Ideal.span {(P.ramificationIdx ℤ : 𝓞 L)} : Ideal (𝓞 L)) ≠ ⊥ := by
    simpa only [ne_eq, Ideal.span_singleton_eq_bot] using heO
  have hEmult := multiplicity_map_eq_of_prime_maps_to_maximal (𝓞 L) B P hP0 hmapP
    (Ideal.span {(P.ramificationIdx ℤ : 𝓞 L)}) hI0
  rw [Ideal.map_span, Set.image_singleton, map_natCast] at hEmult
  rw [he, hDmult, hEmult, primeAbove_multiplicity_natCast L p hp P he0] at hlocal
  exact (not_pow_dvd_global_different_iff L P _).mpr hlocal

/-- A genuine generating uniformizer in the matched local model gives the exact pointwise
global bound without an assumed Serre or Hilbert bound, and without an assumed degree equality.
The global-to-local ideal/model identifications are still explicit conditional inputs. -/
theorem serreDifferentBound_atPrime_of_generating_uniformizer_model
    (L : Type*) [Field L] [NumberField L] (p : ℕ) (hp : p.Prime)
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (A K M B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field M] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A K] [Algebra B M] [Algebra A B] [Algebra K M] [Algebra A M]
    [IsScalarTower A K M] [IsScalarTower A B M] [IsFractionRing A K]
    [IsIntegralClosure B A M] [Module.IsTorsionFree A B] [Module.Finite A B]
    [FiniteDimensional K M] [Algebra.IsSeparable K M]
    [(maximalIdeal B).LiesOver (maximalIdeal A)]
    [Algebra (𝓞 L) B] [FaithfulSMul (𝓞 L) B]
    (hmapP : P.map (algebraMap (𝓞 L) B) = maximalIdeal B)
    (hmapD : (differentIdeal ℤ (𝓞 L)).map (algebraMap (𝓞 L) B) = differentIdeal A B)
    (he : (maximalIdeal B).ramificationIdx A = P.ramificationIdx ℤ)
    {π : B} (hπ : Irreducible π) (hgen : Algebra.adjoin A {π} = ⊤) :
    ¬ P ^ (P.ramificationIdx ℤ - 1 +
        P.ramificationIdx ℤ * padicValNat p (P.ramificationIdx ℤ) + 1)
      ∣ differentIdeal ℤ (𝓞 L) :=
  serreDifferentBound_atPrime_of_local_ideal_model L p hp P A B hmapP hmapD he
    (differentIdeal_bound_of_generating_uniformizer A K M B hπ hgen)

end ZInQ.Contrib.DifferentBound
