import Mathlib.RingTheory.RamificationInertia.Ramification

/-!
# Localization-length ramification and uniformizer powers

These are bridges for the genuine `Ideal.ramificationIdx` used by T2.
The local DVR hypothesis is explicit here; `Primes.lean` proves it at every
integral-closure prime from the baseline field/root hypotheses.

The exponent comparison follows the argument of
`TauCeti/RingTheory/RamificationInertia/DiscreteValuationRing.lean` at
revision `30f41378f0cb1d569f51d8a4d0cb74aea8a80e44` (Apache-2.0),
but directly computes the length at an arbitrary specified prime.
-/

namespace ZInQ.Contrib.Abhyankar

open Ideal IsLocalRing IsDiscreteValuationRing

/-- A proved maximal-ideal power identity computes the actual index at the specified prime. -/
theorem ramificationIdx_eq_of_local_map_eq_pow
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    [IsDomain (Localization.AtPrime q)] [IsDiscreteValuationRing (Localization.AtPrime q)]
    {n : ℕ}
    (hn : p.map (algebraMap R (Localization.AtPrime q)) =
      maximalIdeal (Localization.AtPrime q) ^ n) : q.ramificationIdx R = n := by
  rw [ramificationIdx_eq p q, hn, length_quotient_pow_maximalIdeal, ENat.toNat_natCast]

/-- In a local DVR the mapped ideal is the power with exponent equal to the actual index.
Nonvanishing excludes the infinite-length junk value in the definition. -/
theorem local_map_eq_pow_ramificationIdx
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    [IsDomain (Localization.AtPrime q)] [IsDiscreteValuationRing (Localization.AtPrime q)]
    (hp : p.map (algebraMap R (Localization.AtPrime q)) ≠ ⊥) :
    p.map (algebraMap R (Localization.AtPrime q)) =
      maximalIdeal (Localization.AtPrime q) ^ q.ramificationIdx R := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible (Localization.AtPrime q)
  obtain ⟨n, hn⟩ := ideal_eq_span_pow_irreducible hp hϖ
  have hpow : p.map (algebraMap R (Localization.AtPrime q)) =
      maximalIdeal (Localization.AtPrime q) ^ n := by
    rw [hn, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  have hidx := ramificationIdx_eq_of_local_map_eq_pow p q hpow
  simpa only [hidx] using hpow

/-- A base uniformizer has valuation equal to the actual ramification index at `q`. -/
theorem addVal_algebraMap_uniformizer
    {R S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [Algebra R S] {π : R} (hπ : Irreducible π)
    (q : Ideal S) [q.IsPrime] [q.LiesOver (maximalIdeal R)]
    [IsDomain (Localization.AtPrime q)] [IsDiscreteValuationRing (Localization.AtPrime q)]
    (hπq : algebraMap R (Localization.AtPrime q) π ≠ 0) :
    addVal (Localization.AtPrime q) (algebraMap R (Localization.AtPrime q) π) =
      (q.ramificationIdx R : ℕ∞) := by
  have hp : (maximalIdeal R).map (algebraMap R (Localization.AtPrime q)) ≠ ⊥ := by
    rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
    simpa only [ne_eq, Ideal.span_singleton_eq_bot] using hπq
  have hpow := local_map_eq_pow_ramificationIdx (maximalIdeal R) q hp
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible (Localization.AtPrime q)
  rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton,
    hϖ.maximalIdeal_eq, Ideal.span_singleton_pow,
    Ideal.span_singleton_eq_span_singleton] at hpow
  calc
    addVal (Localization.AtPrime q) (algebraMap R (Localization.AtPrime q) π) =
        addVal (Localization.AtPrime q) (ϖ ^ q.ramificationIdx R) :=
      (addVal_eq_iff_associated _ _).mpr hpow
    _ = (q.ramificationIdx R : ℕ∞) := hϖ.addVal_pow _

/-- An integral root of a base uniformizer forces its positive exponent to divide
ramification at each specified local DVR. This is the lower-divisibility direction;
no tame hypothesis supplies the reverse divisibility here. -/
theorem exponent_dvd_ramificationIdx
    {R S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [Algebra R S] {π : R} (hπ : Irreducible π)
    (q : Ideal S) [q.IsPrime] [q.LiesOver (maximalIdeal R)]
    [IsDomain (Localization.AtPrime q)] [IsDiscreteValuationRing (Localization.AtPrime q)]
    (hπq : algebraMap R (Localization.AtPrime q) π ≠ 0)
    {n : ℕ} (hn : 0 < n) {t : S} (ht : t ^ n = algebraMap R S π) :
    n ∣ q.ramificationIdx R := by
  let A := Localization.AtPrime q
  have hroot : (algebraMap S A t) ^ n = algebraMap R A π := by
    rw [← map_pow, ht, ← IsScalarTower.algebraMap_apply R S A]
  have htq : algebraMap S A t ≠ 0 := by
    intro hz
    apply hπq
    rw [← hroot, hz, zero_pow hn.ne']
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible A
  obtain ⟨m, u, hm⟩ := eq_unit_mul_pow_irreducible htq hϖ
  have hval := congrArg (addVal A) hroot
  rw [addVal_pow, hm, addVal_def' u hϖ m,
    addVal_algebraMap_uniformizer hπ q hπq, nsmul_eq_mul, ← Nat.cast_mul] at hval
  exact ⟨m, (ENat.natCast_inj.mp hval).symm⟩

end ZInQ.Contrib.Abhyankar
