import ZInQKernel.HDecomp.Conductor.Breaks

/-!
# Global normalization and exceptional cases for T21

These lemmas concern the exact global objects in
`GlueConductor.SerreDifferentBound`. They do not prove its wild case.
The baseline and the frozen proposed target are not modified.
-/

namespace ZInQ.Contrib.DifferentBound

open NumberField IsDedekindDomain WithZero

/-- A natural prime generates a nonzero ideal of `ℤ`. -/
theorem span_natPrime_ne_bot {p : ℕ} (hp : p.Prime) :
    Ideal.span {(p : ℤ)} ≠ ⊥ := by
  simpa only [ne_eq, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero] using hp.ne_zero

/-- The nonzero-prime condition follows from the target's lying-over hypothesis. -/
theorem primeAbove_ne_bot (L : Type*) [Field L] [NumberField L]
    {p : ℕ} (hp : p.Prime) (P : Ideal (𝓞 L))
    [P.LiesOver (Ideal.span {(p : ℤ)})] : P ≠ ⊥ :=
  Ideal.ne_bot_of_liesOver_of_ne_bot (span_natPrime_ne_bot hp) P

/-- The ramification index appearing in T21 cannot be zero. -/
theorem global_ramificationIdx_pos (L : Type*) [Field L] [NumberField L]
    (P : Ideal (𝓞 L)) [P.IsPrime] : 0 < P.ramificationIdx ℤ :=
  P.ramificationIdx_pos ℤ

/-- The global different in T21 is nonzero, including for the rational number field. -/
theorem global_different_ne_bot (L : Type*) [Field L] [NumberField L] :
    differentIdeal ℤ (𝓞 L) ≠ ⊥ :=
  differentIdeal_ne_bot

/-- Prime-power divisibility is the characteristic property of the global different exponent. -/
theorem pow_dvd_global_different_iff (L : Type*) [Field L] [NumberField L]
    (P : Ideal (𝓞 L)) [P.IsPrime] (n : ℕ) :
    P ^ n ∣ differentIdeal ℤ (𝓞 L) ↔ n ≤ multiplicity P (differentIdeal ℤ (𝓞 L)) := by
  have hfin := FiniteMultiplicity.of_not_isUnit
    (mt Ideal.isUnit_iff.mp (Ideal.IsPrime.ne_top (inferInstance : P.IsPrime)))
    (global_different_ne_bot L)
  exact hfin.pow_dvd_iff_le_multiplicity

/-- The `+ 1` in the target converts an upper exponent bound to nondivisibility. -/
theorem not_pow_dvd_global_different_iff (L : Type*) [Field L] [NumberField L]
    (P : Ideal (𝓞 L)) [P.IsPrime] (b : ℕ) :
    ¬ P ^ (b + 1) ∣ differentIdeal ℤ (𝓞 L) ↔
      multiplicity P (differentIdeal ℤ (𝓞 L)) ≤ b := by
  rw [pow_dvd_global_different_iff, not_le]
  omega

/-- The complete `e = 1` case of the exact global target, with no Galois assumption. -/
theorem serreDifferentBound_of_ramificationIdx_eq_one
    (L : Type*) [Field L] [NumberField L] (p : ℕ) (P : Ideal (𝓞 L)) [P.IsPrime]
    (he : P.ramificationIdx ℤ = 1) :
    ¬ P ^ (P.ramificationIdx ℤ - 1 +
        P.ramificationIdx ℤ * padicValNat p (P.ramificationIdx ℤ) + 1)
      ∣ differentIdeal ℤ (𝓞 L) := by
  have hunram : Algebra.IsUnramifiedAt ℤ P := Ideal.ramificationIdx_eq_one_iff.mp he
  have hnot : ¬ P ∣ differentIdeal ℤ (𝓞 L) := not_dvd_differentIdeal_iff.mpr hunram
  simpa [he] using hnot

/-- Unramified primes satisfy the exact T21 bound, for every natural `p`. -/
theorem serreDifferentBound_of_isUnramifiedAt
    (L : Type*) [Field L] [NumberField L] (p : ℕ) (P : Ideal (𝓞 L)) [P.IsPrime]
    [Algebra.IsUnramifiedAt ℤ P] :
    ¬ P ^ (P.ramificationIdx ℤ - 1 +
        P.ramificationIdx ℤ * padicValNat p (P.ramificationIdx ℤ) + 1)
      ∣ differentIdeal ℤ (𝓞 L) :=
  serreDifferentBound_of_ramificationIdx_eq_one L p P (P.ramificationIdx_eq_one ℤ)

/-- The prime ideal associated to a natural prime, with normalized integral valuation. -/
def rationalPrimePlace (p : ℕ) (hp : p.Prime) : HeightOneSpectrum ℤ :=
  ⟨Ideal.span {(p : ℤ)},
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp),
    span_natPrime_ne_bot hp⟩

/-- Integral prime-ideal multiplicity agrees with `padicValNat`, without the zero convention. -/
theorem multiplicity_span_natCast (p : ℕ) (hp : p.Prime) {n : ℕ} (hn : n ≠ 0) :
    multiplicity (Ideal.span {(p : ℤ)}) (Ideal.span {(n : ℤ)}) = padicValNat p n := by
  let v := rationalPrimePlace p hp
  have hnI : (Ideal.span {(n : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simpa only [ne_eq, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero] using hn
  have hfin := FiniteMultiplicity.of_prime_left v.prime hnI
  have hpow (k : ℕ) : (Ideal.span {(p : ℤ)}) ^ k ∣ Ideal.span {(n : ℤ)} ↔
      k ≤ padicValNat p n := by
    rw [Ideal.span_singleton_pow, Ideal.dvd_span_singleton, Ideal.mem_span_singleton]
    norm_cast
    exact Nat.pow_dvd_iff_le_padicValNat hp.ne_one hn
  have hle (k : ℕ) :
      k ≤ multiplicity (Ideal.span {(p : ℤ)}) (Ideal.span {(n : ℤ)}) ↔
        k ≤ padicValNat p n := hfin.pow_dvd_iff_le_multiplicity.symm.trans (hpow k)
  exact le_antisymm ((hle _).mp le_rfl) ((hle _).mpr le_rfl)

/-- The normalized valuation of a nonzero natural integer at `(p)`. -/
theorem rationalPrimePlace_intValuation_natCast (p : ℕ) (hp : p.Prime)
    {n : ℕ} (hn : n ≠ 0) :
    (rationalPrimePlace p hp).intValuation (n : ℤ) = exp (-(padicValNat p n : ℤ)) := by
  rw [HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ (by exact_mod_cast hn)]
  rw [show (rationalPrimePlace p hp).asIdeal = Ideal.span {(p : ℤ)} from rfl,
    multiplicity_span_natCast p hp hn]

/-- Global integer normalization: `v_P(n) = e(P|p) v_p(n)` in multiplicative notation. -/
theorem primeAbove_intValuation_natCast (L : Type*) [Field L] [NumberField L]
    (p : ℕ) (hp : p.Prime) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})] {n : ℕ} (hn : n ≠ 0) :
    w.intValuation (n : 𝓞 L) =
      exp (-((w.asIdeal.ramificationIdx ℤ * padicValNat p n : ℕ) : ℤ)) := by
  let v := rationalPrimePlace p hp
  have : w.asIdeal.LiesOver v.asIdeal := inferInstanceAs
    (w.asIdeal.LiesOver (Ideal.span {(p : ℤ)}))
  have h := HeightOneSpectrum.intValuation_liesOver v w (n : ℤ)
  rw [show v.intValuation (n : ℤ) = exp (-(padicValNat p n : ℤ)) from
    rationalPrimePlace_intValuation_natCast p hp hn] at h
  rw [map_natCast, ← exp_nsmul] at h
  rw [← h]
  congr 1
  simp

/-- Global integer normalization, directly as an ideal multiplicity. -/
theorem primeAbove_multiplicity_natCast (L : Type*) [Field L] [NumberField L]
    (p : ℕ) (hp : p.Prime) (P : Ideal (𝓞 L)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] {n : ℕ} (hn : n ≠ 0) :
    multiplicity P (Ideal.span {(n : 𝓞 L)}) = P.ramificationIdx ℤ * padicValNat p n := by
  let w : HeightOneSpectrum (𝓞 L) := ⟨P, inferInstance, primeAbove_ne_bot L hp P⟩
  have h := primeAbove_intValuation_natCast L p hp w hn
  rw [HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ (by exact_mod_cast hn),
    exp_inj, neg_inj, Int.natCast_inj] at h
  exact h

end ZInQ.Contrib.DifferentBound
