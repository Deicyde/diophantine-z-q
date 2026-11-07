import ZInQKernel.Multiplication.Certificate.Constants

/-!
# Valuations of the pattern values

A value `ε k p` of the twenty-two-prime pattern, with `k = d h` (`d ∣ P_s⁴`, `h ∈ 𝓗`) and `p` a
prime outside the old primes, has valuation in `[0, 4]` at primes `q ≤ 324`, in `[0, 1]` at
catalogue primes, and at any other prime `q` it is divisible by `q` only when `q = p`, with
valuation one.
-/

namespace ZInQ.Mult

open scoped BigOperators

theorem catalogueSet_prime {q : ℕ} (hq : q ∈ catalogueSet) : q.Prime ∧ 324 < q := by
  obtain ⟨r, i, hr, hcop, -, rfl⟩ := hq
  exact ⟨(cataloguePrime_spec hr hcop i).1, (cataloguePrime_spec hr hcop i).2.1⟩

theorem le_catalogue_sup {q : ℕ} (hq : q ∈ catalogueSet) : q ≤ catalogue.sup id :=
  Finset.le_sup (f := id) (mem_catalogue.mpr hq)

theorem padicValNat_le_of_dvd' {q a b : ℕ} [Fact q.Prime] (hb : b ≠ 0) (hab : a ∣ b) :
    padicValNat q a ≤ padicValNat q b := by
  have ha : a ≠ 0 := fun h => hb (Nat.eq_zero_of_zero_dvd (h ▸ hab))
  exact (padicValNat_dvd_iff_le hb).mp ((pow_padicValNat_dvd (p := q) (n := a)).trans hab)

theorem padicValNat_primorial_le_one (q n : ℕ) [Fact q.Prime] : padicValNat q (primorial n) ≤ 1 := by
  rw [← Nat.factorization_def _ Fact.out]
  exact (squarefree_primorial n).natFactorization_le_one q

theorem padicValNat_prime_le_one {q h : ℕ} [Fact q.Prime] (hh : h.Prime) : padicValNat q h ≤ 1 := by
  by_cases hqh : q = h
  · subst hqh; rw [padicValNat_self]
  · have : Fact h.Prime := ⟨hh⟩
    rw [padicValNat_primes hqh]; omega

/-- At a prime `q ≤ 324`, a catalogue multiplier has valuation at most `4`. -/
theorem padicValNat_multiplier_le_small {k q : ℕ} (hk : k ∈ catalogueMultipliers) (hq : q.Prime)
    (hq324 : q ≤ 324) : padicValNat q k ≤ 4 := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨d, h, hd, hd0, hh, rfl⟩ := hk
  obtain ⟨hhp, hh324⟩ := catalogueSet_prime hh
  have : Fact h.Prime := ⟨hhp⟩
  rw [padicValNat.mul hd0.ne' hhp.ne_zero, padicValNat_primes (by omega : q ≠ h), add_zero]
  calc padicValNat q d ≤ padicValNat q (primorial 324 ^ 4) :=
        padicValNat_le_of_dvd' (pow_ne_zero _ (primorial_pos _).ne') hd
    _ = 4 * padicValNat q (primorial 324) := padicValNat.pow _ _
    _ ≤ 4 := by have := padicValNat_primorial_le_one q 324; omega

/-- A prime above `324` does not divide `P_s⁴`. -/
theorem not_dvd_primorial_pow {q d : ℕ} (hq : q.Prime) (hq324 : 324 < q)
    (hd : d ∣ primorial 324 ^ 4) : ¬ q ∣ d := by
  intro hqd
  have := hq.dvd_of_dvd_pow (hqd.trans hd)
  have := (hq.dvd_primorial_iff).mp this
  omega

/-- At a catalogue prime, a catalogue multiplier has valuation at most `1`. -/
theorem padicValNat_multiplier_le_cat {k q : ℕ} (hk : k ∈ catalogueMultipliers)
    (hq : q ∈ catalogueSet) : padicValNat q k ≤ 1 := by
  obtain ⟨hqp, hq324⟩ := catalogueSet_prime hq
  have : Fact q.Prime := ⟨hqp⟩
  obtain ⟨d, h, hd, hd0, hh, rfl⟩ := hk
  obtain ⟨hhp, -⟩ := catalogueSet_prime hh
  rw [padicValNat.mul hd0.ne' hhp.ne_zero,
    padicValNat.eq_zero_of_not_dvd (not_dvd_primorial_pow hqp hq324 hd), zero_add]
  exact padicValNat_prime_le_one hhp

/-- A prime above `324` outside the catalogue does not divide a catalogue multiplier. -/
theorem not_dvd_multiplier {k q : ℕ} (hk : k ∈ catalogueMultipliers) (hq : q.Prime)
    (hq324 : 324 < q) (hcat : q ∉ catalogueSet) : ¬ q ∣ k := by
  obtain ⟨d, h, hd, -, hh, rfl⟩ := hk
  intro hdvd
  rcases (Nat.Prime.dvd_mul hq).mp hdvd with h1 | h1
  · exact not_dvd_primorial_pow hq hq324 hd h1
  · obtain ⟨hhp, -⟩ := catalogueSet_prime hh
    have := (Nat.prime_dvd_prime_iff_eq hq hhp).mp h1
    exact hcat (this ▸ hh)

/-- The valuation of a pattern value `ε k p`. -/
theorem padicValInt_pattern_value {q : ℕ} [Fact q.Prime] {ε : ℤ} {k p : ℕ} (hε : ε = 1 ∨ ε = -1)
    (hk : 0 < k) (hp : p.Prime) :
    padicValInt q (ε * k * p) = padicValNat q k + padicValNat q p := by
  have hεk : ε * k * p = ((k * p : ℕ) : ℤ) * ε := by push_cast; ring
  rw [hεk, padicValInt.mul (by exact_mod_cast (Nat.mul_pos hk hp.pos).ne')
    (by rcases hε with rfl | rfl <;> norm_num)]
  have : padicValInt q ε = 0 := by
    rcases hε with rfl | rfl
    · simp
    · rw [show (-1 : ℤ) = -(1 : ℤ) from rfl, padicValInt, Int.natAbs_neg]; simp
  rw [this, add_zero, padicValInt.of_nat, padicValNat.mul hk.ne' hp.ne_zero]

end ZInQ.Mult
