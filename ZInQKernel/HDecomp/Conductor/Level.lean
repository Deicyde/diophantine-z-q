import ZInQKernel.Hypotheses.Height

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt from
`scratch/glue-conductor/Level.lean`.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/


/-!
# glue-conductor: the level product `N ≤ Q_R M²` (h-trust D4-D5, N5 L846-857)

Over the repository's own definitions (`ZInQ.heightE0`, `ZInQ.heightQ`,
`ZInQ.contactSupport`). The conductor exponents `a_p = v_p(N)` (Carayol's Théorème A turns the
conductor exponents of `r₅` (and of `r₃` at `p = 5`) into the exponents of the level `N`) enter
through `N.factorization`. Hypotheses, as in N5:

* `a_p ≤ E₀` at primes `p ≤ R` (D4, first case);
* at primes `p > R`, `a_p ≤ 2` (D4, tame case), and `a_p = 0` unless `p ∈ T = S ∪ supp M_S(u)`
  (D4, third case: outside `T`, `L` is unramified, `A` has good reduction and `β` is unramified).

Since `max S ≤ R`, a prime `p > R` with `a_p > 0` divides `M = M_S(u)`, a product of distinct
primes, so the large part of `N` is at most `M²`; the small part is at most
`(∏_{p ≤ R} p)^{E₀} ≤ R^{R E₀} = Q_R`. No `sorry`.
-/

namespace GlueConductor

open ZInQ

/-- `M_S(u) > 0`. -/
lemma contactSupport_pos' (S : Finset ℕ) (u : ℚ) : 0 < contactSupport S u := by
  classical
  unfold contactSupport
  apply Finset.prod_pos
  intro p hp
  exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos

/-- `∏_{p prime, p ≤ R} p^E ≤ R^(R E)` for real `R ≥ 1`, over any finset of primes `≤ R`. -/
lemma prod_small_le (R : ℝ) (hR : 1 ≤ R) (E : ℕ) (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime ∧ (p : ℝ) ≤
    R) :
    ∏ p ∈ s, (p : ℝ) ^ E ≤ R ^ (R * E) := by
  have hR0 : (0 : ℝ) ≤ R := by linarith
  have hcard : (s.card : ℝ) ≤ R := by
    have hsub : s ⊆ Finset.Icc 1 ⌊R⌋₊ := by
      intro p hp
      obtain ⟨hpp, hpR⟩ := hs p hp
      simp only [Finset.mem_Icc]
      exact ⟨hpp.one_lt.le, Nat.le_floor hpR⟩
    have h1 : s.card ≤ ⌊R⌋₊ := by
      simpa using Finset.card_le_card hsub
    calc (s.card : ℝ) ≤ ⌊R⌋₊ := by exact_mod_cast h1
      _ ≤ R := Nat.floor_le hR0
  calc ∏ p ∈ s, (p : ℝ) ^ E = (∏ p ∈ s, (p : ℝ)) ^ E := by rw [Finset.prod_pow]
    _ ≤ (R ^ s.card) ^ E := by
        apply pow_le_pow_left₀ (Finset.prod_nonneg fun p _ => by positivity)
        calc ∏ p ∈ s, (p : ℝ) ≤ ∏ _p ∈ s, R :=
              Finset.prod_le_prod₀ (fun p _ => by positivity) (fun p hp => (hs p hp).2)
          _ = R ^ s.card := Finset.prod_const R
    _ = R ^ ((s.card : ℝ) * E) := by
        rw [Real.rpow_mul hR0, Real.rpow_natCast, Real.rpow_natCast]
    _ ≤ R ^ (R * E) := by
        apply Real.rpow_le_rpow_of_exponent_le hR
        exact mul_le_mul_of_nonneg_right hcard (by positivity)

/-- **D5's product (N5 L852-857).** Let `N ≥ 1` have exponents `a_p = v_p(N)` with `a_p ≤ E₀`
at `p ≤ R`, and, at `p > R`, `a_p ≤ 2` and `a_p = 0` unless `p ∈ S` or `p ∣ M_S(u)`. If every
prime of `S` is at most `R` and `R ≥ 1`, then `N ≤ Q_R · M_S(u)²`. -/
theorem level_le (S : Finset ℕ) (u : ℚ) (R : ℝ) (hR : 1 ≤ R) (hS : ∀ p ∈ S, (p : ℝ) ≤ R)
    (N : ℕ) (hN : N ≠ 0)
    (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ R → N.factorization p ≤ heightE0)
    (hlarge : ∀ p : ℕ, p.Prime → R < p → N.factorization p ≤ 2)
    (houtside : ∀ p : ℕ, p.Prime → p ∣ N → p ∈ S ∨ p ∣ contactSupport S u) :
    (N : ℝ) ≤ heightQ R * (contactSupport S u : ℝ) ^ 2 := by
  classical
  set M := contactSupport S u
  have hM : 0 < M := contactSupport_pos' S u
  have hN' : (N : ℝ) = ∏ p ∈ N.primeFactors, (p : ℝ) ^ (N.factorization p) := by
    conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hN]
    push_cast
    rfl
  rw [hN', ← Finset.prod_filter_mul_prod_filter_not N.primeFactors (fun p : ℕ => (p : ℝ) ≤ R)]
  set sm := N.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ R)
  set lg := N.primeFactors.filter (fun p : ℕ => ¬ (p : ℝ) ≤ R)
  -- small primes
  have h1 : ∏ p ∈ sm, (p : ℝ) ^ (N.factorization p) ≤ heightQ R := by
    calc ∏ p ∈ sm, (p : ℝ) ^ (N.factorization p) ≤ ∏ p ∈ sm, (p : ℝ) ^ heightE0 := by
          apply Finset.prod_le_prod₀ (fun p _ => by positivity)
          intro p hp
          obtain ⟨hpN, hpR⟩ := Finset.mem_filter.mp hp
          have hpp := Nat.prime_of_mem_primeFactors hpN
          exact pow_le_pow_right₀ (by exact_mod_cast hpp.one_lt.le) (hsmall p hpp hpR)
      _ ≤ R ^ (R * heightE0) := by
          apply prod_small_le R hR heightE0 sm
          intro p hp
          obtain ⟨hpN, hpR⟩ := Finset.mem_filter.mp hp
          exact ⟨Nat.prime_of_mem_primeFactors hpN, hpR⟩
      _ = heightQ R := rfl
  -- large primes
  have h2 : ∏ p ∈ lg, (p : ℝ) ^ (N.factorization p) ≤ (M : ℝ) ^ 2 := by
    have hdvd : (∏ p ∈ lg, p) ∣ M := by
      apply Finset.prod_primes_dvd
      · intro p hp
        exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).prime
      · intro p hp
        obtain ⟨hpN, hpR⟩ := Finset.mem_filter.mp hp
        have hpp := Nat.prime_of_mem_primeFactors hpN
        rcases houtside p hpp (Nat.dvd_of_mem_primeFactors hpN) with h | h
        · exact absurd (hS p h) hpR
        · exact h
    have hle : (∏ p ∈ lg, p) ≤ M := Nat.le_of_dvd hM hdvd
    calc ∏ p ∈ lg, (p : ℝ) ^ (N.factorization p) ≤ ∏ p ∈ lg, (p : ℝ) ^ 2 := by
          apply Finset.prod_le_prod₀ (fun p _ => by positivity)
          intro p hp
          obtain ⟨hpN, hpR⟩ := Finset.mem_filter.mp hp
          have hpp := Nat.prime_of_mem_primeFactors hpN
          exact pow_le_pow_right₀ (by exact_mod_cast hpp.one_lt.le)
            (hlarge p hpp (lt_of_not_ge hpR))
      _ = ((∏ p ∈ lg, p : ℕ) : ℝ) ^ 2 := by push_cast; rw [Finset.prod_pow]
      _ ≤ (M : ℝ) ^ 2 := by
          apply pow_le_pow_left₀ (by positivity)
          exact_mod_cast hle
  have hQ : 0 ≤ heightQ R := Real.rpow_nonneg (by linarith) _
  calc (∏ p ∈ sm, (p : ℝ) ^ (N.factorization p)) * ∏ p ∈ lg, (p : ℝ) ^ (N.factorization p)
      ≤ heightQ R * (M : ℝ) ^ 2 :=
        mul_le_mul h1 h2 (Finset.prod_nonneg fun p _ => by positivity) hQ

end GlueConductor

