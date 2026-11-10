/-
The lemma `prod_factors_sum_pow_mult` below is adapted from `Sieve.prod_factors_sum_pow_compMult`
of PrimeNumberTheoremAnd (`PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/SelbergBounds.lean`,
Copyright (c) 2023 Arend Mellendijk, released under the Apache 2.0 license; see
`ZInQKernel/Sieve/LICENSE`). The only change: the hypothesis "completely multiplicative" is weakened
to "multiplicative", which is all the proof uses.
-/
import ZInQKernel.Sieve.SelbergBounds
import ZInQKernel.Density.GaussSieve.Harmonic

/-!
# A lower bound for the Selberg sum `S`

For a Selberg sieve whose terms satisfy `g(q) ≥ (1 - 1/q)⁻² - 1 = Σ_{k ≥ 1} (k + 1)/q^k` at the
sifting primes and whose level is `w²`:

  `S ≥ Σ_{m ≤ w, rad m ∣ P} τ(m)/m`   (`selbergBoundingSum_ge_tau`).
-/

open ArithmeticFunction Finset

namespace ZInQ.Density.GaussSieve

noncomputable section

open scoped Classical

theorem prod_factors_sum_pow_mult (M : ℕ) (hM : M ≠ 0) (f : ArithmeticFunction ℝ)
    (hf : IsMultiplicative f) (d : ℕ) (hd : Squarefree d) :
    ∏ p ∈ d.primeFactors, ∑ n ∈ Finset.Icc 1 M, f (p^n)
    = ∑ m ∈ (d^M).divisors.filter (d ∣ ·), f m := by
  rw [Finset.prod_sum]
  let i : (a:_) → (ha : a ∈ Finset.pi d.primeFactors fun p => Finset.Icc 1 M) → ℕ :=
    fun a _ => ∏ p ∈ d.primeFactors.attach, p.1 ^ (a p p.2)
  have hfact_i : ∀ a ha,
      ∀ p , Nat.factorization (i a ha) p = if hp : p ∈ d.primeFactors then a p hp else 0 := by
    intro a ha p
    by_cases hp : p ∈ d.primeFactors
    · rw [dite_eq_left hp, Nat.factorization_prod, Finset.sum_apply',
        Finset.sum_eq_single ⟨p, hp⟩, Nat.factorization_pow, Finsupp.smul_apply,
        Nat.Prime.factorization_self (Nat.prime_of_mem_primeFactorsList <| List.mem_toFinset.mp hp)]
      · ring
      · intro q _ hq
        rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_zero]; right
        apply Nat.factorization_eq_zero_of_not_dvd
        rw [Nat.Prime.dvd_iff_eq, ← exists_eq_subtype_mk_iff]
        · push Not
          exact fun _ => hq
        · exact Nat.prime_of_mem_primeFactorsList <| List.mem_toFinset.mp q.2
        · exact (Nat.prime_of_mem_primeFactorsList <| List.mem_toFinset.mp hp).ne_one
      · intro h
        exfalso
        exact h (Finset.mem_attach _ _)
      · exact fun q _ => pow_ne_zero _ (ne_of_gt (Nat.pos_of_mem_primeFactorsList
          (List.mem_toFinset.mp q.2)))
    · rw [dite_eq_right hp]
      by_cases hpp : p.Prime
      swap
      · apply Nat.factorization_eq_zero_of_not_prime _ hpp
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hp_dvd
      obtain ⟨⟨q, hq⟩, _, hp_dvd_pow⟩ := Prime.exists_mem_finset_dvd hpp.prime hp_dvd
      apply hp
      rw [Nat.mem_primeFactors]
      constructor
      · exact hpp
      refine ⟨?_, hd.ne_zero⟩
      trans q
      · apply Nat.Prime.dvd_of_dvd_pow hpp hp_dvd_pow
      · apply Nat.dvd_of_mem_primeFactorsList <| List.mem_toFinset.mp hq

  have hi_ne_zero : ∀ (a : _) (ha : a ∈ Finset.pi d.primeFactors fun _p => Finset.Icc 1 M),
      i a ha ≠ 0 := by
    intro a ha
    erw [Finset.prod_ne_zero_iff]
    exact fun p _ => pow_ne_zero _ (ne_of_gt (Nat.pos_of_mem_primeFactorsList
      (List.mem_toFinset.mp p.property)))
  have hi : ∀ (a : _) (ha : a ∈ Finset.pi d.primeFactors fun _p => Finset.Icc 1 M),
      i a ha ∈ (d^M).divisors.filter (d ∣ ·) := by
    intro a ha
    rw [Finset.mem_filter, Nat.mem_divisors, ←Nat.factorization_le_iff_dvd hd.ne_zero
      (hi_ne_zero a ha),← Nat.factorization_le_iff_dvd (hi_ne_zero a ha) (pow_ne_zero _ hd.ne_zero)]
    constructor; constructor
    · rw [Finsupp.le_iff]; intro p _
      rw [hfact_i a ha]
      by_cases hp : p ∈ d.primeFactors
      · rw [dite_eq_left hp]
        rw [Nat.factorization_pow, Finsupp.smul_apply]
        simp_rw [Finset.mem_pi, Finset.mem_Icc] at ha
        trans (M • 1)
        · norm_num
          exact (ha p hp).2
        · gcongr
          rw [Nat.mem_primeFactors_of_ne_zero hd.ne_zero] at hp
          rw [←Nat.Prime.dvd_iff_one_le_factorization hp.1 hd.ne_zero]
          exact hp.2
      · rw [dite_eq_right hp]; norm_num
    · apply pow_ne_zero _ hd.ne_zero
    · rw [Finsupp.le_iff]; intro p hp
      rw [Nat.support_factorization] at hp
      rw [hfact_i a ha]
      rw [dite_eq_left hp]
      trans 1
      · exact hd.natFactorization_le_one p
      simp_rw [Finset.mem_pi, Finset.mem_Icc] at ha
      exact (ha p hp).1

  have h : ∀ (a : _) (ha : a ∈ Finset.pi d.primeFactors fun _p => Finset.Icc 1 M),
      ∏ p ∈ d.primeFactors.attach, f (p.1 ^ (a p p.2)) = f (i a ha) := by
    intro a ha
    apply symm
    apply hf.map_prod
    intro x _ y _ hxy
    simp_rw [Finset.mem_pi, Finset.mem_Icc, Nat.succ_le_iff] at ha
    apply (Nat.coprime_pow_left_iff (ha x x.2).1 ..).mpr
    apply (Nat.coprime_pow_right_iff (ha y y.2).1 ..).mpr
    have hxp := Nat.prime_of_mem_primeFactorsList (List.mem_toFinset.mp x.2)
    rw [Nat.Prime.coprime_iff_not_dvd hxp]
    rw [Nat.prime_dvd_prime_iff_eq hxp <| Nat.prime_of_mem_primeFactorsList
      (List.mem_toFinset.mp y.2)]
    exact fun hc => hxy (Subtype.ext hc)

  have i_inj : ∀ a ha b hb, i a ha = i b hb → a = b := by
    intro a ha b hb hiab
    apply_fun Nat.factorization at hiab
    ext p hp
    obtain hiabp := DFunLike.ext_iff.mp hiab p
    rw [hfact_i a ha, hfact_i b hb, dite_eq_left hp, dite_eq_left hp] at hiabp
    exact hiabp

  have i_surj : ∀ (b : ℕ), b ∈ (d^M).divisors.filter (d ∣ ·) → ∃ a ha, i a ha = b := by
    intro b hb
    have h : (fun p _ => b.factorization p) ∈ Finset.pi d.primeFactors fun p => Finset.Icc 1 M := by
      rw [Finset.mem_pi]; intro p hp
      rw [Finset.mem_Icc]
      rw [Finset.mem_filter] at hb
      have hb_ne_zero : b ≠ 0 := ne_of_gt <| Nat.pos_of_mem_divisors hb.1
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      constructor
      · rw [←Nat.Prime.dvd_iff_one_le_factorization hpp hb_ne_zero]
        · exact Trans.trans (Nat.dvd_of_mem_primeFactors hp) hb.2
      · rw [Nat.mem_divisors] at hb
        trans Nat.factorization (d^M) p
        · exact (Nat.factorization_le_iff_dvd hb_ne_zero hb.left.right).mpr hb.left.left p
        rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
        have : d.factorization p ≤ 1 := by
          apply hd.natFactorization_le_one
        exact (mul_le_iff_le_one_right (Nat.pos_of_ne_zero hM)).mpr this
    use (fun p _ => Nat.factorization b p)
    use h
    apply Nat.eq_of_factorization_eq
    · apply hi_ne_zero _ h
    · exact ne_of_gt <| Nat.pos_of_mem_divisors (Finset.mem_filter.mp hb).1
    intro p
    rw [hfact_i (fun p _ => (Nat.factorization b) p) h p]
    rw [Finset.mem_filter, Nat.mem_divisors] at hb
    by_cases hp : p ∈ d.primeFactors
    · rw [dite_eq_left hp]
    · rw [dite_eq_right hp, eq_comm, Nat.factorization_eq_zero_iff, ←or_assoc]
      rw [Nat.mem_primeFactors] at hp
      left
      push Not at hp
      by_cases hpp : p.Prime
      · right; intro h
        apply absurd (hp hpp)
        push Not
        exact ⟨hpp.dvd_of_dvd_pow (h.trans hb.1.1), hd.ne_zero⟩
      · left; exact hpp

  exact Finset.sum_bij i hi i_inj i_surj h

/-- `Σ_{k=1}^{M} (k + 1)·x^k ≤ (1 - x)⁻² - 1` for `0 ≤ x < 1`. -/
theorem sum_succ_mul_pow_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (M : ℕ) :
    ∑ k ∈ Icc 1 M, ((k : ℝ) + 1) * x ^ k ≤ 1 / (1 - x) ^ 2 - 1 := by
  have closed : ∀ M : ℕ, (∑ k ∈ range (M + 1), ((k : ℝ) + 1) * x ^ k) * (1 - x) ^ 2 =
      1 - (M + 2) * x ^ (M + 1) + (M + 1) * x ^ (M + 2) := by
    intro M
    induction M with
    | zero => simp; ring
    | succ M ih => rw [sum_range_succ, add_mul, ih]; push_cast; ring
  have hpos : 0 < (1 - x) ^ 2 := by have : 0 < 1 - x := by linarith
                                    positivity
  have hr : ∑ k ∈ range (M + 1), ((k : ℝ) + 1) * x ^ k ≤ 1 / (1 - x) ^ 2 := by
    rw [le_div_iff₀ hpos, closed]
    have h1 : 0 ≤ x ^ (M + 1) * ((M + 2) - (M + 1) * x) :=
      mul_nonneg (pow_nonneg hx0 _) (by nlinarith)
    have h2 : x ^ (M + 2) = x ^ (M + 1) * x := pow_succ x (M + 1)
    rw [h2]
    nlinarith [h1]
  have hsplit : ∑ k ∈ range (M + 1), ((k : ℝ) + 1) * x ^ k =
      1 + ∑ k ∈ Icc 1 M, ((k : ℝ) + 1) * x ^ k := by
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (Nat.succ_pos M)]
    simp only [CharP.cast_eq_zero, zero_add, pow_zero, mul_one]
    rfl
  linarith

theorem tauDiv_prime_pow {q : ℕ} (hq : q.Prime) (k : ℕ) :
    tauDiv (q ^ k) = ((k : ℝ) + 1) * (1 / (q : ℝ)) ^ k := by
  rw [tauDiv_apply, card_divisors_prime_pow' hq, one_div_pow, Nat.cast_pow, div_eq_mul_one_div]

/-- For `l ∣ P`, `g(l) ≥ Σ_{l ∣ m ∣ l^M} τ(m)/m`. -/
theorem selbergTerms_ge_sum_tau (s : BoundingSieve)
    (hg : ∀ q, q.Prime → q ∣ s.prodPrimes →
      1 / (1 - 1 / (q : ℝ)) ^ 2 - 1 ≤ SelbergSieve.selbergTerms s q)
    (M : ℕ) (hM : M ≠ 0) {l : ℕ} (hl : l ∣ s.prodPrimes) :
    ∑ m ∈ (l ^ M).divisors.filter (l ∣ ·), tauDiv m ≤ SelbergSieve.selbergTerms s l := by
  have hlsq : Squarefree l := Squarefree.squarefree_of_dvd hl s.prodPrimes_squarefree
  rw [← prod_factors_sum_pow_mult M hM tauDiv tauDiv_mult l hlsq,
    ← (SelbergSieve.selbergTerms_mult s).prod_primeFactors hlsq]
  refine Finset.prod_le_prod₀ (fun q _ => sum_nonneg fun k _ => by rw [tauDiv_apply]; positivity)
    fun q hq => ?_
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hqP : q ∣ s.prodPrimes := (Nat.dvd_of_mem_primeFactors hq).trans hl
  simp_rw [tauDiv_prime_pow hqp]
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hqp.one_lt
  refine le_trans (sum_succ_mul_pow_le (by positivity) ?_ M) (hg q hqp hqP)
  rw [div_lt_one (by linarith)]; exact hq1

/-- **The lower bound for `S`.** If the level is `w²` and `g(q) ≥ (1 - 1/q)⁻² - 1` at the sifting
primes, then `S ≥ Σ_{m ≤ w, rad m ∣ P} τ(m)/m`. -/
theorem selbergBoundingSum_ge_tau (s : SelbergSieve) (w : ℕ) (hw : 1 ≤ w)
    (hlevel : s.level = (w : ℝ) ^ 2)
    (hg : ∀ q, q.Prime → q ∣ s.prodPrimes →
      1 / (1 - 1 / (q : ℝ)) ^ 2 - 1 ≤ SelbergSieve.selbergTerms s.toBoundingSieve q) :
    ∑ m ∈ (Icc 1 w).filter (fun m => (∏ p ∈ m.primeFactors, p) ∣ s.prodPrimes), tauDiv m
      ≤ s.selbergBoundingSum := by
  have hP0 : s.prodPrimes ≠ 0 := s.prodPrimes_squarefree.ne_zero
  set A : ℕ → Finset ℕ := fun l => (l ^ w).divisors.filter (l ∣ ·) with hA
  set L := s.prodPrimes.divisors.filter (fun l : ℕ => ((l : ℝ) ^ 2 ≤ s.level)) with hL
  -- step 1: compare with the sum over `L` of the sums over `A l`
  have h1 : ∑ l ∈ L, ∑ m ∈ A l, tauDiv m ≤ s.selbergBoundingSum := by
    rw [SelbergSieve.selbergBoundingSum, ← sum_filter]
    refine sum_le_sum fun l hl => ?_
    have hlP : l ∣ s.prodPrimes := (Nat.mem_divisors.1 (mem_filter.1 hl).1).1
    push_cast at hl ⊢
    exact selbergTerms_ge_sum_tau s.toBoundingSieve hg w (by omega) hlP
  -- step 2: the sets `A l` are pairwise disjoint
  have hdisj : (L : Set ℕ).PairwiseDisjoint A := by
    intro i hi j hj hij t hti htj x hx
    simp only [Finset.bot_eq_empty, Finset.notMem_empty]
    specialize hti hx
    specialize htj hx
    simp only [hA, hL, Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors] at *
    have h : ∀ i j {n}, i ∣ s.prodPrimes → i ∣ x → x ∣ j ^ n → i ∣ j := by
      intro i j n hiP hix hij
      apply Sieve.Nat.squarefree_dvd_pow i j n (Squarefree.squarefree_of_dvd hiP s.prodPrimes_squarefree)
      exact Trans.trans hix hij
    exact hij <| Nat.dvd_antisymm (h i j hi.1.1 hti.2 htj.1.1) (h j i hj.1.1 htj.2 hti.1.1)
  rw [← sum_biUnion hdisj] at h1
  refine le_trans (sum_le_sum_of_subset_of_nonneg ?_ fun m _ _ => by
    rw [tauDiv_apply]; positivity) h1
  -- step 3: every `m ≤ w` with `rad m ∣ P` lies in `A (rad m)`
  intro m hm
  simp only [mem_filter, mem_Icc] at hm
  obtain ⟨⟨hm1, hmw⟩, hrad⟩ := hm
  have hm0 : m ≠ 0 := by omega
  have hrad0 : (∏ p ∈ m.primeFactors, p) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun p hp => (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hradle : (∏ p ∈ m.primeFactors, p) ≤ m := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd m)
  rw [mem_biUnion]
  refine ⟨∏ p ∈ m.primeFactors, p, ?_, ?_⟩
  · simp only [hL, mem_filter, Nat.mem_divisors, hlevel]
    refine ⟨⟨hrad, hP0⟩, ?_⟩
    have : ((∏ p ∈ m.primeFactors, p : ℕ) : ℝ) ≤ w := by exact_mod_cast hradle.trans hmw
    have h0 : (0 : ℝ) ≤ ((∏ p ∈ m.primeFactors, p : ℕ) : ℝ) := Nat.cast_nonneg _
    push_cast at this h0 ⊢
    nlinarith
  · simp only [hA, mem_filter, Nat.mem_divisors]
    refine ⟨⟨?_, pow_ne_zero _ hrad0⟩, Nat.prod_primeFactors_dvd m⟩
    rw [← Nat.factorization_le_iff_dvd hm0 (pow_ne_zero _ hrad0)]
    intro p
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    by_cases hp : p ∈ m.primeFactors
    · have hpp := Nat.prime_of_mem_primeFactors hp
      have h1 : 1 ≤ (∏ p ∈ m.primeFactors, p).factorization p := by
        rw [← Nat.Prime.dvd_iff_one_le_factorization hpp hrad0]
        exact Finset.dvd_prod_of_mem _ hp
      have h2 : m.factorization p < m := Nat.factorization_lt p hm0
      nlinarith
    · rw [Finsupp.notMem_support_iff.1 (by rwa [Nat.support_factorization])]
      exact Nat.zero_le _

end

end ZInQ.Density.GaussSieve
