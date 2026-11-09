import Mathlib

/-!
# Sums of `Λ(n)/n` over prime powers

* `sum_vonMangoldt_mul_le_sum_primePow`: a sum of `Λ(n) h(n)` (`h ≥ 0`) over a set of integers
  is at most the double sum of `log p · h(p^k)` over primes `p` and exponents `k` that cover
  the prime powers of the set.
* `sum_nonprime_vonMangoldt_div_le_two`: the prime powers `p^k` with `k ≥ 2` contribute at most
  `2` to `Σ Λ(n)/n`: `Σ_{n ≤ N, n not prime} Λ(n)/n ≤ Σ_p log p/(p(p − 1)) ≤ 2`.
* `sum_nonunit_vonMangoldt_div_le_log`: the integers not coprime to `q` contribute at most
  `log q`.
-/

namespace ZInQ.Progressions

open Finset Real
open ArithmeticFunction hiding log

/-- A sum of `Λ(n) h(n)` with `h ≥ 0` over `A` is bounded by the double sum of `log p · h(p^k)`
over primes `p ∈ P` and exponents `k ∈ K`, provided every prime power of `A` is some `p^k`. -/
theorem sum_vonMangoldt_mul_le_sum_primePow {A P K : Finset ℕ} (h : ℕ → ℝ)
    (hh : ∀ n, 0 ≤ h n) (hP : ∀ p ∈ P, p.Prime) (hK : ∀ k ∈ K, k ≠ 0)
    (hA : ∀ n ∈ A, IsPrimePow n → ∃ p ∈ P, ∃ k ∈ K, p ^ k = n) :
    ∑ n ∈ A, Λ n * h n ≤ ∑ p ∈ P, ∑ k ∈ K, Real.log p * h (p ^ k) := by
  have hinj : Set.InjOn (fun pk : ℕ × ℕ ↦ pk.1 ^ pk.2) ↑(P ×ˢ K) := by
    rintro ⟨p₁, k₁⟩ h₁ ⟨p₂, k₂⟩ h₂ H
    simp only [coe_product, Set.mem_prod, mem_coe] at h₁ h₂
    obtain ⟨rfl, rfl⟩ := (hP _ h₁.1).pow_inj' (hP _ h₂.1) (hK _ h₁.2) (hK _ h₂.2) H
    rfl
  calc ∑ n ∈ A, Λ n * h n = ∑ n ∈ A with IsPrimePow n, Λ n * h n := by
        rw [sum_filter]
        refine sum_congr rfl fun n _ ↦ ?_
        split_ifs with hn
        · rfl
        · rw [vonMangoldt_eq_zero_iff.mpr hn, zero_mul]
    _ ≤ ∑ n ∈ (P ×ˢ K).image (fun pk : ℕ × ℕ ↦ pk.1 ^ pk.2), Λ n * h n := by
        refine sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ ↦
          mul_nonneg vonMangoldt_nonneg (hh n)
        intro n hn
        rw [mem_filter] at hn
        obtain ⟨p, hp, k, hk, rfl⟩ := hA n hn.1 hn.2
        exact mem_image.mpr ⟨(p, k), mem_product.mpr ⟨hp, hk⟩, rfl⟩
    _ = ∑ pk ∈ P ×ˢ K, Λ (pk.1 ^ pk.2) * h (pk.1 ^ pk.2) := sum_image hinj
    _ = ∑ p ∈ P, ∑ k ∈ K, Real.log p * h (p ^ k) := by
        rw [sum_product]
        refine sum_congr rfl fun p hp ↦ sum_congr rfl fun k hk ↦ ?_
        rw [vonMangoldt_apply_pow (hK k hk), vonMangoldt_apply_prime (hP p hp)]

/-- For a prime `p` (indeed any `p ≥ 2`), `Σ_{m ≤ k < n} p^{-k} ≤ p^{-m} · p/(p − 1)`, used as
`Σ_{k ∈ Ico m n} (1/p)^k ≤ (1/p)^m / (1 − 1/p)`. -/
lemma sum_Ico_one_div_pow_le_of_two_le {p : ℕ} (hp : 2 ≤ p) (m n : ℕ) :
    ∑ k ∈ Ico m n, (1 / (p : ℝ)) ^ k ≤ (1 / (p : ℝ)) ^ m / (1 - 1 / p) := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  exact geom_sum_Ico_le_of_lt_one (by positivity) (by rw [div_lt_one (by linarith)]; linarith)

/-- The telescoping bound `Σ_{s < n ≤ N} log n / (n (n − 1)) ≤ (log s + 2)/s − (log N + 2)/N`
for `1 ≤ s ≤ N`. -/
lemma sum_Icc_log_div_mul_pred_le {s : ℕ} (hs : 1 ≤ s) (N : ℕ) (hsN : s ≤ N) :
    ∑ n ∈ Icc (s + 1) N, Real.log n / (n * (n - 1)) ≤
      (Real.log s + 2) / s - (Real.log N + 2) / N := by
  induction N, hsN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    rw [sum_Icc_succ_top (by omega)]
    have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hs.trans hN
    have hN0 : (0 : ℝ) < N := by linarith
    -- the step: `log(N+1)/((N+1)N) ≤ (log N + 2)/N − (log(N+1) + 2)/(N+1)`
    have hstep : Real.log ((N + 1 : ℕ) : ℝ) / (((N + 1 : ℕ) : ℝ) * (((N + 1 : ℕ) : ℝ) - 1)) ≤
        (Real.log N + 2) / N - (Real.log ((N + 1 : ℕ) : ℝ) + 2) / ((N + 1 : ℕ) : ℝ) := by
      push_cast
      have hlog : Real.log (N + 1) - Real.log N ≤ 1 / N := by
        have h := log_le_sub_one_of_pos (x := (N + 1) / N) (by positivity)
        rw [log_div (by positivity) hN0.ne'] at h
        have : (N + 1 : ℝ) / N - 1 = 1 / N := by field_simp; ring
        linarith
      have e1 : (N : ℝ) + 1 - 1 = N := by ring
      rw [e1, div_le_iff₀ (by positivity)]
      have e2 : ((Real.log N + 2) / N - (Real.log (N + 1) + 2) / (N + 1)) * ((N + 1) * N) =
          (N + 1) * (Real.log N + 2) - N * (Real.log (N + 1) + 2) := by
        field_simp
      rw [e2]
      have : (N + 1) * (Real.log (N + 1) - Real.log N) ≤ 2 := by
        calc (N + 1) * (Real.log (N + 1) - Real.log N) ≤ (N + 1) * (1 / N) := by gcongr
          _ = 1 + 1 / N := by field_simp
          _ ≤ 2 := by
            have : 1 / (N : ℝ) ≤ 1 := by rw [div_le_one hN0]; exact hN'
            linarith
      nlinarith
    linarith

/-- `Σ_{s < n ≤ N} log n / (n (n − 1)) ≤ (log s + 2)/s` for `s ≥ 1`. -/
lemma sum_Icc_log_div_mul_pred_le' {s : ℕ} (hs : 1 ≤ s) (N : ℕ) :
    ∑ n ∈ Icc (s + 1) N, Real.log n / (n * (n - 1)) ≤ (Real.log s + 2) / s := by
  rcases le_or_gt s N with hsN | hNs
  · have h := sum_Icc_log_div_mul_pred_le hs N hsN
    have : 0 ≤ (Real.log N + 2) / N := by
      have : (1 : ℝ) ≤ N := by exact_mod_cast hs.trans hsN
      have := Real.log_nonneg this
      positivity
    linarith
  · rw [Icc_eq_empty (by omega), sum_empty]
    have : (1 : ℝ) ≤ s := by exact_mod_cast hs
    have := Real.log_nonneg this
    positivity

/-- The telescoping bound `Σ_{2 ≤ n ≤ N} log n / (n (n − 1)) ≤ 2 − (log N + 2)/N` (`N ≥ 1`). -/
lemma sum_log_div_mul_pred_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Icc 2 N, Real.log n / (n * (n - 1)) ≤ 2 - (Real.log N + 2) / N := by
  simpa using sum_Icc_log_div_mul_pred_le le_rfl N hN

/-- `Σ_{2 ≤ n ≤ N} log n / (n (n − 1)) ≤ 2`. -/
lemma sum_log_div_mul_pred_le_two (N : ℕ) :
    ∑ n ∈ Icc 2 N, Real.log n / (n * (n - 1)) ≤ 2 := by
  rcases N.eq_zero_or_pos with rfl | hN
  · simp
  have h := sum_log_div_mul_pred_le N hN
  have : 0 ≤ (Real.log N + 2) / N := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have := Real.log_nonneg this
    positivity
  linarith

/-- The prime powers `p^k` with `k ≥ 2` contribute at most `2` to `Σ Λ(n)/n`:
`Σ_{n ≤ N, n not prime} Λ(n)/n ≤ 2`. -/
theorem sum_nonprime_vonMangoldt_div_le_two (N : ℕ) :
    ∑ n ∈ Ioc 0 N with ¬ n.Prime, Λ n / n ≤ 2 := by
  have hmain := sum_vonMangoldt_mul_le_sum_primePow (A := (Ioc 0 N).filter (fun n ↦ ¬ n.Prime))
    (P := (Icc 2 N).filter Nat.Prime) (K := Icc 2 N) (fun n ↦ 1 / (n : ℝ))
    (fun n ↦ by positivity) (fun p hp ↦ (mem_filter.mp hp).2)
    (fun k hk ↦ by simp at hk; omega) ?cover
  case cover =>
    intro n hn hpp
    rw [mem_filter, mem_Ioc] at hn
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp hpp
    have hk2 : 2 ≤ k := by
      by_contra h
      have : k = 1 := by omega
      subst this
      exact hn.2 (by simpa using hp)
    have hpk : p ≤ p ^ k := Nat.le_self_pow (by omega) p
    have hkp : k < p ^ k := (Nat.lt_pow_self (by have := hp.two_le; omega)).trans_le le_rfl
    refine ⟨p, mem_filter.mpr ⟨mem_Icc.mpr ⟨hp.two_le, hpk.trans hn.1.2⟩, hp⟩, k,
      mem_Icc.mpr ⟨hk2, hkp.le.trans hn.1.2⟩, rfl⟩
  calc ∑ n ∈ Ioc 0 N with ¬ n.Prime, Λ n / n
        = ∑ n ∈ Ioc 0 N with ¬ n.Prime, Λ n * (1 / (n : ℝ)) := by
          simp_rw [mul_one_div]
    _ ≤ _ := hmain
    _ ≤ ∑ p ∈ Icc 2 N with p.Prime, Real.log p / (p * (p - 1)) := by
        refine sum_le_sum fun p hp ↦ ?_
        have hp2 : 2 ≤ p := (mem_filter.mp hp).2.two_le
        have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp2
        have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
        calc ∑ k ∈ Icc 2 N, Real.log p * (1 / ((p ^ k : ℕ) : ℝ))
            = Real.log p * ∑ k ∈ Ico 2 (N + 1), (1 / (p : ℝ)) ^ k := by
              rw [mul_sum]
              refine sum_congr (by ext; simp only [mem_Icc, mem_Ico]; omega) fun k _ ↦ ?_
              push_cast; rw [one_div_pow]
          _ ≤ Real.log p * ((1 / (p : ℝ)) ^ 2 / (1 - 1 / p)) := by
              gcongr; exact sum_Ico_one_div_pow_le_of_two_le hp2 _ _
          _ = Real.log p / (p * (p - 1)) := by
              have : (p : ℝ) - 1 ≠ 0 := by linarith
              field_simp
    _ ≤ ∑ n ∈ Icc 2 N, Real.log n / (n * (n - 1)) := by
        refine sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun n hn _ ↦ ?_
        have hn' : (2 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
        have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ n)
        apply div_nonneg this
        nlinarith
    _ ≤ 2 := sum_log_div_mul_pred_le_two N

/-- The prime powers `p^k` with `k ≥ 2` and `p^k > Y` contribute at most
`E(Y) = (log s + 2 + 2 log 4)/s`, where `s = ⌊√Y⌋` (about `(log Y / 2 + 4.8)/√Y`):
`Σ_{Y < n ≤ M, n not prime} Λ(n)/n ≤ E(Y)` for `Y ≥ 1`. The primes `p ≤ √Y` contribute at most
`2 θ(√Y)/Y`, the primes `p > √Y` at most `Σ_{n > s} log n/(n(n − 1))`. -/
theorem sum_Ioc_nonprime_vonMangoldt_div_le {Y : ℕ} (hY : 1 ≤ Y) (M : ℕ) :
    ∑ n ∈ Ioc Y M with ¬ n.Prime, Λ n / n ≤
      (Real.log (Nat.sqrt Y) + 2 + 2 * Real.log 4) / Nat.sqrt Y := by
  set s := Nat.sqrt Y with hsdef
  have hs1 : 1 ≤ s := Nat.le_sqrt.mpr (by simpa using hY)
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs1
  have hss : s * s ≤ Y := Nat.sqrt_le Y
  have hY0 : (0 : ℝ) < Y := by exact_mod_cast hY
  set h : ℕ → ℝ := fun n ↦ if Y < n then 1 / (n : ℝ) else 0 with hhdef
  have hh : ∀ n, 0 ≤ h n := fun n ↦ by simp only [hhdef]; split_ifs <;> positivity
  have hmain := sum_vonMangoldt_mul_le_sum_primePow (A := (Ioc Y M).filter (fun n ↦ ¬ n.Prime))
    (P := (Icc 2 M).filter Nat.Prime) (K := Icc 2 M) h hh (fun p hp ↦ (mem_filter.mp hp).2)
    (fun k hk ↦ by simp at hk; omega) ?cover
  case cover =>
    intro n hn hpp
    rw [mem_filter, mem_Ioc] at hn
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp hpp
    have hk2 : 2 ≤ k := by
      by_contra h
      have : k = 1 := by omega
      subst this
      exact hn.2 (by simpa using hp)
    have hpk : p ≤ p ^ k := Nat.le_self_pow (by omega) p
    have hkp : k < p ^ k := Nat.lt_pow_self (by have := hp.two_le; omega)
    refine ⟨p, mem_filter.mpr ⟨mem_Icc.mpr ⟨hp.two_le, hpk.trans hn.1.2⟩, hp⟩, k,
      mem_Icc.mpr ⟨hk2, hkp.le.trans hn.1.2⟩, rfl⟩
  -- the bound for each prime
  have hsmall : ∀ p ∈ (Icc 2 M).filter Nat.Prime,
      ∑ k ∈ Icc 2 M, Real.log p * h (p ^ k) ≤ 2 * Real.log p / Y := by
    intro p hp
    have hp2 : 2 ≤ p := (mem_filter.mp hp).2.two_le
    have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
    set k₀ := Nat.log p Y + 1
    have hk₀ : Y < p ^ k₀ := Nat.lt_pow_succ_log_self (by omega) Y
    have hk₀' : (Y : ℝ) < (p : ℝ) ^ k₀ := by exact_mod_cast hk₀
    calc ∑ k ∈ Icc 2 M, Real.log p * h (p ^ k)
        = Real.log p * ∑ k ∈ (Icc 2 M).filter (fun k ↦ Y < p ^ k), (1 / (p : ℝ)) ^ k := by
          rw [mul_sum, sum_filter]
          refine sum_congr rfl fun k _ ↦ ?_
          simp only [hhdef]
          split_ifs <;> simp
      _ ≤ Real.log p * ∑ k ∈ Ico k₀ (M + 1), (1 / (p : ℝ)) ^ k := by
          refine mul_le_mul_of_nonneg_left
            (sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ ↦ by positivity) hlog
          intro k hk
          simp only [mem_filter, mem_Icc] at hk
          have := Nat.log_lt_of_lt_pow (by omega) hk.2
          simp only [mem_Ico]; omega
      _ ≤ Real.log p * ((1 / (p : ℝ)) ^ k₀ / (1 - 1 / p)) := by
          gcongr; exact sum_Ico_one_div_pow_le_of_two_le hp2 _ _
      _ ≤ Real.log p * (2 / Y) := by
          refine mul_le_mul_of_nonneg_left ?_ hlog
          have h2 : 1 / 2 ≤ 1 - 1 / (p : ℝ) := by
            have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp'
            linarith
          rw [div_le_iff₀ (by linarith), one_div_pow]
          calc 1 / (p : ℝ) ^ k₀ ≤ 1 / Y := one_div_le_one_div_of_le hY0 hk₀'.le
            _ = 2 / Y * (1 / 2) := by ring
            _ ≤ 2 / Y * (1 - 1 / p) := by gcongr
      _ = 2 * Real.log p / Y := by ring
  have hlarge : ∀ p ∈ (Icc 2 M).filter Nat.Prime,
      ∑ k ∈ Icc 2 M, Real.log p * h (p ^ k) ≤ Real.log p / (p * (p - 1)) := by
    intro p hp
    have hp2 : 2 ≤ p := (mem_filter.mp hp).2.two_le
    have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
    calc ∑ k ∈ Icc 2 M, Real.log p * h (p ^ k)
        ≤ ∑ k ∈ Icc 2 M, Real.log p * (1 / ((p ^ k : ℕ) : ℝ)) := by
          refine sum_le_sum fun k _ ↦ ?_
          gcongr
          simp only [hhdef]
          split_ifs
          · exact le_rfl
          · positivity
      _ = Real.log p * ∑ k ∈ Ico 2 (M + 1), (1 / (p : ℝ)) ^ k := by
          rw [mul_sum]
          refine sum_congr (by ext; simp only [mem_Icc, mem_Ico]; omega) fun k _ ↦ ?_
          push_cast; rw [one_div_pow]
      _ ≤ Real.log p * ((1 / (p : ℝ)) ^ 2 / (1 - 1 / p)) := by
          gcongr; exact sum_Ico_one_div_pow_le_of_two_le hp2 _ _
      _ = Real.log p / (p * (p - 1)) := by
          have : (p : ℝ) - 1 ≠ 0 := by linarith
          field_simp
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  calc ∑ n ∈ Ioc Y M with ¬ n.Prime, Λ n / n
        = ∑ n ∈ Ioc Y M with ¬ n.Prime, Λ n * h n := by
          refine sum_congr rfl fun n hn ↦ ?_
          simp only [mem_filter, mem_Ioc] at hn
          simp only [hhdef, hn.1.1, ↓reduceIte, mul_one_div]
    _ ≤ _ := hmain
    _ = (∑ p ∈ (Icc 2 M).filter Nat.Prime with p ≤ s, ∑ k ∈ Icc 2 M, Real.log p * h (p ^ k)) +
        ∑ p ∈ (Icc 2 M).filter Nat.Prime with ¬ p ≤ s, ∑ k ∈ Icc 2 M, Real.log p * h (p ^ k) :=
          (sum_filter_add_sum_filter_not _ _ _).symm
    _ ≤ (∑ p ∈ (Icc 2 M).filter Nat.Prime with p ≤ s, 2 * Real.log p / Y) +
        ∑ p ∈ (Icc 2 M).filter Nat.Prime with ¬ p ≤ s, Real.log p / (p * (p - 1)) := by
          gcongr with p hp p hp
          · exact hsmall p (mem_filter.mp hp).1
          · exact hlarge p (mem_filter.mp hp).1
    _ ≤ 2 / Y * (Real.log 4 * s) + (Real.log s + 2) / s := by
          gcongr
          · rw [← sum_div, ← mul_sum, div_mul_eq_mul_div]
            gcongr
            calc ∑ p ∈ (Icc 2 M).filter Nat.Prime with p ≤ s, Real.log p
                ≤ ∑ p ∈ Ioc 0 s with p.Prime, Real.log p := by
                  refine sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ ↦
                    Real.log_natCast_nonneg p
                  intro p hp
                  simp only [mem_filter, mem_Icc, mem_Ioc] at hp ⊢
                  exact ⟨⟨by omega, hp.2⟩, hp.1.2⟩
              _ = Chebyshev.theta s := by rw [Chebyshev.theta, Nat.floor_natCast]
              _ ≤ Real.log 4 * s := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg _)
          · calc ∑ p ∈ (Icc 2 M).filter Nat.Prime with ¬ p ≤ s, Real.log p / (p * (p - 1))
                ≤ ∑ n ∈ Icc (s + 1) M, Real.log n / (n * (n - 1)) := by
                  refine sum_le_sum_of_subset_of_nonneg ?_ fun n hn _ ↦ ?_
                  · intro p hp
                    simp only [mem_filter, mem_Icc] at hp ⊢
                    omega
                  · have hn' : (2 : ℝ) ≤ n := by
                      have := (mem_Icc.mp hn).1
                      exact_mod_cast (by omega : 2 ≤ n)
                    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ n)
                    apply div_nonneg this
                    nlinarith
              _ ≤ (Real.log s + 2) / s := sum_Icc_log_div_mul_pred_le' hs1 M
    _ ≤ (Real.log s + 2 + 2 * Real.log 4) / s := by
          have hss' : (s : ℝ) * s ≤ Y := by exact_mod_cast hss
          have hs0 : (0 : ℝ) < s := by linarith
          have : 2 / Y * (Real.log 4 * s) ≤ 2 * Real.log 4 / s := by
            rw [div_mul_eq_mul_div, div_le_div_iff₀ hY0 hs0]
            nlinarith
          rw [add_div _ (2 * Real.log 4)]
          linarith

/-- The integers not coprime to `q` contribute at most `log q` to `Σ Λ(n)/n`. -/
theorem sum_nonunit_vonMangoldt_div_le_log {q : ℕ} (hq : q ≠ 0) (N : ℕ) :
    ∑ n ∈ Ioc 0 N with ¬ n.Coprime q, Λ n / n ≤ Real.log q := by
  have hmain := sum_vonMangoldt_mul_le_sum_primePow
    (A := (Ioc 0 N).filter (fun n ↦ ¬ n.Coprime q))
    (P := q.primeFactors) (K := Icc 1 N) (fun n ↦ 1 / (n : ℝ))
    (fun n ↦ by positivity) (fun p hp ↦ Nat.prime_of_mem_primeFactors hp)
    (fun k hk ↦ by simp at hk; omega) ?cover
  case cover =>
    intro n hn hpp
    rw [mem_filter, mem_Ioc] at hn
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp hpp
    have hpq : p ∣ q := by
      by_contra h
      exact hn.2 (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr h))
    have hkp : k < p ^ k := Nat.lt_pow_self (by have := hp.two_le; omega)
    exact ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpq, hq⟩, k,
      mem_Icc.mpr ⟨hk, hkp.le.trans hn.1.2⟩, rfl⟩
  calc ∑ n ∈ Ioc 0 N with ¬ n.Coprime q, Λ n / n
        = ∑ n ∈ Ioc 0 N with ¬ n.Coprime q, Λ n * (1 / (n : ℝ)) := by
          simp_rw [mul_one_div]
    _ ≤ _ := hmain
    _ ≤ ∑ p ∈ q.primeFactors, Real.log p := by
        refine sum_le_sum fun p hp ↦ ?_
        have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
        have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp2
        have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
        calc ∑ k ∈ Icc 1 N, Real.log p * (1 / ((p ^ k : ℕ) : ℝ))
            = Real.log p * ∑ k ∈ Ico 1 (N + 1), (1 / (p : ℝ)) ^ k := by
              rw [mul_sum]
              refine sum_congr (by ext; simp only [mem_Icc, mem_Ico]; omega) fun k _ ↦ ?_
              push_cast; rw [one_div_pow]
          _ ≤ Real.log p * ((1 / (p : ℝ)) ^ 1 / (1 - 1 / p)) := by
              gcongr; exact sum_Ico_one_div_pow_le_of_two_le hp2 _ _
          _ ≤ Real.log p * 1 := by
              gcongr
              rw [pow_one, div_le_one (by rw [sub_pos, div_lt_one (by linarith)]; linarith)]
              rw [le_sub_iff_add_le]
              have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp'
              linarith
          _ = Real.log p := mul_one _
    _ = Real.log (∏ p ∈ q.primeFactors, (p : ℝ)) := by
        rw [Real.log_prod]
        intro p hp
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    _ ≤ Real.log q := by
        apply Real.log_le_log
        · exact prod_pos fun p hp ↦ by
            exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
        · rw [← Nat.cast_prod]
          exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hq) (Nat.prod_primeFactors_dvd q)

end ZInQ.Progressions
