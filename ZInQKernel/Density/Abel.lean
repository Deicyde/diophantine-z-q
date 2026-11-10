import Mathlib
import ZInQKernel.Hypotheses.GreenTao

/-!
# Dirichlet density implies positive relative upper density (pd-paper §5, Lemma 5.2, Prop. 5.3)

For a set `S ⊆ ℕ` put `θ_S(N) = Σ_{n ≤ N, n ∈ S} log n` (`thetaS`) and, for `x > 1`,
`Φ_S(x) = Σ_{n ∈ S} (log n) / n^x` (`PhiS`).

* `abel_partial_sum_le`, `abel_bound` (Lemma 5.2(1)): if `θ_S(N) ≤ κ N + B` for every `N`, then
  for `x ∈ (1, 2]` the series `Φ_S(x)` converges and `Φ_S(x) ≤ κ x / (x − 1) + B`.
* `primesRelUpperDensityPos_of_dirichlet` (Proposition 5.3): a set of primes of positive lower
  Dirichlet density in the von Mangoldt normalisation (`η/(x − 1) − K ≤ Φ_S(x)` on `(1, 2]`) has
  positive relative upper density in the primes (`ZInQ.PrimesRelUpperDensityPos`).

The proof is discrete Abel summation (by induction), an elementary bound
`Σ_{n ≤ M} n^{−x} ≤ x/(x − 1)` (from Bernoulli's inequality) and Chebyshev's bound
`Chebyshev.eventually_primeCounting_le`.
-/

namespace ZInQ.Density

open Finset Filter

/-- `θ_S(N) = Σ_{n ≤ N, n ∈ S} log n`. -/
noncomputable def thetaS (S : Set ℕ) (N : ℕ) : ℝ :=
  ∑ n ∈ range (N + 1), S.indicator (fun n : ℕ => Real.log n) n

/-- The terms `1_S(n) log n / n^x` of `Φ_S(x)`. -/
noncomputable def phiTerm (S : Set ℕ) (x : ℝ) (n : ℕ) : ℝ :=
  S.indicator (fun n : ℕ => Real.log n) n / (n : ℝ) ^ x

/-- `Φ_S(x) = Σ_{n ∈ S} log n / n^x`. -/
noncomputable def PhiS (S : Set ℕ) (x : ℝ) : ℝ :=
  ∑' n : ℕ, phiTerm S x n

theorem indicator_log_nonneg (S : Set ℕ) (n : ℕ) :
    0 ≤ S.indicator (fun n : ℕ => Real.log n) n :=
  Set.indicator_nonneg (fun n _ => Real.log_natCast_nonneg n) n

theorem phiTerm_nonneg (S : Set ℕ) (x : ℝ) (n : ℕ) : 0 ≤ phiTerm S x n :=
  div_nonneg (indicator_log_nonneg S n) (Real.rpow_nonneg (Nat.cast_nonneg n) x)

theorem thetaS_nonneg (S : Set ℕ) (N : ℕ) : 0 ≤ thetaS S N :=
  sum_nonneg fun n _ => indicator_log_nonneg S n

theorem thetaS_mono (S : Set ℕ) {M N : ℕ} (h : M ≤ N) : thetaS S M ≤ thetaS S N :=
  sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (by omega))
    fun n _ _ => indicator_log_nonneg S n

theorem thetaS_mono_set {S T : Set ℕ} (h : S ⊆ T) (N : ℕ) : thetaS S N ≤ thetaS T N :=
  sum_le_sum fun n _ => Set.indicator_le_indicator_of_subset h
    (fun n => Real.log_natCast_nonneg n) n

/-- Discrete Abel summation: `Σ_{n ≤ M} b_n u_n = Σ_{m < M} B_m (u_m − u_{m+1}) + B_M u_M`, where
`B_m = Σ_{n ≤ m} b_n`. -/
theorem abel_summation (b u : ℕ → ℝ) (M : ℕ) :
    ∑ n ∈ range (M + 1), b n * u n =
      ∑ m ∈ range M, (∑ n ∈ range (m + 1), b n) * (u m - u (m + 1)) +
        (∑ n ∈ range (M + 1), b n) * u M := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [sum_range_succ, ih, sum_range_succ (fun m => (∑ n ∈ range (m + 1), b n) *
      (u m - u (m + 1))), sum_range_succ (fun n => b n) (M + 1)]
    ring

/-- Bernoulli step: `p (t + 1)^{−(p+1)} ≤ t^{−p} − (t + 1)^{−p}` for `t ≥ 1`, `0 < p ≤ 1`. -/
theorem rpow_neg_step {t p : ℝ} (ht : 1 ≤ t) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    p * (1 / (t + 1) ^ (p + 1)) ≤ 1 / t ^ p - 1 / (t + 1) ^ p := by
  have ht0 : 0 < t := by linarith
  have ht1 : 0 < t + 1 := by linarith
  have hs : (-1 : ℝ) ≤ -1 / (t + 1) := by
    rw [le_div_iff₀ ht1]; linarith
  have hb := rpow_one_add_le_one_add_mul_self hs hp0.le hp1
  have h1 : (1 : ℝ) + -1 / (t + 1) = t / (t + 1) := by field_simp; ring
  rw [h1, Real.div_rpow ht0.le ht1.le] at hb
  set u := t ^ p with hu
  set v := (t + 1) ^ p with hv
  have hu0 : 0 < u := Real.rpow_pos_of_pos ht0 p
  have hv0 : 0 < v := Real.rpow_pos_of_pos ht1 p
  have huv : u ≤ v := Real.rpow_le_rpow ht0.le (by linarith) hp0.le
  rw [Real.rpow_add_one ht1.ne' p, ← hv]
  -- hb : u / v ≤ 1 + p * (-1 / (t + 1))
  rw [div_le_iff₀ hv0] at hb
  have key : p * v / (t + 1) ≤ v - u := by
    have : p * v / (t + 1) = - (v * (p * (-1 / (t + 1)))) := by field_simp
    rw [this]; nlinarith
  have key2 : p * u / (t + 1) ≤ v - u := by
    refine le_trans ?_ key
    apply div_le_div_of_nonneg_right _ ht1.le
    exact mul_le_mul_of_nonneg_left huv hp0.le
  rw [div_sub_div _ _ hu0.ne' hv0.ne', le_div_iff₀ (mul_pos hu0 hv0)]
  have : p * (1 / (v * (t + 1))) * (u * v) = p * u / (t + 1) := by
    field_simp
  rw [this]; linarith

/-- `Σ_{n < M} (n + 1)^{−x} ≤ x/(x − 1)` for `x ∈ (1, 2]`. -/
theorem sum_one_div_rpow_le {x : ℝ} (hx1 : 1 < x) (hx2 : x ≤ 2) (M : ℕ) :
    ∑ n ∈ range M, 1 / ((n : ℝ) + 1) ^ x ≤ x / (x - 1) := by
  have hp0 : 0 < x - 1 := by linarith
  have hstep : ∀ n : ℕ, 1 / ((n : ℝ) + 1 + 1) ^ x ≤
      (1 / (x - 1)) * (1 / ((n : ℝ) + 1) ^ (x - 1) - 1 / ((n : ℝ) + 1 + 1) ^ (x - 1)) := by
    intro n
    have h := rpow_neg_step (t := (n : ℝ) + 1) (p := x - 1) (by simp) hp0 (by linarith)
    rw [sub_add_cancel] at h
    have e : ∀ D : ℝ, 1 / (x - 1) * D = D / (x - 1) := fun D => by ring
    rw [e, le_div_iff₀ hp0]
    linarith
  have htel : ∀ K : ℕ, ∑ n ∈ range K, (1 / ((n : ℝ) + 1) ^ (x - 1) -
      1 / ((n : ℝ) + 1 + 1) ^ (x - 1)) = 1 - 1 / ((K : ℝ) + 1) ^ (x - 1) := by
    intro K
    induction K with
    | zero => simp
    | succ K ih => rw [sum_range_succ, ih]; push_cast; ring
  cases M with
  | zero => simp; exact div_nonneg (by linarith) hp0.le
  | succ K =>
    rw [sum_range_succ']
    simp only [Nat.cast_zero, zero_add, Real.one_rpow, div_one, Nat.cast_add, Nat.cast_one]
    have h1 : ∑ n ∈ range K, 1 / ((n : ℝ) + 1 + 1) ^ x ≤ 1 / (x - 1) := by
      calc ∑ n ∈ range K, 1 / ((n : ℝ) + 1 + 1) ^ x
          ≤ ∑ n ∈ range K, (1 / (x - 1)) *
              (1 / ((n : ℝ) + 1) ^ (x - 1) - 1 / ((n : ℝ) + 1 + 1) ^ (x - 1)) :=
            sum_le_sum fun n _ => hstep n
        _ = (1 / (x - 1)) * (1 - 1 / ((K : ℝ) + 1) ^ (x - 1)) := by rw [← mul_sum, htel]
        _ ≤ 1 / (x - 1) := by
            have : 0 ≤ 1 / ((K : ℝ) + 1) ^ (x - 1) := by positivity
            have : 0 ≤ 1 / (x - 1) := by positivity
            nlinarith
    have h2 : x / (x - 1) = 1 / (x - 1) + 1 := by field_simp; ring
    rw [h2]; linarith

/-- **Abel summation bound.** Let `a 0 = 0` and `Σ_{n ≤ N} a_n ≤ κ N + B` for all
`N`. Then every partial sum of `Σ a_n / n^x` is at most `κ x/(x − 1) + B`, for `x ∈ (1, 2]`. -/
theorem abel_partial_sum_le (a : ℕ → ℝ) (ha0 : a 0 = 0) {κ B : ℝ}
    (hκ : 0 ≤ κ) (hA : ∀ N : ℕ, ∑ n ∈ range (N + 1), a n ≤ κ * N + B) {x : ℝ} (hx1 : 1 < x)
    (hx2 : x ≤ 2) (M : ℕ) : ∑ n ∈ range M, a n / (n : ℝ) ^ x ≤ κ * (x / (x - 1)) + B := by
  -- reduce to `b n = a (n + 1)`, `u n = 1 / (n + 1)^x`
  set u : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) ^ x with hu
  set b : ℕ → ℝ := fun n => a (n + 1) with hb
  have hu0 : ∀ n, 0 ≤ u n := fun n => by simp only [hu]; positivity
  have hd : ∀ n, 0 ≤ u n - u (n + 1) := by
    intro n
    simp only [hu, sub_nonneg]
    push_cast
    apply one_div_le_one_div_of_le (by positivity)
    exact Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
  have hBsum : ∀ m, ∑ n ∈ range (m + 1), b n ≤ κ * ((m : ℝ) + 1) + B := by
    intro m
    have := hA (m + 1)
    rw [sum_range_succ', ha0, add_zero] at this
    push_cast at this
    exact this
  -- comparison sequence `b' n = κ + B [n = 0]`, with partial sums `κ (m + 1) + B`
  set b' : ℕ → ℝ := fun n => κ + if n = 0 then B else 0 with hb'
  have hB'sum : ∀ m, ∑ n ∈ range (m + 1), b' n = κ * ((m : ℝ) + 1) + B := by
    intro m
    induction m with
    | zero => simp [hb']
    | succ m ih => rw [sum_range_succ, ih]; simp [hb']; ring
  have hmain : ∀ K : ℕ, ∑ n ∈ range (K + 1), b n * u n ≤ κ * (x / (x - 1)) + B := by
    intro K
    rw [abel_summation]
    calc ∑ m ∈ range K, (∑ n ∈ range (m + 1), b n) * (u m - u (m + 1)) +
          (∑ n ∈ range (K + 1), b n) * u K
        ≤ ∑ m ∈ range K, (∑ n ∈ range (m + 1), b' n) * (u m - u (m + 1)) +
          (∑ n ∈ range (K + 1), b' n) * u K := by
          refine add_le_add (sum_le_sum fun m _ => mul_le_mul_of_nonneg_right ?_ (hd m))
            (mul_le_mul_of_nonneg_right ?_ (hu0 K))
          · rw [hB'sum]; exact hBsum m
          · rw [hB'sum]; exact hBsum K
      _ = ∑ n ∈ range (K + 1), b' n * u n := (abel_summation b' u K).symm
      _ = κ * ∑ n ∈ range (K + 1), u n + B := by
          rw [sum_range_succ']
          simp only [hb', hu, Nat.cast_zero, zero_add, Real.one_rpow, ite_true]
          simp only [Nat.add_one_ne_zero, ite_false, add_zero]
          rw [← mul_sum, sum_range_succ' (fun n => 1 / ((n : ℝ) + 1) ^ x)]
          simp
          ring
      _ ≤ κ * (x / (x - 1)) + B := by
          gcongr
          exact sum_one_div_rpow_le hx1 hx2 (K + 1)
  -- conclude
  have hpos : 0 ≤ κ * (x / (x - 1)) + B := by
    have h0 := hA 0
    simp [ha0] at h0
    have : 0 ≤ x / (x - 1) := div_nonneg (by linarith) (by linarith)
    have := mul_nonneg hκ this
    linarith
  cases M with
  | zero => simpa using hpos
  | succ K =>
    rw [sum_range_succ', ha0, zero_div, add_zero]
    cases K with
    | zero => simpa using hpos
    | succ K =>
      convert hmain K using 2 with n hn
      simp only [hb, hu]
      push_cast
      rw [div_eq_mul_one_div]

/-- **Lemma 5.2(1).** If `θ_S(N) ≤ κ N + B` for all `N`, then for `x ∈ (1, 2]` the series
`Φ_S(x)` converges and `Φ_S(x) ≤ κ x/(x − 1) + B`. -/
theorem abel_bound {S : Set ℕ} {κ B : ℝ} (hκ : 0 ≤ κ) (hθ : ∀ N : ℕ, thetaS S N ≤ κ * N + B)
    {x : ℝ} (hx1 : 1 < x) (hx2 : x ≤ 2) :
    Summable (phiTerm S x) ∧ PhiS S x ≤ κ * (x / (x - 1)) + B := by
  have h := abel_partial_sum_le (fun n => S.indicator (fun n : ℕ => Real.log n) n) (by simp) hκ hθ hx1 hx2
  exact ⟨summable_of_sum_range_le (phiTerm_nonneg S x) h,
    Real.tsum_le_of_sum_range_le (phiTerm_nonneg S x) h⟩

/-- Chebyshev's bound: `θ_S(N) ≤ log 4 · N` for a set of primes `S`. -/
theorem thetaS_le_log4 {S : Set ℕ} (hS : S ⊆ {p | p.Prime}) (N : ℕ) :
    thetaS S N ≤ Real.log 4 * N + 0 := by
  rw [add_zero]
  have h1 : thetaS S N ≤ thetaS {p | p.Prime} N := thetaS_mono_set hS N
  have h2 : thetaS {p | p.Prime} N = Chebyshev.theta N := by
    rw [Chebyshev.theta_eq_sum_primesLE_log, Nat.primesLE_eq_filter_range, sum_filter]
    unfold thetaS
    refine sum_congr rfl fun n _ => ?_
    by_cases h : n.Prime
    · simp [h]
    · simp [h]
  rw [h2] at h1
  exact h1.trans (Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg N))

/-- `θ_S(N) ≤ log N · #(S ∩ [0, N])`. -/
theorem thetaS_le_log_mul_card (S : Set ℕ) (N : ℕ) [DecidablePred (· ∈ S)] :
    thetaS S N ≤ Real.log N * (((range (N + 1)).filter (· ∈ S)).card : ℝ) := by
  unfold thetaS
  rw [← sum_filter_add_sum_filter_not (range (N + 1)) (· ∈ S)]
  have h2 : ∑ n ∈ (range (N + 1)).filter (fun n => ¬ n ∈ S),
      S.indicator (fun n : ℕ => Real.log n) n = 0 :=
    sum_eq_zero fun n hn => Set.indicator_of_notMem (mem_filter.1 hn).2 _
  rw [h2, add_zero, mul_comm, ← nsmul_eq_mul]
  refine sum_le_card_nsmul _ _ _ fun n hn => ?_
  obtain ⟨hn1, hn2⟩ := mem_filter.1 hn
  rw [Set.indicator_of_mem hn2]
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp [Real.log_natCast_nonneg]
  · exact Real.log_le_log (by exact_mod_cast h)
      (by exact_mod_cast Nat.lt_succ_iff.1 (mem_range.1 hn1))

/-- An eventual bound `θ_S(N) ≤ κ N` gives a bound `θ_S(N) ≤ κ N + B` for all `N`. -/
theorem thetaS_le_of_eventually {S : Set ℕ} {κ : ℝ} (hκ : 0 ≤ κ)
    (h : ∀ᶠ N : ℕ in atTop, thetaS S N ≤ κ * N) : ∃ B : ℝ, ∀ N : ℕ, thetaS S N ≤ κ * N + B := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 h
  refine ⟨thetaS S N₀, fun N => ?_⟩
  rcases le_or_gt N₀ N with hN | hN
  · have := hN₀ N hN
    have := thetaS_nonneg S N₀
    linarith
  · have := thetaS_mono S hN.le
    have : 0 ≤ κ * N := mul_nonneg hκ (Nat.cast_nonneg N)
    linarith

/-- `Φ_S(x)` converges for a set of primes `S` and `x ∈ (1, 2]`. -/
theorem summable_phiTerm {S : Set ℕ} (hS : S ⊆ {p | p.Prime}) {x : ℝ} (hx1 : 1 < x)
    (hx2 : x ≤ 2) : Summable (phiTerm S x) :=
  (abel_bound (Real.log_nonneg (by norm_num)) (thetaS_le_log4 hS) hx1 hx2).1

open Classical in
/-- **Proposition 5.3.** A set `S` (in the application, a set of primes) with positive lower Dirichlet density in the von
Mangoldt normalisation, `η/(x − 1) − K ≤ Φ_S(x)` for `x ∈ (1, 2]` with `η > 0`, has positive
relative upper density in the primes. -/
theorem primesRelUpperDensityPos_of_dirichlet {S : Set ℕ} {η K : ℝ}
    (hη : 0 < η) (h : ∀ x ∈ Set.Ioc (1 : ℝ) 2, η / (x - 1) - K ≤ PhiS S x) :
    PrimesRelUpperDensityPos S := by
  by_contra hneg
  unfold PrimesRelUpperDensityPos at hneg
  push Not at hneg
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  set c : ℝ := η / (4 * (Real.log 4 + 1)) with hc
  have hc0 : 0 < c := by positivity
  have hev1 := hneg c hc0
  have hcheb : ∀ᶠ N : ℕ in atTop,
      (Nat.primeCounting N : ℝ) ≤ (Real.log 4 + 1) * N / Real.log N := by
    have h1 := Chebyshev.eventually_primeCounting_le (ε := 1) one_pos
    have h2 := tendsto_natCast_atTop_atTop.eventually h1
    filter_upwards [h2] with N hN
    simpa using hN
  have hθ : ∀ᶠ N : ℕ in atTop, thetaS S N ≤ (η / 4) * N := by
    filter_upwards [hev1, hcheb, eventually_ge_atTop 2] with N h1 h2 h3
    have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast h3)
    calc thetaS S N ≤ Real.log N * (((range (N + 1)).filter (· ∈ S)).card : ℝ) :=
          thetaS_le_log_mul_card S N
      _ ≤ Real.log N * (c * Nat.primeCounting N) := by gcongr
      _ ≤ Real.log N * (c * ((Real.log 4 + 1) * N / Real.log N)) := by gcongr
      _ = (η / 4) * N := by rw [hc]; field_simp
  obtain ⟨B, hB⟩ := thetaS_le_of_eventually (by positivity) hθ
  have hB0 : 0 ≤ B := by
    have h1 := hB 0
    have h2 := thetaS_nonneg S 0
    simp only [Nat.cast_zero, mul_zero, zero_add] at h1
    linarith
  set t : ℝ := min 1 (η / (4 * (|K| + B + 1))) with ht
  have hKB : 0 < |K| + B + 1 := by positivity
  have ht0 : 0 < t := lt_min one_pos (by positivity)
  have ht1 : t ≤ 1 := min_le_left _ _
  have ht2 : t * (|K| + B + 1) ≤ η / 4 := by
    have := min_le_right 1 (η / (4 * (|K| + B + 1)))
    calc t * (|K| + B + 1) ≤ η / (4 * (|K| + B + 1)) * (|K| + B + 1) := by gcongr
      _ = η / 4 := by field_simp
  have hx : (1 + t) ∈ Set.Ioc (1 : ℝ) 2 := ⟨by linarith, by linarith⟩
  have hlow := h _ hx
  have hup := (abel_bound (by positivity) hB (x := 1 + t) (by linarith) (by linarith)).2
  simp only [add_sub_cancel_left] at hlow hup
  have hcomb := mul_le_mul_of_nonneg_left (hlow.trans hup) ht0.le
  have e1 : t * (η / t - K) = η - K * t := by field_simp
  have e2 : t * (η / 4 * ((1 + t) / t) + B) = η / 4 * (1 + t) + B * t := by field_simp
  rw [e1, e2] at hcomb
  have hK : K * t ≤ |K| * t := mul_le_mul_of_nonneg_right (le_abs_self K) ht0.le
  have hη4 : η / 4 * t ≤ η / 4 := by nlinarith
  nlinarith

end ZInQ.Density
