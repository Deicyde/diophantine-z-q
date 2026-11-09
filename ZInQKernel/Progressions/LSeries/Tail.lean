import ZInQKernel.Progressions.LSeries.CharSum

/-!
# Tails of Dirichlet series of a nontrivial character

Plan step 1 (second half), `docs/effective-dirichlet-plan.md`. For `χ ≠ 1` mod `q`:

* finite tails, every real `σ ≥ 0` (resp. `σ ≥ 1` for the logarithmic sum):
  `‖∑_{N < n ≤ K} χ(n) n^(-σ)‖ ≤ q (N+1)^(-σ)` and, for `N ≥ 2`,
  `‖∑_{N < n ≤ K} χ(n) log n · n^(-σ)‖ ≤ q log(N+1) (N+1)^(-σ)`;
* infinite tails for `σ > 1`, as the difference between the (absolutely convergent) L-series
  and a partial sum;
* the plan's forms `2q/N` and `2q log N / N` for `N ≥ 3`.
-/

open Finset Complex

namespace ZInQ.Progressions

variable {q : ℕ} [NeZero q]

/-- If `a 0 = 0` and `a` has sum `S`, a uniform bound on the finite sums `∑_{N < n ≤ K} a n`
bounds the tail `S - ∑_{0 < n ≤ N} a n`. -/
theorem norm_hasSum_sub_sum_Ioc_le_of_forall {a : ℕ → ℂ} {S : ℂ} (h : HasSum a S) (ha : a 0 = 0) (N : ℕ)
    {C : ℝ} (hC : ∀ K, ‖∑ n ∈ Ioc N K, a n‖ ≤ C) : ‖S - ∑ n ∈ Ioc 0 N, a n‖ ≤ C := by
  have e : ∀ K, ∑ n ∈ Ioc 0 K, a n = ∑ n ∈ range (K + 1), a n := by
    intro K
    induction K with
    | zero => simp [ha]
    | succ K ih => rw [Finset.sum_Ioc_succ_top (by omega), ih, Finset.sum_range_succ _ (K + 1)]
  have ht : Filter.Tendsto (fun K ↦ ∑ n ∈ Ioc 0 K, a n) Filter.atTop (nhds S) := by
    simp_rw [e]
    exact (Filter.tendsto_add_atTop_iff_nat 1).mpr h.tendsto_sum_nat
  refine le_of_tendsto ((ht.sub_const _).norm) ?_
  filter_upwards [Filter.eventually_ge_atTop N] with K hK
  rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le N) hK, add_sub_cancel_left]
  exact hC K

omit [NeZero q] in
/-- `χ(n)/n^σ` as `χ(n)` times a real weight. -/
theorem char_div_cpow_eq (χ : DirichletCharacter ℂ q) (σ : ℝ) (n : ℕ) :
    χ n / (n : ℂ) ^ (σ : ℂ) = χ n * (((n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_neg, Complex.cpow_neg,
    div_eq_mul_inv, Complex.ofReal_natCast]

omit [NeZero q] in
/-- `χ(n) log n / n^σ` as `χ(n)` times a real weight. -/
theorem char_log_div_cpow_eq (χ : DirichletCharacter ℂ q) (σ : ℝ) (n : ℕ) :
    χ n * (Real.log n : ℂ) / (n : ℂ) ^ (σ : ℂ) =
      χ n * ((Real.log n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  rw [Complex.ofReal_mul, Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_neg,
    Complex.cpow_neg, Complex.ofReal_natCast]
  ring

/-- `log x / x^σ` is nonincreasing on naturals `n ≥ 3` when `σ ≥ 1`. -/
theorem log_mul_rpow_neg_succ_le {σ : ℝ} (hσ : 1 ≤ σ) {n : ℕ} (hn : 3 ≤ n) :
    Real.log ((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) ^ (-σ) ≤
      Real.log (n : ℝ) * (n : ℝ) ^ (-σ) := by
  have split : ∀ x : ℝ, 0 < x → Real.log x * x ^ (-σ) = Real.log x / x * x ^ (1 - σ) := by
    intro x hx
    rw [show -σ = (1 - σ) - 1 by ring, Real.rpow_sub_one hx.ne']
    ring
  have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  rw [split _ hn0, split _ hn1]
  have he : Real.exp 1 ≤ (n : ℝ) := (Real.exp_one_lt_d9.le.trans (by norm_num)).trans h3
  have hle : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
  have h1 : Real.log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) ≤ Real.log n / n :=
    Real.log_div_self_antitoneOn (Set.mem_Ici.mpr he) (Set.mem_Ici.mpr (he.trans hle)) hle
  have h2 : ((n + 1 : ℕ) : ℝ) ^ (1 - σ) ≤ (n : ℝ) ^ (1 - σ) :=
    Real.rpow_le_rpow_of_nonpos hn0 hle (by linarith)
  have hlog : 0 ≤ Real.log n / n :=
    div_nonneg (Real.log_nonneg (by linarith)) hn0.le
  have hlog' : 0 ≤ Real.log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) :=
    div_nonneg (Real.log_nonneg (by push_cast; linarith)) hn1.le
  exact mul_le_mul h1 h2 (by positivity) hlog

/-- Finite tails: `‖∑_{N < n ≤ K} χ(n)/n^σ‖ ≤ q (N+1)^(-σ)` for `σ ≥ 0`. -/
theorem norm_sum_Ioc_char_div_cpow_le {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {σ : ℝ}
    (hσ : 0 ≤ σ) (N K : ℕ) :
    ‖∑ n ∈ Ioc N K, χ n / (n : ℂ) ^ (σ : ℂ)‖ ≤ q * ((N + 1 : ℕ) : ℝ) ^ (-σ) := by
  simp_rw [char_div_cpow_eq χ σ]
  refine norm_sum_mul_antitone_le (fun n ↦ χ n) (fun n ↦ (n : ℝ) ^ (-σ))
    (norm_sum_Ioc_char_le hχ N) (fun n _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _) ?_ K
  intro n hn
  exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast (by omega : 0 < n))
    (by push_cast; linarith) (by linarith)

/-- Finite logarithmic tails: for `σ ≥ 1` and `N ≥ 2`,
`‖∑_{N < n ≤ K} χ(n) log n/n^σ‖ ≤ q log(N+1) (N+1)^(-σ)`. -/
theorem norm_sum_Ioc_char_log_div_cpow_le {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {σ : ℝ}
    (hσ : 1 ≤ σ) {N : ℕ} (hN : 2 ≤ N) (K : ℕ) :
    ‖∑ n ∈ Ioc N K, χ n * (Real.log n : ℂ) / (n : ℂ) ^ (σ : ℂ)‖ ≤
      q * (Real.log ((N + 1 : ℕ) : ℝ) * ((N + 1 : ℕ) : ℝ) ^ (-σ)) := by
  simp_rw [char_log_div_cpow_eq χ σ]
  refine norm_sum_mul_antitone_le (fun n ↦ χ n) (fun n ↦ Real.log n * (n : ℝ) ^ (-σ))
    (norm_sum_Ioc_char_le hχ N) ?_ ?_ K
  · intro n _
    exact mul_nonneg (Real.log_natCast_nonneg n) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · intro n hn
    exact log_mul_rpow_neg_succ_le hσ (by omega)

/-- `(N+1)^(-σ) ≤ 1/(N+1)` for `σ ≥ 1`. -/
theorem natSucc_rpow_neg_le_inv {σ : ℝ} (hσ : 1 ≤ σ) (N : ℕ) :
    ((N + 1 : ℕ) : ℝ) ^ (-σ) ≤ ((N + 1 : ℕ) : ℝ)⁻¹ := by
  rw [← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ N + 1))
    (by linarith)

/-- The plan's form of the finite tail: `‖∑_{N < n ≤ K} χ(n)/n^σ‖ ≤ 2q/N` for `σ ≥ 1`, `N ≥ 1`. -/
theorem norm_sum_Ioc_char_div_cpow_le_two_mul {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {σ : ℝ}
    (hσ : 1 ≤ σ) {N : ℕ} (hN : 1 ≤ N) (K : ℕ) :
    ‖∑ n ∈ Ioc N K, χ n / (n : ℂ) ^ (σ : ℂ)‖ ≤ 2 * q / N := by
  refine (norm_sum_Ioc_char_div_cpow_le hχ (by linarith) N K).trans ?_
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  calc (q : ℝ) * ((N + 1 : ℕ) : ℝ) ^ (-σ) ≤ q * ((N + 1 : ℕ) : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_left (natSucc_rpow_neg_le_inv hσ N) hq
    _ ≤ 2 * q / N := by
        rw [div_eq_mul_inv, mul_comm 2 (q : ℝ), mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ hq
        rw [Nat.cast_add, Nat.cast_one]
        rw [inv_le_iff_one_le_mul₀ (by positivity)]
        field_simp
        linarith

/-- `log(N+1)/(N+1) ≤ log N / N` for `N ≥ 3`. -/
theorem log_natSucc_div_le_log_div {N : ℕ} (hN : 3 ≤ N) :
    Real.log ((N + 1 : ℕ) : ℝ) / ((N + 1 : ℕ) : ℝ) ≤ Real.log N / N := by
  have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have he : Real.exp 1 ≤ (N : ℝ) := (Real.exp_one_lt_d9.le.trans (by norm_num)).trans h3
  have hle : (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by push_cast; linarith
  exact Real.log_div_self_antitoneOn (Set.mem_Ici.mpr he) (Set.mem_Ici.mpr (he.trans hle)) hle

/-- The plan's form of the finite logarithmic tail: `≤ 2q log N / N` for `σ ≥ 1`, `N ≥ 3`. -/
theorem norm_sum_Ioc_char_log_div_cpow_le_two_mul {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    {σ : ℝ} (hσ : 1 ≤ σ) {N : ℕ} (hN : 3 ≤ N) (K : ℕ) :
    ‖∑ n ∈ Ioc N K, χ n * (Real.log n : ℂ) / (n : ℂ) ^ (σ : ℂ)‖ ≤ 2 * q * Real.log N / N := by
  refine (norm_sum_Ioc_char_log_div_cpow_le hχ hσ (by omega) K).trans ?_
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : 0 ≤ Real.log N / N := div_nonneg (Real.log_nonneg (by linarith)) (by linarith)
  calc (q : ℝ) * (Real.log ((N + 1 : ℕ) : ℝ) * ((N + 1 : ℕ) : ℝ) ^ (-σ))
      ≤ q * (Real.log ((N + 1 : ℕ) : ℝ) / ((N + 1 : ℕ) : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ hq
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (natSucc_rpow_neg_le_inv hσ N)
          (Real.log_natCast_nonneg _)
    _ ≤ q * (Real.log N / N) := mul_le_mul_of_nonneg_left (log_natSucc_div_le_log_div hN) hq
    _ ≤ 2 * q * Real.log N / N := by
        rw [mul_div_assoc, mul_assoc]
        exact le_mul_of_one_le_left (mul_nonneg hq hlogN) (by norm_num)

omit [NeZero q] in
/-- For `σ > 1` the L-series of `χ` has abscissa of absolute convergence `≤ 1`. -/
theorem abscissaOfAbsConv_char_le_one (χ : DirichletCharacter ℂ q) :
    LSeries.abscissaOfAbsConv (fun n ↦ χ n) ≤ 1 := by
  exact_mod_cast LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    fun y hy ↦ χ.LSeriesSummable_of_one_lt_re (by simpa using hy)

/-- Infinite tails, `σ > 1`: `‖L(σ,χ) - ∑_{0 < n ≤ N} χ(n)/n^σ‖ ≤ q (N+1)^(-σ)`. -/
theorem norm_LFunction_sub_sum_le {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {σ : ℝ}
    (hσ : 1 < σ) (N : ℕ) :
    ‖DirichletCharacter.LFunction χ σ - ∑ n ∈ Ioc 0 N, χ n / (n : ℂ) ^ (σ : ℂ)‖ ≤
      q * ((N + 1 : ℕ) : ℝ) ^ (-σ) := by
  have hs : 1 < (σ : ℂ).re := by simpa using hσ
  rw [χ.LFunction_eq_LSeries hs]
  have hsum := (χ.LSeriesSummable_of_one_lt_re hs).LSeriesHasSum
  have e : ∀ s : Finset ℕ, (∀ n ∈ s, n ≠ 0) →
      ∑ n ∈ s, LSeries.term (fun n ↦ χ n) σ n = ∑ n ∈ s, χ n / (n : ℂ) ^ (σ : ℂ) :=
    fun s hs ↦ Finset.sum_congr rfl fun n hn ↦ LSeries.term_of_ne_zero (hs n hn) _ _
  have hpos : ∀ M K : ℕ, ∀ n ∈ Ioc M K, n ≠ 0 := fun M K n hn ↦ by
    have := (Finset.mem_Ioc.mp hn).1; omega
  rw [← e _ (hpos 0 N)]
  refine norm_hasSum_sub_sum_Ioc_le_of_forall hsum (LSeries.term_zero _ _) N fun K ↦ ?_
  rw [e _ (hpos N K)]
  exact norm_sum_Ioc_char_div_cpow_le hχ (by linarith) N K

omit [NeZero q] in
/-- The terms of `LSeries (logMul χ)` in the spelling of the partial sums. -/
theorem term_logMul_char_eq (χ : DirichletCharacter ℂ q) (s : ℂ) {n : ℕ} (hn : n ≠ 0) :
    LSeries.term (LSeries.logMul (fun n ↦ χ n)) s n =
      χ n * (Real.log n : ℂ) / (n : ℂ) ^ s := by
  rw [LSeries.term_of_ne_zero hn, LSeries.logMul, Complex.natCast_log]
  ring

/-- Infinite logarithmic tails, `σ > 1`, `N ≥ 2`:
`‖∑_{n ≥ 1} χ(n) log n/n^σ - ∑_{0<n≤N} χ(n) log n/n^σ‖ ≤ q log(N+1) (N+1)^(-σ)`. -/
theorem norm_LSeries_logMul_sub_sum_le {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {σ : ℝ}
    (hσ : 1 < σ) {N : ℕ} (hN : 2 ≤ N) :
    ‖LSeries (LSeries.logMul (fun n ↦ χ n)) σ -
        ∑ n ∈ Ioc 0 N, χ n * (Real.log n : ℂ) / (n : ℂ) ^ (σ : ℂ)‖ ≤
      q * (Real.log ((N + 1 : ℕ) : ℝ) * ((N + 1 : ℕ) : ℝ) ^ (-σ)) := by
  have ha : LSeries.abscissaOfAbsConv (fun n ↦ χ n) < (σ : ℂ).re := by
    simp only [Complex.ofReal_re]
    exact (abscissaOfAbsConv_char_le_one χ).trans_lt (by exact_mod_cast hσ)
  have hsum := (LSeriesSummable_logMul_of_lt_re ha).LSeriesHasSum
  have hpos : ∀ M K : ℕ, ∀ n ∈ Ioc M K, n ≠ 0 := fun M K n hn ↦ by
    have := (Finset.mem_Ioc.mp hn).1; omega
  have e : ∀ s : Finset ℕ, (∀ n ∈ s, n ≠ 0) →
      ∑ n ∈ s, LSeries.term (LSeries.logMul (fun n ↦ χ n)) σ n =
        ∑ n ∈ s, χ n * (Real.log n : ℂ) / (n : ℂ) ^ (σ : ℂ) :=
    fun s hs ↦ Finset.sum_congr rfl fun n hn ↦ term_logMul_char_eq χ _ (hs n hn)
  rw [← e _ (hpos 0 N)]
  refine norm_hasSum_sub_sum_Ioc_le_of_forall hsum (LSeries.term_zero _ _) N fun K ↦ ?_
  rw [e _ (hpos N K)]
  exact norm_sum_Ioc_char_log_div_cpow_le hχ hσ.le hN K

/-- Plan step 1, infinite tail, `σ > 1`, `N ≥ 1`:
`‖∑_{n > N} χ(n)/n^σ‖ = ‖L(σ,χ) - ∑_{0<n≤N} χ(n)/n^σ‖ ≤ 2q/N`. -/
theorem norm_tail_le {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {σ : ℝ} (hσ : 1 < σ) {N : ℕ}
    (hN : 1 ≤ N) :
    ‖DirichletCharacter.LFunction χ σ - ∑ n ∈ Ioc 0 N, χ n / (n : ℂ) ^ (σ : ℂ)‖ ≤
      2 * q / N := by
  refine (norm_LFunction_sub_sum_le hχ hσ N).trans ?_
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  refine (mul_le_mul_of_nonneg_left (natSucc_rpow_neg_le_inv hσ.le N) hq).trans ?_
  rw [← div_eq_mul_inv, Nat.cast_add, Nat.cast_one, div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- Plan step 1, infinite logarithmic tail, `σ > 1`, `N ≥ 3`:
`‖∑_{n > N} χ(n) log n/n^σ‖ ≤ 2q log N / N`. -/
theorem norm_tail_log_le {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {σ : ℝ} (hσ : 1 < σ)
    {N : ℕ} (hN : 3 ≤ N) :
    ‖LSeries (LSeries.logMul (fun n ↦ χ n)) σ -
        ∑ n ∈ Ioc 0 N, χ n * (Real.log n : ℂ) / (n : ℂ) ^ (σ : ℂ)‖ ≤
      2 * q * Real.log N / N := by
  refine (norm_LSeries_logMul_sub_sum_le hχ hσ (by omega)).trans ?_
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : 0 ≤ Real.log N / N := div_nonneg (Real.log_nonneg (by linarith)) (by linarith)
  calc (q : ℝ) * (Real.log ((N + 1 : ℕ) : ℝ) * ((N + 1 : ℕ) : ℝ) ^ (-σ))
      ≤ q * (Real.log ((N + 1 : ℕ) : ℝ) / ((N + 1 : ℕ) : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ hq
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (natSucc_rpow_neg_le_inv hσ.le N)
          (Real.log_natCast_nonneg _)
    _ ≤ q * (Real.log N / N) := mul_le_mul_of_nonneg_left (log_natSucc_div_le_log_div hN) hq
    _ ≤ 2 * q * Real.log N / N := by
        rw [mul_div_assoc, mul_assoc]
        exact le_mul_of_one_le_left (mul_nonneg hq hlogN) (by norm_num)

end ZInQ.Progressions
