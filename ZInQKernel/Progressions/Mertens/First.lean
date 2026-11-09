import Mathlib

/-!
# Mertens' first theorem (plan step 4.1)

`S(x) = Σ_{n ≤ x} Λ(n)/n` satisfies `|S(x) − log x| ≤ 3` for real `x ≥ 1`; along the way,
Chebyshev's bound in the explicit form `ψ(x) ≤ 3x`.
-/

namespace ZInQ.Progressions

open Finset Real
open ArithmeticFunction hiding log
open scoped Chebyshev Nat

/-- `S(x) = Σ_{n ≤ x} Λ(n)/n`. -/
noncomputable def mertensSum (x : ℝ) : ℝ := ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n

lemma mertensSum_eq_floor (x : ℝ) : mertensSum x = mertensSum ⌊x⌋₊ := by
  simp [mertensSum]

lemma mertensSum_nonneg (x : ℝ) : 0 ≤ mertensSum x :=
  sum_nonneg fun _ _ ↦ div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)

/-- Chebyshev's bound with the explicit constant 3: `ψ(x) ≤ 3x` for `x ≥ 0`. -/
theorem psi_le_three_mul {x : ℝ} (hx : 0 ≤ x) : ψ x ≤ 3 * x := by
  rcases lt_or_ge x 1 with h1 | h1
  · rw [Chebyshev.psi_eq_zero_of_lt_two (by linarith)]; linarith
  have hs : 0 ≤ √x := sqrt_nonneg x
  have he := exp_one_gt_d9
  have hl := log_two_lt_d9
  have hlog : log x ≤ 2 * √x / exp 1 := by
    have h := log_le_sub_one_of_pos (x := √x / exp 1) (by positivity)
    rw [log_div (by positivity) (exp_pos 1).ne', log_exp, log_sqrt hx] at h
    have : 2 * √x / exp 1 = 2 * (√x / exp 1) := by ring
    linarith
  have h4 : log 4 = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hxx : √x * √x = x := mul_self_sqrt hx
  have key : 2 * √x * log x ≤ 4 / exp 1 * x := by
    calc 2 * √x * log x ≤ 2 * √x * (2 * √x / exp 1) := by gcongr
      _ = 4 / exp 1 * (√x * √x) := by ring
      _ = 4 / exp 1 * x := by rw [hxx]
  have h4e : 4 / exp 1 ≤ 1.5 := by
    rw [div_le_iff₀ (exp_pos 1)]; linarith
  calc ψ x ≤ log 4 * x + 2 * √x * log x := Chebyshev.psi_le h1
    _ ≤ log 4 * x + 1.5 * x := by nlinarith
    _ ≤ 3 * x := by rw [h4]; nlinarith

/-- `ψ(x)/x ≤ 3` for `x > 0`. -/
theorem psi_div_le_three {x : ℝ} (hx : 0 < x) : ψ x / x ≤ 3 := by
  rw [div_le_iff₀ hx]; exact psi_le_three_mul hx.le

lemma prod_Ioc_natCast_eq_factorial_real (N : ℕ) : ∏ n ∈ Ioc 0 N, (n : ℝ) = (N ! : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [prod_Ioc_succ_top (Nat.zero_le N), ih, Nat.factorial_succ]; push_cast; ring

/-- `Σ_{n ≤ N} log n = Σ_{d ≤ N} Λ(d) ⌊N/d⌋`. -/
lemma sum_log_eq_sum_vonMangoldt_mul_div (N : ℕ) :
    ∑ n ∈ Ioc 0 N, Real.log n = ∑ d ∈ Ioc 0 N, Λ d * ((N / d : ℕ) : ℝ) := by
  rw [← sum_Ioc_mul_zeta_eq_sum, vonMangoldt_mul_zeta]
  simp [ArithmeticFunction.log_apply]

lemma sum_Ioc_log_le_mul_log (N : ℕ) : ∑ n ∈ Ioc 0 N, Real.log n ≤ N * Real.log N := by
  calc ∑ n ∈ Ioc 0 N, Real.log n ≤ ∑ _n ∈ Ioc 0 N, Real.log N := by
        refine sum_le_sum fun n hn ↦ ?_
        rw [mem_Ioc] at hn
        exact log_le_log (by exact_mod_cast hn.1) (by exact_mod_cast hn.2)
    _ = N * Real.log N := by simp

lemma mul_log_sub_le_sum_Ioc_log (N : ℕ) : N * Real.log N - N ≤ ∑ n ∈ Ioc 0 N, Real.log n := by
  rcases N.eq_zero_or_pos with rfl | hN
  · simp
  have hpos : (0 : ℝ) < N ! := by exact_mod_cast N.factorial_pos
  have h := Real.pow_div_factorial_le_exp (x := (N : ℝ)) (by positivity) N
  have h' := log_le_log (by positivity) h
  rw [log_exp, log_div (by positivity) hpos.ne', Real.log_pow] at h'
  rw [← log_prod (fun n hn ↦ by simp at hn; exact_mod_cast hn.1.ne'), prod_Ioc_natCast_eq_factorial_real]
  linarith

/-- `N·S(N)` lies between `Σ_{n ≤ N} log n` and `Σ_{n ≤ N} log n + ψ(N)`. -/
lemma mul_mertensSum_bounds (N : ℕ) :
    ∑ n ∈ Ioc 0 N, Real.log n ≤ N * mertensSum N ∧
      N * mertensSum N ≤ ∑ n ∈ Ioc 0 N, Real.log n + ψ N := by
  rw [sum_log_eq_sum_vonMangoldt_mul_div, Chebyshev.psi, mertensSum, Nat.floor_natCast, mul_sum,
    ← sum_add_distrib]
  constructor
  · refine sum_le_sum fun d hd ↦ ?_
    have hd0 : (0 : ℝ) < d := by simp at hd; exact_mod_cast hd.1
    have h : ((N / d : ℕ) : ℝ) ≤ N / d := Nat.cast_div_le
    calc Λ d * ((N / d : ℕ) : ℝ) ≤ Λ d * (N / d) := mul_le_mul_of_nonneg_left h vonMangoldt_nonneg
      _ = N * (Λ d / d) := by ring
  · refine sum_le_sum fun d hd ↦ ?_
    have hd0 : (0 : ℝ) < d := by simp at hd; exact_mod_cast hd.1
    have h : (N : ℝ) / d ≤ ((N / d : ℕ) : ℝ) + 1 := by
      have := Nat.lt_floor_add_one ((N : ℝ) / d)
      rw [Nat.floor_div_eq_div] at this
      exact this.le
    calc N * (Λ d / d) = Λ d * (N / d) := by ring
      _ ≤ Λ d * (((N / d : ℕ) : ℝ) + 1) := mul_le_mul_of_nonneg_left h vonMangoldt_nonneg
      _ = Λ d * ((N / d : ℕ) : ℝ) + Λ d := by ring

/-- Lower half of Mertens' first theorem: `S(x) ≥ log x − 2` for `x ≥ 1`. -/
theorem log_sub_two_le_mertensSum {x : ℝ} (hx : 1 ≤ x) : log x - 2 ≤ mertensSum x := by
  set N := ⌊x⌋₊ with hNdef
  have hN1 : 1 ≤ N := Nat.one_le_floor_iff x |>.mpr hx
  have hN : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNx : (N : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxN : x < N + 1 := Nat.lt_floor_add_one x
  have hlog : log x ≤ log N + 1 := by
    have h := log_le_sub_one_of_pos (x := x / N) (by positivity)
    rw [log_div (by positivity) hN.ne'] at h
    have : x / N - 1 ≤ 1 := by
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
      rw [div_sub_one hN.ne', div_le_one hN]; linarith
    linarith
  obtain ⟨h1, -⟩ := mul_mertensSum_bounds N
  have h2 := mul_log_sub_le_sum_Ioc_log N
  rw [mertensSum_eq_floor]
  have : log N - 1 ≤ mertensSum N := by
    rw [← mul_le_mul_iff_of_pos_left hN]; nlinarith
  linarith

/-- Upper half of Mertens' first theorem: `S(x) ≤ log x + 3` for `x ≥ 1`. -/
theorem mertensSum_le_log_add_three {x : ℝ} (hx : 1 ≤ x) : mertensSum x ≤ log x + 3 := by
  set N := ⌊x⌋₊ with hNdef
  have hN1 : 1 ≤ N := Nat.one_le_floor_iff x |>.mpr hx
  have hN : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNx : (N : ℝ) ≤ x := Nat.floor_le (by linarith)
  obtain ⟨-, h1⟩ := mul_mertensSum_bounds N
  have h2 := sum_Ioc_log_le_mul_log N
  have h3 := psi_le_three_mul hN.le
  rw [mertensSum_eq_floor]
  have : mertensSum N ≤ log N + 3 := by
    rw [← mul_le_mul_iff_of_pos_left hN]; nlinarith
  have := log_le_log hN hNx
  linarith

/-- **Mertens' first theorem**, with the explicit constant `C₀ = 3`:
`|Σ_{n ≤ x} Λ(n)/n − log x| ≤ 3` for real `x ≥ 1`. -/
theorem abs_mertensSum_sub_log_le {x : ℝ} (hx : 1 ≤ x) : |mertensSum x - log x| ≤ 3 := by
  have := log_sub_two_le_mertensSum hx
  have := mertensSum_le_log_add_three hx
  rw [abs_le]; constructor <;> linarith

end ZInQ.Progressions
