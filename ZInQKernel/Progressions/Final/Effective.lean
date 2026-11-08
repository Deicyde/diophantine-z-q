/-
Plan steps 2–4 combined (effective Dirichlet): a uniform lower bound for `‖L(1, χ)‖` over all
characters `χ ≠ 1`, and twenty-two primes `p ≡ a (mod q)` with `q² < p < 2^(q⁸)` for
`q ≥ 2^24`.
-/
import ZInQKernel.Progressions.Final.RealBound
import ZInQKernel.Progressions.LSeries
import ZInQKernel.Progressions.Mertens

namespace ZInQ.Progressions

open Finset

/-- **All characters** (plan steps 2 and 3): for `χ ≠ 1` modulo `q`,
`‖L(1, χ)‖ ≥ min (1/(256 (log q + 3)^7)) (1/(54 q √q))`. -/
theorem min_le_norm_LFunction_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    min (1 / (256 * (Real.log q + 3) ^ 7)) (1 / (54 * (q * √q))) ≤
      ‖DirichletCharacter.LFunction χ 1‖ := by
  by_cases h2 : χ ^ 2 = 1
  · exact (min_le_right _ _).trans (norm_LFunction_one_ge_of_sq_eq_one hχ h2)
  · exact (min_le_left _ _).trans (norm_LFunction_one_ge_of_sq_ne_one h2)

/-- The uniform constant `c_q = 1/(2^14 (log q + 3)^7 q²)`, below both bounds of
`min_le_norm_LFunction_one`. -/
noncomputable def effectiveLBound (q : ℕ) : ℝ := 1 / (2 ^ 14 * (Real.log q + 3) ^ 7 * q ^ 2)

theorem effectiveLBound_pos {q : ℕ} (hq : q ≠ 0) : 0 < effectiveLBound q := by
  have : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  have : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
  unfold effectiveLBound
  positivity

/-- `c_q ≤ ‖L(1, χ)‖` for every `χ ≠ 1` modulo `q`. -/
theorem effectiveLBound_le_norm_LFunction_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) : effectiveLBound q ≤ ‖DirichletCharacter.LFunction χ 1‖ := by
  refine le_trans ?_ (min_le_norm_LFunction_one hχ)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hlog : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  have hM : 1 ≤ (Real.log q + 3) ^ 7 := one_le_pow₀ (by linarith)
  have hs : √(q : ℝ) ≤ q := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hs0 : 0 < √(q : ℝ) := Real.sqrt_pos.2 (by linarith)
  unfold effectiveLBound
  refine le_min ?_ ?_
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [one_le_pow₀ (n := 2) hq1]
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : (q : ℝ) * √q ≤ q ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hM (by positivity : (0 : ℝ) ≤ 2 ^ 14 * q ^ 2)]

/-- The size estimate behind `effective_dirichlet`: for `q ≥ 2^24`,
`8 log q + 5q (M² + 6q)/c_q < q⁸ log 2` with `M = log q + 3`. -/
theorem effective_exponent_lt {q : ℕ} (hq : 2 ^ 24 ≤ q) :
    8 * Real.log q + 5 * q * (((Real.log q + 3) ^ 2 + 6 * q) / effectiveLBound q) <
      (q : ℝ) ^ 8 * Real.log 2 := by
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hq24 : (2 : ℝ) ^ 24 ≤ q := by exact_mod_cast hq
  set t : ℝ := (q : ℝ) ^ ((8 : ℕ)⁻¹ : ℝ) with ht
  have ht0 : 0 ≤ t := Real.rpow_nonneg hq0 _
  have ht8 : t ^ 8 = q := Real.rpow_inv_natCast_pow hq0 (by norm_num)
  have ht8' : (8 : ℝ) ≤ t := by
    have : (8 : ℝ) ^ 8 ≤ t ^ 8 := by rw [ht8]; norm_num at hq24 ⊢; linarith
    exact (pow_le_pow_iff_left₀ (by norm_num) ht0 (by norm_num)).1 this
  set M := Real.log q + 3 with hMdef
  have hlog0 : 0 ≤ Real.log q := Real.log_nonneg (by linarith)
  have hlogt : Real.log q ≤ 8 * t := by
    have := Real.log_le_rpow_div hq0 (ε := ((8 : ℕ)⁻¹ : ℝ)) (by norm_num)
    rw [← ht] at this
    calc Real.log q ≤ t / ((8 : ℕ)⁻¹ : ℝ) := this
      _ = 8 * t := by push_cast; field_simp
  have hM0 : 0 ≤ M := by linarith
  have hM9 : M ≤ 9 * t := by linarith
  have ht6 : (81 : ℝ) ≤ t ^ 6 := by
    calc (81 : ℝ) ≤ 8 ^ 6 := by norm_num
      _ ≤ t ^ 6 := pow_le_pow_left₀ (by norm_num) ht8' 6
  have hA : M ^ 2 + 6 * q ≤ 7 * t ^ 8 := by
    have h1 : M ^ 2 ≤ (9 * t) ^ 2 := pow_le_pow_left₀ hM0 hM9 2
    have h2 : 81 * t ^ 2 ≤ t ^ 8 := by
      have : t ^ 8 = t ^ 2 * t ^ 6 := by ring
      rw [this]; nlinarith [sq_nonneg t]
    rw [← ht8]; nlinarith
  have hB : M ^ 7 ≤ 9 ^ 7 * t ^ 7 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hM0 hM9 7
  have hE : 5 * q * ((M ^ 2 + 6 * q) / effectiveLBound q) ≤ 35 * 2 ^ 14 * 9 ^ 7 * t ^ 39 := by
    unfold effectiveLBound
    rw [div_div_eq_mul_div, div_one, ← hMdef]
    calc 5 * (q : ℝ) * ((M ^ 2 + 6 * q) * (2 ^ 14 * M ^ 7 * q ^ 2))
        ≤ 5 * q * ((7 * t ^ 8) * (2 ^ 14 * (9 ^ 7 * t ^ 7) * q ^ 2)) := by gcongr
      _ = 35 * 2 ^ 14 * 9 ^ 7 * t ^ 39 := by rw [← ht8]; ring
  have hL : 8 * Real.log q ≤ t ^ 39 := by
    have h38 : (64 : ℝ) ≤ t ^ 38 :=
      le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) ht8' 38)
    have : t ^ 39 = t * t ^ 38 := by ring
    rw [this]; nlinarith
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have h25 : (2 : ℝ) ^ 75 ≤ t ^ 25 :=
    le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) ht8' 25)
  have ht39 : 0 < t ^ 39 := by positivity
  have hq8 : (q : ℝ) ^ 8 = t ^ 25 * t ^ 39 * t ^ 0 := by rw [← ht8]; ring
  rw [hq8, pow_zero, mul_one]
  have hfin : 8 * Real.log q + 5 * q * ((M ^ 2 + 6 * q) / effectiveLBound q) ≤
      2 ^ 74 * t ^ 39 := by
    nlinarith
  have : (2 : ℝ) ^ 74 * t ^ 39 < t ^ 25 * t ^ 39 * Real.log 2 := by
    have h1 : (2 : ℝ) ^ 74 * t ^ 39 ≤ t ^ 25 * t ^ 39 * (1 / 2) := by nlinarith
    have h2 : t ^ 25 * t ^ 39 * (1 / 2) < t ^ 25 * t ^ 39 * Real.log 2 := by
      have : 0 < t ^ 25 * t ^ 39 := by positivity
      exact mul_lt_mul_of_pos_left hlog2 this
    linarith
  linarith

/-- The upper end of the interval: `q⁸ exp(5q (M² + 6q)/c_q) < 2^(q⁸)` for `q ≥ 2^24`. -/
theorem effective_upper_lt {q : ℕ} (hq : 2 ^ 24 ≤ q) :
    (q : ℝ) ^ 8 * Real.exp (5 * q * (((Real.log q + 3) ^ 2 + 6 * q) / effectiveLBound q)) <
      ((2 ^ q ^ 8 : ℕ) : ℝ) := by
  have hq0 : (0 : ℝ) < q := by
    have : (2 : ℝ) ^ 24 ≤ q := by exact_mod_cast hq
    linarith
  rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.exp_log (by positivity : (0 : ℝ) < (q : ℝ) ^ 8),
    ← Real.exp_add, ← Real.exp_log (by positivity : (0 : ℝ) < 2 ^ q ^ 8), Real.exp_lt_exp,
    Real.log_pow, Real.log_pow, Nat.cast_pow]
  have := effective_exponent_lt hq
  push_cast
  linarith

/-- **Effective Dirichlet theorem** (plan, "The theorem to prove", with `q₀ = 2^24`). For
`q ≥ 2^24` and `a` coprime to `q`, at least 22 primes `p ≡ a (mod q)` satisfy
`q² < p < 2^(q⁸)`. -/
theorem effective_dirichlet {q : ℕ} (hq : 2 ^ 24 ≤ q) {a : ℕ} (ha : a.Coprime q) :
    22 ≤ #{p ∈ Ioo (q ^ 2) (2 ^ q ^ 8) | p.Prime ∧ p ≡ a [MOD q]} := by
  have hq0 : q ≠ 0 := by omega
  have : NeZero q := ⟨hq0⟩
  have h := twentytwo_primes_of_LFunction_lower_bound (by omega) ha (effectiveLBound_pos hq0)
    fun χ hχ ↦ effectiveLBound_le_norm_LFunction_one hχ
  refine h.trans (card_le_card fun p hp ↦ ?_)
  simp only [mem_filter, mem_Ioc, mem_Ioo] at hp ⊢
  refine ⟨⟨lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) (by norm_num)) hp.1.1, ?_⟩, hp.2⟩
  have hup := effective_upper_lt hq
  have hpos : 0 ≤ (q : ℝ) ^ 8 *
      Real.exp (5 * q * (((Real.log q + 3) ^ 2 + 6 * q) / effectiveLBound q)) := by positivity
  exact lt_of_le_of_lt hp.1.2 ((Nat.floor_lt hpos).2 hup)

end ZInQ.Progressions
