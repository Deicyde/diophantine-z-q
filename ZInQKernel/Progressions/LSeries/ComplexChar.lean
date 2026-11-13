import ZInQKernel.Progressions.LSeries.Bounds

/-!
# Lower bound for `L(1, χ)`, `χ` complex

Plan step 2, `docs/effective-dirichlet-plan.md`: if `χ² ≠ 1` then
`‖L(1,χ)‖ ≥ 1/(256 M⁷)` with `M = log q + 3`
(`ZInQ.Progressions.norm_LFunction_one_ge_of_sq_ne_one`).

The proof evaluates Mathlib's `DirichletCharacter.norm_LSeries_product_ge_one` at the real point
`1 + x`, `x = 1/(256 M⁹)`, with `‖L(1+x, χ₀)‖ ≤ 1 + 1/x`, `‖L(1+x, χ²)‖ ≤ M` and
`‖L(1+x, χ)‖ ≤ ‖L(1,χ)‖ + x M²`.
-/

open Finset Complex

namespace ZInQ.Progressions

variable {q : ℕ}

/-- `∑_{n ≥ 1} n^(-(1+x)) ≤ 1 + 1/x` for `x > 0`. -/
theorem tsum_one_div_succ_rpow_le_one_add_inv {x : ℝ} (hx : 0 < x) :
    ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ (1 + x) ≤ 1 + 1 / x := by
  have hs : (1 : ℝ) < 1 + x := by linarith
  have h := ZetaAsymptotics.zeta_limit_aux1 hs
  have h0 : 0 ≤ ZetaAsymptotics.termTSum (1 + x) :=
    tsum_nonneg fun n ↦ ZetaAsymptotics.term_nonneg (n + 1) _
  rw [show 1 + x - 1 = x by ring] at h
  nlinarith

/-- For the trivial character `χ₀` mod `q` and real `x > 0`, `‖L(1+x, χ₀)‖ ≤ 1 + 1/x`. -/
theorem norm_LSeries_one_le {x : ℝ} (hx : 0 < x) :
    ‖LSeries (fun n ↦ (1 : DirichletCharacter ℂ q) n) (1 + x)‖ ≤ 1 + 1 / x := by
  set f : ℕ → ℂ := fun n ↦ (1 : DirichletCharacter ℂ q) n
  have hs : 1 < (1 + (x : ℂ)).re := by simpa using hx
  have hsum : Summable (LSeries.term f (1 + x)) :=
    DirichletCharacter.LSeriesSummable_of_one_lt_re _ hs
  have hnorm : Summable fun n ↦ ‖LSeries.term f (1 + x) n‖ := hsum.norm
  have hg : Summable fun n : ℕ ↦ 1 / ((n : ℝ) + 1) ^ (1 + x) := by
    have := (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_rpow.mpr (by linarith : (1 : ℝ) < 1 + x))
    exact_mod_cast this
  have hle : ∀ n : ℕ, ‖LSeries.term f (1 + x) (n + 1)‖ ≤ 1 / ((n : ℝ) + 1) ^ (1 + x) := by
    intro n
    rw [LSeries.norm_term_eq]
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    have hre : (1 + (x : ℂ)).re = 1 + x := by simp
    rw [hre]
    push_cast
    exact div_le_div_of_nonneg_right (DirichletCharacter.norm_le_one _ _) (by positivity)
  calc ‖LSeries f (1 + x)‖ ≤ ∑' n, ‖LSeries.term f (1 + x) n‖ := norm_tsum_le_tsum_norm hnorm
    _ = ∑' n : ℕ, ‖LSeries.term f (1 + x) (n + 1)‖ := by
        rw [hnorm.tsum_eq_zero_add, LSeries.term_zero, norm_zero, zero_add]
    _ ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ (1 + x) :=
        ((summable_nat_add_iff 1).mpr hnorm).tsum_le_tsum hle hg
    _ ≤ 1 + 1 / x := tsum_one_div_succ_rpow_le_one_add_inv hx

variable [NeZero q]

/-- Plan step 2: for a complex character (`χ² ≠ 1`), `‖L(1,χ)‖ ≥ 1/(256 M⁷)`,
`M = log q + 3`. -/
theorem norm_LFunction_one_ge_of_sq_ne_one {χ : DirichletCharacter ℂ q} (hχ : χ ^ 2 ≠ 1) :
    1 / (256 * (Real.log q + 3) ^ 7) ≤ ‖DirichletCharacter.LFunction χ 1‖ := by
  have hχ1 : χ ≠ 1 := by rintro rfl; exact hχ (one_pow 2)
  set M := Real.log q + 3 with hM
  have hM3 : 3 ≤ M := by
    have : 0 ≤ Real.log q := Real.log_natCast_nonneg q
    linarith
  have hM0 : 0 < M := by linarith
  set x : ℝ := 1 / (256 * M ^ 9) with hxdef
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 := by
    rw [hxdef, div_le_one (by positivity)]
    have : (1 : ℝ) ≤ M ^ 9 := one_le_pow₀ (by linarith)
    linarith
  have hxM : x * M ^ 2 = 1 / (256 * M ^ 7) := by
    rw [hxdef]; field_simp
  rw [← hxM]
  by_contra hlt
  rw [not_le] at hlt
  -- The three factors at `s = 1 + x`.
  have hs : ((1 + x : ℝ) : ℂ) = 1 + (x : ℂ) := by push_cast; ring
  have hs' : 1 < (1 + (x : ℂ)).re := by simpa using hx0
  have P := DirichletCharacter.norm_LSeries_product_ge_one χ hx0 0
  simp only [Complex.ofReal_zero, mul_zero, add_zero] at P
  rw [← χ.LFunction_eq_LSeries hs', ← (χ ^ 2).LFunction_eq_LSeries hs', norm_mul, norm_mul,
    norm_pow, norm_pow, ← hs] at P
  set A := ‖LSeries (fun n ↦ (1 : DirichletCharacter ℂ q) n) ((1 + x : ℝ) : ℂ)‖
  set B := ‖DirichletCharacter.LFunction χ ((1 + x : ℝ) : ℂ)‖
  set C := ‖DirichletCharacter.LFunction (χ ^ 2) ((1 + x : ℝ) : ℂ)‖
  have hA : A ≤ 2 / x := by
    refine (le_of_eq (by simp only [A, hs])).trans ((norm_LSeries_one_le (q := q) hx0).trans ?_)
    rw [le_div_iff₀ hx0, add_mul, one_div, inv_mul_cancel₀ hx0.ne']
    linarith
  have hB : B ≤ 2 * (x * M ^ 2) := by
    have h1 := norm_LFunction_sub_one_le hχ1 (σ := 1 + x) (by linarith)
    rw [show 1 + x - 1 = x by ring] at h1
    have h2 := norm_le_norm_sub_add (DirichletCharacter.LFunction χ ((1 + x : ℝ) : ℂ))
      (DirichletCharacter.LFunction χ 1)
    linarith
  have hC : C ≤ M := norm_LFunction_le hχ (by linarith)
  have hA0 : 0 ≤ A := norm_nonneg _
  have hB0 : 0 ≤ B := norm_nonneg _
  have hC0 : 0 ≤ C := norm_nonneg _
  have hprod : A ^ 3 * B ^ 4 * C ≤ (2 / x) ^ 3 * (2 * (x * M ^ 2)) ^ 4 * M :=
    mul_le_mul (mul_le_mul (pow_le_pow_left₀ hA0 hA 3) (pow_le_pow_left₀ hB0 hB 4)
      (by positivity) (by positivity)) hC hC0 (by positivity)
  have hval : (2 / x) ^ 3 * (2 * (x * M ^ 2)) ^ 4 * M = 1 / 2 := by
    rw [hxdef]; field_simp; ring
  linarith

end ZInQ.Progressions
