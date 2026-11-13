import PGLight
/-! # period-glue: `S8Nonzero` reduced to a statement about one explicit matrix

Task period-glue, 2026-11-13. `S8Nonzero` (period-map, `PGLight`, unchanged) says
`Σ_{m even} θ_m(Ω(√2 + i))⁸ ≠ 0`. Proved here: `Ω(√2 + i) = Ω₀ := [[(−1+i)/2, 1], [1, −1+i]]`
exactly (`omega_cm4`), so `S8Nonzero ⇔ S8Omega0` (`s8Nonzero_iff`). `S8Omega0` is a statement about
theta constants at an explicit point of `𝔥₂` with `Im Ω₀ = diag(1/2, 1)`; its certificate is in
`docs/research/period-glue.md` §3 (`py/s8_exact.py`): `Σθ⁸(Ω₀) = −9 ϑ₀₀(i)¹⁶` numerically to 60
digits, each `θ_m(Ω₀)⁸ ∈ {−¼, −1, −4, 0}·ϑ₀₀(i)¹⁶`. -/

noncomputable section

namespace HSyn.G0Split.FibreQM.PeriodGlue

open Complex Matrix HSyn.G0Split.FibreQM HSyn.G0Split.FibreQM.PeriodMap

/-- The period matrix at the CM point `√2 + i` (discriminant `−4`). -/
def Omega0 : Matrix (Fin 2) (Fin 2) ℂ := !![(-1 + I) / 2, 1; 1, -1 + I]

theorem dF_cm4_ne : dF ((√2 : ℂ) + I) ≠ 0 := by
  unfold dF
  have h2 : (√2 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have h3 : (√2 : ℂ) + I - 3 ≠ 0 := fun h => by simpa using congrArg Complex.im h
  have h4 : (√2 : ℂ) + I + 1 ≠ 0 := fun h => by simpa using congrArg Complex.im h
  have := mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr h2) h3) h4
  exact div_ne_zero this two_ne_zero

/-- **`Ω(√2 + i) = Ω₀` (proved).** Closed form `omega_eq` (period-map) and `√2² = 2`, `i² = −1`;
the `linear_combination` coefficients are from `py/omega0_lc.py`. -/
theorem omega_cm4 : PkgI1.Omega ((√2 : ℂ) + I) = Omega0 := by
  ext i j
  rw [omega_eq, div_eq_iff dF_cm4_ne]
  fin_cases i <;> fin_cases j <;> simp only [Nf, dF, Omega0] <;> simp
  · linear_combination
      (2 * I ^ 2 + I * (√2 : ℂ) + (√2 : ℂ) + 4) / 4 * sqrt2_sq + (I * (√2 : ℂ) - √2 + 2) / 4 * I_mul_I
  · linear_combination (-1 : ℂ) * sqrt2_sq + I_mul_I
  · linear_combination (-1 : ℂ) * sqrt2_sq + I_mul_I
  · linear_combination
      (2 * I ^ 2 + I * (√2 : ℂ) + (√2 : ℂ) + 4) / 2 * sqrt2_sq + (I * (√2 : ℂ) - √2 + 2) / 2 * I_mul_I

/-- **GLUE (numerical, at an explicit matrix).** `Σ_{m even} θ_m(Ω₀)⁸ ≠ 0` for
`Ω₀ = [[(−1+i)/2, 1], [1, −1+i]]`.

Certificate (period-glue §3, `py/s8_exact.py`, VERIFIED numerically): since `(Ω₀)₀₁ = 1`, every
term factors, `θ_{(a,b)}(Ω₀) = u·ϑ[a₁, b₁+a₂]((−1+i)/2)·ϑ[a₂, b₂+a₁](−1+i)` with `u ∈ {1, −i}`;
`|exp(πi vᵀΩ₀v)| = exp(−π(v₀²/2 + v₁²))`, so truncating at `|n_k| ≤ 2` leaves a tail
`< 2.2·10⁻⁴` per theta constant; the truncated sums give `Σθ⁸ ∈ −33.9079 ± 0.01`. Exactly:
`θ_m(Ω₀)⁸ = −c_m ϑ₀₀(i)¹⁶` with `c_m = ¼, 1, 4, 0` (four, four, one, one characteristics), so
`Σθ⁸(Ω₀) = −9 ϑ₀₀(i)¹⁶ < 0` (60 digits); a symbolic proof needs the transformation of
one-variable theta constants under `τ ↦ τ + 1`, `τ ↦ −1/τ` (Mathlib:
`jacobiTheta₂_functional_equation`) and the factorization. -/
def S8Omega0 : Prop := PkgI1.thetaSum8 Omega0 ≠ 0

/-- **`S8Nonzero ⇔ S8Omega0` (proved).** -/
theorem s8Nonzero_iff : S8Nonzero ↔ S8Omega0 := by
  unfold S8Nonzero S8Omega0
  rw [omega_cm4]

theorem s8Nonzero_of (h : S8Omega0) : S8Nonzero := s8Nonzero_iff.mpr h

/-! ## `S8Omega0` proved: every `θ_m(Ω₀)⁸` has non-positive real part

Proof (no numerics beyond crude bounds on `e^{−π/2}`):
* `(Ω₀)₀₁ = 1` makes each theta constant a product of two one-variable theta series,
  `θ_m(Ω₀) = u·Θ[a₁, b₁+a₂](τ₁)·Θ[a₂, b₂+a₁](τ₂)` with `τ₁ = (−1+i)/2`, `τ₂ = −1+i`, `u⁸ = 1`
  (`thetaConst_factor`);
* at `τ₂` every term of `Θ[a,b]` is a fixed eighth root of unity times a real number, so
  `Θ[a,b](τ₂)⁸ ≥ 0` is real (`th1_τ2`);
* at `τ₁`, `Θ[1,b](τ₁) = ω·R` with `ω⁸ = −1`, `R` real (`th1_τ1_one`), and
  `Θ[0,b](τ₁) = P + σ E i` with `σ = ±1`, `1 ≤ P ≤ 1 + 2q³/(1−q²)`, `2q ≤ E ≤ 2q/(1−q²)`,
  `q = e^{−π/2} ∈ [0.173, 0.2798]`; then `Re (P + σEi)⁸ < 0` (`re_th1_τ1_zero`);
* so `Re θ_m(Ω₀)⁸ ≤ 0` for every characteristic, `< 0` for `m = ((0,0),(0,1))`. -/

open Real in
/-- `τ₁ = (−1+i)/2`. -/
def τ1 : ℂ := (-1 + I) / 2
/-- `τ₂ = −1+i`. -/
def τ2 : ℂ := -1 + I

theorem τ1_im : 0 < τ1.im := by simp [τ1]
theorem τ2_im : 0 < τ2.im := by simp [τ2]

/-- The terms of the one-variable theta series with characteristic `[a/2, b/2]`. -/
def thT (a b : ℕ) (τ : ℂ) (n : ℤ) : ℂ :=
  cexp (Real.pi * I * ((n : ℂ) + (a : ℂ) / 2) ^ 2 * τ +
    Real.pi * I * ((n : ℂ) + (a : ℂ) / 2) * (b : ℂ))

/-- `Θ[a, b](τ) = Σ_n exp(πi(n + a/2)²τ + πi(n + a/2)b)`. -/
def th1 (a b : ℕ) (τ : ℂ) : ℂ := ∑' n : ℤ, thT a b τ n

theorem thT_eq_jac (a b : ℕ) (τ : ℂ) (n : ℤ) :
    thT a b τ n = cexp (Real.pi * I * (a : ℂ) ^ 2 * τ / 4 + Real.pi * I * (a : ℂ) * b / 2) *
      jacobiTheta₂_term n (((a : ℂ) * τ + b) / 2) τ := by
  unfold thT jacobiTheta₂_term
  rw [← Complex.exp_add]
  congr 1
  ring

theorem summable_thT (a b : ℕ) {τ : ℂ} (hτ : 0 < τ.im) : Summable (thT a b τ) := by
  have h := ((summable_jacobiTheta₂_term_iff (((a : ℂ) * τ + b) / 2) τ).mpr hτ).mul_left
    (cexp (Real.pi * I * (a : ℂ) ^ 2 * τ / 4 + Real.pi * I * (a : ℂ) * b / 2))
  convert h using 1
  funext n
  exact thT_eq_jac a b τ n

theorem summable_norm_thT (a b : ℕ) {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (fun n => ‖thT a b τ n‖) :=
  summable_norm_iff.mpr (summable_thT a b hτ)

/-- **Factorization at `Ω₀` (proved).** -/
theorem thetaConst_factor (m : PkgI1.Char2) :
    PkgI1.thetaConst m Omega0 =
      cexp (-(Real.pi * I * ((m.1 0 : ℕ) : ℂ) * ((m.1 1 : ℕ) : ℂ) / 2)) *
        (th1 (m.1 0 : ℕ) ((m.2 0 : ℕ) + (m.1 1 : ℕ)) τ1 *
          th1 (m.1 1 : ℕ) ((m.2 1 : ℕ) + (m.1 0 : ℕ)) τ2) := by
  unfold PkgI1.thetaConst th1
  rw [tsum_mul_tsum_of_summable_norm (summable_norm_thT _ _ τ1_im) (summable_norm_thT _ _ τ2_im),
    ← tsum_mul_left, ← (piFinTwoEquiv fun _ => ℤ).symm.tsum_eq]
  congr 1
  funext p
  simp only [piFinTwoEquiv_symm_apply, thT]
  rw [← Complex.exp_add, ← Complex.exp_add]
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨p.1 * p.2, ?_⟩
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Omega0, τ1, τ2, Fin.cons_zero,
    Fin.cons_one, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one]
  push_cast
  ring

/-! ### Phases of the one-variable terms -/

theorem exp_int_piI (k : ℤ) : cexp ((k : ℂ) * (Real.pi * I)) = (-1) ^ k := by
  rw [Complex.exp_int_mul, Complex.exp_pi_mul_I]

/-- A tsum of terms `ω · (real)` is `ω · (real)`. -/
theorem tsum_ofReal_mul (ω : ℂ) (f : ℤ → ℂ) (h : ∀ n, ∃ r : ℝ, f n = ω * r) :
    ∃ ρ : ℝ, ∑' n, f n = ω * ρ := by
  choose r hr using h
  refine ⟨∑' n, r n, ?_⟩
  rw [Complex.ofReal_tsum, ← tsum_mul_left]
  exact tsum_congr hr

theorem thT_τ2_zero (b : ℕ) (n : ℤ) :
    thT 0 b τ2 n = (((-1 : ℝ) ^ (n * (b : ℤ) - n ^ 2) * Real.exp (-Real.pi * (n : ℝ) ^ 2) : ℝ) : ℂ) := by
  have e : Real.pi * I * ((n : ℂ) + ((0 : ℕ) : ℂ) / 2) ^ 2 * τ2 +
      Real.pi * I * ((n : ℂ) + ((0 : ℕ) : ℂ) / 2) * (b : ℂ) =
      ((-Real.pi * (n : ℝ) ^ 2 : ℝ) : ℂ) + ((n * (b : ℤ) - n ^ 2 : ℤ) : ℂ) * (Real.pi * I) := by
    simp only [τ2]; push_cast
    linear_combination (Real.pi * (n : ℂ) ^ 2) * Complex.I_sq
  unfold thT
  rw [e, Complex.exp_add, exp_int_piI, ← Complex.ofReal_exp]
  push_cast; ring

theorem thT_τ2_one (b : ℕ) (n : ℤ) :
    thT 1 b τ2 n = cexp (Real.pi * I * ((b : ℂ) / 2 - 1 / 4)) *
      (((-1 : ℝ) ^ (n * (b : ℤ) - n ^ 2 - n) *
        Real.exp (-Real.pi * ((n : ℝ) + 1 / 2) ^ 2) : ℝ) : ℂ) := by
  have e : Real.pi * I * ((n : ℂ) + ((1 : ℕ) : ℂ) / 2) ^ 2 * τ2 +
      Real.pi * I * ((n : ℂ) + ((1 : ℕ) : ℂ) / 2) * (b : ℂ) =
      ((-Real.pi * ((n : ℝ) + 1 / 2) ^ 2 : ℝ) : ℂ) +
        ((n * (b : ℤ) - n ^ 2 - n : ℤ) : ℂ) * (Real.pi * I) +
        Real.pi * I * ((b : ℂ) / 2 - 1 / 4) := by
    simp only [τ2]; push_cast
    linear_combination (Real.pi * ((n : ℂ) + 1 / 2) ^ 2) * Complex.I_sq
  unfold thT
  rw [e, Complex.exp_add, Complex.exp_add, exp_int_piI, ← Complex.ofReal_exp]
  push_cast; ring

theorem thT_τ1_one (b : ℕ) (n : ℤ) : ∃ r : ℝ,
    thT 1 b τ1 n = cexp (Real.pi * I * ((b : ℂ) / 2 - 1 / 8)) * r := by
  obtain ⟨k, hk⟩ := Int.even_mul_succ_self n
  have hk' : (n : ℂ) ^ 2 + n = 2 * k := by
    have := congrArg (fun t : ℤ => (t : ℂ)) hk
    push_cast at this; linear_combination this
  refine ⟨(-1 : ℝ) ^ (n * (b : ℤ) - k) * Real.exp (-Real.pi * ((n : ℝ) + 1 / 2) ^ 2 / 2), ?_⟩
  have e : Real.pi * I * ((n : ℂ) + ((1 : ℕ) : ℂ) / 2) ^ 2 * τ1 +
      Real.pi * I * ((n : ℂ) + ((1 : ℕ) : ℂ) / 2) * (b : ℂ) =
      ((-Real.pi * ((n : ℝ) + 1 / 2) ^ 2 / 2 : ℝ) : ℂ) +
        ((n * (b : ℤ) - k : ℤ) : ℂ) * (Real.pi * I) +
        Real.pi * I * ((b : ℂ) / 2 - 1 / 8) := by
    simp only [τ1]; push_cast
    linear_combination (Real.pi * ((n : ℂ) + 1 / 2) ^ 2 / 2) * Complex.I_sq +
      (-(Real.pi * I) / 2) * hk'
  unfold thT
  rw [e, Complex.exp_add, Complex.exp_add, exp_int_piI, ← Complex.ofReal_exp]
  push_cast; ring

theorem omega_τ2_pow (b : ℕ) : cexp (Real.pi * I * ((b : ℂ) / 2 - 1 / 4)) ^ 8 = 1 := by
  rw [← Complex.exp_nat_mul]
  have : ((8 : ℕ) : ℂ) * (Real.pi * I * ((b : ℂ) / 2 - 1 / 4)) =
      ((4 * (b : ℤ) - 2 : ℤ) : ℂ) * (Real.pi * I) := by push_cast; ring
  rw [this, exp_int_piI]
  exact Even.neg_one_zpow ⟨2 * (b : ℤ) - 1, by ring⟩

theorem omega_τ1_pow (b : ℕ) : cexp (Real.pi * I * ((b : ℂ) / 2 - 1 / 8)) ^ 8 = -1 := by
  rw [← Complex.exp_nat_mul]
  have : ((8 : ℕ) : ℂ) * (Real.pi * I * ((b : ℂ) / 2 - 1 / 8)) =
      ((4 * (b : ℤ) - 1 : ℤ) : ℂ) * (Real.pi * I) := by push_cast; ring
  rw [this, exp_int_piI]
  exact Odd.neg_one_zpow ⟨2 * (b : ℤ) - 1, by ring⟩

/-- `Θ[a,b](τ₂)⁸` is a non-negative real number (`a ∈ {0, 1}`). -/
theorem th1_τ2 (a b : ℕ) (ha : a = 0 ∨ a = 1) : ∃ ρ : ℝ, th1 a b τ2 ^ 8 = ((ρ ^ 8 : ℝ) : ℂ) := by
  rcases ha with rfl | rfl
  · obtain ⟨ρ, hρ⟩ := tsum_ofReal_mul 1 (thT 0 b τ2) fun n => ⟨_, by rw [thT_τ2_zero, one_mul]⟩
    refine ⟨ρ, ?_⟩
    unfold th1; rw [hρ, one_mul]; push_cast; ring
  · obtain ⟨ρ, hρ⟩ := tsum_ofReal_mul _ (thT 1 b τ2) fun n => ⟨_, thT_τ2_one b n⟩
    refine ⟨ρ, ?_⟩
    unfold th1; rw [hρ, mul_pow, omega_τ2_pow, one_mul]; push_cast; ring

/-- `Θ[1,b](τ₁)⁸ = −R⁸` with `R` real. -/
theorem th1_τ1_one (b : ℕ) : ∃ R : ℝ, th1 1 b τ1 ^ 8 = -((R ^ 8 : ℝ) : ℂ) := by
  obtain ⟨R, hR⟩ := tsum_ofReal_mul _ (thT 1 b τ1) (thT_τ1_one b)
  refine ⟨R, ?_⟩
  unfold th1; rw [hR, mul_pow, omega_τ1_pow]; push_cast; ring

/-! ### `Θ[0,b](τ₁)`: real and imaginary parts -/

/-- `E(n) = e^{−πn²/2} = |Θ[0,b](τ₁)`'s `n`-th term`|`. -/
def Eg (n : ℤ) : ℝ := Real.exp (-Real.pi * (n : ℝ) ^ 2 / 2)

theorem thT_τ1_zero_even (b : ℕ) (m : ℤ) : thT 0 b τ1 (2 * m) = ((Eg (2 * m) : ℝ) : ℂ) := by
  have e : Real.pi * I * (((2 * m : ℤ) : ℂ) + ((0 : ℕ) : ℂ) / 2) ^ 2 * τ1 +
      Real.pi * I * (((2 * m : ℤ) : ℂ) + ((0 : ℕ) : ℂ) / 2) * (b : ℂ) =
      ((-Real.pi * ((2 * m : ℤ) : ℝ) ^ 2 / 2 : ℝ) : ℂ) +
        ((2 * (m * (b : ℤ) - m ^ 2) : ℤ) : ℂ) * (Real.pi * I) := by
    simp only [τ1]; push_cast
    linear_combination (Real.pi * (2 * (m : ℂ)) ^ 2 / 2) * Complex.I_sq
  unfold thT Eg
  rw [e, Complex.exp_add, exp_int_piI, Even.neg_one_zpow ⟨m * (b : ℤ) - m ^ 2, by ring⟩, mul_one,
    ← Complex.ofReal_exp]

theorem exp_neg_pi_div_two_I : cexp (Real.pi * I * (-1 / 2)) = -I := by
  have : Real.pi * I * (-1 / 2) = ((-(Real.pi / 2) : ℝ) : ℂ) * I := by push_cast; ring
  rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg,
    Real.sin_neg, Real.cos_pi_div_two, Real.sin_pi_div_two]
  push_cast; ring

theorem thT_τ1_zero_odd (b : ℕ) (m : ℤ) :
    thT 0 b τ1 (2 * m + 1) = ((Eg (2 * m + 1) : ℝ) : ℂ) * ((((-1 : ℝ) ^ b : ℝ) : ℂ) * (-I)) := by
  have e : Real.pi * I * (((2 * m + 1 : ℤ) : ℂ) + ((0 : ℕ) : ℂ) / 2) ^ 2 * τ1 +
      Real.pi * I * (((2 * m + 1 : ℤ) : ℂ) + ((0 : ℕ) : ℂ) / 2) * (b : ℂ) =
      ((-Real.pi * ((2 * m + 1 : ℤ) : ℝ) ^ 2 / 2 : ℝ) : ℂ) +
        ((2 * (m * (b : ℤ) - m ^ 2 - m) : ℤ) : ℂ) * (Real.pi * I) + ((b : ℤ) : ℂ) * (Real.pi * I) +
        Real.pi * I * (-1 / 2) := by
    simp only [τ1]; push_cast
    linear_combination (Real.pi * (2 * (m : ℂ) + 1) ^ 2 / 2) * Complex.I_sq
  unfold thT Eg
  rw [e, Complex.exp_add, Complex.exp_add, Complex.exp_add, exp_int_piI, exp_int_piI,
    Even.neg_one_zpow ⟨m * (b : ℤ) - m ^ 2 - m, by ring⟩, exp_neg_pi_div_two_I,
    ← Complex.ofReal_exp, zpow_natCast]
  push_cast; ring

theorem Eg_nonneg (n : ℤ) : 0 ≤ Eg n := (Real.exp_pos _).le

/-- The real part, the sign `σ` and the (non-negative) imaginary weight of the terms. -/
theorem thT_τ1_zero_parts (b : ℕ) (n : ℤ) :
    0 ≤ (thT 0 b τ1 n).re ∧ 0 ≤ (-(-1 : ℝ) ^ b) * (thT 0 b τ1 n).im ∧
      (thT 0 b τ1 n).re + (-(-1 : ℝ) ^ b) * (thT 0 b τ1 n).im = Eg n := by
  have hb : ((-1 : ℝ) ^ b) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' n
  · rw [thT_τ1_zero_even]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, add_zero, le_refl, and_true]
    exact Eg_nonneg _
  · rw [thT_τ1_zero_odd]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
    refine ⟨by simp, ?_, ?_⟩
    · have := Eg_nonneg (2 * m + 1)
      nlinarith [hb]
    · linear_combination (Eg (2 * m + 1)) * hb

theorem thT_τ1_zero_at0 (b : ℕ) : (thT 0 b τ1 0).re = 1 := by
  have := thT_τ1_zero_even b 0
  rw [mul_zero] at this
  rw [this]; simp [Eg]

theorem thT_τ1_zero_at1 (b : ℕ) (n : ℤ) (hn : n = 1 ∨ n = -1) :
    (-(-1 : ℝ) ^ b) * (thT 0 b τ1 n).im = Real.exp (-Real.pi / 2) := by
  have hb : ((-1 : ℝ) ^ b) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have key : ∀ m : ℤ, (2 * m + 1 = 1 ∨ 2 * m + 1 = -1) →
      (-(-1 : ℝ) ^ b) * (thT 0 b τ1 (2 * m + 1)).im = Real.exp (-Real.pi / 2) := by
    intro m hm
    rw [thT_τ1_zero_odd]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
      Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
    have hE : Eg (2 * m + 1) = Real.exp (-Real.pi / 2) := by
      unfold Eg; congr 1
      rcases hm with h | h <;> rw [show (((2 * m + 1 : ℤ)) : ℝ) = ((2 * m + 1 : ℤ) : ℝ) from rfl, h] <;>
        push_cast <;> ring
    rw [hE]; linear_combination (Real.exp (-Real.pi / 2)) * hb
  rcases hn with rfl | rfl
  · have h := key 0 (by norm_num)
    rwa [show (2 * 0 + 1 : ℤ) = 1 by norm_num] at h
  · have h := key (-1) (by norm_num)
    rwa [show (2 * (-1) + 1 : ℤ) = -1 by norm_num] at h

/-! ### Crude bounds and the sign of `Re Θ[0,b](τ₁)⁸` -/

theorem hasSum_geom_int {s : ℝ} (h0 : 0 ≤ s) (h1 : s < 1) :
    HasSum (fun n : ℤ => s ^ n.natAbs) ((1 - s)⁻¹ + s * (1 - s)⁻¹) := by
  apply HasSum.of_nat_of_neg_add_one
  · convert hasSum_geometric_of_lt_one h0 h1 using 1
    funext n; simp
  · convert (hasSum_geometric_of_lt_one h0 h1).mul_left s using 1
    funext n
    rw [show (-((n : ℤ) + 1)).natAbs = n + 1 by omega, pow_succ, mul_comm]

theorem Eg_le (n : ℤ) : Eg n ≤ Real.exp (Real.pi / 2) * Real.exp (-Real.pi) ^ n.natAbs -
    (if n = 0 then Real.exp (Real.pi / 2) - 1 else 0) := by
  by_cases hn : n = 0
  · subst hn; simp [Eg]
  · rw [ite_eq_right_iff.mpr (fun h => absurd h hn), sub_zero, ← Real.exp_nat_mul, ← Real.exp_add]
    unfold Eg
    apply Real.exp_le_exp.mpr
    have ha : ((n.natAbs : ℕ) : ℝ) = |(n : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
    rw [ha]
    nlinarith [Real.pi_pos, sq_nonneg (|(n : ℝ)| - 1), sq_abs (n : ℝ)]

theorem re_pow8 (x y : ℝ) : (((x : ℂ) + (y : ℂ) * I) ^ 8).re =
    x ^ 8 - 28 * x ^ 6 * y ^ 2 + 70 * x ^ 4 * y ^ 4 - 28 * x ^ 2 * y ^ 6 + y ^ 8 := by
  simp [pow_succ, Complex.mul_re, Complex.mul_im]
  ring

theorem q_lower : (0.173 : ℝ) ≤ Real.exp (-Real.pi / 2) := by
  have h8 : Real.exp (-Real.pi / 2) = Real.exp (-Real.pi / 16) ^ 8 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h1 : 1 - Real.pi / 16 ≤ Real.exp (-Real.pi / 16) := by
    have := Real.add_one_le_exp (-Real.pi / 16); linarith
  have h2 : (0.803125 : ℝ) ≤ 1 - Real.pi / 16 := by have := Real.pi_lt_d2; linarith
  rw [h8]
  calc (0.173 : ℝ) ≤ 0.803125 ^ 8 := by norm_num
    _ ≤ Real.exp (-Real.pi / 16) ^ 8 := pow_le_pow_left₀ (by norm_num) (h2.trans h1) 8

theorem q_upper : Real.exp (-Real.pi / 2) ≤ (0.2532 : ℝ) := by
  have h8 : Real.exp (Real.pi / 2) = Real.exp (Real.pi / 16) ^ 8 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h1 : 1 + Real.pi / 16 ≤ Real.exp (Real.pi / 16) := by
    have := Real.add_one_le_exp (Real.pi / 16); linarith
  have h2 : (1.1875 : ℝ) ≤ 1 + Real.pi / 16 := by have := Real.pi_gt_three; linarith
  have h3 : (3.95 : ℝ) ≤ Real.exp (Real.pi / 2) := by
    rw [h8]
    calc (3.95 : ℝ) ≤ 1.1875 ^ 8 := by norm_num
      _ ≤ Real.exp (Real.pi / 16) ^ 8 := pow_le_pow_left₀ (by norm_num) (h2.trans h1) 8
  have h4 : Real.exp (-Real.pi / 2) = (Real.exp (Real.pi / 2))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; ring
  rw [h4]
  calc (Real.exp (Real.pi / 2))⁻¹ ≤ (3.95 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h3
    _ ≤ 0.2532 := by norm_num

theorem poly8_neg (p u : ℝ) (hp1 : 1 ≤ p) (hp2 : p ≤ 1.0707) (hu1 : 0.1197 ≤ u)
    (hu2 : u ≤ 0.2928) :
    p ^ 4 - 28 * p ^ 3 * u + 70 * p ^ 2 * u ^ 2 - 28 * p * u ^ 3 + u ^ 4 < 0 := by
  have h1 : 0 ≤ u - 0.11 * p := by linarith
  have h2 : 0 ≤ 0.293 * p - u := by linarith
  have h3 : 0 < p * (1.2561 * p - 0.21 * u) := mul_pos (by linarith) (by linarith)
  have key : p ^ 2 - 28 * p * u + 70 * u ^ 2 < 0 := by nlinarith [mul_nonneg h1 h2]
  have hu3 : 0 ≤ u ^ 3 * (28 * p - u) := mul_nonneg (by positivity) (by linarith)
  have h4 : 0 < p ^ 2 * -(p ^ 2 - 28 * p * u + 70 * u ^ 2) :=
    mul_pos (by positivity) (neg_pos.mpr key)
  nlinarith [h4, hu3]

theorem q_frac_bounds (q : ℝ) (hq1 : 0.173 ≤ q) (hq2 : q ≤ 0.2532) :
    2 * q ^ 3 / (1 - q ^ 2) ≤ 0.0347 ∧ 2 * q / (1 - q ^ 2) ≤ 0.5411 := by
  have h0 : 0 ≤ q := by linarith
  have hq2' : q ^ 2 ≤ 0.2532 ^ 2 := pow_le_pow_left₀ h0 hq2 2
  have hq3 : q ^ 3 ≤ 0.2532 ^ 3 := pow_le_pow_left₀ h0 hq2 3
  have hd : 0 < 1 - q ^ 2 := by nlinarith
  constructor
  · rw [div_le_iff₀ hd]; nlinarith
  · rw [div_le_iff₀ hd]; nlinarith

set_option maxHeartbeats 1000000 in
/-- **`Re Θ[0,b](τ₁)⁸ < 0` (proved).** -/
theorem re_th1_τ1_zero (b : ℕ) : (th1 0 b τ1 ^ 8).re < 0 := by
  set σ : ℝ := -(-1 : ℝ) ^ b with hσdef
  have hσ : σ ^ 2 = 1 := by
    rw [hσdef, neg_sq, ← pow_mul, mul_comm, pow_mul]; norm_num
  have hsum := summable_thT 0 b τ1_im
  have hre : Summable (fun n => (thT 0 b τ1 n).re) := Complex.reCLM.summable hsum
  have him : Summable (fun n => (thT 0 b τ1 n).im) := Complex.imCLM.summable hsum
  have hen : Summable (fun n => σ * (thT 0 b τ1 n).im) := him.mul_left σ
  set P := ∑' n, (thT 0 b τ1 n).re with hPdef
  set Es := ∑' n, σ * (thT 0 b τ1 n).im with hEdef
  have hΘ : th1 0 b τ1 = (P : ℂ) + ((σ * Es : ℝ) : ℂ) * I := by
    apply Complex.ext
    · simp [th1, Complex.re_tsum hsum, hPdef]
    · simp only [th1, Complex.im_tsum hsum, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, hEdef]
      rw [tsum_mul_left, ← mul_assoc, ← sq, hσ, one_mul]
      simp
  have hP1 : 1 ≤ P := by
    rw [← thT_τ1_zero_at0 b]
    exact hre.le_tsum 0 (fun j _ => (thT_τ1_zero_parts b j).1)
  set q := Real.exp (-Real.pi / 2) with hq
  have hE1 : 2 * q ≤ Es := by
    have := hen.sum_le_tsum {1, -1} (fun j _ => (thT_τ1_zero_parts b j).2.1)
    rw [Finset.sum_pair (by norm_num), thT_τ1_zero_at1 b 1 (Or.inl rfl),
      thT_τ1_zero_at1 b (-1) (Or.inr rfl)] at this
    linarith
  have hq1 := q_lower
  have hq2 := q_upper
  rw [← hq] at hq1 hq2
  have hs : Real.exp (-Real.pi) = q ^ 2 := by
    rw [hq, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hqi : Real.exp (Real.pi / 2) = q⁻¹ := by
    rw [hq, ← Real.exp_neg]; congr 1; ring
  have hs1 : q ^ 2 < 1 := by nlinarith
  have hM := ((hasSum_geom_int (s := Real.exp (-Real.pi)) (Real.exp_pos _).le
    (by rw [hs]; exact hs1)).mul_left (Real.exp (Real.pi / 2))).sub
    (hasSum_ite_eq (0 : ℤ) (Real.exp (Real.pi / 2) - 1))
  have hG : P + Es ≤ 1 + 2 * q / (1 - q ^ 2) := by
    rw [hPdef, hEdef, ← hre.tsum_add hen]
    refine ((hre.add hen).tsum_le_tsum (fun n => ?_) hM.summable).trans (le_of_eq ?_)
    · rw [(thT_τ1_zero_parts b n).2.2]
      exact Eg_le n
    · rw [hM.tsum_eq, hs, hqi]
      have hq0 : q ≠ 0 := (Real.exp_pos _).ne'
      have h1q : 1 - q ^ 2 ≠ 0 := by nlinarith
      field_simp
      ring
  have hPup : P ≤ 1 + 2 * q ^ 3 / (1 - q ^ 2) := by
    have h1q : 0 < 1 - q ^ 2 := by nlinarith
    have : 2 * q / (1 - q ^ 2) - 2 * q = 2 * q ^ 3 / (1 - q ^ 2) := by
      field_simp; ring
    linarith
  obtain ⟨hb1, hb2⟩ := q_frac_bounds q hq1 hq2
  have hPb : P ≤ 1.0347 := by linarith
  have hEb : Es ≤ 0.5411 := by linarith
  have hEl : 0.346 ≤ Es := by linarith
  rw [hΘ, re_pow8]
  set p := P ^ 2 with hp
  set u := Es ^ 2 with hu
  have e : P ^ 8 - 28 * P ^ 6 * (σ * Es) ^ 2 + 70 * P ^ 4 * (σ * Es) ^ 4 -
      28 * P ^ 2 * (σ * Es) ^ 6 + (σ * Es) ^ 8 =
      p ^ 4 - 28 * p ^ 3 * u + 70 * p ^ 2 * u ^ 2 - 28 * p * u ^ 3 + u ^ 4 := by
    have h2 : (σ * Es) ^ 2 = u := by rw [mul_pow, hσ, one_mul]
    have h4 : (σ * Es) ^ 4 = u ^ 2 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h2]
    have h6 : (σ * Es) ^ 6 = u ^ 3 := by rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, h2]
    have h8 : (σ * Es) ^ 8 = u ^ 4 := by rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, h2]
    rw [h2, h4, h6, h8, hp]; ring
  rw [e]
  have hP0 : 0 ≤ P := by linarith
  have hE0 : 0 ≤ Es := by linarith
  exact poly8_neg p u (by rw [hp]; nlinarith) (by rw [hp]; nlinarith) (by rw [hu]; nlinarith)
    (by rw [hu]; nlinarith)

/-! ### Assembly -/

theorem fin2_val (x : Fin 2) : (x : ℕ) = 0 ∨ (x : ℕ) = 1 := by have := x.isLt; omega

theorem u_pow8 (a1 a2 : ℕ) :
    cexp (-(Real.pi * I * (a1 : ℂ) * (a2 : ℂ) / 2)) ^ 8 = 1 := by
  rw [← Complex.exp_nat_mul]
  have : ((8 : ℕ) : ℂ) * -(Real.pi * I * (a1 : ℂ) * (a2 : ℂ) / 2) =
      ((-2 * (a1 : ℤ) * a2 : ℤ) : ℂ) * (2 * Real.pi * I) := by push_cast; ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

/-- **Every `θ_m(Ω₀)⁸` has non-positive real part (proved).** -/
theorem re_theta8_nonpos (m : PkgI1.Char2) : (PkgI1.thetaConst m Omega0 ^ 8).re ≤ 0 := by
  rw [thetaConst_factor, mul_pow, u_pow8, one_mul, mul_pow]
  obtain ⟨ρ, hρ⟩ := th1_τ2 (m.1 1 : ℕ) ((m.2 1 : ℕ) + (m.1 0 : ℕ)) (fin2_val _)
  rw [hρ, Complex.re_mul_ofReal]
  have hρ8 : 0 ≤ ρ ^ 8 := Even.pow_nonneg ⟨4, by norm_num⟩ ρ
  rcases fin2_val (m.1 0) with h | h
  · rw [h]
    exact mul_nonpos_of_nonpos_of_nonneg (re_th1_τ1_zero _).le hρ8
  · rw [h]
    obtain ⟨R, hR⟩ := th1_τ1_one ((m.2 0 : ℕ) + (m.1 1 : ℕ))
    rw [hR]
    simp only [Complex.neg_re, Complex.ofReal_re]
    have hR8 : 0 ≤ R ^ 8 := Even.pow_nonneg ⟨4, by norm_num⟩ R
    nlinarith [mul_nonneg hR8 hρ8]

/-- `Θ[0,1](τ₂) = Σ e^{−πn²} ≥ 1`. -/
theorem th1_τ2_01 : ∃ ρ : ℝ, 1 ≤ ρ ∧ th1 0 1 τ2 = ρ := by
  have hterm : ∀ n : ℤ, thT 0 1 τ2 n = ((Real.exp (-Real.pi * (n : ℝ) ^ 2) : ℝ) : ℂ) := by
    intro n
    rw [thT_τ2_zero]
    have hev : Even (n * ((1 : ℕ) : ℤ) - n ^ 2) := by
      obtain ⟨k, hk⟩ := Int.even_mul_succ_self (n - 1)
      exact ⟨-k, by push_cast; linear_combination (-1 : ℤ) * hk⟩
    rw [hev.neg_one_zpow, one_mul]
  have hsum := summable_thT 0 1 τ2_im
  have hre : Summable (fun n => (thT 0 1 τ2 n).re) := Complex.reCLM.summable hsum
  have hre' : ∀ n, (thT 0 1 τ2 n).re = Real.exp (-Real.pi * (n : ℝ) ^ 2) := fun n => by
    rw [hterm, Complex.ofReal_re]
  refine ⟨∑' n, (thT 0 1 τ2 n).re, ?_, ?_⟩
  · have h0 := hre.le_tsum 0 (fun j _ => by rw [hre']; exact (Real.exp_pos _).le)
    rw [hre'] at h0
    simpa using h0
  · rw [Complex.ofReal_tsum]
    unfold th1
    exact tsum_congr fun n => by rw [hre', hterm]

/-- The characteristic `((0,0),(0,1))`. -/
def m0 : PkgI1.Char2 := (![0, 0], ![0, 1])

theorem re_theta8_m0 : (PkgI1.thetaConst m0 Omega0 ^ 8).re < 0 := by
  rw [thetaConst_factor, mul_pow, u_pow8, one_mul, mul_pow]
  have e1 : ((m0.1 0 : Fin 2) : ℕ) = 0 := rfl
  have e2 : ((m0.1 1 : Fin 2) : ℕ) = 0 := rfl
  have e3 : ((m0.2 0 : Fin 2) : ℕ) = 0 := rfl
  have e4 : ((m0.2 1 : Fin 2) : ℕ) = 1 := rfl
  rw [e1, e2, e3, e4]
  obtain ⟨ρ, hρ1, hρ⟩ := th1_τ2_01
  rw [show (1 + 0 : ℕ) = 1 from rfl, show (0 + 0 : ℕ) = 0 from rfl, hρ, ← Complex.ofReal_pow,
    Complex.re_mul_ofReal]
  have : 0 < ρ ^ 8 := by positivity
  exact mul_neg_of_neg_of_pos (re_th1_τ1_zero 0) this

/-- **`S8Omega0` (proved): `Re Σθ⁸(Ω₀) < 0`.** -/
theorem s8Omega0_re_neg : (PkgI1.thetaSum8 Omega0).re < 0 := by
  unfold PkgI1.thetaSum8
  rw [Complex.re_sum]
  have hm0 : m0 ∈ PkgI1.evenChars := by decide
  rw [← Finset.add_sum_erase _ _ hm0]
  have hrest : ∑ x ∈ PkgI1.evenChars.erase m0, (PkgI1.thetaConst x Omega0 ^ 8).re ≤ 0 :=
    Finset.sum_nonpos fun m _ => re_theta8_nonpos m
  linarith [re_theta8_m0]

theorem s8Omega0_proof : S8Omega0 := fun h => by
  have := s8Omega0_re_neg
  rw [h, Complex.zero_re] at this
  exact lt_irrefl 0 this

/-- **`S8Nonzero` (proved).** -/
theorem s8Nonzero_proof : S8Nonzero := s8Nonzero_of s8Omega0_proof

end HSyn.G0Split.FibreQM.PeriodGlue

#print axioms HSyn.G0Split.FibreQM.PeriodGlue.s8Nonzero_iff
#print axioms HSyn.G0Split.FibreQM.PeriodGlue.s8Nonzero_proof
