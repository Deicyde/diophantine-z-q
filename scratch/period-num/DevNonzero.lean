import PNBase

/-! ## period-num: `S8Nonzero` proved

`Ω(√2 + i) = [[(−1+i)/2, 1], [1, −1+i]]` (exact; `omega_s2I`). Because the off-diagonal entry is `1`,
each genus-2 theta constant splits as a product of two genus-1 theta constants with characteristics
(`thetaConst_split`), and
`Σ_{m even} θ_m⁸(Ω(√2+i)) = (Z₀⁸ + Z₁⁸ + T⁸)(P₀⁸ + P₁⁸ + Q⁸)` (`thetaSum8_s2I`), with
`Z_b = ϑ[0,b]((−1+i)/2)`, `T = ϑ[1,0]((−1+i)/2)`, `P_b = ϑ[0,b](−1+i)`, `Q = ϑ[1,0](−1+i)`.
* `P₀, P₁` are real and `Q = e^{−iπ/4}R` with `R > 0`, so the second factor is a positive real.
* `T = e^{−iπ/8}C` with `C` real, so `Re T⁸ = −C⁸ ≤ 0`; `Z₀ = 1 − 2ie^{−π/2} + O(e^{−2π})` and
  `Z₁ = 1 + 2ie^{−π/2} + O(e^{−2π})`, so `Re Z_b⁸ < 0` (certified with `e^{π/2} ∈ (4.41, 7.39)`,
  `e^{−π} < 1/20`, tail `≤ e^{−2π}/(1−e^{−π}) < 1/380`). Hence `Re` of the first factor is `< 0`. -/

noncomputable section

namespace HSyn.G0Split.FibreQM.PeriodNum

open Complex
open scoped Real
open HSyn.G0Split.FibreQM.PeriodMap

/-! ### `Ω(√2 + i)` -/

/-- The period matrix at `√2 + i`. -/
def Om0 : Matrix (Fin 2) (Fin 2) ℂ := !![(-1 + I) / 2, 1; 1, -1 + I]

theorem dF_s2I_ne : dF ((√2 : ℂ) + I) ≠ 0 := by
  have h2 : (√2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]; positivity
  have ha : (√2 : ℂ) + I - 3 ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this
  have hb : (√2 : ℂ) + I + 1 ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this
  simp only [dF]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr h2) ha) hb) two_ne_zero

theorem omega_s2I : PkgI1.Omega ((√2 : ℂ) + I) = Om0 := by
  ext i j
  rw [omega_eq, div_eq_iff dF_s2I_ne]
  fin_cases i <;> fin_cases j <;> simp only [Nf, Om0, dF, Fin.zero_eta, Fin.mk_one, Fin.isValue,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  · linear_combination (1 + 1 / 2 * I * I + 1 / 4 * (√2 : ℂ) + 1 / 4 * (√2 : ℂ) * I) * sqrt2_sq +
      (1 / 2 - 1 / 4 * (√2 : ℂ) + 1 / 4 * (√2 : ℂ) * I) * I_sq
  · linear_combination (-1 : ℂ) * sqrt2_sq + (1 : ℂ) * I_sq
  · linear_combination (-1 : ℂ) * sqrt2_sq + (1 : ℂ) * I_sq
  · linear_combination (2 + I * I + 1 / 2 * (√2 : ℂ) + 1 / 2 * (√2 : ℂ) * I) * sqrt2_sq +
      (1 - 1 / 2 * (√2 : ℂ) + 1 / 2 * (√2 : ℂ) * I) * I_sq

/-! ### Genus-one theta constants with characteristics -/

/-- The term `exp(πi(n + a/2)²w + πi(n + a/2)b)`. -/
def thT (a b w : ℂ) (n : ℤ) : ℂ :=
  cexp (π * I * ((n : ℂ) + a / 2) ^ 2 * w + π * I * ((n : ℂ) + a / 2) * b)

/-- `ϑ[a, b](w) = Σ_n exp(πi(n + a/2)²w + πi(n + a/2)b)`. -/
def th1 (a b w : ℂ) : ℂ := ∑' n : ℤ, thT a b w n

theorem thT_eq (a b w : ℂ) (n : ℤ) :
    thT a b w n = cexp (π * I * a ^ 2 * w / 4 + π * I * a * b / 2) *
      jacobiTheta₂_term n (a * w / 2 + b / 2) w := by
  rw [thT, jacobiTheta₂_term, ← Complex.exp_add]; congr 1; ring

theorem summable_norm_thT (a b : ℂ) {w : ℂ} (hw : 0 < w.im) :
    Summable (fun n => ‖thT a b w n‖) := by
  have h := (summable_jacobiTheta₂_term_iff (a * w / 2 + b / 2) w).mpr hw
  have h2 : Summable (fun n => thT a b w n) := by
    simp_rw [thT_eq]; exact h.mul_left _
  exact summable_norm_iff.mpr h2

theorem exp_add_int_mul (z : ℂ) (k : ℤ) : cexp (z + k * (2 * π * I)) = cexp z := by
  rw [Complex.exp_add, exp_int_mul_two_pi_mul_I, mul_one]

/-! ### Splitting the genus-2 theta constants at `[[w₁, 1], [1, w₂]]` -/

theorem thetaConst_split (m : PkgI1.Char2) (w1 w2 : ℂ) (h1 : 0 < w1.im) (h2 : 0 < w2.im) :
    PkgI1.thetaConst m !![w1, 1; 1, w2] =
      cexp (-(π * I * ((m.1 0 : ℕ) : ℂ) * ((m.1 1 : ℕ) : ℂ) / 2)) *
        (th1 ((m.1 0 : ℕ) : ℂ) (((m.2 0 : ℕ) : ℂ) + ((m.1 1 : ℕ) : ℂ)) w1 *
         th1 ((m.1 1 : ℕ) : ℂ) (((m.2 1 : ℕ) : ℂ) + ((m.1 0 : ℕ) : ℂ)) w2) := by
  set a0 : ℂ := ((m.1 0 : ℕ) : ℂ)
  set a1 : ℂ := ((m.1 1 : ℕ) : ℂ)
  set b0 : ℂ := ((m.2 0 : ℕ) : ℂ)
  set b1 : ℂ := ((m.2 1 : ℕ) : ℂ)
  set c : ℂ := cexp (-(π * I * a0 * a1 / 2))
  set f1 : ℤ → ℂ := thT a0 (b0 + a1) w1
  set f2 : ℤ → ℂ := thT a1 (b1 + a0) w2
  have e1 : PkgI1.thetaConst m !![w1, 1; 1, w2] = ∑' n : Fin 2 → ℤ, c * (f1 (n 0) * f2 (n 1)) := by
    unfold PkgI1.thetaConst
    refine tsum_congr fun n => ?_
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      f1, f2, c, thT, ← Complex.exp_add]
    conv_rhs => rw [← exp_add_int_mul _ (n 0 * n 1)]
    congr 1
    simp only [a0, a1, b0, b1]
    push_cast
    ring
  have e2 : ∑' n : Fin 2 → ℤ, f1 (n 0) * f2 (n 1) = ∑' p : ℤ × ℤ, f1 p.1 * f2 p.2 := by
    rw [← (finTwoArrowEquiv ℤ).symm.tsum_eq]
    rfl
  rw [e1, tsum_mul_left, e2,
    ← tsum_mul_tsum_of_summable_norm (summable_norm_thT _ _ h1) (summable_norm_thT _ _ h2)]
  rfl

/-! ### Elementary identities -/

theorem th1_zero_two (w : ℂ) : th1 0 2 w = th1 0 0 w := by
  unfold th1
  refine tsum_congr fun n => ?_
  simp only [thT]
  conv_rhs => rw [← exp_add_int_mul _ n]
  congr 1
  ring

theorem th1_one_two (w : ℂ) : th1 1 2 w = -th1 1 0 w := by
  unfold th1
  rw [← tsum_neg]
  refine tsum_congr fun n => ?_
  simp only [thT]
  have : π * I * ((n : ℂ) + 1 / 2) ^ 2 * w + π * I * ((n : ℂ) + 1 / 2) * 2 =
      (π * I * ((n : ℂ) + 1 / 2) ^ 2 * w + π * I * ((n : ℂ) + 1 / 2) * 0 + π * I) +
        (n : ℂ) * (2 * π * I) := by ring
  rw [this, exp_add_int_mul, Complex.exp_add, exp_pi_mul_I]
  ring

theorem th1_one_one (w : ℂ) : th1 1 1 w = 0 := by
  have h : th1 1 1 w = -th1 1 1 w := by
    unfold th1
    rw [← tsum_neg, ← (Equiv.subLeft (-1 : ℤ)).tsum_eq]
    refine tsum_congr fun n => ?_
    simp only [thT, Equiv.subLeft_apply]
    have : π * I * ((((-1 - n : ℤ)) : ℂ) + 1 / 2) ^ 2 * w + π * I * ((((-1 - n : ℤ)) : ℂ) + 1 / 2) * 1
        = (π * I * ((n : ℂ) + 1 / 2) ^ 2 * w + π * I * ((n : ℂ) + 1 / 2) * 1 + π * I) +
          ((-n - 1 : ℤ) : ℂ) * (2 * π * I) := by push_cast; ring
    rw [this, exp_add_int_mul, Complex.exp_add, exp_pi_mul_I]
    ring
  have : (2 : ℂ) * th1 1 1 w = 0 := by linear_combination h
  simpa using this

end HSyn.G0Split.FibreQM.PeriodNum

end
