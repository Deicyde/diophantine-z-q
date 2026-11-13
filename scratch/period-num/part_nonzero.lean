
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

/-! ### Real and positive parts -/

theorem tsum_ofReal_of_im {f : ℤ → ℂ} (h : ∀ n, (f n).im = 0) :
    ∑' n, f n = ((∑' n, (f n).re : ℝ) : ℂ) := by
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  exact Complex.ext (by simp) (by simp [h n])

theorem exp_real_add_int_pi (r : ℝ) (k : ℤ) :
    cexp ((r : ℂ) + k * (π * I)) = ((Real.exp r * (-1 : ℝ) ^ k : ℝ) : ℂ) := by
  rw [Complex.exp_add, Complex.exp_int_mul, exp_pi_mul_I, ← Complex.ofReal_exp]
  push_cast
  rfl

theorem im_exp_real_add_int_pi (r : ℝ) (k : ℤ) : (cexp ((r : ℂ) + k * (π * I))).im = 0 := by
  rw [exp_real_add_int_pi, Complex.ofReal_im]

theorem norm_exp_pi_I_div (c : ℕ) : ‖cexp (π * I / c)‖ = 1 := by
  rw [show (π * I / c : ℂ) = ((π / c : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- `ϑ[0, b](−1 + i)` is real. -/
theorem P_real (b : ℤ) : ∃ p : ℝ, th1 0 b (-1 + I) = p := by
  refine ⟨_, tsum_ofReal_of_im fun n => ?_⟩
  have : thT 0 b (-1 + I) n = cexp (((-π * (n : ℝ) ^ 2 : ℝ) : ℂ) + ((n * b - n ^ 2 : ℤ) : ℂ) * (π * I)) := by
    rw [thT]; congr 1; push_cast; ring_nf; rw [I_sq]; ring
  rw [this]
  exact im_exp_real_add_int_pi _ _

/-- `ϑ[1, 0](−1 + i) = e^{−iπ/4} R` with `R > 0`. -/
theorem Q_eq : ∃ R : ℝ, 0 < R ∧ th1 1 0 (-1 + I) = cexp (-(π * I / 4)) * R := by
  set g : ℤ → ℂ := fun n => cexp (π * I / 4) * thT 1 0 (-1 + I) n with hg
  have hk : ∀ n : ℤ, ∃ k : ℤ, g n =
      cexp (((-π * ((n : ℝ) + 1 / 2) ^ 2 : ℝ) : ℂ) + ((-(2 * k)) : ℤ) * (π * I)) := by
    intro n
    obtain ⟨k, hk⟩ := Int.even_mul_succ_self n
    refine ⟨k, ?_⟩
    have hk' : ((n : ℂ) * ((n : ℂ) + 1)) = (k : ℂ) + k := by exact_mod_cast hk
    simp only [hg, thT, ← Complex.exp_add]
    congr 1
    push_cast
    linear_combination (-(π : ℂ) * I) * hk' + ((π : ℂ) * ((n : ℂ) + 1 / 2) ^ 2) * I_sq
  have him : ∀ n, (g n).im = 0 := fun n => by
    obtain ⟨k, hk⟩ := hk n; rw [hk]; exact im_exp_real_add_int_pi _ _
  have hre : ∀ n, 0 < (g n).re := fun n => by
    obtain ⟨k, hk⟩ := hk n
    rw [hk, exp_real_add_int_pi, Complex.ofReal_re]
    have : ((-1 : ℝ) ^ (-(2 * k))) = 1 := by
      rw [zpow_neg, zpow_mul]; simp
    rw [this, mul_one]; exact Real.exp_pos _
  have hsum : Summable fun n => (g n).re := by
    refine Summable.of_norm_bounded (summable_norm_thT 1 0 (w := -1 + I) (by simp)) fun n => ?_
    rw [Real.norm_eq_abs]
    refine (Complex.abs_re_le_norm _).trans ?_
    simp only [hg, norm_mul]
    rw [show (4 : ℂ) = ((4 : ℕ) : ℂ) by norm_num, norm_exp_pi_I_div, one_mul]
  refine ⟨∑' n, (g n).re, hsum.tsum_pos (fun n => (hre n).le) 0 (hre 0), ?_⟩
  rw [← tsum_ofReal_of_im him, ← tsum_mul_left]
  unfold th1
  refine tsum_congr fun n => ?_
  simp only [hg, ← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]

/-- `ϑ[1, 0]((−1 + i)/2) = e^{−iπ/8} C` with `C` real. -/
theorem T_eq : ∃ C : ℝ, th1 1 0 ((-1 + I) / 2) = cexp (-(π * I / 8)) * C := by
  set g : ℤ → ℂ := fun n => cexp (π * I / 8) * thT 1 0 ((-1 + I) / 2) n with hg
  have hk : ∀ n : ℤ, ∃ k : ℤ, g n =
      cexp (((-π * ((n : ℝ) + 1 / 2) ^ 2 / 2 : ℝ) : ℂ) + ((-k) : ℤ) * (π * I)) := by
    intro n
    obtain ⟨k, hk⟩ := Int.even_mul_succ_self n
    refine ⟨k, ?_⟩
    have hk' : ((n : ℂ) * ((n : ℂ) + 1)) = (k : ℂ) + k := by exact_mod_cast hk
    simp only [hg, thT, ← Complex.exp_add]
    congr 1
    push_cast
    linear_combination (-(π : ℂ) * I / 2) * hk' + ((π : ℂ) * ((n : ℂ) + 1 / 2) ^ 2 / 2) * I_sq
  have him : ∀ n, (g n).im = 0 := fun n => by
    obtain ⟨k, hk⟩ := hk n; rw [hk]; exact im_exp_real_add_int_pi _ _
  refine ⟨∑' n, (g n).re, ?_⟩
  rw [← tsum_ofReal_of_im him, ← tsum_mul_left]
  unfold th1
  refine tsum_congr fun n => ?_
  simp only [hg, ← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]

/-! ### `Z_b` via `jacobiTheta`, and the certified numerics -/

theorem th1_zero_zero (w : ℂ) : th1 0 0 w = jacobiTheta w := by
  unfold th1 jacobiTheta
  refine tsum_congr fun n => ?_
  simp [thT]

theorem th1_zero_one (w : ℂ) : th1 0 1 w = jacobiTheta (w + 1) := by
  unfold th1 jacobiTheta
  refine tsum_congr fun n => ?_
  obtain ⟨k, hk⟩ := Int.even_mul_pred_self n
  have hk' : ((n : ℂ) * ((n : ℂ) - 1)) = (k : ℂ) + k := by exact_mod_cast hk
  simp only [thT]
  rw [← exp_add_int_mul _ k]
  congr 1
  linear_combination (-(π : ℂ) * I) * hk'

theorem jt_approx {τ : ℂ} (hτ : τ.im = 1 / 2) : ∃ R : ℂ,
    jacobiTheta τ = 1 + 2 * cexp (π * I * τ) + 2 * R ∧
      ‖R‖ ≤ Real.exp (-π) ^ 2 / (1 - Real.exp (-π)) := by
  have hτ' : 0 < τ.im := by rw [hτ]; norm_num
  set f : ℕ → ℂ := fun n => cexp (π * I * ((n : ℂ) + 1) ^ 2 * τ) with hf
  set r := Real.exp (-π) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos])
  have hb : ∀ n : ℕ, ‖f (n + 1)‖ ≤ r ^ 2 * r ^ n := by
    intro n
    simp only [hf]
    rw [Complex.norm_exp]
    have hre : (π * I * (((n + 1 : ℕ) : ℂ) + 1) ^ 2 * τ).re = -π * ((n : ℝ) + 2) ^ 2 * τ.im := by
      rw [show (π * I * (((n + 1 : ℕ) : ℂ) + 1) ^ 2 * τ : ℂ) =
          ((π * ((n : ℝ) + 2) ^ 2 : ℝ) : ℂ) * (τ * I) by push_cast; ring,
        Complex.re_ofReal_mul, Complex.mul_I_re]
      ring
    rw [hre, hτ, ← pow_add, hr, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    push_cast
    have : 0 ≤ π * (((n : ℝ) + 2) * n) := by positivity
    nlinarith [Real.pi_pos]
  have hgeo : Summable (fun n : ℕ => r ^ 2 * r ^ n) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hs : Summable (fun n : ℕ => ‖f (n + 1)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hgeo
  have hsf : Summable f := (summable_nat_add_iff 1).mp hs.of_norm
  refine ⟨∑' n : ℕ, f (n + 1), ?_, ?_⟩
  · rw [jacobiTheta_eq_tsum_nat hτ', hsf.tsum_eq_zero_add]
    simp only [hf, Nat.cast_zero, zero_add, one_pow, mul_one]
    push_cast
    ring
  · calc ‖∑' n : ℕ, f (n + 1)‖ ≤ ∑' n : ℕ, ‖f (n + 1)‖ := norm_tsum_le_tsum_norm hs
      _ ≤ ∑' n : ℕ, r ^ 2 * r ^ n := hs.tsum_le_tsum hb hgeo
      _ = r ^ 2 / (1 - r) := by rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, div_eq_mul_inv]

theorem exp_bounds : 0.135 < Real.exp (-π / 2) ∧ Real.exp (-π / 2) < 0.227 ∧
    Real.exp (-π) ^ 2 / (1 - Real.exp (-π)) ≤ 1 / 380 := by
  have he1 := Real.exp_one_gt_d9
  have he2 := Real.exp_one_lt_d9
  have hp1 := Real.pi_gt_three
  have hp2 := Real.pi_lt_four
  have h2 : Real.exp (π / 2) < Real.exp 1 ^ 2 := by
    rw [← Real.exp_nat_mul]; exact Real.exp_lt_exp.mpr (by push_cast; linarith)
  have hhalf : (1.625 : ℝ) ≤ Real.exp (1 / 2) := by
    have := Real.quadratic_le_exp_of_nonneg (x := 1 / 2) (by norm_num)
    norm_num at this ⊢; linarith
  have h3 : Real.exp 1 * Real.exp (1 / 2) < Real.exp (π / 2) := by
    rw [← Real.exp_add]; exact Real.exp_lt_exp.mpr (by linarith)
  have h4 : Real.exp 1 ^ 3 < Real.exp π := by
    rw [← Real.exp_nat_mul]; exact Real.exp_lt_exp.mpr (by push_cast; linarith)
  have hpos := Real.exp_pos (π / 2)
  have hpos' := Real.exp_pos π
  rw [show -π / 2 = -(π / 2) by ring, Real.exp_neg]
  refine ⟨?_, ?_, ?_⟩
  · rw [lt_inv_comm₀ (by norm_num) hpos]; nlinarith
  · rw [inv_lt_comm₀ hpos (by norm_num)]; nlinarith
  · rw [Real.exp_neg]
    have h20 : 20 < Real.exp π := by nlinarith
    have hi : (Real.exp π)⁻¹ < 1 / 20 := by rw [inv_lt_comm₀ hpos' (by norm_num)]; linarith
    have hi0 : 0 < (Real.exp π)⁻¹ := inv_pos.mpr hpos'
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith

theorem re_pow8 (x y : ℝ) : (((x : ℂ) + y * I) ^ 8).re =
    x ^ 8 - 28 * x ^ 6 * y ^ 2 + 70 * x ^ 4 * y ^ 4 - 28 * x ^ 2 * y ^ 6 + y ^ 8 := by
  simp [pow_succ, Complex.mul_re, Complex.mul_im]
  ring

theorem re_pow8_neg (x y : ℝ) (hx : |x - 1| ≤ 1 / 150) (hy1 : 0.26 ≤ |y|) (hy2 : |y| ≤ 0.46) :
    (((x : ℂ) + y * I) ^ 8).re < 0 := by
  rw [re_pow8]
  have hx' := abs_le.mp hx
  have hy0 : 0 ≤ |y| := abs_nonneg y
  set s := x ^ 2 with hs
  set t := y ^ 2 with ht
  have ht' : t = |y| ^ 2 := by rw [ht, sq_abs]
  have hs0 : 0.9867 ≤ s := by rw [hs]; nlinarith
  have hs1 : s ≤ 1.0134 := by rw [hs]; nlinarith
  have ht0 : 0.0676 ≤ t := by rw [ht']; nlinarith
  have ht1 : t ≤ 0.2116 := by rw [ht']; nlinarith
  have hE : s ^ 2 - 28 * s * t + 70 * t ^ 2 < 0 := by
    have h1 : 0 ≤ (t - 0.0676) * (0.2116 - t) := mul_nonneg (by linarith) (by linarith)
    have h2 : 0 ≤ (t - 0.0676) * (s - 0.9867) := mul_nonneg (by linarith) (by linarith)
    have h3 : 0 ≤ (s - 0.9867) * (1.0134 - s) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hF : t ^ 3 * (t - 28 * s) < 0 :=
    mul_neg_of_pos_of_neg (pow_pos (by linarith) 3) (by linarith)
  have hG : s ^ 2 * (s ^ 2 - 28 * s * t + 70 * t ^ 2) < 0 :=
    mul_neg_of_pos_of_neg (pow_pos (by linarith) 2) hE
  have : x ^ 8 - 28 * x ^ 6 * y ^ 2 + 70 * x ^ 4 * y ^ 4 - 28 * x ^ 2 * y ^ 6 + y ^ 8 =
      s ^ 2 * (s ^ 2 - 28 * s * t + 70 * t ^ 2) + t ^ 3 * (t - 28 * s) := by
    rw [hs, ht]; ring
  rw [this]; linarith

theorem exp_w1 : cexp (π * I * ((-1 + I) / 2)) = -((Real.exp (-π / 2) : ℂ) * I) := by
  have hz : (π * I * ((-1 + I) / 2) : ℂ) = ((-π / 2 : ℝ) : ℂ) + ((-π / 2 : ℝ) : ℂ) * I := by
    push_cast; linear_combination ((π : ℂ) / 2) * I_sq
  rw [hz, Complex.exp_add, ← Complex.ofReal_exp, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, show -π / 2 = -(π / 2) by ring, Real.cos_neg, Real.sin_neg,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  push_cast; ring

theorem exp_w1' : cexp (π * I * ((-1 + I) / 2 + 1)) = (Real.exp (-π / 2) : ℂ) * I := by
  have hz : (π * I * ((-1 + I) / 2 + 1) : ℂ) = ((-π / 2 : ℝ) : ℂ) + ((π / 2 : ℝ) : ℂ) * I := by
    push_cast; linear_combination ((π : ℂ) / 2) * I_sq
  rw [hz, Complex.exp_add, ← Complex.ofReal_exp, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]
  push_cast; ring

/-- `Re ϑ(τ)⁸ < 0` for `jacobiTheta τ = 1 + 2(±iq) + 2R`. -/
theorem re_jt_pow8_neg {τ : ℂ} (hτ : τ.im = 1 / 2) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (hc : cexp (π * I * τ) = σ * ((Real.exp (-π / 2) : ℂ) * I)) : (jacobiTheta τ ^ 8).re < 0 := by
  obtain ⟨R, hR, hRb⟩ := jt_approx hτ
  obtain ⟨hq1, hq2, hε⟩ := exp_bounds
  set q := Real.exp (-π / 2)
  have hRn : ‖R‖ ≤ 1 / 380 := hRb.trans hε
  have hre := (abs_re_le_norm R).trans hRn
  have him := (abs_im_le_norm R).trans hRn
  have hZ : jacobiTheta τ = ((1 + 2 * R.re : ℝ) : ℂ) + ((2 * σ * q + 2 * R.im : ℝ) : ℂ) * I := by
    rw [hR, hc]
    apply Complex.ext <;> simp
    ring
  rw [hZ]
  apply re_pow8_neg
  · rw [abs_le] at hre ⊢; constructor <;> linarith
  · rw [abs_le] at him
    rcases hσ with h | h <;> subst h
    · rw [abs_of_pos (by linarith)]; linarith
    · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_le] at him ⊢
    rcases hσ with h | h <;> subst h <;> constructor <;> linarith

theorem re_Z0 : (th1 0 0 ((-1 + I) / 2) ^ 8).re < 0 := by
  rw [th1_zero_zero]
  exact re_jt_pow8_neg (by simp) (-1) (Or.inr rfl) (by rw [exp_w1]; push_cast; ring)

theorem re_Z1 : (th1 0 1 ((-1 + I) / 2) ^ 8).re < 0 := by
  rw [th1_zero_one]
  exact re_jt_pow8_neg (by simp) 1 (Or.inl rfl) (by rw [exp_w1']; push_cast; ring)

/-! ### Assembly -/

theorem evenChars_eq : PkgI1.evenChars =
    {(![0, 0], ![0, 0]), (![0, 0], ![0, 1]), (![0, 0], ![1, 0]), (![0, 0], ![1, 1]),
     (![1, 0], ![0, 0]), (![1, 0], ![0, 1]), (![0, 1], ![0, 0]), (![0, 1], ![1, 0]),
     (![1, 1], ![0, 0]), (![1, 1], ![1, 1])} := by
  decide

theorem c8_eq_one (m : PkgI1.Char2) :
    cexp (-(π * I * ((m.1 0 : ℕ) : ℂ) * ((m.1 1 : ℕ) : ℂ) / 2)) ^ 8 = 1 := by
  rw [← Complex.exp_nat_mul]
  rw [show ((8 : ℕ) : ℂ) * -(π * I * ((m.1 0 : ℕ) : ℂ) * ((m.1 1 : ℕ) : ℂ) / 2) =
      ((-2 * ((m.1 0 : ℕ) : ℤ) * ((m.1 1 : ℕ) : ℤ) : ℤ) : ℂ) * (2 * π * I) by push_cast; ring]
  exact exp_int_mul_two_pi_mul_I _

theorem thetaSum8_s2I : PkgI1.thetaSum8 Om0 =
    (th1 0 0 ((-1 + I) / 2) ^ 8 + th1 0 1 ((-1 + I) / 2) ^ 8 + th1 1 0 ((-1 + I) / 2) ^ 8) *
      (th1 0 0 (-1 + I) ^ 8 + th1 0 1 (-1 + I) ^ 8 + th1 1 0 (-1 + I) ^ 8) := by
  have h1 : 0 < ((-1 + I) / 2 : ℂ).im := by simp
  have h2 : 0 < ((-1 + I) : ℂ).im := by simp
  have hs : ∀ m : PkgI1.Char2, PkgI1.thetaConst m Om0 ^ 8 =
      th1 ((m.1 0 : ℕ) : ℂ) (((m.2 0 : ℕ) : ℂ) + ((m.1 1 : ℕ) : ℂ)) ((-1 + I) / 2) ^ 8 *
        th1 ((m.1 1 : ℕ) : ℂ) (((m.2 1 : ℕ) : ℂ) + ((m.1 0 : ℕ) : ℂ)) (-1 + I) ^ 8 := by
    intro m
    rw [Om0, thetaConst_split m _ _ h1 h2, mul_pow, mul_pow, c8_eq_one, one_mul]
  unfold PkgI1.thetaSum8
  rw [Finset.sum_congr rfl fun m _ => hs m, evenChars_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.isValue, Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one, add_zero, zero_add,
    one_add_one_eq_two, th1_zero_two, th1_one_two, th1_one_one]
  ring

/-- **`S8Nonzero`, proved.** -/
theorem s8Nonzero_proof : S8Nonzero := by
  unfold S8Nonzero
  rw [omega_s2I, thetaSum8_s2I]
  apply mul_ne_zero
  · intro h
    have hre := congrArg Complex.re h
    obtain ⟨C, hC⟩ := T_eq
    have hT : (th1 1 0 ((-1 + I) / 2) ^ 8).re = -C ^ 8 := by
      rw [hC, mul_pow, ← Complex.exp_nat_mul,
        show ((8 : ℕ) : ℂ) * -(π * I / 8) = ((-1 : ℤ) : ℂ) * (π * I) by push_cast; ring,
        Complex.exp_int_mul, exp_pi_mul_I]
      norm_num
      rw [← Complex.ofReal_pow, Complex.ofReal_re]
    simp only [Complex.add_re, Complex.zero_re, hT] at hre
    have := re_Z0
    have := re_Z1
    have : 0 ≤ C ^ 8 := by positivity
    linarith
  · obtain ⟨p0, hp0⟩ := P_real 0
    obtain ⟨p1, hp1⟩ := P_real 1
    obtain ⟨R, hR, hQ⟩ := Q_eq
    push_cast at hp0 hp1
    rw [hp0, hp1, hQ, mul_pow, ← Complex.exp_nat_mul,
      show ((8 : ℕ) : ℂ) * -(π * I / 4) = ((-1 : ℤ) : ℂ) * (2 * π * I) by push_cast; ring,
      exp_int_mul_two_pi_mul_I, one_mul]
    have : (0 : ℝ) < p0 ^ 8 + p1 ^ 8 + R ^ 8 := by positivity
    exact_mod_cast this.ne'

end HSyn.G0Split.FibreQM.PeriodNum

end

#print axioms HSyn.G0Split.FibreQM.PeriodNum.s8Nonzero_proof
