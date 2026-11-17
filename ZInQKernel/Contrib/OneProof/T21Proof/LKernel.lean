import ZInQKernel.Contrib.TYZChain.Lcal

/-!
# t21-proof: the shifted-lattice theta kernel minus its four nearest terms

Task t21-proof. For `a, b ∈ [0, 1)` and `x ≥ 1`, the Hurwitz kernels of Mathlib minus their terms
`n ∈ {0, −1}` are `O(e^{−πx})`, and `Λ_{a,b}(1)` (`HeckeFE.gaussLambda`) is the closed form `mainL a b`
of the four nearest lattice points `(a − m, b − n)`, `m, n ∈ {0, 1}`, up to an explicit error.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

noncomputable section

namespace ZInQ.Contrib.T21Proof

open Complex Real Set MeasureTheory HurwitzZeta ZInQ.Contrib.HeckeFE ZInQ.Contrib.TYZLcal

/-! ## Geometric majorants -/

/-- `e^{−3π} ≤ 1/8000`. -/
theorem exp_neg_three_pi_le : Real.exp (-(3 * π)) ≤ 1 / 8000 := by
  have h := exp_nat_ge 9
  have : Real.exp 9 ≤ Real.exp (3 * π) := Real.exp_le_exp.mpr (by linarith [pi_gt'])
  refine exp_neg_le_of (by norm_num) ?_
  push_cast at h; nlinarith

/-- The majorant `m ↦ [m ≥ 1] E (m + 1) q^{m−1}`. -/
def majO (E q : ℝ) (m : ℕ) : ℝ := if m = 0 then 0 else E * ((m : ℝ) + 1) * q ^ (m - 1)

/-- The majorant `m ↦ [m ≥ 1] E q^{m−1}`. -/
def majE (E q : ℝ) (m : ℕ) : ℝ := if m = 0 then 0 else E * q ^ (m - 1)

theorem hasSum_majO {E q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1) :
    HasSum (majO E q) (E * (q / (1 - q) ^ 2 + 2 * (1 - q)⁻¹)) := by
  rw [← hasSum_nat_add_iff' 1]
  simp only [majO, Finset.range_one, Finset.sum_singleton, if_pos, sub_zero]
  have := (hasSum_lin_geom h0 h1 2).mul_left E
  convert this using 1
  funext m
  simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, Nat.add_sub_cancel]
  push_cast; ring

theorem hasSum_majE {E q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1) :
    HasSum (majE E q) (E * (1 - q)⁻¹) := by
  rw [← hasSum_nat_add_iff' 1]
  simp only [majE, Finset.range_one, Finset.sum_singleton, if_pos, sub_zero]
  have := (hasSum_geometric_of_lt_one h0 h1).mul_left E
  convert this using 1
  funext m
  simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, Nat.add_sub_cancel]

/-- `e^{−π m² x} ≤ e^{−πx} q^{m−1}` for `m ≥ 1`, `x ≥ 1`, `q = e^{−3π}`. -/
theorem exp_sq_le {m : ℕ} (hm : 1 ≤ m) {x : ℝ} (hx : 1 ≤ x) :
    Real.exp (-π * (m : ℝ) ^ 2 * x) ≤ Real.exp (-π * x) * Real.exp (-(3 * π)) ^ (m - 1) := by
  rw [exp_pow_eq, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by push_cast [Nat.cast_sub hm]; ring
  rw [hcast]
  have hpi := Real.pi_pos
  have hmm : (0 : ℝ) ≤ ((m : ℝ) - 1) * ((m : ℝ) - 2) := by
    rcases Nat.lt_or_ge m 2 with h | h
    · have : m = 1 := by omega
      subst this; norm_num
    · have : (2 : ℝ) ≤ m := by exact_mod_cast h
      nlinarith
  have h1 : (m : ℝ) ^ 2 ≥ 1 + 3 * ((m : ℝ) - 1) := by nlinarith
  have h2 : 0 ≤ ((m : ℝ) ^ 2 - 1) * (x - 1) := mul_nonneg (by nlinarith) (by linarith)
  nlinarith

/-! ## The odd and even kernels minus two terms -/

/-- The two terms `n = 0, −1` of `oddKernel a x`. -/
def oddMain (a x : ℝ) : ℝ := a * Real.exp (-π * a ^ 2 * x) + (a - 1) * Real.exp (-π * (a - 1) ^ 2 * x)

/-- The two terms `n = 0, −1` of `evenKernel b x`. -/
def evenMain (b x : ℝ) : ℝ := Real.exp (-π * b ^ 2 * x) + Real.exp (-π * (b - 1) ^ 2 * x)

theorem int_cases3 (n : ℤ) : n = 0 ∨ n = -1 ∨ (∃ m : ℕ, 1 ≤ m ∧ n = m) ∨
    ∃ m : ℕ, 1 ≤ m ∧ n = -((m : ℤ) + 1) := by
  rcases int_cases' n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rcases Nat.eq_zero_or_pos m with h | h
    · left; simp [h]
    · right; right; left; exact ⟨m, h, rfl⟩
  · rcases Nat.eq_zero_or_pos m with h | h
    · right; left; simp [h]
    · right; right; right; exact ⟨m, h, rfl⟩

/-- **`|oddKernel a x − oddMain a x| ≤ 4.01 e^{−πx}`** (`0 ≤ a < 1`, `x ≥ 1`). -/
theorem abs_odd_sub_main_le {a x : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hx : 1 ≤ x) :
    |oddKernel (a : UnitAddCircle) x - oddMain a x| ≤ 4.01 * Real.exp (-π * x) := by
  classical
  set E := Real.exp (-π * x)
  set q := Real.exp (-(3 * π))
  have hq : q ≤ 1 / 8000 := exp_neg_three_pi_le
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hpi := Real.pi_pos
  set f : ℤ → ℝ := fun n => (n + a) * Real.exp (-π * (n + a) ^ 2 * x)
  have hf := hasSum_int_oddKernel a (by linarith : 0 < x)
  set g : ℤ → ℝ := fun n => if n = 0 ∨ n = -1 then 0 else f n
  have hfin : HasSum (fun n : ℤ => if n = 0 ∨ n = -1 then f n else 0) (f 0 + f (-1)) := by
    have : (fun n : ℤ => if n = 0 ∨ n = -1 then f n else 0) =
        fun n => (if n = 0 then f 0 else 0) + (if n = -1 then f (-1) else 0) := by
      funext n
      by_cases h0 : n = 0
      · subst h0; simp
      · by_cases h1 : n = -1
        · subst h1; simp
        · simp [h0, h1]
    rw [this]
    exact (hasSum_ite_eq 0 (f 0)).add (hasSum_ite_eq (-1) (f (-1)))
  have hg : HasSum g (oddKernel (a : UnitAddCircle) x - (f 0 + f (-1))) := by
    have := hf.sub hfin
    convert this using 1
    funext n
    by_cases h : n = 0 ∨ n = -1
    · simp only [g, if_pos h, f, sub_self]
    · simp only [g, if_neg h, f, sub_zero]
  have hmain : f 0 + f (-1) = oddMain a x := by
    simp only [f, oddMain]; push_cast; ring_nf
  rw [hmain] at hg
  have hmaj := hasSum_zmaj (hasSum_majO (E := E) hq0 (by linarith)) (hasSum_majO (E := E) hq0 (by linarith))
  have key := HasSum.norm_le_of_bounded hg hmaj (fun n => ?_)
  · rw [Real.norm_eq_abs] at key
    refine key.trans ?_
    have hpos : 0 < 1 - q := by linarith
    have : q / (1 - q) ^ 2 + 2 * (1 - q)⁻¹ ≤ 2.005 := by
      rw [← div_eq_mul_inv, div_add_div _ _ (by positivity) hpos.ne', div_le_iff₀ (by positivity)]
      nlinarith
    nlinarith
  · rcases int_cases3 n with rfl | rfl | ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩
    · show ‖g ((0 : ℕ) : ℤ)‖ ≤ zmaj (majO E q) (majO E q) ((0 : ℕ) : ℤ)
      rw [zmaj_nat]; simp [g, majO]
    · have : (-1 : ℤ) = -((0 : ℕ) + 1 : ℤ) := by norm_num
      rw [this, zmaj_neg]; simp [g, majO]
    · rw [zmaj_nat]
      have hne : ¬ ((m : ℤ) = 0 ∨ (m : ℤ) = -1) := by omega
      simp only [g, hne, if_false, f, majO, show m ≠ 0 by omega, Int.cast_natCast]
      have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ m + a),
        abs_of_nonneg (Real.exp_pos _).le]
      have hexp : Real.exp (-π * ((m : ℝ) + a) ^ 2 * x) ≤ Real.exp (-π * (m : ℝ) ^ 2 * x) := by
        refine Real.exp_le_exp.mpr ?_
        have : (m : ℝ) ^ 2 ≤ ((m : ℝ) + a) ^ 2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ π * x)]
      calc ((m : ℝ) + a) * Real.exp (-π * ((m : ℝ) + a) ^ 2 * x)
          ≤ ((m : ℝ) + 1) * (E * q ^ (m - 1)) :=
            mul_le_mul (by linarith) (hexp.trans (exp_sq_le hm hx)) (Real.exp_pos _).le
              (by positivity)
        _ = E * ((m : ℝ) + 1) * q ^ (m - 1) := by ring
    · rw [zmaj_neg]
      have hne : ¬ (-((m : ℤ) + 1) = 0 ∨ -((m : ℤ) + 1) = -1) := by omega
      simp only [g, hne, if_false, f, majO, show m ≠ 0 by omega]
      push_cast
      have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonpos (by linarith : -((m : ℝ) + 1) + a ≤ 0),
        abs_of_nonneg (Real.exp_pos _).le]
      have hexp : Real.exp (-π * (-((m : ℝ) + 1) + a) ^ 2 * x) ≤ Real.exp (-π * (m : ℝ) ^ 2 * x) := by
        refine Real.exp_le_exp.mpr ?_
        have : (m : ℝ) ^ 2 ≤ (-((m : ℝ) + 1) + a) ^ 2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ π * x)]
      calc -(-((m : ℝ) + 1) + a) * Real.exp (-π * (-((m : ℝ) + 1) + a) ^ 2 * x)
          ≤ ((m : ℝ) + 1) * (E * q ^ (m - 1)) :=
            mul_le_mul (by linarith) (hexp.trans (exp_sq_le hm hx)) (Real.exp_pos _).le
              (by positivity)
        _ = E * ((m : ℝ) + 1) * q ^ (m - 1) := by ring

/-- **`|evenKernel b x − evenMain b x| ≤ 2.01 e^{−πx}`** (`0 ≤ b < 1`, `x ≥ 1`). -/
theorem abs_even_sub_main_le {b x : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) (hx : 1 ≤ x) :
    |evenKernel (b : UnitAddCircle) x - evenMain b x| ≤ 2.01 * Real.exp (-π * x) := by
  classical
  set E := Real.exp (-π * x)
  set q := Real.exp (-(3 * π))
  have hq : q ≤ 1 / 8000 := exp_neg_three_pi_le
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hpi := Real.pi_pos
  set f : ℤ → ℝ := fun n => Real.exp (-π * (n + b) ^ 2 * x)
  have hf := hasSum_int_evenKernel b (by linarith : 0 < x)
  set g : ℤ → ℝ := fun n => if n = 0 ∨ n = -1 then 0 else f n
  have hfin : HasSum (fun n : ℤ => if n = 0 ∨ n = -1 then f n else 0) (f 0 + f (-1)) := by
    have : (fun n : ℤ => if n = 0 ∨ n = -1 then f n else 0) =
        fun n => (if n = 0 then f 0 else 0) + (if n = -1 then f (-1) else 0) := by
      funext n
      by_cases h0 : n = 0
      · subst h0; simp
      · by_cases h1 : n = -1
        · subst h1; simp
        · simp [h0, h1]
    rw [this]
    exact (hasSum_ite_eq 0 (f 0)).add (hasSum_ite_eq (-1) (f (-1)))
  have hg : HasSum g (evenKernel (b : UnitAddCircle) x - (f 0 + f (-1))) := by
    have := hf.sub hfin
    convert this using 1
    funext n
    by_cases h : n = 0 ∨ n = -1
    · simp only [g, if_pos h, f, sub_self]
    · simp only [g, if_neg h, f, sub_zero]
  have hmain : f 0 + f (-1) = evenMain b x := by
    simp only [f, evenMain]; push_cast; ring_nf
  rw [hmain] at hg
  have hmaj := hasSum_zmaj (hasSum_majE (E := E) hq0 (by linarith)) (hasSum_majE (E := E) hq0 (by linarith))
  have key := HasSum.norm_le_of_bounded hg hmaj (fun n => ?_)
  · rw [Real.norm_eq_abs] at key
    refine key.trans ?_
    have hpos : 0 < 1 - q := by linarith
    have : (1 - q)⁻¹ ≤ 1.005 := by
      rw [inv_le_comm₀ hpos (by norm_num)]; linarith
    nlinarith
  · rcases int_cases3 n with rfl | rfl | ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩
    · show ‖g ((0 : ℕ) : ℤ)‖ ≤ zmaj (majE E q) (majE E q) ((0 : ℕ) : ℤ)
      rw [zmaj_nat]; simp [g, majE]
    · have : (-1 : ℤ) = -((0 : ℕ) + 1 : ℤ) := by norm_num
      rw [this, zmaj_neg]; simp [g, majE]
    · rw [zmaj_nat]
      have hne : ¬ ((m : ℤ) = 0 ∨ (m : ℤ) = -1) := by omega
      simp only [g, hne, if_false, f, majE, show m ≠ 0 by omega, Int.cast_natCast]
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      refine le_trans ?_ (exp_sq_le hm hx)
      refine Real.exp_le_exp.mpr ?_
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have : (m : ℝ) ^ 2 ≤ ((m : ℝ) + b) ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ π * x)]
    · rw [zmaj_neg]
      have hne : ¬ (-((m : ℤ) + 1) = 0 ∨ -((m : ℤ) + 1) = -1) := by omega
      simp only [g, hne, if_false, f, majE, show m ≠ 0 by omega]
      push_cast
      have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      refine le_trans ?_ (exp_sq_le hm hx)
      refine Real.exp_le_exp.mpr ?_
      have : (m : ℝ) ^ 2 ≤ (-((m : ℝ) + 1) + b) ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ π * x)]

/-- `t e^{−πt²x} ≤ 0.3` for `t ≥ 0`, `x ≥ 1`. -/
theorem mul_exp_le {t x : ℝ} (ht : 0 ≤ t) (hx : 1 ≤ x) : t * Real.exp (-π * t ^ 2 * x) ≤ 0.3 := by
  have hpi := pi_gt'
  have h1 : Real.exp (-π * t ^ 2 * x) ≤ Real.exp (-π * t ^ 2) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg t)) (by linarith : (0 : ℝ) ≤ x - 1)]
  have h2 : 1 + π * t ^ 2 ≤ Real.exp (π * t ^ 2) := by
    have := Real.add_one_le_exp (π * t ^ 2); linarith
  have h3 : Real.exp (-π * t ^ 2) * Real.exp (π * t ^ 2) = 1 := by
    rw [← Real.exp_add]; simp
  have h4 : t ≤ 0.3 * (1 + π * t ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_right hpi.le (sq_nonneg t), sq_nonneg (t - 0.531)]
  have hE := (Real.exp_pos (-π * t ^ 2)).le
  calc t * Real.exp (-π * t ^ 2 * x) ≤ t * Real.exp (-π * t ^ 2) := by gcongr
    _ ≤ 0.3 * (1 + π * t ^ 2) * Real.exp (-π * t ^ 2) := by gcongr
    _ ≤ 0.3 * Real.exp (π * t ^ 2) * Real.exp (-π * t ^ 2) := by gcongr
    _ = 0.3 := by rw [mul_assoc, mul_comm (Real.exp _), h3, mul_one]

theorem abs_oddMain_le {a x : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hx : 1 ≤ x) :
    |oddMain a x| ≤ 0.6 := by
  have h1 := mul_exp_le ha0 hx
  have h2 := mul_exp_le (by linarith : 0 ≤ 1 - a) hx
  have e : (a - 1) ^ 2 = (1 - a) ^ 2 := by ring
  rw [oddMain, e]
  have hp1 := (Real.exp_pos (-π * a ^ 2 * x)).le
  have hp2 := (Real.exp_pos (-π * (1 - a) ^ 2 * x)).le
  rw [abs_le]; constructor <;> nlinarith

theorem exp_quarter_le {t x : ℝ} (ht : 1 / 2 ≤ |t|) (hx : 1 ≤ x) :
    Real.exp (-π * t ^ 2 * x) ≤ 0.48 := by
  refine le_trans (Real.exp_le_exp.mpr ?_) exp_neg_pi_div_four_le
  have : 1 / 4 ≤ t ^ 2 := by
    have := sq_le_sq' (by linarith [abs_nonneg t] : -|t| ≤ 1 / 2) ht
    nlinarith [sq_abs t]
  have hpi := Real.pi_pos
  nlinarith [mul_le_mul_of_nonneg_left this hpi.le,
    mul_nonneg (mul_nonneg hpi.le (sq_nonneg t)) (by linarith : (0 : ℝ) ≤ x - 1)]

theorem abs_evenMain_le {b x : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) (hx : 1 ≤ x) :
    |evenMain b x| ≤ 1.48 := by
  have hpi := Real.pi_pos
  have e1 : Real.exp (-π * b ^ 2 * x) ≤ 1 := Real.exp_le_one_iff.mpr
    (by nlinarith [mul_nonneg (mul_nonneg hpi.le (sq_nonneg b)) (by linarith : (0 : ℝ) ≤ x)])
  have e2 : Real.exp (-π * (b - 1) ^ 2 * x) ≤ 1 := Real.exp_le_one_iff.mpr
    (by nlinarith [mul_nonneg (mul_nonneg hpi.le (sq_nonneg (b - 1))) (by linarith : (0 : ℝ) ≤ x)])
  rw [evenMain, abs_of_nonneg (by positivity)]
  rcases le_total b (1 / 2) with h | h
  · have := exp_quarter_le (t := b - 1) (by rw [abs_of_nonpos (by linarith)]; linarith) hx
    linarith
  · have := exp_quarter_le (t := b) (by rw [abs_of_nonneg hb0]; linarith) hx
    linarith

/-! ## The theta kernel and `Λ_{a,b}(1)` -/

/-- The lattice term `(u + iv) e^{−π(u² + v²)x}`. -/
def tm (u v x : ℝ) : ℂ := ((u : ℂ) + I * v) * (Real.exp (-π * (u ^ 2 + v ^ 2) * x) : ℂ)

/-- Its integral over `(1, ∞)`: `(u + iv) e^{−π(u² + v²)}/(π(u² + v²))`. -/
def tmL (u v : ℝ) : ℂ :=
  ((u : ℂ) + I * v) * ((Real.exp (-π * (u ^ 2 + v ^ 2)) / (π * (u ^ 2 + v ^ 2)) : ℝ) : ℂ)

/-- The four nearest lattice terms of `θ_{a,b}`. -/
def thetaMain (a b x : ℝ) : ℂ := tm a b x + tm a (b - 1) x + tm (a - 1) b x + tm (a - 1) (b - 1) x

/-- The closed form `Λ_{a,b}(1) ≈ mainL a b` (four nearest lattice points). -/
def mainL (a b : ℝ) : ℂ := tmL a b + tmL a (b - 1) + tmL (a - 1) b + tmL (a - 1) (b - 1)

theorem exp_mul_exp' (s t x : ℝ) :
    Real.exp (-π * s * x) * Real.exp (-π * t * x) = Real.exp (-π * (s + t) * x) := by
  rw [← Real.exp_add]; ring_nf

theorem thetaMain_eq (a b x : ℝ) :
    thetaMain a b x = ((oddMain a x * evenMain b x : ℝ) : ℂ) +
      I * ((evenMain a x * oddMain b x : ℝ) : ℂ) := by
  simp only [thetaMain, tm, oddMain, evenMain]
  push_cast
  simp only [mul_add, add_mul, Complex.exp_add]
  ring

/-- **`‖θ_{a,b}(x) − θ_main‖ ≤ 15.2 e^{−πx}`** (`0 ≤ a, b < 1`, `x ≥ 1`). -/
theorem norm_theta_sub_main_le {a b x : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hx : 1 ≤ x) :
    ‖gaussTheta (a : UnitAddCircle) (b : UnitAddCircle) x - thetaMain a b x‖ ≤
      15.2 * Real.exp (-π * x) := by
  set X := Real.exp (-π * x)
  have hX0 : 0 ≤ X := (Real.exp_pos _).le
  have hX : X ≤ 1 / 20 := by
    refine le_trans (Real.exp_le_exp.mpr ?_) exp_neg_pi_le
    nlinarith [Real.pi_pos]
  set O := oddKernel (a : UnitAddCircle) x
  set E := evenKernel (b : UnitAddCircle) x
  set O' := oddKernel (b : UnitAddCircle) x
  set E' := evenKernel (a : UnitAddCircle) x
  have h1 := abs_odd_sub_main_le ha0 ha1 hx
  have h2 := abs_even_sub_main_le hb0 hb1 hx
  have h3 := abs_odd_sub_main_le hb0 hb1 hx
  have h4 := abs_even_sub_main_le ha0 ha1 hx
  have m1 := abs_oddMain_le ha0 ha1 hx
  have m2 := abs_evenMain_le hb0 hb1 hx
  have m3 := abs_oddMain_le hb0 hb1 hx
  have m4 := abs_evenMain_le ha0 ha1 hx
  have hE : |E| ≤ 1.581 := by
    have := abs_sub_abs_le_abs_sub E (evenMain b x); linarith
  have hO' : |O'| ≤ 0.8005 := by
    have := abs_sub_abs_le_abs_sub O' (oddMain b x); linarith
  have hA : |O * E - oddMain a x * evenMain b x| ≤ 7.546 * X := by
    have e : O * E - oddMain a x * evenMain b x =
        (O - oddMain a x) * E + oddMain a x * (E - evenMain b x) := by ring
    rw [e]
    calc |(O - oddMain a x) * E + oddMain a x * (E - evenMain b x)|
        ≤ |O - oddMain a x| * |E| + |oddMain a x| * |E - evenMain b x| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ (4.01 * X) * 1.581 + 0.6 * (2.01 * X) := by gcongr
      _ = 7.54581 * X := by ring
      _ ≤ 7.546 * X := by nlinarith
  have hB : |E' * O' - evenMain a x * oddMain b x| ≤ 7.545 * X := by
    have e : E' * O' - evenMain a x * oddMain b x =
        (E' - evenMain a x) * O' + evenMain a x * (O' - oddMain b x) := by ring
    rw [e]
    calc |(E' - evenMain a x) * O' + evenMain a x * (O' - oddMain b x)|
        ≤ |E' - evenMain a x| * |O'| + |evenMain a x| * |O' - oddMain b x| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ (2.01 * X) * 0.8005 + 1.48 * (4.01 * X) := by gcongr
      _ = 7.543805 * X := by ring
      _ ≤ 7.545 * X := by nlinarith
  rw [thetaMain_eq]
  have e : gaussTheta (a : UnitAddCircle) (b : UnitAddCircle) x -
      (((oddMain a x * evenMain b x : ℝ) : ℂ) + I * ((evenMain a x * oddMain b x : ℝ) : ℂ)) =
      ((O * E - oddMain a x * evenMain b x : ℝ) : ℂ) +
        I * ((E' * O' - evenMain a x * oddMain b x : ℝ) : ℂ) := by
    simp only [gaussTheta, O, E, O', E']; push_cast; ring
  rw [e]
  calc ‖((O * E - oddMain a x * evenMain b x : ℝ) : ℂ) +
        I * ((E' * O' - evenMain a x * oddMain b x : ℝ) : ℂ)‖
      ≤ |O * E - oddMain a x * evenMain b x| + |E' * O' - evenMain a x * oddMain b x| := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ 7.546 * X + 7.545 * X := add_le_add hA hB
    _ ≤ 15.2 * X := by nlinarith

theorem integrableOn_tm (u v : ℝ) : IntegrableOn (tm u v) (Ioi 1) := by
  by_cases h : u ^ 2 + v ^ 2 = 0
  · have hu : u = 0 := by nlinarith [sq_nonneg u, sq_nonneg v]
    have hv : v = 0 := by nlinarith [sq_nonneg u, sq_nonneg v]
    have : tm u v = fun _ => 0 := by funext x; simp [tm, hu, hv]
    rw [this]; exact integrableOn_zero
  · have hc : -π * (u ^ 2 + v ^ 2) < 0 := by
      have : 0 < u ^ 2 + v ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h)
      nlinarith [Real.pi_pos]
    have := ((integrableOn_exp_mul_Ioi hc 1).ofReal (𝕜 := ℂ)).const_mul ((u : ℂ) + I * v)
    exact this

theorem integral_tm (u v : ℝ) : ∫ x in Ioi (1 : ℝ), tm u v x = tmL u v := by
  by_cases h : u ^ 2 + v ^ 2 = 0
  · have hu : u = 0 := by nlinarith [sq_nonneg u, sq_nonneg v]
    have hv : v = 0 := by nlinarith [sq_nonneg u, sq_nonneg v]
    simp [tm, tmL, hu, hv]
  · have hpos : 0 < u ^ 2 + v ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h)
    have hc : -π * (u ^ 2 + v ^ 2) < 0 := by nlinarith [Real.pi_pos]
    have e : (fun x => tm u v x) =
        fun x => ((u : ℂ) + I * v) * ((Real.exp ((-π * (u ^ 2 + v ^ 2)) * x) : ℝ) : ℂ) := rfl
    rw [e, integral_const_mul, integral_complex_ofReal, integral_exp_mul_Ioi hc 1, tmL]
    congr 2
    rw [mul_one, neg_mul, neg_div_neg_eq]

/-- `‖θ^dual_{a,b}(x)‖ ≤ 0.2487 e^{−π(x−1)}` for `x ≥ 1`. -/
theorem norm_thetaDual_le (a b : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    ‖gaussThetaDual (a : UnitAddCircle) (b : UnitAddCircle) x‖ ≤
      0.2487 * Real.exp (-π * (x - 1)) := by
  have s1 := abs_sinKernel_le a hx
  have s2 := abs_sinKernel_le b hx
  have c1 := abs_cosKernel_le a hx
  have c2 := abs_cosKernel_le b hx
  have hE := (Real.exp_pos (-π * (x - 1))).le
  rw [gaussThetaDual]
  calc ‖(sinKernel (a : UnitAddCircle) x : ℂ) * cosKernel (b : UnitAddCircle) x +
        I * ((cosKernel (a : UnitAddCircle) x : ℂ) * sinKernel (b : UnitAddCircle) x)‖
      ≤ |sinKernel (a : UnitAddCircle) x| * |cosKernel (b : UnitAddCircle) x| +
        |cosKernel (a : UnitAddCircle) x| * |sinKernel (b : UnitAddCircle) x| := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
          Complex.norm_real, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ (0.112 * Real.exp (-π * (x - 1))) * 1.11 + 1.11 * (0.112 * Real.exp (-π * (x - 1))) := by
        gcongr
    _ ≤ 0.2487 * Real.exp (-π * (x - 1)) := by nlinarith

/-- **`Λ_{a,b}(1) = mainL a b + O(1)`** with an explicit error. -/
theorem norm_gaussLambda_sub_mainL_le {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hb0 : 0 ≤ b)
    (hb1 : b < 1) :
    ‖gaussLambda (a : UnitAddCircle) (b : UnitAddCircle) 1 - mainL a b‖ ≤
      (15.2 * Real.exp (-π) + 0.2487) / π := by
  have hpi := Real.pi_pos
  rw [gaussLambda_one_eq]
  have hθ : IntegrableOn (gaussTheta (a : UnitAddCircle) (b : UnitAddCircle)) (Ioi 1) :=
    (integrableOn_gaussTheta _ _).mono_set (Ioi_subset_Ioi zero_le_one)
  have hm : IntegrableOn (thetaMain a b) (Ioi 1) := by
    unfold thetaMain
    exact (((integrableOn_tm _ _).add (integrableOn_tm _ _)).add (integrableOn_tm _ _)).add
      (integrableOn_tm _ _)
  have hint : ∫ x in Ioi (1 : ℝ), thetaMain a b x = mainL a b := by
    unfold thetaMain mainL
    rw [integral_add (f := fun x => tm a b x + tm a (b - 1) x + tm (a - 1) b x)
        (g := tm (a - 1) (b - 1))
        (((integrableOn_tm _ _).add (integrableOn_tm _ _)).add (integrableOn_tm _ _))
        (integrableOn_tm _ _),
      integral_add (f := fun x => tm a b x + tm a (b - 1) x) (g := tm (a - 1) b)
        ((integrableOn_tm _ _).add (integrableOn_tm _ _)) (integrableOn_tm _ _),
      integral_add (f := tm a b) (g := tm a (b - 1)) (integrableOn_tm _ _) (integrableOn_tm _ _),
      integral_tm, integral_tm, integral_tm, integral_tm]
  have hsplit : (∫ x in Ioi (1 : ℝ), gaussTheta (a : UnitAddCircle) (b : UnitAddCircle) x) =
      (∫ x in Ioi (1 : ℝ), (gaussTheta (a : UnitAddCircle) (b : UnitAddCircle) x - thetaMain a b x)) +
        mainL a b := by
    rw [integral_sub hθ hm, hint]; ring
  rw [hsplit]
  have e1 : ‖∫ x in Ioi (1 : ℝ), (gaussTheta (a : UnitAddCircle) (b : UnitAddCircle) x -
      thetaMain a b x)‖ ≤ 15.2 * Real.exp (-π) / π := by
    refine norm_integral_Ioi_one_le hpi fun x hx => ?_
    refine (norm_theta_sub_main_le ha0 ha1 hb0 hb1 hx.le).trans (le_of_eq ?_)
    rw [mul_assoc, ← Real.exp_add]; ring_nf
  have e2 : ‖∫ x in Ioi (1 : ℝ), gaussThetaDual (a : UnitAddCircle) (b : UnitAddCircle) x‖ ≤
      0.2487 / π := by
    refine norm_integral_Ioi_one_le hpi fun x hx => ?_
    have := norm_thetaDual_le a b hx.le
    simpa [neg_mul] using this
  calc ‖(∫ x in Ioi (1 : ℝ), (gaussTheta (a : UnitAddCircle) (b : UnitAddCircle) x -
          thetaMain a b x)) + mainL a b +
        (∫ x in Ioi (1 : ℝ), gaussThetaDual (a : UnitAddCircle) (b : UnitAddCircle) x) - mainL a b‖
      = ‖(∫ x in Ioi (1 : ℝ), (gaussTheta (a : UnitAddCircle) (b : UnitAddCircle) x -
          thetaMain a b x)) +
        (∫ x in Ioi (1 : ℝ), gaussThetaDual (a : UnitAddCircle) (b : UnitAddCircle) x)‖ := by
        congr 1; ring
    _ ≤ 15.2 * Real.exp (-π) / π + 0.2487 / π := (norm_add_le _ _).trans (add_le_add e1 e2)
    _ = (15.2 * Real.exp (-π) + 0.2487) / π := by ring

end ZInQ.Contrib.T21Proof
