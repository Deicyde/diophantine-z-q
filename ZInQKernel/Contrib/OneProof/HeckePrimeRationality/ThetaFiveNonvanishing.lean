import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.NumberTheory.Modular
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Nonvanishing of the odd theta function at nonzero 5-torsion points

For `τ` in the upper half-plane and integers `a, b` not both divisible by `5`,
the two-variable Jacobi theta function `jacobiTheta₂` (the `θ₃` normalization of
Mathlib) does not vanish at `(a τ + b) / 5 + (τ + 1) / 2`. Up to a nowhere-vanishing
exponential factor this is the odd theta function `θ₁` at a nonzero 5-torsion point.

Proof outline.
* Quasi-periodicity reduces `(a, b)` modulo `5`.
* The `T` and `S` transformation laws of `jacobiTheta₂` (the `S` law is Mathlib's
  `jacobiTheta₂_functional_equation`) show that the statement "nonzero for every
  admissible `(a, b)`" at `τ` is equivalent to the same statement at `T • τ` and at
  `S • τ`. Since `S` and `T` generate `SL(2, ℤ)`, it is `SL(2, ℤ)`-invariant.
* Every point is `SL(2, ℤ)`-equivalent to a point of the standard fundamental domain,
  where `4 (Im τ)^2 ≥ 3`. There an explicit dominant-term estimate of the theta series
  proves nonvanishing: one dominant term when `5 ∤ a`, two dominant terms summing to
  `1 - exp(-2π i b / 5)` when `5 ∣ a`.

No product formula and no description of the zero set is used.
-/

noncomputable section

open Complex ModularGroup
open scoped Modular Real UpperHalfPlane MatrixGroups

namespace ZInQ.Contrib.HeckePrimeRationality.ThetaFive

/-! ### Elementary transformation laws -/

/-- `θ(z, τ + 1) = θ(z + 1/2, τ)`. -/
theorem jacobiTheta₂_add_one_right (z τ : ℂ) :
    jacobiTheta₂ z (τ + 1) = jacobiTheta₂ (z + 1 / 2) τ := by
  unfold jacobiTheta₂
  refine tsum_congr fun n => ?_
  obtain ⟨m, hm⟩ := Int.even_mul_pred_self n
  have hm' : ((n : ℂ) * ((n : ℂ) - 1)) = (m : ℂ) + m := by exact_mod_cast hm
  have h : 2 * (π : ℂ) * I * n * z + π * I * n ^ 2 * (τ + 1) =
      (2 * π * I * n * (z + 1 / 2) + π * I * n ^ 2 * τ) + m * (2 * π * I) := by
    linear_combination (π * I) * hm'
  simp only [jacobiTheta₂_term]
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Integer periodicity in `z`. -/
theorem jacobiTheta₂_add_int_left (z τ : ℂ) (k : ℤ) :
    jacobiTheta₂ (z + k) τ = jacobiTheta₂ z τ := by
  unfold jacobiTheta₂
  refine tsum_congr fun n => ?_
  have h : 2 * (π : ℂ) * I * n * (z + k) + π * I * n ^ 2 * τ =
      (2 * π * I * n * z + π * I * n ^ 2 * τ) + ((n * k : ℤ) : ℂ) * (2 * π * I) := by
    push_cast; ring
  simp only [jacobiTheta₂_term]
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem ne_zero_add_tau_iff (z τ : ℂ) :
    jacobiTheta₂ (z + τ) τ ≠ 0 ↔ jacobiTheta₂ z τ ≠ 0 := by
  rw [jacobiTheta₂_add_left']
  exact ⟨fun h h0 => h (by rw [h0, mul_zero]), fun h => mul_ne_zero (Complex.exp_ne_zero _) h⟩

theorem ne_zero_add_int_mul_tau_iff (z τ : ℂ) (m : ℤ) :
    jacobiTheta₂ (z + m * τ) τ ≠ 0 ↔ jacobiTheta₂ z τ ≠ 0 := by
  induction m using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have h : z + ((k + 1 : ℤ) : ℂ) * τ = (z + ((k : ℤ) : ℂ) * τ) + τ := by push_cast; ring
    rw [h, ne_zero_add_tau_iff, ih]
  | pred k ih =>
    rw [← ih, ← ne_zero_add_tau_iff]
    have h : z + ((-(k : ℤ) - 1 : ℤ) : ℂ) * τ + τ = z + ((-(k : ℤ) : ℤ) : ℂ) * τ := by
      push_cast; ring
    rw [h]

/-! ### The shifted theta function and its symmetries -/

/-- `θ₃` shifted to the nonzero torsion point `(a τ + b) / 5` of the odd theta function. -/
def thetaShift (a b : ℤ) (τ : ℂ) : ℂ :=
  jacobiTheta₂ (((a : ℂ) * τ + b) / 5 + (τ + 1) / 2) τ

/-- Admissible pairs: not both divisible by `5`. -/
def Good (a b : ℤ) : Prop := ¬ (5 ∣ a ∧ 5 ∣ b)

theorem thetaShift_ne_zero_shift_iff (a b m n : ℤ) (τ : ℂ) :
    thetaShift (a + 5 * m) (b + 5 * n) τ ≠ 0 ↔ thetaShift a b τ ≠ 0 := by
  unfold thetaShift
  have h : (((a + 5 * m : ℤ) : ℂ) * τ + ((b + 5 * n : ℤ) : ℂ)) / 5 + (τ + 1) / 2 =
      ((((a : ℂ) * τ + b) / 5 + (τ + 1) / 2) + (m : ℂ) * τ) + (n : ℂ) := by
    push_cast; ring
  rw [h, jacobiTheta₂_add_int_left, ne_zero_add_int_mul_tau_iff]

theorem thetaShift_add_one (a b : ℤ) (τ : ℂ) :
    thetaShift a b (τ + 1) = thetaShift a (a + b) τ := by
  unfold thetaShift
  rw [jacobiTheta₂_add_one_right]
  have h : ((a : ℂ) * (τ + 1) + b) / 5 + (τ + 1 + 1) / 2 + 1 / 2 =
      (((a : ℂ) * τ + ((a + b : ℤ) : ℂ)) / 5 + (τ + 1) / 2) + ((1 : ℤ) : ℂ) := by
    push_cast; ring
  rw [h, jacobiTheta₂_add_int_left]

theorem thetaShift_ne_zero_S_iff (a b : ℤ) {τ : ℂ} (hτ : τ ≠ 0) :
    thetaShift a b τ ≠ 0 ↔ thetaShift (-b) a (-1 / τ) ≠ 0 := by
  have hc : (1 : ℂ) / (-I * τ) ^ (1 / 2 : ℂ) ≠ 0 := by
    refine one_div_ne_zero ?_
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h => mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hτ h.1
  have hz : (((a : ℂ) * τ + b) / 5 + (τ + 1) / 2) / τ =
      ((((-b : ℤ) : ℂ) * (-1 / τ) + a) / 5 + ((-1 / τ) + 1) / 2) + ((-1 : ℤ) : ℂ) * (-1 / τ) := by
    field_simp
    push_cast
    ring
  have key := ne_zero_add_int_mul_tau_iff
    ((((-b : ℤ) : ℂ) * (-1 / τ) + a) / 5 + ((-1 / τ) + 1) / 2) (-1 / τ) (-1)
  unfold thetaShift
  rw [jacobiTheta₂_functional_equation, hz]
  constructor
  · intro h
    refine key.mp fun h0 => h ?_
    rw [h0, mul_zero]
  · intro h
    exact mul_ne_zero (mul_ne_zero hc (Complex.exp_ne_zero _)) (key.mpr h)

/-- The statement to be proved at a point. -/
def Prop5 (τ : ℍ) : Prop := ∀ a b : ℤ, Good a b → thetaShift a b (τ : ℂ) ≠ 0

theorem good_T {a b : ℤ} (h : Good a b) (c : ℤ) : Good a (c * a + b) := by
  rintro ⟨ha, hb⟩
  exact h ⟨ha, by simpa using (Int.dvd_add_right (Dvd.dvd.mul_left ha c)).mp hb⟩

theorem good_S {a b : ℤ} (h : Good a b) : Good (-b) a := by
  rintro ⟨hb, ha⟩
  exact h ⟨ha, by simpa using hb⟩

theorem coe_T_smul (τ : ℍ) : ((T • τ : ℍ) : ℂ) = (τ : ℂ) + 1 := by
  rw [UpperHalfPlane.modular_T_smul, UpperHalfPlane.coe_vadd]; push_cast; ring

theorem coe_S_smul (τ : ℍ) : ((S • τ : ℍ) : ℂ) = -1 / (τ : ℂ) := by
  rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, inv_neg, neg_div, one_div]

theorem prop5_T_iff (τ : ℍ) : Prop5 (T • τ) ↔ Prop5 τ := by
  unfold Prop5
  rw [coe_T_smul]
  constructor
  · intro h a b hab
    have := h a (b - a) (by
      have h' := good_T hab (-1)
      rwa [show (-1) * a + b = b - a by ring] at h')
    rwa [thetaShift_add_one, show a + (b - a) = b by ring] at this
  · intro h a b hab
    rw [thetaShift_add_one]
    exact h a (a + b) (by
      have h' := good_T hab 1
      rwa [one_mul] at h')

theorem prop5_S_iff (τ : ℍ) : Prop5 (S • τ) ↔ Prop5 τ := by
  unfold Prop5
  rw [coe_S_smul]
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have hτ' : -1 / (τ : ℂ) ≠ 0 := div_ne_zero (neg_ne_zero.mpr one_ne_zero) hτ
  have hinv : -1 / (-1 / (τ : ℂ)) = τ := by field_simp
  constructor
  · intro h a b hab
    rw [thetaShift_ne_zero_S_iff a b hτ]
    exact h (-b) a (good_S hab)
  · intro h a b hab
    rw [thetaShift_ne_zero_S_iff a b hτ', hinv]
    exact h (-b) a (good_S hab)

theorem prop5_smul_iff (g : SL(2, ℤ)) (τ : ℍ) : Prop5 (g • τ) ↔ Prop5 τ := by
  have hg : g ∈ Subgroup.closure ({S, T} : Set SL(2, ℤ)) := by
    rw [SpecialLinearGroup.SL2Z_generators]; exact Subgroup.mem_top g
  induction hg using Subgroup.closure_induction generalizing τ with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact prop5_S_iff τ
    · exact prop5_T_iff τ
  | one => rw [one_smul]
  | mul x y _ _ hx hy =>
    rw [mul_smul]
    exact (hx (y • τ)).trans (hy τ)
  | inv x _ hx =>
    have h := hx (x⁻¹ • τ)
    rw [smul_inv_smul] at h
    exact h.symm

/-! ### Dominant-term estimates -/

theorem norm_tsum_sub_finset_le {f : ℤ → ℂ} {M : ℤ → ℝ} (hf : Summable f) (hM : Summable M)
    (s : Finset ℤ) (h : ∀ n ∉ s, ‖f n‖ ≤ M n) :
    ‖(∑' n, f n) - ∑ n ∈ s, f n‖ ≤ (∑' n, M n) - ∑ n ∈ s, M n := by
  rw [← hf.sum_add_tsum_compl (s := s), ← hM.sum_add_tsum_compl (s := s),
    add_sub_cancel_left, add_sub_cancel_left]
  have hle : ∀ x : ↥((s : Set ℤ)ᶜ), ‖f x‖ ≤ M x := fun x => h x (fun hx => x.2 (Finset.mem_coe.mpr hx))
  have hMs : Summable (fun x : ↥((s : Set ℤ)ᶜ) => M x) := hM.subtype _
  have hfs : Summable (fun x : ↥((s : Set ℤ)ᶜ) => ‖f x‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hMs
  exact (norm_tsum_le_tsum_norm hfs).trans (hfs.tsum_mono hMs hle)

theorem hasSum_geom_natAbs (C : ℝ) {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    HasSum (fun n : ℤ => C * ρ ^ n.natAbs) (C / (1 - ρ) + C * ρ / (1 - ρ)) := by
  have hg := hasSum_geometric_of_lt_one h0 h1
  refine HasSum.of_nat_of_neg_add_one ?_ ?_
  · simpa [div_eq_mul_inv] using hg.mul_left C
  · have : (fun n : ℕ => C * ρ ^ (-((n : ℤ) + 1)).natAbs) = fun n : ℕ => (C * ρ) * ρ ^ n := by
      funext n
      rw [Int.natAbs_neg, show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring,
        Int.natAbs_natCast, pow_succ]
      ring
    rw [this]
    simpa [div_eq_mul_inv] using hg.mul_left (C * ρ)

/-- `exp (-1) < 0.371`. -/
theorem exp_neg_one_lt : Real.exp (-1) < 0.371 := by
  rw [Real.exp_neg]
  have h := Real.exp_one_gt_d9
  rw [inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
  calc (0.371 : ℝ)⁻¹ < 2.7182818283 := by norm_num
    _ < Real.exp 1 := h

/-- On the region `4 (Im τ)^2 ≥ 3`, the parameter `X = π Im τ` exceeds `5/2`. -/
theorem five_halves_lt_pi_mul_im {y : ℝ} (hy : 0 < y) (h3 : 3 ≤ 4 * y ^ 2) : 5 / 2 < Real.pi * y := by
  have hy' : 5 / 6 < y := by nlinarith
  nlinarith [Real.pi_gt_three]

/-- One dominant term: if `|Im z| ≤ (3/10) Im τ` and `4 (Im τ)^2 ≥ 3` then `θ(z, τ) ≠ 0`. -/
theorem jacobiTheta₂_ne_zero_of_abs_im_le {z τ : ℂ} (hy : 0 < τ.im) (h3 : 3 ≤ 4 * τ.im ^ 2)
    (hz : |z.im| ≤ 3 / 10 * τ.im) : jacobiTheta₂ z τ ≠ 0 := by
  set y := τ.im with hydef
  set X := Real.pi * y with hX
  have hX5 : 5 / 2 < X := five_halves_lt_pi_mul_im hy h3
  set ρ := Real.exp (-X) with hρ
  set C := Real.exp (3 / 5 * X) with hC
  have hρ0 : 0 ≤ ρ := (Real.exp_pos _).le
  have hρ1 : ρ < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hM := hasSum_geom_natAbs C hρ0 hρ1
  have hf := hasSum_jacobiTheta₂_term z hy
  have hbound : ∀ n ∉ ({0} : Finset ℤ), ‖jacobiTheta₂_term n z τ‖ ≤ C * ρ ^ n.natAbs := by
    intro n _
    refine (norm_jacobiTheta₂_term_le hy hz le_rfl n).trans ?_
    have hk : ((n.natAbs : ℕ) : ℝ) = ((|n| : ℤ) : ℝ) := by
      rw [Nat.cast_natAbs]
    have hsq : (n : ℝ) ^ 2 = ((n.natAbs : ℕ) : ℝ) ^ 2 := by rw [hk, Int.cast_abs, sq_abs]
    rw [hρ, hC, ← Real.exp_nat_mul, ← Real.exp_add, Real.exp_le_exp, ← hk, hsq]
    set k : ℝ := ((n.natAbs : ℕ) : ℝ) with hkdef
    have hkk : (k - 1) * (k - 3 / 5) ≥ 0 := by
      rcases Nat.eq_zero_or_pos n.natAbs with h0 | hpos
      · rw [hkdef, h0]; norm_num
      · have : (1 : ℝ) ≤ k := by rw [hkdef]; exact_mod_cast hpos
        nlinarith
    have hXp : 0 < X := by linarith
    rw [hX]
    nlinarith [mul_nonneg hXp.le hkk]
  have key := norm_tsum_sub_finset_le hf.summable hM.summable {0} hbound
  rw [hf.tsum_eq, hM.tsum_eq] at key
  simp only [Finset.sum_singleton, Int.natAbs_zero, pow_zero, mul_one] at key
  have h0term : jacobiTheta₂_term 0 z τ = 1 := by simp [jacobiTheta₂_term]
  rw [h0term] at key
  -- the bound `2 C ρ / (1 - ρ) < 1`
  have hu := exp_neg_one_lt
  have hCρ : C * ρ ≤ Real.exp (-1) := by
    rw [hC, hρ, ← Real.exp_add, Real.exp_le_exp]; linarith
  have hρu : ρ ≤ Real.exp (-1) * Real.exp (-1) := by
    rw [hρ, ← Real.exp_add, Real.exp_le_exp]; linarith
  have hu0 : 0 < Real.exp (-1) := Real.exp_pos _
  have hlt : C / (1 - ρ) + C * ρ / (1 - ρ) - C < 1 := by
    have h1ρ : 0 < 1 - ρ := by linarith
    have : C / (1 - ρ) + C * ρ / (1 - ρ) - C = 2 * (C * ρ) / (1 - ρ) := by
      field_simp; ring
    rw [this, div_lt_one h1ρ]
    nlinarith
  intro h0
  rw [h0, zero_sub, norm_neg, norm_one] at key
  linarith

/-- `cos (2 π b / 5) ≤ 1/2` for `b ∈ {±1, ±2}`. -/
theorem cos_two_pi_mul_div_five_le {b : ℤ} (hb : b = 1 ∨ b = 2 ∨ b = -1 ∨ b = -2) :
    Real.cos (2 * Real.pi * b / 5) ≤ 1 / 2 := by
  have hpi := Real.pi_pos
  have key : ∀ c : ℝ, (c = 1 ∨ c = 2) → Real.cos (2 * Real.pi * c / 5) ≤ 1 / 2 := by
    intro c hc
    rw [← Real.cos_pi_div_three]
    apply Real.cos_le_cos_of_nonneg_of_le_pi (by positivity)
    · rcases hc with rfl | rfl <;> linarith
    · rcases hc with rfl | rfl <;> linarith
  rcases hb with rfl | rfl | rfl | rfl
  · simpa using key 1 (Or.inl rfl)
  · simpa using key 2 (Or.inr rfl)
  · have := key 1 (Or.inl rfl)
    rw [show 2 * Real.pi * ((-1 : ℤ) : ℝ) / 5 = -(2 * Real.pi * 1 / 5) by push_cast; ring,
      Real.cos_neg]
    exact this
  · have := key 2 (Or.inr rfl)
    rw [show 2 * Real.pi * ((-2 : ℤ) : ℝ) / 5 = -(2 * Real.pi * 2 / 5) by push_cast; ring,
      Real.cos_neg]
    exact this

/-- Two dominant terms: `θ(b/5 + (τ+1)/2, τ) ≠ 0` for `b ∈ {±1, ±2}` when `4 (Im τ)^2 ≥ 3`. -/
theorem jacobiTheta₂_ne_zero_half_shift {τ : ℂ} (hy : 0 < τ.im) (h3 : 3 ≤ 4 * τ.im ^ 2) {b : ℤ}
    (hb : b = 1 ∨ b = 2 ∨ b = -1 ∨ b = -2) :
    jacobiTheta₂ ((b : ℂ) / 5 + (τ + 1) / 2) τ ≠ 0 := by
  set z : ℂ := (b : ℂ) / 5 + (τ + 1) / 2 with hzdef
  set y := τ.im with hydef
  have hzim : z.im = y / 2 := by
    rw [hzdef]; simp [hydef]
  set X := Real.pi * y with hX
  have hX5 : 5 / 2 < X := five_halves_lt_pi_mul_im hy h3
  set ρ := Real.exp (-X) with hρ
  have hρ0 : 0 ≤ ρ := (Real.exp_pos _).le
  have hρ1 : ρ < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hM := hasSum_geom_natAbs 1 hρ0 hρ1
  have hf := hasSum_jacobiTheta₂_term z hy
  have hbound : ∀ n ∉ ({0, -1} : Finset ℤ), ‖jacobiTheta₂_term n z τ‖ ≤ 1 * ρ ^ n.natAbs := by
    intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    rw [norm_jacobiTheta₂_term, hzim, one_mul, hρ, ← Real.exp_nat_mul, Real.exp_le_exp]
    have hint : |n| ≤ n ^ 2 + n := by
      rcases le_or_gt 0 n with h | h
      · rw [abs_of_nonneg h]; nlinarith
      · rw [abs_of_neg h]
        have : n ≤ -2 := by omega
        nlinarith
    have hreal : ((n.natAbs : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 + n := by
      rw [Nat.cast_natAbs]; exact_mod_cast hint
    have hXp : 0 < y := hy
    rw [hX]
    nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_left hreal (mul_pos Real.pi_pos hy).le]
  have key := norm_tsum_sub_finset_le hf.summable hM.summable {0, -1} hbound
  rw [hf.tsum_eq, hM.tsum_eq] at key
  rw [Finset.sum_pair (by norm_num), Finset.sum_pair (by norm_num)] at key
  simp only [Int.natAbs_zero, pow_zero, mul_one, one_mul, Int.natAbs_neg, Int.natAbs_one,
    pow_one] at key
  -- the two dominant terms
  have h0term : jacobiTheta₂_term 0 z τ = 1 := by simp [jacobiTheta₂_term]
  have h1term : jacobiTheta₂_term (-1) z τ = -Complex.exp (-(2 * π * I * b / 5)) := by
    simp only [jacobiTheta₂_term, hzdef]
    have : 2 * (π : ℂ) * I * ((-1 : ℤ) : ℂ) * ((b : ℂ) / 5 + (τ + 1) / 2) +
        π * I * ((-1 : ℤ) : ℂ) ^ 2 * τ = -(2 * π * I * b / 5) + (π * I) * (-1 : ℤ) := by
      push_cast; ring
    rw [this, Complex.exp_add, mul_comm (π * I : ℂ), Complex.exp_int_mul,
      Complex.exp_pi_mul_I]
    norm_num
  rw [h0term, h1term] at key
  -- lower bound for the dominant part
  have hdom : (1 / 2 : ℝ) ≤ ‖(1 : ℂ) + -Complex.exp (-(2 * π * I * b / 5))‖ := by
    refine le_trans ?_ (Complex.re_le_norm _)
    have hre : ((1 : ℂ) + -Complex.exp (-(2 * π * I * b / 5))).re =
        1 - Real.cos (2 * Real.pi * b / 5) := by
      rw [show -(2 * (π : ℂ) * I * b / 5) = ((-(2 * Real.pi * b / 5) : ℝ) : ℂ) * I by
        push_cast; ring]
      rw [Complex.add_re, Complex.neg_re, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
      simp only [Complex.one_re]
      ring
    rw [hre]
    linarith [cos_two_pi_mul_div_five_le hb]
  -- upper bound for the tail
  have hu := exp_neg_one_lt
  have hu0 : 0 < Real.exp (-1) := Real.exp_pos _
  have hρu : ρ ≤ Real.exp (-1) * Real.exp (-1) := by
    rw [hρ, ← Real.exp_add, Real.exp_le_exp]; linarith
  have htail : 1 / (1 - ρ) + ρ / (1 - ρ) - (1 + ρ) < 1 / 2 := by
    have h1ρ : 0 < 1 - ρ := by linarith
    have : 1 / (1 - ρ) + ρ / (1 - ρ) - (1 + ρ) = ρ * (1 + ρ) / (1 - ρ) := by
      field_simp; ring
    rw [this, div_lt_iff₀ h1ρ]
    nlinarith
  intro h0
  rw [h0, zero_sub, norm_neg] at key
  linarith

/-! ### The fundamental domain and the global statement -/

theorem prop5_of_mem_fd {τ : ℍ} (hτ : τ ∈ 𝒟) : Prop5 τ := by
  intro a b hab
  have hy : 0 < (τ : ℂ).im := τ.im_pos
  have h3 : 3 ≤ 4 * (τ : ℂ).im ^ 2 := three_le_four_mul_im_sq_of_mem_fd hτ
  by_cases ha : a % 5 = 0
  · -- `5 ∣ a`, so `5 ∤ b`
    have h5a : (5 : ℤ) ∣ a := Int.dvd_of_emod_eq_zero ha
    have h5b : ¬ (5 : ℤ) ∣ b := fun h => hab ⟨h5a, h⟩
    have hbr : (b + 2) % 5 - 2 = 1 ∨ (b + 2) % 5 - 2 = 2 ∨ (b + 2) % 5 - 2 = -1 ∨
        (b + 2) % 5 - 2 = -2 := by omega
    have e : thetaShift a b (τ : ℂ) =
        thetaShift (0 + 5 * (a / 5)) (((b + 2) % 5 - 2) + 5 * ((b + 2) / 5)) (τ : ℂ) := by
      congr 1 <;> omega
    rw [e, thetaShift_ne_zero_shift_iff]
    unfold thetaShift
    have hz : ((((0 : ℤ) : ℂ) * (τ : ℂ) + (((b + 2) % 5 - 2 : ℤ) : ℂ)) / 5 + ((τ : ℂ) + 1) / 2) =
        (((b + 2) % 5 - 2 : ℤ) : ℂ) / 5 + ((τ : ℂ) + 1) / 2 := by push_cast; ring
    rw [hz]
    exact jacobiTheta₂_ne_zero_half_shift hy h3 hbr
  · have har : a % 5 - 5 = -4 ∨ a % 5 - 5 = -3 ∨ a % 5 - 5 = -2 ∨ a % 5 - 5 = -1 := by omega
    have e : thetaShift a b (τ : ℂ) = thetaShift ((a % 5 - 5) + 5 * (a / 5 + 1)) (b + 5 * 0) (τ : ℂ) := by
      congr 1 <;> omega
    rw [e, thetaShift_ne_zero_shift_iff]
    unfold thetaShift
    apply jacobiTheta₂_ne_zero_of_abs_im_le hy h3
    set a0 : ℤ := a % 5 - 5
    have him : ((((a0 : ℂ) * (τ : ℂ) + (b : ℂ)) / 5 + ((τ : ℂ) + 1) / 2)).im =
        ((a0 : ℝ) / 5 + 1 / 2) * (τ : ℂ).im := by
      simp; ring
    rw [him, abs_mul, abs_of_pos hy]
    refine mul_le_mul_of_nonneg_right ?_ hy.le
    rw [abs_le]
    rcases har with h | h | h | h <;> rw [h] <;> norm_num

/-- **Nonvanishing of the odd theta function at nonzero 5-torsion points.** For every `τ` in
the upper half-plane and integers `a, b` not both divisible by `5`, Mathlib's two-variable
theta function `jacobiTheta₂` does not vanish at `(a τ + b)/5 + (τ + 1)/2`. -/
theorem jacobiTheta₂_fiveTorsion_ne_zero (τ : ℍ) (a b : ℤ) (h : ¬ (5 ∣ a ∧ 5 ∣ b)) :
    jacobiTheta₂ (((a : ℂ) * τ + b) / 5 + ((τ : ℂ) + 1) / 2) (τ : ℂ) ≠ 0 := by
  obtain ⟨g, hg⟩ := exists_smul_mem_fd τ
  exact (prop5_smul_iff g τ).mp (prop5_of_mem_fd hg) a b h

end ZInQ.Contrib.HeckePrimeRationality.ThetaFive
