import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.ThetaFiveTorsionDefinitions
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.BoundedAtCusp
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold

/-!
# Weight-one modular forms on `Γ₁(5)` from five-torsion theta quotients

For integers `a, b` not both divisible by `5`, let
`F_{a,b}(τ) = a/5 + 1/2 + θ'(z, τ) / (2π i θ(z, τ))`, `z = (a τ + b)/5 + (τ + 1)/2`,
where `θ = jacobiTheta₂` (Mathlib's `θ₃` normalization) and `θ'` is its `z`-derivative
`jacobiTheta₂'`. This is `torsionLogDerivative a b`.

Main results.
* `F_T`, `F_S`: `F_{a,b}(τ + 1) = F_{a,a+b}(τ)` and `F_{a,b}(-1/τ) = τ F_{b,-a}(τ)`, obtained from
  the transformation laws of `θ` and `θ'` (the `S` law from Mathlib's functional equations).
  The constant `a/5 + 1/2` absorbs the quasi-periodicity anomaly of the logarithmic derivative.
* `F_slash`: `F_v ∣[1] γ = F_{v γ}` for every `γ ∈ SL(2, ℤ)` (row action), by generation.
* `F_shift`: `F_v` depends only on `v` modulo `5`.
* Holomorphy on `ℍ` (`θ'` via locally uniform convergence of its series) and boundedness at
  `i∞` of every `F_v` (explicit dominant-term estimates), hence at every cusp.
* `torsionForm b hb : ModularForm ((Gamma1 5).map (mapGL ℝ)) 1` with underlying function
  `torsionLogDerivative 0 b`, for `¬ 5 ∣ b`.

No product formula, Fourier expansion, dimension, basis or rationality statement is used.
-/

noncomputable section

open Complex ModularGroup
open scoped Real UpperHalfPlane MatrixGroups ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.ThetaFiveTorsion

/-! ### The logarithmic derivative `θ'/(2π i θ)` and its transformation laws -/

/-- `θ'(z, τ) / (2π i θ(z, τ))`. -/
def logDer (z τ : ℂ) : ℂ := jacobiTheta₂' z τ / (2 * (π : ℂ) * I * jacobiTheta₂ z τ)

theorem two_pi_I_ne_zero : (2 * (π : ℂ) * I) ≠ 0 := by
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  exact mul_ne_zero (mul_ne_zero two_ne_zero hpi) I_ne_zero

theorem term_add_one_right (n : ℤ) (z τ : ℂ) :
    jacobiTheta₂_term n z (τ + 1) = jacobiTheta₂_term n (z + 1 / 2) τ := by
  obtain ⟨m, hm⟩ := Int.even_mul_pred_self n
  have hm' : ((n : ℂ) * ((n : ℂ) - 1)) = (m : ℂ) + m := by exact_mod_cast hm
  have h : 2 * (π : ℂ) * I * n * z + π * I * n ^ 2 * (τ + 1) =
      (2 * π * I * n * (z + 1 / 2) + π * I * n ^ 2 * τ) + m * (2 * π * I) := by
    linear_combination (π * I) * hm'
  simp only [jacobiTheta₂_term]
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem term_add_int_left (n k : ℤ) (z τ : ℂ) :
    jacobiTheta₂_term n (z + k) τ = jacobiTheta₂_term n z τ := by
  have h : 2 * (π : ℂ) * I * n * (z + k) + π * I * n ^ 2 * τ =
      (2 * π * I * n * z + π * I * n ^ 2 * τ) + ((n * k : ℤ) : ℂ) * (2 * π * I) := by
    push_cast; ring
  simp only [jacobiTheta₂_term]
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem jacobiTheta₂'_add_one_right (z τ : ℂ) :
    jacobiTheta₂' z (τ + 1) = jacobiTheta₂' (z + 1 / 2) τ := by
  unfold jacobiTheta₂' jacobiTheta₂'_term
  exact tsum_congr fun n => by rw [term_add_one_right]

theorem jacobiTheta₂'_add_int_left (z τ : ℂ) (k : ℤ) :
    jacobiTheta₂' (z + k) τ = jacobiTheta₂' z τ := by
  unfold jacobiTheta₂' jacobiTheta₂'_term
  exact tsum_congr fun n => by rw [term_add_int_left]

theorem logDer_add_int_left (z τ : ℂ) (k : ℤ) : logDer (z + k) τ = logDer z τ := by
  unfold logDer
  rw [jacobiTheta₂'_add_int_left, ThetaFive.jacobiTheta₂_add_int_left]

theorem logDer_add_one_right (z τ : ℂ) : logDer z (τ + 1) = logDer (z + 1 / 2) τ := by
  unfold logDer
  rw [jacobiTheta₂'_add_one_right, ThetaFive.jacobiTheta₂_add_one_right]

theorem logDer_add_tau {z τ : ℂ} (h : jacobiTheta₂ z τ ≠ 0) :
    logDer (z + τ) τ = logDer z τ - 1 := by
  unfold logDer
  rw [jacobiTheta₂_add_left', jacobiTheta₂'_add_left']
  have he := Complex.exp_ne_zero (-π * I * (τ + 2 * z))
  have h2 := two_pi_I_ne_zero
  field_simp

theorem theta_S_ne_zero {z τ : ℂ} (h : jacobiTheta₂ z τ ≠ 0) :
    jacobiTheta₂ (z / τ) (-1 / τ) ≠ 0 := by
  intro h0
  apply h
  rw [jacobiTheta₂_functional_equation, h0, mul_zero]

theorem logDer_S {z τ : ℂ} (hτ : τ ≠ 0) (h : jacobiTheta₂ z τ ≠ 0) :
    logDer (z / τ) (-1 / τ) = τ * logDer z τ + z := by
  have h1 := theta_S_ne_zero h
  have hc : (-I * τ) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h' => mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hτ h'.1
  have he := Complex.exp_ne_zero (-π * I * z ^ 2 / τ)
  have h2 := two_pi_I_ne_zero
  unfold logDer
  rw [jacobiTheta₂_functional_equation z τ, jacobiTheta₂'_functional_equation z τ]
  generalize jacobiTheta₂ (z / τ) (-1 / τ) = A at h1 ⊢
  generalize jacobiTheta₂' (z / τ) (-1 / τ) = B
  field_simp
  ring

/-! ### The family `F_v` and its laws -/

/-- Admissible index pairs: not both divisible by `5`. -/
def Good (v : ℤ × ℤ) : Prop := ¬ (5 ∣ v.1 ∧ 5 ∣ v.2)

/-- The family `F_{a,b} = torsionLogDerivative a b`. -/
def F (v : ℤ × ℤ) : ℍ → ℂ := fun τ => torsionLogDerivative v.1 v.2 τ

theorem F_apply (a b : ℤ) (τ : ℍ) :
    F (a, b) τ = (a : ℂ) / 5 + 1 / 2 + logDer (shiftedPoint a b τ) τ := rfl

theorem theta_ne_zero {a b : ℤ} (h : Good (a, b)) (τ : ℍ) :
    jacobiTheta₂ (shiftedPoint a b τ) τ ≠ 0 :=
  ThetaFive.jacobiTheta₂_fiveTorsion_ne_zero τ a b h

theorem F_add_five_fst {a b : ℤ} (h : Good (a, b)) (τ : ℍ) : F (a + 5, b) τ = F (a, b) τ := by
  rw [F_apply, F_apply]
  have hz : shiftedPoint (a + 5) b τ = shiftedPoint a b τ + τ := by
    unfold shiftedPoint; push_cast; ring
  rw [hz, logDer_add_tau (theta_ne_zero h τ)]
  push_cast; ring

theorem F_add_five_snd (a b : ℤ) (τ : ℍ) : F (a, b + 5) τ = F (a, b) τ := by
  rw [F_apply, F_apply]
  have hz : shiftedPoint a (b + 5) τ = shiftedPoint a b τ + ((1 : ℤ) : ℂ) := by
    unfold shiftedPoint; push_cast; ring
  rw [hz, logDer_add_int_left]

theorem good_shift {a b : ℤ} (m n : ℤ) : Good (a + 5 * m, b + 5 * n) ↔ Good (a, b) := by
  unfold Good
  simp only
  rw [dvd_add_left (dvd_mul_right 5 m), dvd_add_left (dvd_mul_right 5 n)]

/-- `F_v` depends only on `v` modulo `5`. -/
theorem F_shift {a b : ℤ} (h : Good (a, b)) (m n : ℤ) (τ : ℍ) :
    F (a + 5 * m, b + 5 * n) τ = F (a, b) τ := by
  have hsnd : ∀ a' b' : ℤ, ∀ n : ℤ, F (a', b' + 5 * n) τ = F (a', b') τ := by
    intro a' b' n
    induction n using Int.induction_on with
    | zero => simp
    | succ k ih =>
      rw [show b' + 5 * ((k : ℤ) + 1) = (b' + 5 * k) + 5 by ring, F_add_five_snd, ih]
    | pred k ih =>
      rw [← ih, show b' + 5 * (-(k : ℤ)) = (b' + 5 * (-(k : ℤ) - 1)) + 5 by ring,
        F_add_five_snd]
  have hfst : ∀ m : ℤ, F (a + 5 * m, b) τ = F (a, b) τ := by
    intro m
    induction m using Int.induction_on with
    | zero => simp
    | succ k ih =>
      have hg : Good (a + 5 * k, b) := by
        have := (good_shift (a := a) (b := b) k 0).mpr h
        simpa using this
      rw [show a + 5 * ((k : ℤ) + 1) = (a + 5 * k) + 5 by ring, F_add_five_fst hg, ih]
    | pred k ih =>
      have hg : Good (a + 5 * (-(k : ℤ) - 1), b) := by
        have := (good_shift (a := a) (b := b) (-(k : ℤ) - 1) 0).mpr h
        simpa using this
      rw [← ih, show a + 5 * (-(k : ℤ)) = (a + 5 * (-(k : ℤ) - 1)) + 5 by ring,
        F_add_five_fst hg]
  rw [hsnd, hfst]

/-- The `T` law: `F_{a,b}(τ + 1) = F_{a,a+b}(τ)`. -/
theorem F_T (a b : ℤ) (τ : ℍ) : F (a, b) (T • τ) = F (a, a + b) τ := by
  rw [F_apply, F_apply]
  have h1 : shiftedPoint a b (T • τ) = ((a : ℂ) * ((τ : ℂ) + 1) + b) / 5 + ((τ : ℂ) + 1 + 1) / 2 := by
    unfold shiftedPoint; rw [ThetaFive.coe_T_smul]
  rw [h1, ThetaFive.coe_T_smul, logDer_add_one_right]
  have h2 : ((a : ℂ) * ((τ : ℂ) + 1) + b) / 5 + ((τ : ℂ) + 1 + 1) / 2 + 1 / 2 =
      shiftedPoint a (a + b) τ + ((1 : ℤ) : ℂ) := by
    unfold shiftedPoint; push_cast; ring
  rw [h2, logDer_add_int_left]

/-- The `S` law: `F_{a,b}(-1/τ) = τ F_{b,-a}(τ)`. -/
theorem F_S {a b : ℤ} (h : Good (b, -a)) (τ : ℍ) :
    F (a, b) (S • τ) = (τ : ℂ) * F (b, -a) τ := by
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have hθ := theta_ne_zero h τ
  rw [F_apply, F_apply]
  have h1 : shiftedPoint a b (S • τ) = shiftedPoint b (-a) τ / τ + (-1 / (τ : ℂ)) := by
    unfold shiftedPoint; rw [ThetaFive.coe_S_smul]; push_cast; field_simp; ring
  rw [h1, ThetaFive.coe_S_smul, logDer_add_tau (theta_S_ne_zero hθ), logDer_S hτ hθ]
  unfold shiftedPoint
  push_cast
  ring

/-! ### Covariance under `SL(2, ℤ)` -/

/-- The row action `v ↦ v γ`. -/
def act (v : ℤ × ℤ) (γ : SL(2, ℤ)) : ℤ × ℤ :=
  (v.1 * γ 0 0 + v.2 * γ 1 0, v.1 * γ 0 1 + v.2 * γ 1 1)

theorem act_mul (v : ℤ × ℤ) (γ δ : SL(2, ℤ)) : act (act v γ) δ = act v (γ * δ) := by
  refine Prod.ext ?_ ?_ <;>
    simp [act, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem act_one (v : ℤ × ℤ) : act v 1 = v := by
  refine Prod.ext ?_ ?_ <;> simp [act]

theorem act_S (a b : ℤ) : act (a, b) S = (b, -a) := by
  refine Prod.ext ?_ ?_ <;> simp [act, ModularGroup.coe_S]

theorem act_T (a b : ℤ) : act (a, b) T = (a, a + b) := by
  refine Prod.ext ?_ ?_ <;> simp [act, ModularGroup.coe_T]

theorem good_act {v : ℤ × ℤ} (h : Good v) (γ : SL(2, ℤ)) : Good (act v γ) := by
  rintro ⟨h1, h2⟩
  apply h
  have hv : act (act v γ) γ⁻¹ = v := by rw [act_mul, mul_inv_cancel, act_one]
  rw [← hv]
  set w := act v γ
  exact ⟨dvd_add (dvd_mul_of_dvd_left h1 _) (dvd_mul_of_dvd_left h2 _),
    dvd_add (dvd_mul_of_dvd_left h1 _) (dvd_mul_of_dvd_left h2 _)⟩

theorem F_slash_S {v : ℤ × ℤ} (h : Good v) : F v ∣[(1 : ℤ)] S = F (act v S) := by
  obtain ⟨a, b⟩ := v
  have hg : Good (b, -a) := by
    have := good_act h S
    rwa [act_S] at this
  funext τ
  rw [ModularForm.SL_slash_apply, act_S, F_S hg τ, ModularGroup.denom_S, zpow_neg_one]
  field_simp [τ.ne_zero]

theorem F_slash_T {v : ℤ × ℤ} (_h : Good v) : F v ∣[(1 : ℤ)] T = F (act v T) := by
  obtain ⟨a, b⟩ := v
  funext τ
  have hd : UpperHalfPlane.denom T τ = 1 := by
    rw [ModularGroup.denom_apply]; simp [ModularGroup.coe_T]
  rw [ModularForm.SL_slash_apply, act_T, F_T, hd]
  simp

/-- **Covariance**: `F_v ∣[1] γ = F_{v γ}` for all `γ ∈ SL(2, ℤ)`. -/
theorem F_slash (γ : SL(2, ℤ)) : ∀ v : ℤ × ℤ, Good v → F v ∣[(1 : ℤ)] γ = F (act v γ) := by
  have hg : γ ∈ Subgroup.closure ({S, T} : Set SL(2, ℤ)) := by
    rw [SpecialLinearGroup.SL2Z_generators]; exact Subgroup.mem_top γ
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact fun v hv => F_slash_S hv
    · exact fun v hv => F_slash_T hv
  | one =>
    intro v _
    rw [SlashAction.slash_one, act_one]
  | mul x y _ _ hx hy =>
    intro v hv
    rw [SlashAction.slash_mul, hx v hv, hy _ (good_act hv x), act_mul]
  | inv x _ hx =>
    intro v hv
    have hw := good_act hv x⁻¹
    have h1 := hx (act v x⁻¹) hw
    rw [act_mul, inv_mul_cancel, act_one] at h1
    rw [← h1, ← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]

/-! ### Holomorphy -/

/-- The torsion point as a function on `ℂ`. -/
def zc (a b : ℤ) (τ : ℂ) : ℂ := ((a : ℂ) * τ + b) / 5 + (τ + 1) / 2

theorem zc_im (a b : ℤ) (τ : ℂ) : (zc a b τ).im = ((a : ℝ) / 5 + 1 / 2) * τ.im := by
  simp [zc]; ring

theorem differentiableAt_theta_zc (a b : ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ (fun t => jacobiTheta₂ (zc a b t) t) τ := by
  have h1 : DifferentiableAt ℂ (fun t : ℂ => (zc a b t, t)) τ := by
    refine DifferentiableAt.prodMk ?_ differentiableAt_id
    unfold zc; fun_prop
  exact DifferentiableAt.comp (f := fun t : ℂ => (zc a b t, t))
    (g := fun p : ℂ × ℂ => jacobiTheta₂ p.1 p.2) τ
    (hasFDerivAt_jacobiTheta₂ (zc a b τ) hτ).differentiableAt h1

theorem differentiableAt_theta'_zc (a b : ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ (fun t => jacobiTheta₂' (zc a b t) t) τ := by
  set T₀ := τ.im / 2 with hT₀
  set T₁ := τ.im + 1 with hT₁
  set S₀ := (|(a : ℝ)| / 5 + 1 / 2) * T₁ with hS₀
  set U := {t : ℂ | T₀ < t.im ∧ t.im < T₁} with hUdef
  have hT : 0 < T₀ := by positivity
  have hU : IsOpen U :=
    (isOpen_lt continuous_const continuous_im).inter (isOpen_lt continuous_im continuous_const)
  have hτU : τ ∈ U := ⟨by rw [hT₀]; linarith, by rw [hT₁]; linarith⟩
  have hD : DifferentiableOn ℂ (fun t => ∑' n : ℤ, jacobiTheta₂'_term n (zc a b t) t) U := by
    refine differentiableOn_tsum_of_summable_norm
      ((summable_pow_mul_jacobiTheta₂_term_bound S₀ hT 1).mul_left (2 * π)) ?_ hU ?_
    · intro n
      refine Differentiable.differentiableOn ?_
      unfold jacobiTheta₂'_term jacobiTheta₂_term zc
      fun_prop
    · intro n t ht
      have hz : |(zc a b t).im| ≤ S₀ := by
        rw [zc_im, abs_mul]
        have h1 : |((a : ℝ) / 5 + 1 / 2)| ≤ |(a : ℝ)| / 5 + 1 / 2 := by
          calc |((a : ℝ) / 5 + 1 / 2)| ≤ |(a : ℝ) / 5| + |(1 : ℝ) / 2| := abs_add_le _ _
            _ = |(a : ℝ)| / 5 + 1 / 2 := by
              rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 5)]; norm_num
        have h2 : |t.im| ≤ T₁ := by
          rw [abs_of_pos (by linarith [ht.1])]; exact ht.2.le
        exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      refine (norm_jacobiTheta₂'_term_le hT hz ht.1.le n).trans (le_of_eq ?_)
      ring
  exact hD.differentiableAt (hU.mem_nhds hτU)

theorem F_diffOn {a b : ℤ} (h : Good (a, b)) :
    DifferentiableOn ℂ (F (a, b) ∘ UpperHalfPlane.ofComplex) {z | 0 < z.im} := by
  have hD : DifferentiableOn ℂ (fun t : ℂ => (a : ℂ) / 5 + 1 / 2 +
      jacobiTheta₂' (zc a b t) t / (2 * (π : ℂ) * I * jacobiTheta₂ (zc a b t) t))
      {z | 0 < z.im} := by
    intro t ht
    have hne : 2 * (π : ℂ) * I * jacobiTheta₂ (zc a b t) t ≠ 0 :=
      denominator_ne_zero ⟨t, ht⟩ a b h
    refine DifferentiableAt.differentiableWithinAt ?_
    exact (differentiableAt_const _).add ((differentiableAt_theta'_zc a b ht).div
      ((differentiableAt_const _).mul (differentiableAt_theta_zc a b ht)) hne)
  refine hD.congr fun t ht => ?_
  simp only [Function.comp, UpperHalfPlane.ofComplex_apply_of_im_pos ht]
  rfl

/-! ### Boundedness at `i∞` -/

/-- A uniform bound for `θ'` used at `i∞`. -/
def Kθ : ℝ :=
  ∑' n : ℤ, (2 * π * (((|n| : ℤ) : ℝ) ^ 1 *
    Real.exp (-π * (1 * (n : ℝ) ^ 2 - 2 * (1 / 2) * ((|n| : ℤ) : ℝ)))) : ℝ)

theorem norm_theta'_le {z τ : ℂ} (hy : 1 ≤ τ.im) (hz : |z.im| ≤ τ.im / 2) :
    ‖jacobiTheta₂' z τ‖ ≤ Kθ := by
  have hy0 : 0 < τ.im := by linarith
  have hsum := (summable_pow_mul_jacobiTheta₂_term_bound (1 / 2 : ℝ) one_pos 1).mul_left (2 * π)
  have hle : ∀ n : ℤ, ‖jacobiTheta₂'_term n z τ‖ ≤
      2 * π * (((|n| : ℤ) : ℝ) ^ 1 *
        Real.exp (-π * (1 * (n : ℝ) ^ 2 - 2 * (1 / 2) * ((|n| : ℤ) : ℝ)))) := by
    intro n
    refine (norm_jacobiTheta₂'_term_le hy0 hz le_rfl n).trans ?_
    rw [pow_one, ← mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [Real.exp_le_exp]
    have hn : ((|n| : ℤ) : ℝ) ≤ (n : ℝ) ^ 2 := by
      have h0 : |n| ≤ n ^ 2 := by
        have := Int.natAbs_le_self_sq n
        rwa [Int.natCast_natAbs] at this
      exact_mod_cast h0
    nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hy)) (sub_nonneg.mpr hn)]
  have hs : Summable fun n : ℤ => ‖jacobiTheta₂'_term n z τ‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hsum
  exact (norm_tsum_le_tsum_norm hs).trans (hs.tsum_mono hsum hle)

/-- One dominant term, quantitative: `‖θ(z, τ)‖ ≥ 1/10` if `Im τ ≥ 1`, `|Im z| ≤ (3/10) Im τ`. -/
theorem norm_theta_ge_of_abs_im_le {z τ : ℂ} (hy1 : 1 ≤ τ.im)
    (hz : |z.im| ≤ 3 / 10 * τ.im) : 1 / 10 ≤ ‖jacobiTheta₂ z τ‖ := by
  have hy : 0 < τ.im := by linarith
  set y := τ.im with hydef
  set X := Real.pi * y with hX
  have hX3 : 3 < X := by rw [hX]; nlinarith [Real.pi_gt_three]
  set ρ := Real.exp (-X) with hρ
  set C := Real.exp (3 / 5 * X) with hC
  have hρ0 : 0 ≤ ρ := (Real.exp_pos _).le
  have hρ1 : ρ < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hM := ThetaFive.hasSum_geom_natAbs C hρ0 hρ1
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
  have key := ThetaFive.norm_tsum_sub_finset_le hf.summable hM.summable {0} hbound
  rw [hf.tsum_eq, hM.tsum_eq] at key
  simp only [Finset.sum_singleton, Int.natAbs_zero, pow_zero, mul_one] at key
  have h0term : jacobiTheta₂_term 0 z τ = 1 := by simp [jacobiTheta₂_term]
  rw [h0term] at key
  have hu := ThetaFive.exp_neg_one_lt
  have hu0 : 0 < Real.exp (-1) := Real.exp_pos _
  have hCρ : C * ρ ≤ Real.exp (-1) := by
    rw [hC, hρ, ← Real.exp_add, Real.exp_le_exp]; linarith
  have hρu : ρ ≤ Real.exp (-1) * Real.exp (-1) := by
    rw [hρ, ← Real.exp_add, Real.exp_le_exp]; linarith
  have hlt : C / (1 - ρ) + C * ρ / (1 - ρ) - C ≤ 9 / 10 := by
    have h1ρ : 0 < 1 - ρ := by linarith
    have : C / (1 - ρ) + C * ρ / (1 - ρ) - C = 2 * (C * ρ) / (1 - ρ) := by
      field_simp; ring
    rw [this, div_le_iff₀ h1ρ]
    nlinarith
  have h2 := norm_sub_norm_le (1 : ℂ) (jacobiTheta₂ z τ)
  rw [norm_sub_rev, norm_one] at h2
  linarith

/-- Two dominant terms, quantitative: `‖θ(b/5 + (τ+1)/2, τ)‖ ≥ 1/10` for `b ∈ {±1, ±2}` and
`Im τ ≥ 1`. -/
theorem norm_theta_ge_half_shift {τ : ℂ} (hy1 : 1 ≤ τ.im) {b : ℤ}
    (hb : b = 1 ∨ b = 2 ∨ b = -1 ∨ b = -2) :
    1 / 10 ≤ ‖jacobiTheta₂ ((b : ℂ) / 5 + (τ + 1) / 2) τ‖ := by
  have hy : 0 < τ.im := by linarith
  set z : ℂ := (b : ℂ) / 5 + (τ + 1) / 2 with hzdef
  set y := τ.im with hydef
  have hzim : z.im = y / 2 := by
    rw [hzdef]; simp [hydef]
  set X := Real.pi * y with hX
  have hX3 : 3 < X := by rw [hX]; nlinarith [Real.pi_gt_three]
  set ρ := Real.exp (-X) with hρ
  have hρ0 : 0 ≤ ρ := (Real.exp_pos _).le
  have hρ1 : ρ < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hM := ThetaFive.hasSum_geom_natAbs 1 hρ0 hρ1
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
    rw [hX]
    nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_left hreal (mul_pos Real.pi_pos hy).le]
  have key := ThetaFive.norm_tsum_sub_finset_le hf.summable hM.summable {0, -1} hbound
  rw [hf.tsum_eq, hM.tsum_eq] at key
  rw [Finset.sum_pair (by norm_num), Finset.sum_pair (by norm_num)] at key
  simp only [Int.natAbs_zero, pow_zero, mul_one, one_mul, Int.natAbs_neg, Int.natAbs_one,
    pow_one] at key
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
    linarith [ThetaFive.cos_two_pi_mul_div_five_le hb]
  have hu := ThetaFive.exp_neg_one_lt
  have hu0 : 0 < Real.exp (-1) := Real.exp_pos _
  have hρu : ρ ≤ Real.exp (-1) * Real.exp (-1) := by
    rw [hρ, ← Real.exp_add, Real.exp_le_exp]; linarith
  have htail : 1 / (1 - ρ) + ρ / (1 - ρ) - (1 + ρ) ≤ 2 / 5 := by
    have h1ρ : 0 < 1 - ρ := by linarith
    have : 1 / (1 - ρ) + ρ / (1 - ρ) - (1 + ρ) = ρ * (1 + ρ) / (1 - ρ) := by
      field_simp; ring
    rw [this, div_le_iff₀ h1ρ]
    nlinarith
  have h2 := norm_sub_norm_le ((1 : ℂ) + -Complex.exp (-(2 * π * I * b / 5))) (jacobiTheta₂ z τ)
  rw [norm_sub_rev] at h2
  linarith

theorem norm_two_pi_I : ‖(2 * (π : ℂ) * I)‖ = 2 * π := by
  rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  simp

/-- Bound on a representative pair. -/
theorem norm_F_le_rep {a b : ℤ}
    (hrep : (a = -4 ∨ a = -3 ∨ a = -2 ∨ a = -1) ∨ (a = 0 ∧ (b = 1 ∨ b = 2 ∨ b = -1 ∨ b = -2)))
    (τ : ℍ) (hτ : 1 ≤ τ.im) : ‖F (a, b) τ‖ ≤ 1 + 10 * Kθ := by
  have hy1 : 1 ≤ (τ : ℂ).im := hτ
  have hz : (shiftedPoint a b τ).im = ((a : ℝ) / 5 + 1 / 2) * (τ : ℂ).im := by
    unfold shiftedPoint; simp; ring
  have hα : |(a : ℝ) / 5 + 1 / 2| ≤ 1 / 2 ∧ ((a : ℝ) / 5 + 1 / 2 ≠ 1 / 2 →
      |(a : ℝ) / 5 + 1 / 2| ≤ 3 / 10) := by
    rcases hrep with (h | h | h | h) | ⟨h, _⟩ <;> subst h <;> norm_num [abs_le]
  have hyp : 0 < (τ : ℂ).im := by linarith
  have hθ' : ‖jacobiTheta₂' (shiftedPoint a b τ) τ‖ ≤ Kθ := by
    refine norm_theta'_le hy1 ?_
    rw [hz, abs_mul, abs_of_pos hyp]
    nlinarith [hα.1]
  have hθ : 1 / 10 ≤ ‖jacobiTheta₂ (shiftedPoint a b τ) τ‖ := by
    rcases hrep with ha | ⟨rfl, hb⟩
    · refine norm_theta_ge_of_abs_im_le hy1 ?_
      rw [hz, abs_mul, abs_of_pos hyp]
      have : |(a : ℝ) / 5 + 1 / 2| ≤ 3 / 10 := by
        rcases ha with h | h | h | h <;> subst h <;> norm_num [abs_le]
      nlinarith
    · have e : shiftedPoint 0 b τ = (b : ℂ) / 5 + ((τ : ℂ) + 1) / 2 := by
        unfold shiftedPoint; push_cast; ring
      rw [e]
      exact norm_theta_ge_half_shift hy1 hb
  have hK : 0 ≤ Kθ := le_trans (norm_nonneg _) hθ'
  have hden : 1 / 10 ≤ ‖2 * (π : ℂ) * I * jacobiTheta₂ (shiftedPoint a b τ) τ‖ := by
    rw [norm_mul, norm_two_pi_I]
    nlinarith [Real.pi_gt_three]
  rw [F_apply]
  have hconst : ‖(a : ℂ) / 5 + 1 / 2‖ ≤ 1 := by
    have : (a : ℂ) / 5 + 1 / 2 = (((a : ℝ) / 5 + 1 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs]
    linarith [hα.1]
  have hq : ‖logDer (shiftedPoint a b τ) τ‖ ≤ 10 * Kθ := by
    unfold logDer
    rw [norm_div, div_le_iff₀ (by linarith)]
    nlinarith
  calc ‖(a : ℂ) / 5 + 1 / 2 + logDer (shiftedPoint a b τ) τ‖
      ≤ ‖(a : ℂ) / 5 + 1 / 2‖ + ‖logDer (shiftedPoint a b τ) τ‖ := norm_add_le _ _
    _ ≤ 1 + 10 * Kθ := add_le_add hconst hq

/-- Every admissible `F_v` is bounded at `i∞`. -/
theorem F_isBoundedAtImInfty {v : ℤ × ℤ} (h : Good v) :
    UpperHalfPlane.IsBoundedAtImInfty (F v) := by
  obtain ⟨a, b⟩ := v
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  refine ⟨1 + 10 * Kθ, 1, fun τ hτ => ?_⟩
  by_cases ha : a % 5 = 0
  · have hb : ¬ (5 : ℤ) ∣ b := fun hb => h ⟨Int.dvd_of_emod_eq_zero ha, hb⟩
    have hbr : (b + 2) % 5 - 2 = 1 ∨ (b + 2) % 5 - 2 = 2 ∨ (b + 2) % 5 - 2 = -1 ∨
        (b + 2) % 5 - 2 = -2 := by omega
    have hg : Good (0, (b + 2) % 5 - 2) := by unfold Good; omega
    rw [show ((a, b) : ℤ × ℤ) = (0 + 5 * (a / 5), ((b + 2) % 5 - 2) + 5 * ((b + 2) / 5)) from
      Prod.ext (by dsimp only; omega) (by dsimp only; omega), F_shift hg]
    exact norm_F_le_rep (Or.inr ⟨rfl, hbr⟩) τ hτ
  · have har : a % 5 - 5 = -4 ∨ a % 5 - 5 = -3 ∨ a % 5 - 5 = -2 ∨ a % 5 - 5 = -1 := by omega
    have hg : Good (a % 5 - 5, b) := by unfold Good; omega
    rw [show ((a, b) : ℤ × ℤ) = ((a % 5 - 5) + 5 * (a / 5 + 1), b + 5 * 0) from
      Prod.ext (by dsimp only; omega) (by dsimp only; omega), F_shift hg]
    exact norm_F_le_rep (Or.inl har) τ hτ

/-! ### Level `Γ₁(5)` and the modular forms -/

theorem F_slash_Gamma1 {b : ℤ} (hb : ¬ (5 : ℤ) ∣ b) (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma1 5) : F (0, b) ∣[(1 : ℤ)] γ = F (0, b) := by
  have hg : Good (0, b) := fun h => hb h.2
  rw [F_slash γ _ hg]
  rw [CongruenceSubgroup.Gamma1_mem] at hγ
  obtain ⟨_, h11, h10⟩ := hγ
  have h10' : ((5 : ℕ) : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp h10
  have h11'' : ((γ 1 1 : ℤ) : ZMod 5) = ((1 : ℤ) : ZMod 5) := by simpa using h11
  have h11' : ((5 : ℕ) : ℤ) ∣ 1 - γ 1 1 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 5).mp h11''
  obtain ⟨m, hm⟩ := h10'
  obtain ⟨n, hn⟩ := h11'
  push_cast at hm hn
  have hact : act (0, b) γ = (0 + 5 * (b * m), b + 5 * (-(b * n))) := by
    refine Prod.ext ?_ ?_
    · dsimp only [act]; rw [hm]; ring
    · dsimp only [act]; linear_combination (-b) * hn
  rw [hact]
  funext τ
  exact F_shift hg _ _ τ

theorem F_bdd_cusp {b : ℤ} (hb : ¬ (5 : ℤ) ∣ b) {c : OnePoint ℝ}
    (hc : IsCusp c ((CongruenceSubgroup.Gamma1 5).map (Matrix.SpecialLinearGroup.mapGL ℝ))) :
    c.IsBoundedAt (F (0, b)) 1 := by
  have hg : Good (0, b) := fun h => hb h.2
  have hc' : IsCusp c 𝒮ℒ := IsCusp.mono (Subgroup.map_le_range _ _) hc
  rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc']
  intro γ _
  rw [F_slash γ _ hg]
  exact F_isBoundedAtImInfty (good_act hg γ)

/-- **The weight-one modular form** on `Γ₁(5)` with underlying function
`torsionLogDerivative 0 b`, for `b` not divisible by `5`. -/
def torsionForm (b : ℤ) (hb : ¬ (5 : ℤ) ∣ b) :
    ModularForm ((CongruenceSubgroup.Gamma1 5).map (Matrix.SpecialLinearGroup.mapGL ℝ)) 1 where
  toFun := F (0, b)
  slash_action_eq' γ hγ := by
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hγ
    have := F_slash_Gamma1 hb g hg
    rwa [ModularForm.SL_slash] at this
  holo' := UpperHalfPlane.mdifferentiable_iff.mpr (F_diffOn (fun h => hb h.2))
  bdd_at_cusps' hc := F_bdd_cusp hb hc

theorem torsionForm_apply (b : ℤ) (hb : ¬ (5 : ℤ) ∣ b) (τ : ℍ) :
    torsionForm b hb τ = torsionLogDerivative 0 b τ := rfl

end ZInQ.Contrib.HeckePrimeRationality.ThetaFiveTorsion
