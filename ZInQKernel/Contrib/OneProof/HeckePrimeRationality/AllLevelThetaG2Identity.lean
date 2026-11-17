import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelThetaG2
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-!
# The theta finite-part constant is `-G2`

For the completed theta function `H`, the constant `c(τ) = ThetaWeierstrass.finitePart τ` in
`℘_τ(z) = -(H'/H)'(z) + c(τ)` equals `-G2(τ)`, with Mathlib's Eisenstein series `G2`.

Proof. `F = c + G2` is weight-two invariant under `SL(2, ℤ)` (previous file). Writing
`c = H'''(0)/(3 H'(0))` through the termwise derivative series `θ^{(k)}` of `jacobiTheta₂`, `c` is
holomorphic in `τ`, and it is bounded as `Im τ → ∞` since `H'(0) → 2π i`. Hence `F` is a
modular form of weight two and level one, and every such form vanishes
(`levelOne_weight_two_rank_zero`).
-/

noncomputable section

open Complex Filter Topology ModularGroup
open scoped Real UpperHalfPlane MatrixGroups ModularForm Manifold

namespace ZInQ.Contrib.HeckePrimeRationality.ThetaG2

open CompletedTheta ThetaWeierstrass

/-! ### Termwise derivative series of `θ` -/

/-- The series of the `k`-th `z`-derivative of `jacobiTheta₂`. -/
def th (k : ℕ) (w τ : ℂ) : ℂ := ∑' n : ℤ, (2 * π * I * n) ^ k * jacobiTheta₂_term n w τ

theorem th_zero (w τ : ℂ) : th 0 w τ = jacobiTheta₂ w τ := by
  simp [th, jacobiTheta₂]

theorem th_one (w τ : ℂ) : th 1 w τ = jacobiTheta₂' w τ := by
  simp [th, jacobiTheta₂', jacobiTheta₂'_term]

theorem norm_coeff (k : ℕ) (n : ℤ) :
    ‖(2 * π * I * n : ℂ) ^ k‖ = (2 * π) ^ k * ((|n| : ℤ) : ℝ) ^ k := by
  rw [norm_pow, ← mul_pow]
  congr 1
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_intCast,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos, Int.cast_abs]
  norm_num

theorem norm_term_coeff_le (k : ℕ) {S T : ℝ} (hT : 0 < T) {z τ : ℂ} (hz : |z.im| ≤ S)
    (hτ : T ≤ τ.im) (n : ℤ) :
    ‖(2 * π * I * n : ℂ) ^ k * jacobiTheta₂_term n z τ‖ ≤
      (2 * π) ^ k * (((|n| : ℤ) : ℝ) ^ k * Real.exp (-π * (T * n ^ 2 - 2 * S * ((|n| : ℤ) : ℝ)))) := by
  rw [norm_mul, norm_coeff, mul_assoc]
  gcongr
  exact norm_jacobiTheta₂_term_le hT hz hτ n

theorem hasDerivAt_term (n : ℤ) (τ y : ℂ) :
    HasDerivAt (fun x => jacobiTheta₂_term n x τ) (jacobiTheta₂_term n y τ * (2 * π * I * n)) y := by
  have h := (((hasDerivAt_id y).const_mul (2 * π * I * n : ℂ)).add_const
    (π * I * (n : ℂ) ^ 2 * τ)).cexp
  unfold jacobiTheta₂_term
  convert h using 1
  · simp only [id]
  · simp only [id, mul_one]

theorem hasDerivAt_th (k : ℕ) {τ : ℂ} (hτ : 0 < τ.im) (w : ℂ) :
    HasDerivAt (fun x => th k x τ) (th (k + 1) w τ) w := by
  set S := |w.im| + 1
  have hS : ∀ y ∈ Metric.ball w 1, |y.im| ≤ S := by
    intro y hy
    have h1 : |(y - w).im| ≤ ‖y - w‖ := Complex.abs_im_le_norm _
    have h2 : ‖y - w‖ < 1 := by rwa [Metric.mem_ball, dist_eq_norm] at hy
    have h3 := abs_sub_abs_le_abs_sub y.im w.im
    rw [Complex.sub_im] at h1
    linarith
  have hu := (summable_pow_mul_jacobiTheta₂_term_bound S hτ (k + 1)).mul_left ((2 * π) ^ (k + 1))
  have hw : w ∈ Metric.ball w 1 := Metric.mem_ball_self one_pos
  have h0 : Summable fun n : ℤ => (2 * π * I * n : ℂ) ^ k * jacobiTheta₂_term n w τ :=
    Summable.of_norm_bounded
      ((summable_pow_mul_jacobiTheta₂_term_bound S hτ k).mul_left ((2 * π) ^ k))
      (fun n => norm_term_coeff_le k hτ (hS w hw) le_rfl n)
  exact hasDerivAt_tsum_of_isPreconnected (g := fun (n : ℤ) (x : ℂ) => (2 * π * I * n : ℂ) ^ k *
      jacobiTheta₂_term n x τ) (g' := fun (n : ℤ) (y : ℂ) => (2 * π * I * n : ℂ) ^ (k + 1) *
      jacobiTheta₂_term n y τ) hu Metric.isOpen_ball (convex_ball w 1).isPreconnected
    (fun n y _ => ((hasDerivAt_term n τ y).const_mul _).congr_deriv (by ring))
    (fun n y hy => norm_term_coeff_le (k + 1) hτ (hS y hy) le_rfl n) hw h0 hw

/-! ### Derivatives of `H` at the origin -/

/-- `E_k(z) = exp(π i z) θ^{(k)}(z + (τ+1)/2)`. -/
def Ek (τ : ℍ) (k : ℕ) (z : ℂ) : ℂ := cexp (π * I * z) * th k (z + ((τ : ℂ) + 1) / 2) τ

theorem hasDerivAt_Ek (τ : ℍ) (k : ℕ) (z : ℂ) :
    HasDerivAt (Ek τ k) (π * I * Ek τ k z + Ek τ (k + 1) z) z := by
  have he : HasDerivAt (fun x : ℂ => cexp (π * I * x)) (cexp (π * I * z) * (π * I)) z := by
    simpa using ((hasDerivAt_id z).const_mul (π * I : ℂ)).cexp
  have hθ := (hasDerivAt_th k τ.im_pos (z + ((τ : ℂ) + 1) / 2)).comp_add_const z
    (((τ : ℂ) + 1) / 2)
  refine (he.mul hθ).congr_deriv ?_
  simp only [Ek]
  ring

theorem H_eq_E0 (τ : ℍ) : H τ = Ek τ 0 := by
  funext z; simp [H, Ek, th_zero]

/-- The value `D_k = θ^{(k)}((τ+1)/2, τ)`. -/
def D (k : ℕ) (t : ℂ) : ℂ := th k ((t + 1) / 2) t

theorem Ek_zero (τ : ℍ) (k : ℕ) : Ek τ k 0 = D k τ := by simp [Ek, D]

theorem deriv_H_zero_eq (τ : ℍ) : deriv (H τ) 0 = π * I * D 0 τ + D 1 τ := by
  rw [H_eq_E0, (hasDerivAt_Ek τ 0 0).deriv, Ek_zero, Ek_zero]

theorem iteratedDeriv_three_H_zero_eq (τ : ℍ) :
    iteratedDeriv 3 (H τ) 0 = (π * I) ^ 3 * D 0 τ + 3 * (π * I) ^ 2 * D 1 τ +
      3 * (π * I) * D 2 τ + D 3 τ := by
  set A1 : ℂ → ℂ := fun z => π * I * Ek τ 0 z + Ek τ 1 z
  set A2 : ℂ → ℂ := fun z => (π * I) ^ 2 * Ek τ 0 z + 2 * (π * I) * Ek τ 1 z + Ek τ 2 z
  have h1 : deriv (H τ) = A1 := by
    funext z; rw [H_eq_E0, (hasDerivAt_Ek τ 0 z).deriv]
  have h2 : deriv A1 = A2 := by
    funext z
    refine (((hasDerivAt_Ek τ 0 z).const_mul (π * I)).add (hasDerivAt_Ek τ 1 z)).deriv.trans ?_
    simp only [A2]; ring
  have h3 : deriv A2 0 = (π * I) ^ 3 * Ek τ 0 0 + 3 * (π * I) ^ 2 * Ek τ 1 0 +
      3 * (π * I) * Ek τ 2 0 + Ek τ 3 0 := by
    refine ((((hasDerivAt_Ek τ 0 0).const_mul ((π * I) ^ 2)).add
      ((hasDerivAt_Ek τ 1 0).const_mul (2 * (π * I)))).add (hasDerivAt_Ek τ 2 0)).deriv.trans ?_
    ring
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one, h1, h2, h3, Ek_zero, Ek_zero,
    Ek_zero, Ek_zero]

/-- The explicit formula for `c(τ)`. -/
def cC (t : ℂ) : ℂ :=
  ((π * I) ^ 3 * D 0 t + 3 * (π * I) ^ 2 * D 1 t + 3 * (π * I) * D 2 t + D 3 t) /
    (3 * (π * I * D 0 t + D 1 t))

theorem finitePart_eq_cC (τ : ℍ) : finitePart τ = cC τ := by
  rw [finitePart_eq_third_derivative, iteratedDeriv_three_H_zero_eq, deriv_H_zero_eq, cC]

theorem denom_ne_zero (τ : ℍ) : π * I * D 0 τ + D 1 τ ≠ 0 := by
  rw [← deriv_H_zero_eq]; exact deriv_H_zero_ne_zero τ

/-! ### Holomorphy in `τ` -/

theorem differentiableAt_D (k : ℕ) {t : ℂ} (ht : 0 < t.im) : DifferentiableAt ℂ (D k) t := by
  set T₀ := t.im / 2 with hT₀
  set T₁ := t.im + 1 with hT₁
  set U := {u : ℂ | T₀ < u.im ∧ u.im < T₁} with hUdef
  have hT : 0 < T₀ := by positivity
  have hU : IsOpen U :=
    (isOpen_lt continuous_const continuous_im).inter (isOpen_lt continuous_im continuous_const)
  have htU : t ∈ U := ⟨by rw [hT₀]; linarith, by rw [hT₁]; linarith⟩
  have hD : DifferentiableOn ℂ (fun u => ∑' n : ℤ, (2 * π * I * n : ℂ) ^ k *
      jacobiTheta₂_term n ((u + 1) / 2) u) U := by
    refine differentiableOn_tsum_of_summable_norm
      ((summable_pow_mul_jacobiTheta₂_term_bound (T₁ / 2) hT k).mul_left ((2 * π) ^ k)) ?_ hU ?_
    · intro n
      refine Differentiable.differentiableOn ?_
      unfold jacobiTheta₂_term
      fun_prop
    · intro n u hu
      have hz : |((u + 1) / 2).im| ≤ T₁ / 2 := by
        have : ((u + 1) / 2).im = u.im / 2 := by simp
        rw [this, abs_of_pos (by linarith [hu.1])]
        linarith [hu.2]
      exact norm_term_coeff_le k hT hz hu.1.le n
  exact hD.differentiableAt (hU.mem_nhds htU)

theorem finitePart_diffOn :
    DifferentiableOn ℂ (finitePart ∘ UpperHalfPlane.ofComplex) {z | 0 < z.im} := by
  have hc : DifferentiableOn ℂ cC {z | 0 < z.im} := by
    intro t ht
    have hne : 3 * (π * I * D 0 t + D 1 t) ≠ 0 :=
      mul_ne_zero three_ne_zero (denom_ne_zero ⟨t, ht⟩)
    refine DifferentiableAt.differentiableWithinAt ?_
    unfold cC
    have d0 := differentiableAt_D 0 ht
    have d1 := differentiableAt_D 1 ht
    have d2 := differentiableAt_D 2 ht
    have d3 := differentiableAt_D 3 ht
    exact (((d0.const_mul _).add (d1.const_mul _)).add (d2.const_mul _) |>.add d3).div
      ((d0.const_mul _).add d1 |>.const_mul _) hne
  refine hc.congr fun t ht => ?_
  simp only [Function.comp, UpperHalfPlane.ofComplex_apply_of_im_pos ht]
  exact finitePart_eq_cC ⟨t, ht⟩

/-! ### Boundedness at `i∞` -/

/-- A summable majorant independent of `τ` with `Im τ ≥ 1`. -/
def B (k : ℕ) : ℝ :=
  ∑' n : ℤ, (2 * π) ^ k * (((|n| : ℤ) : ℝ) ^ k *
    Real.exp (-π * (1 * n ^ 2 - 2 * (1 / 2) * ((|n| : ℤ) : ℝ))))

theorem summable_B (k : ℕ) : Summable fun n : ℤ => (2 * π) ^ k * (((|n| : ℤ) : ℝ) ^ k *
    Real.exp (-π * (1 * n ^ 2 - 2 * (1 / 2) * ((|n| : ℤ) : ℝ)))) :=
  (summable_pow_mul_jacobiTheta₂_term_bound (1 / 2) one_pos k).mul_left _

theorem norm_term_at_s (n : ℤ) (t : ℂ) :
    ‖jacobiTheta₂_term n ((t + 1) / 2) t‖ = Real.exp (-π * (t.im * ((n : ℝ) * (n + 1)))) := by
  rw [norm_jacobiTheta₂_term]
  congr 1
  simp
  ring

theorem n_mul_succ_nonneg (n : ℤ) : (0 : ℝ) ≤ (n : ℝ) * (n + 1) := by
  have : (0 : ℤ) ≤ n * (n + 1) := by
    rcases le_or_gt 0 n with h | h
    · positivity
    · nlinarith
  exact_mod_cast this

theorem le_n_mul_succ (n : ℤ) : (n : ℝ) ^ 2 - ((|n| : ℤ) : ℝ) ≤ (n : ℝ) * (n + 1) := by
  rw [Int.cast_abs]
  have := neg_abs_le (n : ℝ)
  nlinarith

theorem norm_coeff_term_le_B (k : ℕ) {t : ℂ} (ht : 1 ≤ t.im) (n : ℤ) :
    ‖(2 * π * I * n : ℂ) ^ k * jacobiTheta₂_term n ((t + 1) / 2) t‖ ≤
      (2 * π) ^ k * (((|n| : ℤ) : ℝ) ^ k *
        Real.exp (-π * (1 * n ^ 2 - 2 * (1 / 2) * ((|n| : ℤ) : ℝ)))) := by
  rw [norm_mul, norm_coeff, norm_term_at_s, mul_assoc]
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
    (by positivity)) (by positivity)
  have h1 := n_mul_succ_nonneg n
  have h2 := le_n_mul_succ n
  nlinarith [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ht h1) Real.pi_pos.le,
    mul_le_mul_of_nonneg_left h2 Real.pi_pos.le]

theorem norm_D_le (k : ℕ) {t : ℂ} (ht : 1 ≤ t.im) : ‖D k t‖ ≤ B k := by
  have hs : Summable fun n : ℤ => ‖(2 * π * I * n : ℂ) ^ k * jacobiTheta₂_term n ((t + 1) / 2) t‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_coeff_term_le_B k ht) (summable_B k)
  exact (norm_tsum_le_tsum_norm hs).trans (hs.tsum_mono (summable_B k) (norm_coeff_term_le_B k ht))

theorem D_zero_eq (τ : ℍ) : D 0 τ = 0 := by
  rw [D, th_zero]
  exact AllLevelThetaZeroSet.jacobiTheta₂_half_shift_eq_zero τ.im_pos

/-- Lower bound for `D 1` at large height. -/
theorem norm_D1_sub_le {t : ℂ} (ht : 1 ≤ t.im) :
    ‖D 1 t - 2 * π * I‖ ≤ Real.exp (-2 * π * (t.im - 1)) * B 1 := by
  have hy : 0 < t.im := by linarith
  set f : ℤ → ℂ := fun n => (2 * π * I * n : ℂ) ^ 1 * jacobiTheta₂_term n ((t + 1) / 2) t
  set M : ℤ → ℝ := fun n => Real.exp (-2 * π * (t.im - 1)) * ((2 * π) ^ 1 * (((|n| : ℤ) : ℝ) ^ 1 *
    Real.exp (-π * (1 * n ^ 2 - 2 * (1 / 2) * ((|n| : ℤ) : ℝ)))))
  have hfs : Summable f :=
    Summable.of_norm_bounded (summable_B 1) (fun n => norm_coeff_term_le_B 1 ht n)
  have hMs : Summable M := (summable_B 1).mul_left _
  have hbound : ∀ n ∉ ({0, -1} : Finset ℤ), ‖f n‖ ≤ M n := by
    intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    have h2 : (2 : ℝ) ≤ (n : ℝ) * (n + 1) := by
      have : (2 : ℤ) ≤ n * (n + 1) := by
        rcases le_or_gt 1 n with h | h
        · nlinarith
        · have : n ≤ -2 := by omega
          nlinarith
      exact_mod_cast this
    simp only [f, M]
    rw [norm_mul, norm_coeff, norm_term_at_s]
    have h3 := le_n_mul_succ n
    have hE : Real.exp (-π * (t.im * ((n : ℝ) * (n + 1)))) ≤
        Real.exp (-2 * π * (t.im - 1)) *
          Real.exp (-π * (1 * n ^ 2 - 2 * (1 / 2) * ((|n| : ℤ) : ℝ))) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      nlinarith [mul_le_mul_of_nonneg_left h3 Real.pi_pos.le,
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (sub_nonneg.mpr ht))
          Real.pi_pos.le]
    calc (2 * π) ^ 1 * ((|n| : ℤ) : ℝ) ^ 1 * Real.exp (-π * (t.im * ((n : ℝ) * (n + 1))))
        ≤ (2 * π) ^ 1 * ((|n| : ℤ) : ℝ) ^ 1 * (Real.exp (-2 * π * (t.im - 1)) *
          Real.exp (-π * (1 * n ^ 2 - 2 * (1 / 2) * ((|n| : ℤ) : ℝ)))) :=
          mul_le_mul_of_nonneg_left hE (by positivity)
      _ = _ := by ring
  have key := AllLevelTheta.norm_tsum_sub_finset_le' hfs hMs {0, -1} hbound
  have hpair : ∑ n ∈ ({0, -1} : Finset ℤ), f n = 2 * π * I := by
    rw [Finset.sum_pair (by norm_num)]
    simp only [f, pow_one, Int.cast_zero, mul_zero, zero_mul, zero_add, Int.cast_neg,
      Int.cast_one]
    have : jacobiTheta₂_term (-1) ((t + 1) / 2) t = -1 := by
      unfold jacobiTheta₂_term
      have e : 2 * (π : ℂ) * I * ((-1 : ℤ) : ℂ) * ((t + 1) / 2) + π * I * ((-1 : ℤ) : ℂ) ^ 2 * t =
          ((-1 : ℤ) : ℂ) * (π * I) := by push_cast; ring
      rw [e, Complex.exp_int_mul, Complex.exp_pi_mul_I]
      norm_num
    rw [this]; ring
  have hD : D 1 t = ∑' n, f n := by simp only [D, th, f]
  rw [hD, ← hpair]
  refine key.trans ?_
  have hM0 : 0 ≤ ∑ n ∈ ({0, -1} : Finset ℤ), M n :=
    Finset.sum_nonneg fun n _ => by positivity
  have hM : ∑' n, M n = Real.exp (-2 * π * (t.im - 1)) * B 1 := by
    simp only [M, B]
    exact tsum_mul_left
  linarith

/-- The finite-part constant is bounded at `i∞`. -/
theorem finitePart_bounded : ∃ M A : ℝ, ∀ τ : ℍ, A ≤ τ.im → ‖finitePart τ‖ ≤ M := by
  have hB1 : 0 ≤ B 1 := tsum_nonneg fun n => by positivity
  have hB2 : 0 ≤ B 2 := tsum_nonneg fun n => by positivity
  have hB3 : 0 ≤ B 3 := tsum_nonneg fun n => by positivity
  set A : ℝ := 1 + Real.log ((B 1 + 1) / π) / (2 * π) with hA
  refine ⟨(3 * π ^ 2 * B 1 + 3 * π * B 2 + B 3) / (3 * π), max 1 A, fun τ hτ => ?_⟩
  have ht1 : 1 ≤ (τ : ℂ).im := le_trans (le_max_left _ _) hτ
  have htA : A ≤ (τ : ℂ).im := le_trans (le_max_right _ _) hτ
  have hsmall : Real.exp (-2 * π * ((τ : ℂ).im - 1)) * B 1 ≤ π := by
    have hpi := Real.pi_pos
    have h1 : Real.log ((B 1 + 1) / π) ≤ 2 * π * ((τ : ℂ).im - 1) := by
      have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * π)).mp (by linarith : Real.log ((B 1 + 1) / π) / (2 * π) ≤ (τ : ℂ).im - 1)
      linarith
    have h2 : Real.exp (-2 * π * ((τ : ℂ).im - 1)) ≤ π / (B 1 + 1) := by
      calc Real.exp (-2 * π * ((τ : ℂ).im - 1)) ≤ Real.exp (-Real.log ((B 1 + 1) / π)) :=
            Real.exp_le_exp.mpr (by linarith)
        _ = π / (B 1 + 1) := by
            rw [Real.exp_neg, Real.exp_log (by positivity)]; field_simp
    calc Real.exp (-2 * π * ((τ : ℂ).im - 1)) * B 1 ≤ π / (B 1 + 1) * B 1 :=
          mul_le_mul_of_nonneg_right h2 hB1
      _ ≤ π := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
  have hD1 : π ≤ ‖D 1 τ‖ := by
    have h := norm_D1_sub_le ht1
    have h2 := norm_sub_norm_le (2 * π * I : ℂ) (D 1 τ)
    rw [norm_sub_rev] at h2
    have h3 : ‖(2 * π * I : ℂ)‖ = 2 * π := by
      rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]; norm_num
    linarith
  rw [finitePart_eq_cC, cC, D_zero_eq, mul_zero, zero_add, mul_zero, zero_add, norm_div]
  have hnum : ‖3 * (π * I : ℂ) ^ 2 * D 1 τ + 3 * (π * I) * D 2 τ + D 3 τ‖ ≤
      3 * π ^ 2 * B 1 + 3 * π * B 2 + B 3 := by
    have hpI : ‖(π * I : ℂ)‖ = π := by
      rw [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
        mul_one]
    calc _ ≤ ‖3 * (π * I : ℂ) ^ 2 * D 1 τ‖ + ‖3 * (π * I) * D 2 τ‖ + ‖D 3 τ‖ :=
          (norm_add_le _ _).trans (by
            linarith [norm_add_le (3 * (π * I : ℂ) ^ 2 * D 1 τ) (3 * (π * I) * D 2 τ)])
      _ ≤ 3 * π ^ 2 * B 1 + 3 * π * B 2 + B 3 := by
          rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, hpI]
          have e3 : ‖(3 : ℂ)‖ = 3 := by norm_num
          rw [e3]
          gcongr
          · exact norm_D_le 1 ht1
          · exact norm_D_le 2 ht1
          · exact norm_D_le 3 ht1
  have hden : 3 * π ≤ ‖3 * D 1 τ‖ := by
    rw [norm_mul]; norm_num; linarith
  calc ‖3 * (π * I : ℂ) ^ 2 * D 1 τ + 3 * (π * I) * D 2 τ + D 3 τ‖ / ‖3 * D 1 τ‖
      ≤ (3 * π ^ 2 * B 1 + 3 * π * B 2 + B 3) / ‖3 * D 1 τ‖ :=
        div_le_div_of_nonneg_right hnum (norm_nonneg _)
    _ ≤ (3 * π ^ 2 * B 1 + 3 * π * B 2 + B 3) / (3 * π) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden

/-! ### The weight-two form and the identification -/

theorem G2_eq_smul_E2 : EisensteinSeries.G2 = (2 * riemannZeta 2) • EisensteinSeries.E2 := by
  have hz : (2 * riemannZeta 2) ≠ 0 := by
    rw [riemannZeta_two]
    have : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    exact mul_ne_zero two_ne_zero (div_ne_zero (pow_ne_zero 2 this) (by norm_num))
  rw [EisensteinSeries.E2, smul_smul, mul_one_div_cancel hz, one_smul]

theorem F_mdiff : MDiff F := by
  have h1 : MDiff finitePart := UpperHalfPlane.mdifferentiable_iff.mpr finitePart_diffOn
  have h2 : MDiff EisensteinSeries.G2 := by
    rw [G2_eq_smul_E2]
    exact MDifferentiable.const_smul _ E2_mdifferentiable
  exact h1.add h2

theorem F_bounded : UpperHalfPlane.IsBoundedAtImInfty F := by
  obtain ⟨M, A, hMA⟩ := finitePart_bounded
  have hG := EisensteinSeries.isBoundedAtImInfty_E2
  rw [UpperHalfPlane.isBoundedAtImInfty_iff] at hG ⊢
  obtain ⟨M2, A2, h2⟩ := hG
  refine ⟨M + ‖2 * riemannZeta 2‖ * M2, max A A2, fun τ hτ => ?_⟩
  have hG2 : EisensteinSeries.G2 τ = (2 * riemannZeta 2) * EisensteinSeries.E2 τ := by
    rw [G2_eq_smul_E2]; rfl
  simp only [F, hG2]
  calc ‖finitePart τ + 2 * riemannZeta 2 * EisensteinSeries.E2 τ‖
      ≤ ‖finitePart τ‖ + ‖2 * riemannZeta 2‖ * ‖EisensteinSeries.E2 τ‖ :=
        (norm_add_le _ _).trans (by rw [norm_mul])
    _ ≤ M + ‖2 * riemannZeta 2‖ * M2 := by
        gcongr
        · exact hMA τ (le_trans (le_max_left _ _) hτ)
        · exact h2 τ (le_trans (le_max_right _ _) hτ)

/-- `F = c + G2` as a modular form of weight two and level one. -/
def Fform : ModularForm 𝒮ℒ 2 where
  toFun := F
  slash_action_eq' γ hγ := by
    obtain ⟨g, rfl⟩ := hγ
    have := F_slash g
    rwa [ModularForm.SL_slash] at this
  holo' := F_mdiff
  bdd_at_cusps' hc := by
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [F_slash γ]
    exact F_bounded

/-- **The theta finite-part constant is `-G2`.** -/
theorem finitePart_eq_neg_G2 (τ : ℍ) : finitePart τ = -EisensteinSeries.G2 τ := by
  have h0 : Fform = 0 :=
    (rank_zero_iff_forall_zero.mp ModularForm.levelOne_weight_two_rank_zero) Fform
  have h := congrArg (fun f : ModularForm 𝒮ℒ 2 => f τ) h0
  simp only [zero_apply] at h
  change F τ = 0 at h
  simp only [F] at h
  linear_combination h

/-- The same identity in the third-derivative form. -/
theorem third_derivative_eq_neg_G2 (τ : ℍ) :
    iteratedDeriv 3 (H τ) 0 / (3 * deriv (H τ) 0) = -EisensteinSeries.G2 τ := by
  rw [← finitePart_eq_third_derivative, finitePart_eq_neg_G2]

end ZInQ.Contrib.HeckePrimeRationality.ThetaG2
