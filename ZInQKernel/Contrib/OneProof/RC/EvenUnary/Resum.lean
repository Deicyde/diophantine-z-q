import ZInQKernel.Contrib.OneProof.RC.EvenUnary.Lines
import ZInQKernel.Contrib.OneProof.RC.OldStageLaw.Grid
import ZInQKernel.Contrib.OneProof.RC.HalfIntegral.Fourier
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-! Finite Fourier expansion and rational Poisson resummation of the
rank-one theta series with the linear factor (tex 9620–9623). -/

noncomputable section

set_option maxHeartbeats 1200000

namespace ZInQ.Manuscript.RC.EvenUnary

open Complex OldStageLaw HalfIntegral
open scoped Real

/-- The two-sided unary series with periodic coefficient weight. Its
argument is the Jacobi parameter, twice the shell's modular parameter. -/
def weightedTheta {B : ℕ} (v : ZMod B → ℂ) (τ : ℂ) : ℂ :=
  ∑' n : ℤ, v (n : ZMod B) * ((n : ℂ) * jacobiTheta₂_term n 0 τ)

theorem weightedTheta_hasSum {B : ℕ} [NeZero B] (v : ZMod B → ℂ)
    {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n : ℤ => v (n : ZMod B) * ((n : ℂ) * jacobiTheta₂_term n 0 τ))
      (weightedTheta v τ) := by
  apply Summable.hasSum
  let C := ∑ r : ZMod B, ‖v r‖
  refine ((linearTheta_hasSum 0 hτ).summable.norm.mul_left C).of_norm_bounded fun n => ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun r _ => norm_nonneg (v r)) (Finset.mem_univ _)) (norm_nonneg _)

private theorem jacobiTerm_addChar {B : ℕ} [NeZero B] (u : ZMod B) (n : ℤ) (τ : ℂ) :
    jacobiTheta₂_term n ((u.val : ℂ) / B) τ =
      ZMod.stdAddChar (u * (n : ZMod B)) * jacobiTheta₂_term n 0 τ := by
  rw [show u * (n : ZMod B) = ((u.val * n : ℤ) : ZMod B) by simp, ZMod.stdAddChar_coe]
  simp only [jacobiTheta₂_term, mul_zero, zero_add, ← exp_add]
  congr 1
  push_cast
  ring

/-- Fourier inversion makes the periodic weight a finite combination of
additively twisted one-variable theta series, including imprimitive weights. -/
theorem weightedTheta_fourier {B : ℕ} [NeZero B] (v : ZMod B → ℂ)
    {τ : ℂ} (hτ : 0 < τ.im) :
    weightedTheta v τ =
      ∑ u : ZMod B, translationWeights v u * linearTheta ((u.val : ℂ) / B) τ := by
  rw [weightedTheta]
  simp_rw [linearTheta, ← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun u _ =>
    (linearTheta_hasSum ((u.val : ℂ) / B) hτ).summable.mul_left _)]
  refine tsum_congr fun n => ?_
  rw [← sum_translationWeights v (n : ZMod B), Finset.sum_mul]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [jacobiTerm_addChar]
  ring

/-- Translation on the Jacobi parameter, hence period one after dilation
by the positive integral shell index. -/
theorem weightedTheta_periodic {B : ℕ} (v : ZMod B → ℂ) :
    Function.Periodic (weightedTheta v) 2 := by
  intro τ
  apply tsum_congr
  intro n
  simp only [jacobiTheta₂_term]
  rw [show (2 * π * I * (n : ℂ) * 0 + π * I * (n : ℂ) ^ 2 * (τ + 2)) =
      (2 * π * I * (n : ℂ) * 0 + π * I * (n : ℂ) ^ 2 * τ) +
        (((n ^ 2 : ℤ) : ℂ) * (2 * π * I)) by push_cast; ring,
    exp_add, exp_int_mul_two_pi_mul_I, mul_one]

private theorem rationalArgument_im (a : ℤ) (C : ℕ) (τ : ℂ) :
    (2 * (a : ℂ) / C + τ / (C : ℂ) ^ 2).im = τ.im / (C : ℝ) ^ 2 := by
  rw [show (2 * (a : ℂ) / C) = (((2 * (a : ℝ) / C) : ℝ) : ℂ) by push_cast; rfl,
    show (C : ℂ)^2 = (((C : ℝ)^2 : ℝ) : ℂ) by push_cast; rfl]
  simp only [add_im, ofReal_im, zero_add, div_ofReal_im]

/-- Split at the rational point `a/C`, for any common modulus `C` of
the quadratic phase and the coefficient weight. This computes the weighted
Poisson identity before any congruence subgroup or character comparison. -/
theorem weightedTheta_rational_resum {B C : ℕ} [NeZero B] [NeZero C]
    (hBC : B ∣ C) (v : ZMod B → ℂ) (a : ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    weightedTheta v (2 * (a : ℂ) / C + τ / (C : ℂ) ^ 2) =
      ((C : ℂ) * ((1 / (-I * τ) ^ (1 / 2 : ℂ)) / τ)) *
        ∑ r : ZMod C, (v (ZMod.castHom hBC (ZMod B) r) *
          ZMod.stdAddChar ((a : ZMod C) * r ^ 2)) *
          linearTheta ((r.val : ℂ) / C) (-1 / τ) := by
  classical
  let w := 2 * (a : ℂ) / C + τ / (C : ℂ) ^ 2
  have hC : (C : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne C)
  have hw : 0 < w.im := by
    rw [rationalArgument_im]
    exact div_pos hτ (pow_pos (Nat.cast_pos.mpr (NeZero.pos C)) _)
  let f (n : ℤ) := v (n : ZMod B) * ((n : ℂ) * jacobiTheta₂_term n 0 w)
  let e := (intResidues C).symm
  have hf : Summable f := (weightedTheta_hasSum v hw).summable
  have hfe : Summable (fun p => f (e p)) := e.summable_iff.mpr hf
  have hs (r : ZMod C) (n : ℤ) :
      f (e (r,n)) = ((C : ℂ) * (v (ZMod.castHom hBC (ZMod B) r) *
        ZMod.stdAddChar ((a : ZMod C) * r ^ 2))) *
        (((n : ℂ) + (r.val : ℂ) / C) * exp (π * I * τ * ((n : ℂ) + (r.val : ℂ) / C) ^ 2)) := by
    have hrC : ((e (r,n) : ℤ) : ZMod C) = r := by
      change ((intResidues C) (e (r,n))).1 = r
      rw [Equiv.apply_symm_apply]
    have hrB : ((e (r,n) : ℤ) : ZMod B) = ZMod.castHom hBC (ZMod B) r := by
      calc
        _ = ZMod.castHom hBC (ZMod B) ((e (r,n) : ℤ) : ZMod C) := (map_intCast _ _).symm
        _ = _ := congrArg (ZMod.castHom hBC (ZMod B)) hrC
    change v ((e (r,n) : ℤ) : ZMod B) * _ = _
    rw [hrB, show (a : ZMod C) * r ^ 2 = ((a * (r.val : ℤ)^2 : ℤ) : ZMod C) by simp,
      ZMod.stdAddChar_coe, jacobiTheta₂_term, mul_zero, zero_add]
    have hperiod := exp_int_mul_two_pi_mul_I (a * (2 * (r.val : ℤ) * n + (C : ℤ) * n^2))
    have hExp :
        exp (π * I * (e (r,n) : ℂ)^2 * w) =
          exp (2 * π * I * ((a * (r.val : ℤ)^2 : ℤ) : ℂ) / C) *
            exp (π * I * τ * ((n : ℂ) + (r.val : ℂ) / C)^2) := by
      rw [← exp_add, ← mul_one (exp (_ + _)), ← hperiod, ← exp_add]
      congr 1
      dsimp [w, e, intResidues]
      push_cast
      field_simp
      ring
    rw [hExp]
    dsimp [e, intResidues]
    push_cast
    field_simp
    ring
  change (∑' n, f n) = _
  rw [← e.tsum_eq f, hfe.tsum_prod, tsum_fintype]
  simp only [hs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [tsum_mul_left]
  change _ * linearLine ((r.val : ℂ) / C) τ = _
  rw [linearLine_poisson _ hτ]
  ring

/-- A bound for a real additive twist, uniform once the imaginary part
of the Jacobi parameter is bounded away from zero. -/
theorem norm_linearTheta_le (u : ℝ) {τ : ℂ} {T : ℝ} (hT : 0 < T) (hτ : T ≤ τ.im) :
    ‖linearTheta (u : ℂ) τ‖ ≤
      ∑' n : ℤ, |(n : ℝ)| * Real.exp (-π * (T * (n : ℝ) ^ 2)) := by
  apply (norm_tsum_le_tsum_norm (linearTheta_hasSum _ (hT.trans_le hτ)).summable.norm).trans
  apply ((linearTheta_hasSum _ (hT.trans_le hτ)).summable.norm).tsum_le_tsum
  · intro n
    rw [norm_mul, norm_intCast]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    simpa using norm_jacobiTheta₂_term_le hT (show |(u : ℂ).im| ≤ 0 by simp) hτ n
  · simpa using summable_pow_mul_jacobiTheta₂_term_bound 0 hT 1

/-- The convergent weighted series is holomorphic in its Jacobi parameter. -/
theorem weightedTheta_differentiableAt {B : ℕ} [NeZero B] (v : ZMod B → ℂ)
    {τ : ℂ} (hτ : 0 < τ.im) : DifferentiableAt ℂ (weightedTheta v) τ := by
  obtain ⟨T, hT, hτT⟩ := exists_between hτ
  let C := ∑ r : ZMod B, ‖v r‖
  let U := {w : ℂ | T < w.im}
  have hU : IsOpen U := continuous_im.isOpen_preimage _ isOpen_Ioi
  apply DifferentiableOn.differentiableAt _ (hU.mem_nhds hτT)
  let f (n : ℤ) (w : ℂ) := v (n : ZMod B) * ((n : ℂ) * jacobiTheta₂_term n 0 w)
  have hs : Summable (fun n : ℤ => C * (|(n : ℝ)| * Real.exp (-π * (T * (n : ℝ)^2)))) := by
    simpa using (summable_pow_mul_jacobiTheta₂_term_bound 0 hT 1).mul_left C
  apply differentiableOn_tsum_of_summable_norm (F := f) hs _ hU
  · intro n w hw
    have hv : ‖v (n : ZMod B)‖ ≤ C :=
      Finset.single_le_sum (fun r _ => norm_nonneg (v r)) (Finset.mem_univ _)
    have hb := norm_jacobiTheta₂_term_le hT (show |(0 : ℂ).im| ≤ 0 by simp)
      (show T ≤ w.im from le_of_lt hw) n
    rw [norm_mul, norm_mul, norm_intCast]
    apply mul_le_mul hv _ (by positivity) (norm_nonneg _ |>.trans hv)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    simpa using hb
  · intro n
    unfold f jacobiTheta₂_term
    fun_prop

end ZInQ.Manuscript.RC.EvenUnary
