import ZInQKernel.Contrib.OneProof.RC.HalfIntegral.ThetaGauss
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable

/-!
# Poisson expansion at a rational point (provenance (c))

Split the ordinary theta series by integer residue classes and apply the
two-variable functional equation to each shifted Gaussian. At a denominator
divisible by four only the even frequencies survive; completing the square
then identifies the remaining series with the original theta function.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.HalfIntegral

open Complex
open scoped Real

private def intResidue (C : ℕ) [NeZero C] : ℤ ≃ (ZMod C × ℤ) where
  toFun n := (n, n / C)
  invFun p := p.1.val + (C : ℤ) * p.2
  left_inv n := by
    change ((n : ZMod C).val : ℤ) + (C : ℤ) * (n / C) = n
    rw [ZMod.val_intCast, Int.emod_add_mul_ediv]
  right_inv p := by
    have hC : (C : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne C)
    have hr : (p.1.val : ℤ) / C = 0 := Int.ediv_eq_zero_of_lt_abs
      (by positivity) (by
        rw [Int.abs_natCast]
        exact_mod_cast p.1.val_lt)
    apply Prod.ext
    · simp
    · change ((p.1.val : ℤ) + C * p.2) / C = p.2
      rw [Int.add_mul_ediv_left _ _ hC, hr, zero_add]

private theorem shiftedGaussian (x τ : ℂ) (hτ : τ ≠ 0) :
    (∑' n : ℤ, exp (π * I * τ * ((n : ℂ) + x)^2)) =
      1 / (-I * τ) ^ (1 / 2 : ℂ) * jacobiTheta₂ x (-1 / τ) := by
  calc
    _ = exp (π * I * τ * x ^ 2) * jacobiTheta₂ (τ * x) τ := by
      rw [jacobiTheta₂, ← tsum_mul_left]
      refine tsum_congr fun n ↦ ?_
      rw [jacobiTheta₂_term, ← Complex.exp_add]
      congr 1
      ring
    _ = _ := by
      rw [jacobiTheta₂_functional_equation]
      have hx : τ * x / τ = x := by field_simp
      have hs : -(π : ℂ) * I * (τ * x) ^ 2 / τ = -(π * I * τ * x ^ 2) := by
        field_simp
      rw [hx, hs]
      calc
        _ = (1 / (-I * τ) ^ (1 / 2 : ℂ)) *
            (exp (π * I * τ * x ^ 2) * exp (-(π * I * τ * x ^ 2))) *
            jacobiTheta₂ x (-1 / τ) := by ring
        _ = _ := by rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]

private theorem pos_im_neg_inv {τ : ℂ} (hτ : 0 < τ.im) : 0 < (-1 / τ).im := by
  have hz : τ ≠ 0 := fun h ↦ by simp [h] at hτ
  rw [neg_div, neg_im, one_div, inv_im, neg_div, neg_neg]
  exact div_pos hτ (normSq_pos.mpr hz)

theorem jacobiTheta_rational_resum {C : ℕ} [NeZero C] (a : ℤ) {τ : ℂ}
    (hτ : 0 < τ.im) :
    jacobiTheta (2 * (a : ℂ) / C + τ / (C : ℂ)^2) =
      1 / (-I * τ) ^ (1 / 2 : ℂ) * ∑' n : ℤ,
        quadraticFourier (a : ZMod C) (n : ZMod C) * exp (π * I * (n : ℂ)^2 * (-1 / τ)) := by
  classical
  let w : ℂ := 2 * (a : ℂ) / C + τ / (C : ℂ)^2
  have hC : (C : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne C)
  have hz : τ ≠ 0 := fun h ↦ by simp [h] at hτ
  have hw : 0 < w.im := by
    have e : w.im = τ.im / (C : ℝ)^2 := by
      dsimp [w]
      rw [show (2 * (a : ℂ) / C) = (((2 * (a : ℝ) / C) : ℝ) : ℂ) by push_cast; rfl,
        show (C : ℂ)^2 = (((C : ℝ)^2 : ℝ) : ℂ) by push_cast; rfl]
      simp only [ofReal_im, zero_add, div_ofReal_im]
    rw [e]
    exact div_pos hτ (pow_pos (Nat.cast_pos.mpr (NeZero.pos C)) _)
  let f (n : ℤ) := exp (π * I * (n : ℂ)^2 * w)
  have hf : Summable f := by
    simpa only [f, jacobiTheta₂_term, mul_zero, zero_add] using
      (summable_jacobiTheta₂_term_iff 0 w).mpr hw
  let e := (intResidue C).symm
  have hfe : Summable (fun p ↦ f (e p)) := e.summable_iff.mpr hf
  have hs (r : ZMod C) (n : ℤ) :
      f (e (r,n)) = ZMod.stdAddChar ((a : ZMod C) * r^2) *
        exp (π * I * τ * ((n : ℂ) + (r.val : ℂ)/C)^2) := by
    rw [show (a : ZMod C) * r^2 = ((a * (r.val : ℤ)^2 : ℤ) : ZMod C) by simp,
      ZMod.stdAddChar_coe, ← Complex.exp_add]
    have hperiod := Complex.exp_int_mul_two_pi_mul_I (a * (2 * (r.val : ℤ) * n + (C : ℤ) * n^2))
    dsimp [f, e, intResidue]
    calc
      _ = exp (2 * π * I * ((a * (r.val : ℤ)^2 : ℤ) : ℂ) / C +
          π * I * τ * ((n : ℂ) + (r.val : ℂ) / C)^2 +
          ((a * (2 * (r.val : ℤ) * n + (C : ℤ) * n^2) : ℤ) : ℂ) * (2 * π * I)) := by
        congr 1
        dsimp [w]
        push_cast
        field_simp
        ring
      _ = _ := by rw [Complex.exp_add, hperiod, mul_one]
  have ht (r : ZMod C) : Summable (jacobiTheta₂_term · ((r.val : ℂ) / C) (-1 / τ)) :=
    (summable_jacobiTheta₂_term_iff _ _).mpr (pos_im_neg_inv hτ)
  change (∑' n, f n) = _
  rw [← e.tsum_eq f, hfe.tsum_prod, tsum_fintype]
  simp_rw [hs, tsum_mul_left, shiftedGaussian _ _ hz, mul_left_comm (ZMod.stdAddChar _),
    ← Finset.mul_sum]
  congr 1
  simp_rw [jacobiTheta₂, ← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun r _ ↦ (ht r).mul_left _)]
  refine tsum_congr fun n ↦ ?_
  rw [quadraticFourier, Finset.sum_mul]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  have hl : exp (2 * π * I * (n : ℂ) * ((r.val : ℂ) / C)) =
      ZMod.stdAddChar ((n : ZMod C) * r) := by
    have hr : (n : ZMod C) * r = ((n * (r.val : ℤ) : ℤ) : ZMod C) := by simp
    rw [hr, ZMod.stdAddChar_coe]
    congr 1
    push_cast
    ring
  rw [jacobiTheta₂_term, Complex.exp_add, hl, ← mul_assoc, ← AddChar.map_add_eq_mul]

private theorem tsum_even_odd (f : ℤ → ℂ) (hf : Summable f) :
    (∑' n, f n) = (∑' n : ℤ, f (2*n)) + (∑' n : ℤ, f (2*n+1)) := by
  let e : Fin 2 × ℤ ≃ ℤ := (intResidue 2).symm
  have he : Summable (fun p ↦ f (e p)) := e.summable_iff.mpr hf
  rw [← e.tsum_eq f, he.tsum_prod, tsum_fintype]
  change (∑ r : Fin 2, ∑' n : ℤ, f (e (r,n))) = _
  rw [Fin.sum_univ_two]
  have hzero (n : ℤ) : e (0,n) = 2*n := zero_add _
  have hone : ∀ n : ℤ, e (1,n) = 2*n+1 := by
    intro n
    change (1 : ℤ) + 2*n = _
    ring
  simp only [hzero, hone]

/-- The unevaluated quadratic sum is the only numerator dependence in the
theta transformation at a cusp with positive denominator divisible by four. -/
theorem jacobiTheta_at_cusp {k : ℕ} [NeZero (4 * k)] (a d : ℤ) {z : ℂ} (hz : 0 < z.im)
    (had : (a : ZMod (4 * k)) * d = 1) :
    let C := (4 * k : ℕ)
    let t : ℂ := z / 2 + (d : ℂ) / (2 * C)
    jacobiTheta (2 * (a : ℂ) / C - 2 / ((C : ℂ) * ((C : ℂ) * z + d))) =
      (1 / (-I * (-1 / t)) ^ (1 / 2 : ℂ)) *
        quadraticFourier (a : ZMod C) 0 * jacobiTheta (2 * z) := by
  let C := 4 * k
  let t : ℂ := z / 2 + (d : ℂ) / (2 * C)
  have hC : (C : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne C)
  have ht : 0 < t.im := by
    dsimp [t]
    rw [show (d : ℂ) / (2 * (C : ℂ)) = (((d : ℝ) / (2 * C) : ℝ) : ℂ) by push_cast; rfl]
    simp only [ofReal_im, add_zero, div_ofNat_im]
    exact div_pos hz (by norm_num)
  have htn : t ≠ 0 := fun h ↦ by simp [h] at ht
  have he : (-1 / t : ℂ) / (C : ℂ)^2 = -(2 / ((C : ℂ) * ((C : ℂ) * z + d))) := by
    have hf : (C : ℂ) * z + d = 2 * (C : ℂ) * t := by dsimp [t]; field_simp
    rw [hf]
    field_simp
  have hneg : -1 / (-1 / t) = t := by field_simp
  change jacobiTheta (2 * (a : ℂ) / C - 2 / _) = _
  rw [sub_eq_add_neg, ← he, jacobiTheta_rational_resum a (pos_im_neg_inv ht), hneg]
  rw [mul_assoc]
  congr 1
  -- split the Fourier frequencies into even and odd
  let f (n : ℤ) := quadraticFourier (a : ZMod C) (n : ZMod C) * exp (π * I * (n : ℂ)^2 * t)
  have hf : Summable f := by
    have hs : Summable (fun n : ℤ ↦ ‖exp (π * I * (n : ℂ)^2 * t)‖) := by
      rw [summable_norm_iff]
      simpa only [jacobiTheta₂_term, mul_zero, zero_add] using (summable_jacobiTheta₂_term_iff 0 t).mpr ht
    refine (hs.mul_left (C : ℝ)).of_norm_bounded fun n ↦ ?_
    dsimp only [f]
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    unfold quadraticFourier
    exact (norm_sum_le _ _).trans (by simp [ZMod.stdAddChar_apply, ZMod.card])
  have hsplit := tsum_even_odd f hf
  have h1 : (∑' n : ℤ, f (2*n+1)) = 0 := by
    calc
      _ = ∑' _ : ℤ, (0 : ℂ) := by
        refine tsum_congr fun n ↦ ?_
        have ho : Odd (2*n+1) := ⟨n, rfl⟩
        dsimp only [f]
        rw [quadraticFourier_odd k _ _ ho, zero_mul]
      _ = 0 := tsum_zero
  have h0 (n : ℤ) : f (2*n) = quadraticFourier (a : ZMod C) 0 *
      exp (π * I * (n : ℂ)^2 * (2 * z)) := by
    dsimp only [f]
    push_cast
    rw [quadraticFourier_even had, mul_comm (ZMod.stdAddChar _), mul_assoc]
    have hcast : -( (d : ZMod C) * (n : ZMod C)^2) =
        ((- (d*n^2) : ℤ) : ZMod C) := by push_cast; rfl
    rw [hcast, ZMod.stdAddChar_coe, ← Complex.exp_add]
    congr 2
    dsimp [t, C]
    push_cast
    field_simp
    ring
  change (∑' n, f n) = _
  rw [hsplit, h1, add_zero]
  simp_rw [h0, tsum_mul_left, jacobiTheta]

#print axioms shiftedGaussian
#print axioms pos_im_neg_inv
#print axioms jacobiTheta_rational_resum
#print axioms tsum_even_odd
#print axioms jacobiTheta_at_cusp

end ZInQ.Manuscript.RC.HalfIntegral
