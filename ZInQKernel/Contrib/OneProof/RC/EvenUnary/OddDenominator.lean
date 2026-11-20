import ZInQKernel.Contrib.OneProof.RC.HalfIntegral.ThetaPoisson

/-! Ordinary Poisson summation at an odd denominator, using the inverse
of two in the finite completion of the square. -/

noncomputable section
set_option maxHeartbeats 1000000

namespace ZInQ.Manuscript.RC.EvenUnary

open Complex HalfIntegral
open scoped Real

/-- For (d) odd, Poisson resummation at (b/d) uses every frequency.
The residual linear phase vanishes when the companion lower-left entry
is a multiple of four. -/
theorem ordinaryTheta_odd_denominator {d : ℕ} [NeZero d] (hd : Odd d)
    (b e : ℤ) (hbe : (b : ZMod d) * (e : ZMod d) = -1) (he : (4 : ℤ) ∣ e)
    {τ w : ℂ} (hτ : 0 < τ.im) (hw : -1 / τ = w - (e : ℂ) / (2 * d)) :
    jacobiTheta (2 * (b : ℂ) / d + τ / (d : ℂ)^2) =
      (1 / (-I * τ) ^ (1 / 2 : ℂ)) * quadraticFourier (b : ZMod d) 0 * jacobiTheta w := by
  obtain ⟨k, hk⟩ := hd
  obtain ⟨l, hl⟩ := he
  let h : ℤ := (k : ℤ) + 1
  have h2 : (2 : ℤ) * h = (d : ℤ) + 1 := by dsimp [h]; omega
  have h2' : (2 : ZMod d) * h = 1 := by
    simpa only [Int.cast_mul, Int.cast_ofNat, Int.cast_add, Int.cast_natCast, ZMod.natCast_self,
      zero_add, Int.cast_one] using congrArg (Int.cast : ℤ → ZMod d) h2
  have hde : (b : ZMod d) * (-(e : ℤ) : ZMod d) = 1 := by rw [mul_neg, hbe, neg_neg]
  have hfactor (n : ℤ) : quadraticFourier (b : ZMod d) (n : ZMod d) =
      ZMod.stdAddChar ((e : ZMod d) * ((h * n : ℤ) : ZMod d)^2) *
        quadraticFourier (b : ZMod d) 0 := by
    have hn : (2 : ZMod d) * (↑(h * n) : ZMod d) = n := by rw [Int.cast_mul, ← mul_assoc, h2', one_mul]
    conv_lhs => rw [← hn]
    rw [quadraticFourier_even hde]
    simp only [neg_mul, neg_neg]
  have hphase (n : ℤ) :
      ZMod.stdAddChar ((e : ZMod d) * ((h * n : ℤ) : ZMod d)^2) *
        exp (π * I * (n : ℂ)^2 * (-1 / τ)) = exp (π * I * (n : ℂ)^2 * w) := by
    rw [show (e : ZMod d) * ((h * n : ℤ) : ZMod d)^2 =
      ((e * (h*n)^2 : ℤ) : ZMod d) by push_cast; rfl, ZMod.stdAddChar_coe, hw, ← exp_add]
    have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
    have hp := exp_int_mul_two_pi_mul_I (l * ((d : ℤ) + 2) * n^2)
    nth_rw 2 [← mul_one (exp _)]
    rw [← hp, ← exp_add]
    congr 1
    have h2C := congrArg (Int.cast : ℤ → ℂ) h2
    push_cast at h2C ⊢
    have heC := congrArg (Int.cast : ℤ → ℂ) hl
    push_cast at heC
    rw [heC]
    field_simp [hdC]
    linear_combination (4 * (l : ℂ) * (n : ℂ)^2 * (2 * (h : ℂ) + (d : ℂ) + 1)) * h2C
  rw [jacobiTheta_rational_resum b hτ, mul_assoc]
  apply congrArg (fun x => (1 / (-I * τ) ^ (1 / 2 : ℂ)) * x)
  rw [jacobiTheta, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [hfactor]
  calc
    _ = quadraticFourier (b : ZMod d) 0 *
      (ZMod.stdAddChar ((e : ZMod d) * ((h * n : ℤ) : ZMod d)^2) *
        exp (π * I * (n : ℂ)^2 * (-1 / τ))) := by ring
    _ = _ := by rw [hphase]

end ZInQ.Manuscript.RC.EvenUnary
