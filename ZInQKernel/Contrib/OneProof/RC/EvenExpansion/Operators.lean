import ZInQKernel.Contrib.OneProof.RC.HalfIntegral.Fourier
import ZInQKernel.Contrib.OneProof.RC.Odd.Operators

/-! The Fourier calculations for the finite operators in tex 9497–9546.
Their comparison as half-integral forms has to use the specified higher
level and theta multiplier. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenExpansion

open UpperHalfPlane HalfIntegral Function Odd
open scoped BigOperators ZMod

set_option maxHeartbeats 800000

/-- Period-one Fourier sums before any transformation-law assertion. -/
def Series (a : ℕ → ℂ) (g : ℍ → ℂ) : Prop :=
  ∀ z : ℍ, HasSum (fun n : ℕ => a n * Periodic.qParam 1 (z : ℂ) ^ n) (g z)

private def dilate (r : ℝ) (hr : 0 < r) (z : ℍ) : ℍ :=
  ⟨(r : ℂ) * (z : ℂ), by rw [Complex.im_ofReal_mul]; exact mul_pos hr z.im_pos⟩

/-- The dilation (V_p), acting on the actual function. -/
def Vp (p : ℕ) (hp : 0 < p) (g : ℍ → ℂ) (z : ℍ) : ℂ :=
  g (dilate p (by exact_mod_cast hp) z)

private def deltaResidue {p : ℕ} [NeZero p] (x : ZMod p) : ℂ :=
  if x = 0 then 1 else 0

/-- The normalized finite additive average (U_p). -/
def Up (p : ℕ) [NeZero p] (g : ℍ → ℂ) (z : ℍ) : ℂ :=
  (p : ℂ)⁻¹ * ∑ u : ZMod p, g (residueShift u +ᵥ dilate (p : ℝ)⁻¹ (inv_pos.mpr (Nat.cast_pos.mpr (NeZero.pos p))) z)

private theorem up_translation (p : ℕ) [NeZero p] (g : ℍ → ℂ) (z : ℍ) :
    Up p g z = translationSum (deltaResidue (p := p)) g (dilate (p : ℝ)⁻¹ (inv_pos.mpr (Nat.cast_pos.mpr (NeZero.pos p))) z) := by
  have hw (u : ZMod p) : translationWeights deltaResidue u = (p : ℂ)⁻¹ := by
    rw [translationWeights, Pi.smul_apply, ZMod.dft_apply]
    have he : (∑ j : ZMod p, ZMod.stdAddChar (-(j * u)) • deltaResidue j) = 1 := by
      simp [deltaResidue, smul_ite]
    rw [he, smul_eq_mul, mul_one]
  simp [Up, translationSum, hw, Finset.mul_sum]

private theorem qParam_dilate (p : ℕ) (hp : 0 < p) (z : ℍ) :
    Periodic.qParam 1 (dilate p (by exact_mod_cast hp) z : ℂ) = Periodic.qParam 1 (z : ℂ) ^ p := by
  unfold Periodic.qParam
  rw [← Complex.exp_nat_mul]
  simp only [dilate, coe_mk, Complex.ofReal_natCast]
  congr 1
  ring

private theorem qParam_undilate (p : ℕ) [NeZero p] (z : ℍ) :
    Periodic.qParam 1 (dilate (p : ℝ)⁻¹ (inv_pos.mpr (Nat.cast_pos.mpr (NeZero.pos p))) z : ℂ) ^ p =
      Periodic.qParam 1 (z : ℂ) := by
  unfold Periodic.qParam
  rw [← Complex.exp_nat_mul]
  simp only [dilate, coe_mk, Complex.ofReal_inv, Complex.ofReal_natCast]
  congr 1
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  field_simp
  <;> ring

/-- (V_p) inserts zero Fourier coefficients at the other indices. -/
theorem series_Vp {a : ℕ → ℂ} {g : ℍ → ℂ} {p : ℕ} (hp : 0 < p) (h : Series a g) :
    Series (divCoeff a p) (Vp p hp g) := by
  intro z
  let f (n : ℕ) := divCoeff a p n * Periodic.qParam 1 (z : ℂ) ^ n
  let e (n : ℕ) := p * n
  have hi : Function.Injective e := fun _ _ h => Nat.eq_of_mul_eq_mul_left hp h
  have hz (n : ℕ) (hn : n ∉ Set.range e) : f n = 0 := by
    have hnd : ¬ p ∣ n := by
      rintro ⟨k, rfl⟩
      exact hn ⟨k, rfl⟩
    simp [f, divCoeff, hnd]
  apply (hi.hasSum_iff hz).mp
  let y := dilate p (by exact_mod_cast hp) z
  change HasSum (fun n => f (e n)) (g y)
  have he : (fun n => f (e n)) = (fun n => a n * Periodic.qParam 1 (y : ℂ) ^ n) := by
    funext n
    dsimp only [f, e, y]
    rw [divCoeff, ite_eq_left (dvd_mul_right p n), Nat.mul_div_cancel_left _ hp,
      qParam_dilate p hp z, pow_mul]
  rw [he]
  exact h y

/-- The normalized additive sum (U_p) retains exactly the (p)-multiple
coefficients and divides their Fourier indices by (p). -/
theorem series_Up {a : ℕ → ℂ} {g : ℍ → ℂ} (p : ℕ) [NeZero p] (h : Series a g) :
    Series (fun n => a (p * n)) (Up p g) := by
  intro z
  let y := dilate (p : ℝ)⁻¹ (inv_pos.mpr (Nat.cast_pos.mpr (NeZero.pos p))) z
  let e (n : ℕ) := p * n
  have hi : Function.Injective e := fun _ _ h => Nat.eq_of_mul_eq_mul_left (NeZero.pos p) h
  let f (n : ℕ) := (deltaResidue (n : ZMod p) * a n) * Periodic.qParam 1 (y : ℂ) ^ n
  have hz (n : ℕ) (hn : n ∉ Set.range e) : f n = 0 := by
    have hnd : ¬ p ∣ n := by
      rintro ⟨k, rfl⟩
      exact hn ⟨k, rfl⟩
    simp [f, deltaResidue, ZMod.natCast_eq_zero_iff, hnd]
  have hs : HasSum f (Up p g z) := by
    rw [up_translation]
    exact hasSum_translationSum deltaResidue h y
  have h' := (hi.hasSum_iff hz).mpr hs
  simpa [Function.comp_def, f, e, deltaResidue, pow_mul, y, qParam_undilate] using h'

/-- The manuscript's actual formula for (U_p-eta(p)V_p), expressed
using the half-integral operator (U_{p^2}) after dilation. -/
def movingOp (p : ℕ) [NeZero p] (η : ℂ) (g : ℍ → ℂ) : ℍ → ℂ :=
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero _ (NeZero.ne p)⟩
  Up (p ^ 2) (Vp p (NeZero.pos p) g) - η • Vp p (NeZero.pos p) g

/-- In particular (U_{p^2}V_p) has the Fourier coefficients of (U_p). -/
theorem series_Up_sq_Vp {a : ℕ → ℂ} {g : ℍ → ℂ} (p : ℕ) [NeZero p] (h : Series a g) :
    letI : NeZero (p ^ 2) := ⟨pow_ne_zero _ (NeZero.ne p)⟩
    Series (fun n => a (p * n)) (Up (p ^ 2) (Vp p (NeZero.pos p) g)) := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero _ (NeZero.ne p)⟩
  have he (n : ℕ) : divCoeff a p (p ^ 2 * n) = a (p * n) := by
    rw [pow_two, mul_assoc, divCoeff, if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ (NeZero.pos p)]
  have hv : Series (divCoeff a p) (Vp p (NeZero.pos p) g) := series_Vp (NeZero.pos p) h
  have hs := series_Up (p ^ 2) hv
  rw [show (fun n => divCoeff a p (p ^ 2 * n)) = (fun n => a (p * n)) from funext he] at hs
  exact hs

/-- All Fourier indices of the actual moving operator satisfy `Top`. -/
theorem movingOp_series {a : ℕ → ℂ} {g : ℍ → ℂ} (p : ℕ) [NeZero p] (η : ℂ)
    (h : Series a g) : Series (Odd.Top p η a) (movingOp p η g) := by
  intro z
  simpa only [Odd.Top, movingOp, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_mul, mul_assoc]
    using (series_Up_sq_Vp p h z).sub ((series_Vp (NeZero.pos p) h z).mul_left η)


end ZInQ.Manuscript.RC.EvenExpansion
