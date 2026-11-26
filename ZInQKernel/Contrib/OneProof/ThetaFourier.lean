import ZInQKernel.Contrib.OneProof.ThetaSeriesConvergence

/-!
# Fourier coefficients of the Riemann theta function

On a real translate of the integer-period torus, the Riemann theta series
is an absolutely convergent Fourier series. Its constant coefficient is
one, so the theta section has a nonzero value on each such slice.
-/

open scoped Topology
open Filter Matrix Complex MeasureTheory UnitAddTorus

noncomputable section

namespace BPAnalytic

variable {g : ℕ}

/-- The restriction of theta to the real translate through `z`, viewed as
a continuous function on the real torus. -/
def thetaOnRealSlice (Ω : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) :
    C(UnitAddTorus (Fin g), ℂ) :=
  ∑' n, riemannThetaSummand Ω n z • mFourier n

private theorem summable_smul_mFourier {a : (Fin g → ℤ) → ℂ}
    (ha : Summable fun n => ‖a n‖) :
    Summable (fun n => a n • mFourier n) := by
  apply Summable.of_norm
  simpa only [norm_smul, mFourier_norm, mul_one] using ha

-- Use the normalized Haar measure of Mathlib's Fourier basis.
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

private theorem mFourierCoeff_tsum_smul_mFourier {a : (Fin g → ℤ) → ℂ}
    (ha : Summable fun n => ‖a n‖) (n : Fin g → ℤ) :
    mFourierCoeff ((∑' k, a k • mFourier k) : C(UnitAddTorus (Fin g), ℂ)) n = a n := by
  classical
  let coeff : C(UnitAddTorus (Fin g), ℂ) →L[ℂ] ℂ :=
    (innerSL ℂ (mFourierLp 2 n)).comp (ContinuousMap.toLp 2 volume ℂ)
  have hcoeff (f : C(UnitAddTorus (Fin g), ℂ)) : coeff f = mFourierCoeff f n := by
    change inner ℂ (mFourierLp 2 n) (f.toLp 2 volume ℂ) = _
    rw [← mFourierCoeff_toLp f n, ← mFourierBasis_repr, HilbertBasis.repr_apply_apply,
      coe_mFourierBasis]
  have hb (k : Fin g → ℤ) : coeff (mFourier k) = if n = k then 1 else 0 := by
    change inner ℂ (mFourierLp 2 n) (mFourierLp 2 k) = _
    exact (orthonormal_iff_ite.mp orthonormal_mFourier) n k
  rw [← hcoeff, coeff.map_tsum (summable_smul_mFourier ha)]
  simp only [map_smul, hb, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [tsum_eq_single n]
  · simp
  · intro k hk
    simp [Ne.symm hk]

private theorem riemannThetaSummand_add_real (Ω : Matrix (Fin g) (Fin g) ℂ)
    (z : Fin g → ℂ) (x : Fin g → ℝ) (n : Fin g → ℤ) :
    riemannThetaSummand Ω n (z + fun j => (x j : ℂ)) =
      riemannThetaSummand Ω n z * mFourier n (fun j => (x j : UnitAddCircle)) := by
  have hm : mFourier n (fun j => (x j : UnitAddCircle)) =
      exp (2 * Real.pi * I * (intVec n ⬝ᵥ fun j => (x j : ℂ))) := by
    simp only [mFourier, ContinuousMap.coe_mk, fourier_coe_apply, Complex.ofReal_one, div_one,
      ← Complex.exp_sum, dotProduct, Finset.mul_sum, intVec]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hm]
  simp only [riemannThetaSummand, dotProduct_add, mul_add, ← add_assoc, Complex.exp_add]

/-- Evaluation on the real torus agrees with the original theta function. -/
theorem thetaOnRealSlice_apply (Ω : Matrix (Fin g) (Fin g) ℂ) (hΩ : Ω ∈ SiegelSpace g)
    (z : Fin g → ℂ) (x : Fin g → ℝ) :
    thetaOnRealSlice Ω z (fun j => (x j : UnitAddCircle)) =
      riemannTheta Ω (z + fun j => (x j : ℂ)) := by
  let eval : C(UnitAddTorus (Fin g), ℂ) →L[ℂ] ℂ :=
    ContinuousMap.evalCLM ℂ (fun j => (x j : UnitAddCircle))
  change eval (∑' n, riemannThetaSummand Ω n z • mFourier n) = _
  rw [eval.map_tsum (summable_smul_mFourier (summable_norm_riemannThetaSummand Ω hΩ z))]
  unfold riemannTheta
  exact tsum_congr (fun n => (riemannThetaSummand_add_real Ω z x n).symm)

/-- The Fourier coefficient at `n` is the corresponding theta summand
at the origin of the slice. -/
theorem mFourierCoeff_thetaOnRealSlice (Ω : Matrix (Fin g) (Fin g) ℂ)
    (hΩ : Ω ∈ SiegelSpace g) (z : Fin g → ℂ) (n : Fin g → ℤ) :
    mFourierCoeff (thetaOnRealSlice Ω z) n = riemannThetaSummand Ω n z :=
  mFourierCoeff_tsum_smul_mFourier (summable_norm_riemannThetaSummand Ω hΩ z) n

@[simp] theorem mFourierCoeff_thetaOnRealSlice_zero (Ω : Matrix (Fin g) (Fin g) ℂ)
    (hΩ : Ω ∈ SiegelSpace g) (z : Fin g → ℂ) : mFourierCoeff (thetaOnRealSlice Ω z) 0 = 1 := by
  rw [mFourierCoeff_thetaOnRealSlice Ω hΩ]
  have hzero : intVec (0 : Fin g → ℤ) = 0 := by
    funext j
    change ((0 : ℤ) : ℂ) = 0
    simp only [Int.cast_zero]
  simp [riemannThetaSummand, hzero]

/-- The Riemann theta function is nonzero somewhere on every real translate. -/
theorem exists_riemannTheta_add_real_ne_zero (Ω : Matrix (Fin g) (Fin g) ℂ)
    (hΩ : Ω ∈ SiegelSpace g) (z : Fin g → ℂ) :
    ∃ x : Fin g → ℝ, riemannTheta Ω (z + fun j => (x j : ℂ)) ≠ 0 := by
  by_contra! h
  have hz : thetaOnRealSlice Ω z = 0 := by
    apply ContinuousMap.ext
    intro q
    let x : Fin g → ℝ := fun j => (q j).out
    have hx : (fun j => (x j : UnitAddCircle)) = q := funext fun j => Quotient.out_eq (q j)
    rw [← hx, thetaOnRealSlice_apply Ω hΩ]
    exact h x
  simpa [hz, mFourierCoeff] using mFourierCoeff_thetaOnRealSlice_zero Ω hΩ z

/-- The holomorphic germ of theta is nonzero at every point of the covering space. -/
theorem riemannTheta_not_eventually_zero (Ω : Matrix (Fin g) (Fin g) ℂ)
    (hΩ : Ω ∈ SiegelSpace g) (z : Fin g → ℂ) :
    ¬ (riemannTheta Ω =ᶠ[𝓝 z] fun _ => 0) := by
  intro h
  have hθ : AnalyticOnNhd ℂ (riemannTheta Ω) Set.univ :=
    fun w _ => analyticAt_riemannTheta Ω hΩ w
  obtain ⟨x, hx⟩ := exists_riemannTheta_add_real_ne_zero Ω hΩ z
  exact hx (congrFun (hθ.eq_of_eventuallyEq analyticOnNhd_const h) _)

end BPAnalytic
