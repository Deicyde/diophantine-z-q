import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelCompletedTheta
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelThetaZeroSet
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Analytic.Order
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionDistributionTwoRegular

/-!
# The intrinsic torsion Kronecker kernel

The normalized quotient uses the actual completed odd theta function.
Its two fractional-period characters have the orientation of the torsion
pairing, and its simple-pole coefficient is exactly the reciprocal level.
These are local analytic ingredients for finite torsion Fourier duality;
no finite Fourier identity is assumed or asserted by the definitions.
-/

noncomputable section

open Complex UpperHalfPlane Filter
open scoped Topology

namespace ZInQ.Contrib.HeckePrimeRationality.TorsionFourierKernel

open CompletedTheta

/-- The normalized theta quotient for a torsion row; the zero row is not a pole kernel. -/
def kernel (N : ℕ) (a b : ℤ) (τ : ℍ) (z : ℂ) : ℂ :=
  Hder τ 0 / H τ (-(torsionPoint N a b τ)) *
    Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * z) *
      (H τ ((N : ℂ) * z - torsionPoint N a b τ) / H τ ((N : ℂ) * z))

lemma Hder_zero_ne (τ : ℍ) : Hder τ 0 ≠ 0 := by
  have h0 := AllLevelThetaZeroSet.jacobiTheta₂_half_shift_eq_zero τ.im_pos
  have h1 := AllLevelThetaZeroSet.jacobiTheta₂'_half_shift_ne_zero τ
  simpa [Hder, h0] using h1

lemma H_minus_torsion_ne (N : ℕ) [NeZero N] (a b : ℤ) (τ : ℍ)
    (hg : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b)) :
    H τ (-(torsionPoint N a b τ)) ≠ 0 := by
  rw [H_neg]
  exact neg_ne_zero.mpr (H_torsion_ne_zero N (NeZero.pos N) τ a b hg)

/-- Translation by 1/N gives the second-coordinate pairing character. -/
lemma kernel_add_one_div (N : ℕ) [NeZero N] (a b : ℤ) (τ : ℍ) (z : ℂ) :
    kernel N a b τ (z + 1 / (N : ℂ)) =
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) / (N : ℂ)) * kernel N a b τ z := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hz : (N : ℂ) * (z + 1 / (N : ℂ)) = (N : ℂ) * z + 1 := by field_simp
  unfold kernel
  rw [hz, show (N : ℂ) * z + 1 - torsionPoint N a b τ =
      ((N : ℂ) * z - torsionPoint N a b τ) + 1 by ring,
    H_add_one, H_add_one, neg_div_neg_eq]
  rw [show -2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * (z + 1 / (N : ℂ)) =
      -2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * z +
      (-2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) / (N : ℂ)) by ring,
    Complex.exp_add]
  ring

/-- Translation by τ/N gives the first-coordinate pairing character. -/
lemma kernel_add_tau_div (N : ℕ) [NeZero N] (a b : ℤ) (τ : ℍ) (z : ℂ) :
    kernel N a b τ (z + (τ : ℂ) / (N : ℂ)) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (b : ℂ) / (N : ℂ)) * kernel N a b τ z := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hz : (N : ℂ) * (z + (τ : ℂ) / (N : ℂ)) = (N : ℂ) * z + τ := by field_simp
  let u := torsionPoint N a b τ
  have hr : H τ ((N : ℂ) * z + τ - u) / H τ ((N : ℂ) * z + τ) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * u) *
        (H τ ((N : ℂ) * z - u) / H τ ((N : ℂ) * z)) := by
    rw [show (N : ℂ) * z + τ - u = ((N : ℂ) * z - u) + τ by ring,
      H_add_tau, H_add_tau]
    rw [show -(Real.pi : ℂ) * Complex.I * τ - 2 * (Real.pi : ℂ) * Complex.I *
        ((N : ℂ) * z - u) =
        (-(Real.pi : ℂ) * Complex.I * τ - 2 * (Real.pi : ℂ) * Complex.I * ((N : ℂ) * z)) +
        (2 * (Real.pi : ℂ) * Complex.I * u) by ring, Complex.exp_add]
    field_simp
  have he : -2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) *
      (z + (τ : ℂ) / (N : ℂ)) + 2 * (Real.pi : ℂ) * Complex.I * u =
      2 * (Real.pi : ℂ) * Complex.I * (b : ℂ) / (N : ℂ) +
        (-2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * z) := by
    dsimp [u, torsionPoint]
    field_simp
    ring
  unfold kernel
  rw [hz]
  change _ * Complex.exp _ * (H τ ((N : ℂ) * z + τ - u) / H τ ((N : ℂ) * z + τ)) = _
  rw [hr]
  rw [← mul_assoc, mul_assoc (Hder τ 0 / H τ (-u)), ← Complex.exp_add, he, Complex.exp_add]
  ring

/-- The punctured origin limit gives the true simple-pole coefficient 1/N. -/
theorem kernel_residue_zero (N : ℕ) [NeZero N] (a b : ℤ) (τ : ℍ)
    (hg : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b)) :
    Tendsto (fun z : ℂ => z * kernel N a b τ z) (𝓝[≠] 0) (𝓝 ((N : ℂ)⁻¹)) := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hH := Hder_zero_ne τ
  have hden := H_minus_torsion_ne N a b τ hg
  have hd : HasDerivAt (fun z : ℂ => H τ ((N : ℂ) * z))
      (Hder τ 0 * (N : ℂ)) 0 := by
    have hmul : HasDerivAt (fun z : ℂ => (N : ℂ) * z) (N : ℂ) 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_mul (N : ℂ)
    simpa only [Function.comp_def, mul_zero] using
      (hasDerivAt_H τ ((N : ℂ) * 0)).comp (0 : ℂ) hmul
  have hs : Tendsto (fun z : ℂ => H τ ((N : ℂ) * z) / z) (𝓝[≠] 0)
      (𝓝 (Hder τ 0 * (N : ℂ))) := by
    simpa [smul_eq_mul, H_zero, div_eq_mul_inv, mul_comm] using hd.tendsto_slope_zero
  have hinv := hs.inv₀ (mul_ne_zero hH hN)
  have hexp : Tendsto (fun z : ℂ => Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * z))
      (𝓝[≠] 0) (𝓝 (1 : ℂ)) := by
    have hc : ContinuousAt (fun z : ℂ =>
        Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * z)) 0 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hnum : Tendsto (fun z : ℂ => H τ ((N : ℂ) * z - torsionPoint N a b τ))
      (𝓝[≠] 0) (𝓝 (H τ (-(torsionPoint N a b τ)))) := by
    have hc : ContinuousAt (fun z : ℂ => H τ ((N : ℂ) * z - torsionPoint N a b τ)) 0 :=
      (differentiable_H τ).continuous.continuousAt.comp
        (by fun_prop : ContinuousAt (fun z : ℂ => (N : ℂ) * z - torsionPoint N a b τ) 0)
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hl := (((tendsto_const_nhds (x := Hder τ 0 / H τ (-(torsionPoint N a b τ)))).mul hexp).mul hnum).mul hinv
  convert hl using 1
  · ext z
    dsimp [kernel]
    simp only [inv_div]
    ring
  · field_simp

lemma Hder_neg (τ : ℍ) (z : ℂ) : Hder τ (-z) = Hder τ z := by
  have hl := (hasDerivAt_H τ (-z)).comp z (hasDerivAt_id z).neg
  have hr : HasDerivAt (fun w : ℂ => H τ (-w)) (-Hder τ z) z := by
    simpa only [H_neg] using (hasDerivAt_H τ z).fun_neg
  have he := hl.unique hr
  simpa using he

lemma Hder_analytic (τ : ℍ) (z : ℂ) : AnalyticAt ℂ (Hder τ) z := by
  have hh : AnalyticAt ℂ (H τ) z := (differentiable_H τ).analyticAt z
  have he : deriv (H τ) = Hder τ := funext (deriv_H τ)
  rw [← he]
  exact hh.deriv

lemma deriv_Hder_zero (τ : ℍ) : deriv (Hder τ) 0 = 0 := by
  have hd := (Hder_analytic τ 0).differentiableAt.hasDerivAt
  have hd' : HasDerivAt (Hder τ) (deriv (Hder τ) 0) (- (0 : ℂ)) := by simpa using hd
  have hl := hd'.comp (0 : ℂ) (hasDerivAt_id (0 : ℂ)).neg
  have hr : HasDerivAt (fun w : ℂ => Hder τ (-w)) (deriv (Hder τ) 0) 0 := by
    simpa only [Hder_neg] using hd
  have he := hl.unique hr
  linear_combination -he / 2

/-- A genuine odd-theta Taylor factor with no quadratic term. -/
lemma H_cubic_germ (τ : ℍ) : ∃ A : ℂ → ℂ, AnalyticAt ℂ A 0 ∧
    H τ =ᶠ[𝓝 0] (fun z => Hder τ 0 * z + z ^ 3 * A z) := by
  have hh : AnalyticAt ℂ (H τ) 0 := (differentiable_H τ).analyticAt 0
  have h2 : iteratedDeriv 2 (H τ) 0 = 0 := by
    rw [iteratedDeriv_succ', iteratedDeriv_one]
    change deriv (deriv (H τ)) 0 = 0
    rw [funext (deriv_H τ)]
    exact deriv_Hder_zero τ
  obtain ⟨A, hA, hEq⟩ := hh.exists_eventuallyEq_sum_add_pow_mul 3
  refine ⟨A, hA, ?_⟩
  change ∀ᶠ z in 𝓝 0, H τ z = Hder τ 0 * z + z ^ 3 * A z
  simpa [Finset.sum_range_succ, smul_eq_mul, H_zero, iteratedDeriv_one, deriv_H, h2,
    mul_comm] using hEq

/-- The actual Laurent finite part at zero is minus `2πi` times the original torsion function. -/
theorem kernel_finitePart_zero (N : ℕ) [NeZero N] (a b : ℤ) (τ : ℍ)
    (hg : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b)) :
    Tendsto (fun z : ℂ => kernel N a b τ z - 1 / ((N : ℂ) * z))
      (𝓝[≠] 0) (𝓝 (-2 * (Real.pi : ℂ) * Complex.I * TorsionDistributionTwo.reg N a b τ)) := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hH := Hder_zero_ne τ
  have hden := H_minus_torsion_ne N a b τ hg
  let u := torsionPoint N a b τ
  obtain ⟨A, hA, hEq⟩ := H_cubic_germ τ
  let D : ℂ → ℂ := fun z => (N : ℂ) * (Hder τ 0 + ((N : ℂ) * z) ^ 2 * A ((N : ℂ) * z))
  let B : ℂ → ℂ := fun z => Hder τ 0 / H τ (-u) *
    Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * z) * H τ ((N : ℂ) * z - u)
  let E : ℂ → ℂ := fun z => B z / D z
  have hAcomp : AnalyticAt ℂ (fun z : ℂ => A ((N : ℂ) * z)) 0 := by
    have hAz : AnalyticAt ℂ A ((N : ℂ) * 0) := by simpa using hA
    exact hAz.comp (by fun_prop : AnalyticAt ℂ (fun z : ℂ => (N : ℂ) * z) 0)
  have hD : HasDerivAt D 0 0 := by
    dsimp [D]
    convert (hasDerivAt_const 0 (Hder τ 0)).add
      ((((hasDerivAt_id (0 : ℂ)).const_mul (N : ℂ)).pow 2).mul
        hAcomp.differentiableAt.hasDerivAt) |>.const_mul (N : ℂ) using 1 <;> simp
  have hD0 : D 0 = (N : ℂ) * Hder τ 0 := by simp [D]
  have hB : HasDerivAt B
      (Hder τ 0 / H τ (-u) *
        ((-2 * (Real.pi : ℂ) * Complex.I * (a : ℂ)) * H τ (-u) +
          Hder τ (-u) * (N : ℂ))) 0 := by
    have hexp : HasDerivAt (fun z : ℂ =>
        Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * z))
        (-2 * (Real.pi : ℂ) * Complex.I * (a : ℂ)) 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).const_mul
        (-2 * (Real.pi : ℂ) * Complex.I * (a : ℂ))).cexp
    have hnum : HasDerivAt (fun z : ℂ => H τ ((N : ℂ) * z - u))
        (Hder τ (-u) * (N : ℂ)) 0 := by
      have hm : HasDerivAt (fun z : ℂ => (N : ℂ) * z - u) (N : ℂ) 0 := by
        simpa using ((hasDerivAt_id (0 : ℂ)).const_mul (N : ℂ)).sub_const u
      simpa only [Function.comp_def, mul_zero, zero_sub] using
        (hasDerivAt_H τ ((N : ℂ) * 0 - u)).comp (0 : ℂ) hm
    simpa only [B, Pi.mul_apply, mul_assoc, mul_zero, Complex.exp_zero, zero_sub, mul_one, one_mul]
      using (hexp.mul hnum).const_mul (Hder τ 0 / H τ (-u))
  have hDne : D 0 ≠ 0 := by rw [hD0]; exact mul_ne_zero hN hH
  have hE := hB.div hD hDne
  have hE0 : E 0 = (N : ℂ)⁻¹ := by
    have hu : H τ (-u) ≠ 0 := hden
    dsimp [E, B, D]
    simp only [mul_zero, Complex.exp_zero, zero_sub, mul_one, zero_pow (by norm_num : 2 ≠ 0),
      zero_mul, add_zero]
    field_simp [hu, hH, hN]
  have hgerm : (fun z => kernel N a b τ z - 1 / ((N : ℂ) * z)) =ᶠ[𝓝[≠] 0]
      (fun z => (E z - E 0) / z) := by
    have hc : Tendsto (fun z : ℂ => (N : ℂ) * z) (𝓝 0) (𝓝 0) := by
      simpa using (by fun_prop : ContinuousAt (fun z : ℂ => (N : ℂ) * z) 0).tendsto
    have heNz : ∀ᶠ z in 𝓝 0, H τ ((N : ℂ) * z) =
        Hder τ 0 * ((N : ℂ) * z) + ((N : ℂ) * z) ^ 3 * A ((N : ℂ) * z) :=
      hEq.comp_tendsto hc
    have hDloc : ∀ᶠ z in 𝓝 0, D z ≠ 0 := hD.continuousAt.eventually_ne hDne
    filter_upwards [heNz.filter_mono nhdsWithin_le_nhds,
      hDloc.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hez hDz hz
    rw [hE0]
    have htheta : H τ ((N : ℂ) * z) = z * D z := by
      rw [hez]
      dsimp [D]
      ring
    dsimp [kernel, E, B, u]
    rw [htheta]
    have hz0 : z ≠ 0 := hz
    field_simp [hden, hz0, hDz, hN]
  have ht := hE.tendsto_slope_zero
  have hdE : (Hder τ 0 / H τ (-u) *
      (-2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * H τ (-u) + Hder τ (-u) * (N : ℂ)) * D 0 -
      B 0 * 0) / D 0 ^ 2 =
      -2 * (Real.pi : ℂ) * Complex.I * TorsionDistributionTwo.reg N a b τ := by
    rw [TorsionDistributionTwo.reg_of_good hg, torsionLogDerivative_eq N (NeZero.pos N) τ a b hg]
    rw [hD0, Hder_neg, H_neg]
    dsimp [B, u]
    have hu := H_torsion_ne_zero N (NeZero.pos N) τ a b hg
    field_simp [hu, hden, hH, hN]
    ring
  rw [hdE] at ht
  exact ht.congr' (by
    filter_upwards [hgerm] with z hz
    simpa [E, Pi.div_apply, smul_eq_mul, sub_eq_add_neg, div_eq_mul_inv, mul_comm, add_comm] using hz.symm)

lemma kernel_zero_row (N : ℕ) (τ : ℍ) (z : ℂ) : kernel N 0 0 τ z = 0 := by
  simp [kernel, torsionPoint, H_zero]

lemma kernel_add_nat_one_div (N : ℕ) [NeZero N] (a b : ℤ) (τ : ℍ) (z : ℂ) (s : ℕ) :
    kernel N a b τ (z + (s : ℂ) / (N : ℂ)) =
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) / (N : ℂ)) ^ s * kernel N a b τ z := by
  induction s with
  | zero => simp
  | succ s ih =>
      rw [show (z + ((s + 1 : ℕ) : ℂ) / (N : ℂ)) =
        (z + (s : ℂ) / (N : ℂ)) + 1 / (N : ℂ) by push_cast; ring,
        kernel_add_one_div, ih, pow_succ]
      ring

lemma kernel_add_nat_tau_div (N : ℕ) [NeZero N] (a b : ℤ) (τ : ℍ) (z : ℂ) (r : ℕ) :
    kernel N a b τ (z + (r : ℂ) * (τ : ℂ) / (N : ℂ)) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (b : ℂ) / (N : ℂ)) ^ r * kernel N a b τ z := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [show (z + ((r + 1 : ℕ) : ℂ) * (τ : ℂ) / (N : ℂ)) =
        (z + (r : ℂ) * (τ : ℂ) / (N : ℂ)) + (τ : ℂ) / (N : ℂ) by push_cast; ring,
        kernel_add_tau_div, ih, pow_succ]
      ring

/-- The exact finite-label Weil character of the intrinsic kernel. -/
theorem kernel_add_torsion (N : ℕ) [NeZero N] (a b : ℤ) (τ : ℍ) (z : ℂ) (r s : ℕ) :
    kernel N a b τ (z + torsionPoint N r s τ) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        ((b : ℂ) * (r : ℂ) - (a : ℂ) * (s : ℂ)) / (N : ℂ)) * kernel N a b τ z := by
  have hp : torsionPoint N r s τ = (r : ℂ) * (τ : ℂ) / (N : ℂ) + (s : ℂ) / (N : ℂ) := by
    dsimp [torsionPoint]
    push_cast
    ring
  rw [hp, ← add_assoc, kernel_add_nat_one_div, kernel_add_nat_tau_div,
    ← mul_assoc, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 2
  ring

/-- All finite torsion poles have the actual character-weighted simple-pole coefficient. -/
theorem kernel_residue_torsion (N : ℕ) [NeZero N] (a b : ℤ) (τ : ℍ)
    (hg : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b)) (r s : ℕ) :
    Tendsto (fun z : ℂ => z * kernel N a b τ (z + torsionPoint N r s τ))
      (𝓝[≠] 0) (𝓝 (Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        ((b : ℂ) * (r : ℂ) - (a : ℂ) * (s : ℂ)) / (N : ℂ)) / (N : ℂ))) := by
  simp_rw [kernel_add_torsion]
  simpa only [div_eq_mul_inv, mul_left_comm] using (kernel_residue_zero N a b τ hg).const_mul
    (Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
      ((b : ℂ) * (r : ℂ) - (a : ℂ) * (s : ℂ)) / (N : ℂ)))

/-- The actual finite part at any finite torsion translate has the same Weil character. -/
theorem kernel_finitePart_torsion (N : ℕ) [NeZero N] (a b : ℤ) (τ : ℍ)
    (hg : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b)) (r s : ℕ) :
    Tendsto (fun z : ℂ => kernel N a b τ (z + torsionPoint N r s τ) -
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
          ((b : ℂ) * (r : ℂ) - (a : ℂ) * (s : ℂ)) / (N : ℂ)) / ((N : ℂ) * z))
      (𝓝[≠] 0) (𝓝 (-2 * (Real.pi : ℂ) * Complex.I *
        TorsionDistributionTwo.reg N a b τ * Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
          ((b : ℂ) * (r : ℂ) - (a : ℂ) * (s : ℂ)) / (N : ℂ)))) := by
  simp_rw [kernel_add_torsion]
  convert (kernel_finitePart_zero N a b τ hg).const_mul
    (Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
      ((b : ℂ) * (r : ℂ) - (a : ℂ) * (s : ℂ)) / (N : ℂ))) using 1
  · ext z
    ring
  · ring

end ZInQ.Contrib.HeckePrimeRationality.TorsionFourierKernel
