import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionMuFourierLaurent
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelWeierstrassDistributionNat

/-!
# Actual weight-two torsion Fourier duality

The forward transform is extracted by differentiating a proved ordinary analytic
germ of the actual global kernel comparison. All coordinates use the given
zero-extension convention. The inverse transform follows by finite character
orthogonality, not by defining a proxy for the quadratic torsion value.
-/

noncomputable section
set_option autoImplicit false
open Complex UpperHalfPlane Filter Function
open scoped Topology

namespace ZInQ.Contrib.HeckePrimeRationality.TorsionMuFourier

open CompletedTheta TorsionFourierKernel TorsionFourierComparison
open TorsionMuFourierKernel TorsionWeierstrassData

variable (N : ℕ) [NeZero N]

/-- The character-weighted analytic units of the actual finite kernel family. -/
def unitSum (τ : ℍ) (r s : Fin N) (z : ℂ) : ℂ :=
  -(N : ℂ) * ∑ a : Fin N, ∑ b : Fin N,
    kernelUnit N (a : ℕ) (b : ℕ) τ z * character N (a : ℕ) (b : ℕ) (r : ℕ) (s : ℕ)

lemma analyticAt_unitSum (τ : ℍ) (r s : Fin N) : AnalyticAt ℂ (unitSum N τ r s) 0 := by
  have hi (a : Fin N) : AnalyticAt ℂ (fun z : ℂ => ∑ b : Fin N,
      kernelUnit N (a : ℕ) (b : ℕ) τ z * character N (a : ℕ) (b : ℕ) (r : ℕ) (s : ℕ)) 0 :=
    Finset.analyticAt_fun_sum _ fun b _ =>
      (analyticAt_kernelUnit N (a : ℕ) (b : ℕ) τ).mul analyticAt_const
  exact analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun a _ => hi a)

lemma unitSum_second (τ : ℍ) (r s : Fin N) :
    iteratedDeriv 2 (unitSum N τ r s) 0 = -(2 * (N : ℂ) ^ 2) *
      ∑ a : Fin N, ∑ b : Fin N, muValue N (a : ℕ) (b : ℕ) τ *
        character N (a : ℕ) (b : ℕ) (r : ℕ) (s : ℕ) := by
  change iteratedDeriv 2 (fun z => -(N : ℂ) * ∑ a : Fin N, ∑ b : Fin N,
    kernelUnit N (a : ℕ) (b : ℕ) τ z * character N (a : ℕ) (b : ℕ) (r : ℕ) (s : ℕ)) 0 = _
  have hinA (a : Fin N) : AnalyticAt ℂ (fun z : ℂ => ∑ b : Fin N,
      kernelUnit N (a : ℕ) (b : ℕ) τ z * character N (a : ℕ) (b : ℕ) (r : ℕ) (s : ℕ)) 0 :=
    Finset.analyticAt_fun_sum (Finset.univ : Finset (Fin N)) fun (b : Fin N) _ =>
      (analyticAt_kernelUnit N (a : ℕ) (b : ℕ) τ).mul analyticAt_const
  have hout : iteratedDeriv 2 (fun z : ℂ => ∑ a : Fin N, ∑ b : Fin N,
      kernelUnit N (a : ℕ) (b : ℕ) τ z * character N (a : ℕ) (b : ℕ) (r : ℕ) (s : ℕ)) 0 =
      ∑ a : Fin N, iteratedDeriv 2 (fun z : ℂ => ∑ b : Fin N,
        kernelUnit N (a : ℕ) (b : ℕ) τ z * character N (a : ℕ) (b : ℕ) (r : ℕ) (s : ℕ)) 0 :=
    iteratedDeriv_fun_sum (fun a _ => (hinA a).contDiffAt)
  rw [iteratedDeriv_const_mul_field, hout]
  have hin (a : Fin N) : iteratedDeriv 2 (fun z : ℂ => ∑ b : Fin N,
      kernelUnit N (a : ℕ) (b : ℕ) τ z * character N (a : ℕ) (b : ℕ) (r : ℕ) (s : ℕ)) 0 =
      ∑ b : Fin N, (2 * (N : ℂ) * muValue N (a : ℕ) (b : ℕ) τ) *
        character N (a : ℕ) (b : ℕ) (r : ℕ) (s : ℕ) := by
    have hi : iteratedDeriv 2 (fun z : ℂ => ∑ b : Fin N,
        kernelUnit N (a : ℕ) (b : ℕ) τ z * character N (a : ℕ) (b : ℕ) (r : ℕ) (s : ℕ)) 0 =
        ∑ b : Fin N, iteratedDeriv 2 (fun z : ℂ => kernelUnit N (a : ℕ) (b : ℕ) τ z *
          character N (a : ℕ) (b : ℕ) (r : ℕ) (s : ℕ)) 0 :=
      iteratedDeriv_fun_sum (f := fun (b : Fin N) (z : ℂ) => kernelUnit N (a : ℕ) (b : ℕ) τ z *
        character N (a : ℕ) (b : ℕ) (r : ℕ) (s : ℕ)) (fun b _ =>
        ((analyticAt_kernelUnit N (a : ℕ) (b : ℕ) τ).mul analyticAt_const).contDiffAt)
    rw [hi]
    apply Finset.sum_congr rfl
    intro b _
    rw [iteratedDeriv_mul_const_field, kernelUnit_second_finite]
  simp_rw [hin, mul_assoc, ← Finset.mul_sum]
  ring

private lemma ordinary_germ_of_punctured {f g : ℂ → ℂ}
    (hf : ContinuousAt f 0) (hg : ContinuousAt g 0)
    (he : f =ᶠ[𝓝[≠] (0 : ℂ)] g) : f =ᶠ[𝓝 (0 : ℂ)] g := by
  have h0 : f 0 = g 0 := tendsto_nhds_unique
    ((hf.tendsto.mono_left nhdsWithin_le_nhds).congr' he)
    (hg.tendsto.mono_left nhdsWithin_le_nhds)
  have hn := eventually_nhdsWithin_iff.mp he
  filter_upwards [hn] with z hz
  by_cases hzne : z = 0
  · simpa only [hzne] using h0
  · exact hz hzne

private lemma scaled_zero_free (τ : ℍ) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), H τ ((N : ℂ) * z) ≠ 0 := by
  have hn := (differentiable_unitDenominator N τ 0).continuousAt.eventually_ne
    (unitDenominator_zero_ne N τ)
  filter_upwards [hn.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hzne
  rw [dilated_factorization]
  exact mul_ne_zero hzne hz

private lemma dilated_translate_ne (τ : ℍ) (r s : Fin N) {z : ℂ}
    (hz : H τ ((N : ℂ) * z) ≠ 0) :
    dilated N τ (z + torsionPoint N (r : ℕ) (s : ℕ) τ) ≠ 0 := by
  let p := torsionPoint N (r : ℕ) (s : ℕ) τ
  have hp : (N : ℂ) * p = ((r : ℕ) : ℂ) * (τ : ℂ) + ((s : ℕ) : ℂ) := by
    have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    dsimp [p, torsionPoint]
    push_cast
    field_simp [hN]
  have hmem : (N : ℂ) * p ∈ (ThetaWeierstrass.periodPair τ).lattice := by
    rw [hp]
    exact (ThetaWeierstrass.mem_periodPair_lattice_iff τ _).mpr ⟨s, r, by push_cast; ring⟩
  intro h
  apply hz
  apply (ThetaWeierstrass.H_zero_iff_mem_lattice τ _).mpr
  have hm := (ThetaWeierstrass.H_zero_iff_mem_lattice τ _).mp h
  have hsub := (ThetaWeierstrass.periodPair τ).lattice.sub_mem hm hmem
  simpa only [dilated, p, mul_add, add_sub_cancel_right] using hsub

private lemma log_dilated_translate (τ : ℍ) (r s : Fin N) {z : ℂ}
    (hz : H τ ((N : ℂ) * z) ≠ 0) :
    ThetaWeierstrass.logDerivative (H τ) ((N : ℂ) *
      (z + torsionPoint N (r : ℕ) (s : ℕ) τ)) =
      ThetaWeierstrass.logDerivative (H τ) ((N : ℂ) * z) -
        2 * (Real.pi : ℂ) * Complex.I * ((r : ℕ) : ℂ) := by
  have hp : (N : ℂ) * (z + torsionPoint N (r : ℕ) (s : ℕ) τ) =
      (N : ℂ) * z + ((r : ℕ) : ℂ) * (τ : ℂ) + ((s : ℕ) : ℂ) := by
    have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    dsimp [torsionPoint]
    push_cast
    field_simp [hN]
    ring
  rw [hp]
  have hper : Periodic (ThetaWeierstrass.logDerivative (H τ)) (1 : ℂ) :=
    ThetaWeierstrass.H_logDerivative_add_one τ
  have hs := hper.nat_mul (s : ℕ) ((N : ℂ) * z + ((r : ℕ) : ℂ) * (τ : ℂ))
  simp only [mul_one] at hs
  rw [hs]
  exact H_log_add_nat_tau τ ((N : ℂ) * z) hz (r : ℕ)

private lemma unitSum_germ_raw (τ : ℍ) (r s : Fin N) :
    unitSum N τ r s =ᶠ[𝓝[≠] (0 : ℂ)] fun z => z *
      ((N : ℂ) * ThetaWeierstrass.logDerivative (H τ) ((N : ℂ) * z) -
        2 * (Real.pi : ℂ) * Complex.I * (N : ℂ) * ((r : ℕ) : ℂ) -
        (N : ℂ) ^ 2 * ThetaWeierstrass.logDerivative (H τ)
          (z + torsionPoint N (r : ℕ) (s : ℕ) τ)) := by
  have hE : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ∀ a b : Fin N,
      z * kernel N (a : ℕ) (b : ℕ) τ z = kernelUnit N (a : ℕ) (b : ℕ) τ z :=
    Filter.eventually_all.mpr fun a => Filter.eventually_all.mpr fun b => kernelUnit_germ N _ _ τ
  filter_upwards [hE, scaled_zero_free N τ] with z hEz hz
  have hc := global_kernel_comparison N τ (z + torsionPoint N (r : ℕ) (s : ℕ) τ)
    (dilated_translate_ne N τ r s hz)
  have hlog (w : ℂ) : Hder τ w / H τ w = ThetaWeierstrass.logDerivative (H τ) w := by
    rw [ThetaWeierstrass.logDerivative, deriv_H]
  simp only [hlog] at hc
  rw [log_dilated_translate N τ r s hz] at hc
  have hl : unitSum N τ r s z = z * (-(N : ℂ) * ∑ a : Fin N, ∑ b : Fin N,
      kernel N (a : ℕ) (b : ℕ) τ (z + torsionPoint N (r : ℕ) (s : ℕ) τ)) := by
    simp_rw [kernel_add_torsion]
    unfold unitSum
    simp only [mul_assoc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [← hEz a b]
    unfold character
    push_cast
    ring
  rw [hl, hc]
  ring

/-- The ordinary analytic expression on the right for a nonzero torsion row. -/
def rightGood (τ : ℍ) (r s : Fin N) (z : ℂ) : ℂ :=
  1 + (N : ℂ) * z * ThetaWeierstrass.unitLogDerivative (H τ) 0 ((N : ℂ) * z) -
    2 * (Real.pi : ℂ) * Complex.I * (N : ℂ) * ((r : ℕ) : ℂ) * z -
    (N : ℂ) ^ 2 * z * ThetaWeierstrass.logDerivative (H τ)
      (z + torsionPoint N (r : ℕ) (s : ℕ) τ)

lemma analyticAt_rightGood (τ : ℍ) (r s : Fin N)
    (hg : ¬ ((N : ℤ) ∣ ((r : ℕ) : ℤ) ∧ (N : ℤ) ∣ ((s : ℕ) : ℤ))) :
    AnalyticAt ℂ (rightGood N τ r s) 0 := by
  have hu := H_torsion_ne_zero N (NeZero.pos N) τ (r : ℕ) (s : ℕ) hg
  have hU0 : AnalyticAt ℂ (ThetaWeierstrass.unitLogDerivative (H τ) 0) ((N : ℂ) * 0) := by
    simpa only [mul_zero] using ThetaWeierstrass.analyticAt_unitLogDerivative_zero τ
  have hmul : AnalyticAt ℂ (fun z : ℂ => ThetaWeierstrass.unitLogDerivative (H τ) 0 ((N : ℂ) * z)) 0 :=
    hU0.comp (by fun_prop : AnalyticAt ℂ (fun z : ℂ => (N : ℂ) * z) 0)
  have hL0 : AnalyticAt ℂ (ThetaWeierstrass.logDerivative (H τ))
      (0 + torsionPoint N (r : ℕ) (s : ℕ) τ) := by
    simpa only [zero_add] using ThetaWeierstrass.analyticAt_logDerivative (differentiable_H τ) hu
  have hshift : AnalyticAt ℂ (fun z : ℂ => ThetaWeierstrass.logDerivative (H τ)
      (z + torsionPoint N (r : ℕ) (s : ℕ) τ)) 0 :=
    hL0.comp (f := fun z : ℂ => z + torsionPoint N (r : ℕ) (s : ℕ) τ) (x := (0 : ℂ))
      (by fun_prop : AnalyticAt ℂ (fun z : ℂ => z + torsionPoint N (r : ℕ) (s : ℕ) τ) 0)
  exact (((analyticAt_const.add ((analyticAt_const.mul analyticAt_id).mul hmul)).sub
    (analyticAt_const.mul analyticAt_id)).sub ((analyticAt_const.mul analyticAt_id).mul hshift))

/-- Ordinary analytic germ equality, so it can be differentiated twice at zero. -/
lemma unitSum_germ_good (τ : ℍ) (r s : Fin N)
    (hg : ¬ ((N : ℤ) ∣ ((r : ℕ) : ℤ) ∧ (N : ℤ) ∣ ((s : ℕ) : ℤ))) :
    unitSum N τ r s =ᶠ[𝓝 (0 : ℂ)] rightGood N τ r s := by
  apply ordinary_germ_of_punctured (analyticAt_unitSum N τ r s).continuousAt
    (analyticAt_rightGood N τ r s hg).continuousAt
  have hsplit := (dilate_tendsto_zero N).eventually (ThetaWeierstrass.H_logDerivative_laurent τ)
  filter_upwards [unitSum_germ_raw N τ r s, hsplit, self_mem_nhdsWithin] with z hz hs hzne
  rw [hz]
  change deriv (H τ) ((N : ℂ) * z) / H τ ((N : ℂ) * z) = _ at hs
  change z * ((N : ℂ) * (deriv (H τ) ((N : ℂ) * z) / H τ ((N : ℂ) * z)) - _ - _) = _
  rw [hs]
  unfold rightGood
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hz0 : z ≠ 0 := hzne
  field_simp [hN, hz0] <;> ring

private lemma second_z_mul {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    iteratedDeriv 2 (fun z : ℂ => z * f z) 0 = 2 * deriv f 0 := by
  rw [iteratedDeriv_fun_mul (by fun_prop) hf.contDiffAt]
  simp only [Finset.sum_range_succ, iteratedDeriv_fun_id, iteratedDeriv_zero, iteratedDeriv_one]
  norm_num

lemma rightGood_second (τ : ℍ) (r s : Fin N)
    (hg : ¬ ((N : ℤ) ∣ ((r : ℕ) : ℤ) ∧ (N : ℤ) ∣ ((s : ℕ) : ℤ))) :
    iteratedDeriv 2 (rightGood N τ r s) 0 =
      2 * (N : ℂ) ^ 2 * xValue N (r : ℕ) (s : ℕ) τ := by
  let p := torsionPoint N (r : ℕ) (s : ℕ) τ
  let U := ThetaWeierstrass.unitLogDerivative (H τ) 0
  let L := ThetaWeierstrass.logDerivative (H τ)
  have hU := ThetaWeierstrass.analyticAt_unitLogDerivative_zero τ
  have hp := H_torsion_ne_zero N (NeZero.pos N) τ (r : ℕ) (s : ℕ) hg
  have hL := ThetaWeierstrass.analyticAt_logDerivative (differentiable_H τ) hp
  have hU0 : AnalyticAt ℂ U ((N : ℂ) * 0) := by simpa only [mul_zero] using hU
  have hmA : AnalyticAt ℂ (fun z : ℂ => U ((N : ℂ) * z)) 0 :=
    hU0.comp (by fun_prop : AnalyticAt ℂ (fun z : ℂ => (N : ℂ) * z) 0)
  have hL0 : AnalyticAt ℂ L (0 + p) := by simpa only [zero_add] using hL
  have hsA : AnalyticAt ℂ (fun z : ℂ => L (z + p)) 0 :=
    hL0.comp (f := fun z : ℂ => z + p) (x := (0 : ℂ))
      (by fun_prop : AnalyticAt ℂ (fun z : ℂ => z + p) 0)
  have hmD : deriv (fun z : ℂ => U ((N : ℂ) * z)) 0 =
      ThetaWeierstrass.finitePart τ * (N : ℂ) := by
    have hd := hU0.differentiableAt.hasDerivAt.comp
      (0 : ℂ) ((hasDerivAt_id' (0 : ℂ)).const_mul (N : ℂ))
    simpa only [Function.comp_def, mul_zero, mul_one, ThetaWeierstrass.finitePart, U] using hd.deriv
  have hsD : deriv (fun z : ℂ => L (z + p)) 0 = deriv L p := by
    simpa only [zero_add] using
      (HasDerivAt.comp_add_const (0 : ℂ) p hL0.differentiableAt.hasDerivAt).deriv
  have he : rightGood N τ r s = fun z : ℂ =>
      1 + (N : ℂ) * (z * U ((N : ℂ) * z)) -
        (2 * (Real.pi : ℂ) * Complex.I * (N : ℂ) * ((r : ℕ) : ℂ)) * z -
        (N : ℂ) ^ 2 * (z * L (z + p)) := by
    funext z
    unfold rightGood
    ring
  have hA : AnalyticAt ℂ (fun z : ℂ => 1 + (N : ℂ) * (z * U ((N : ℂ) * z))) 0 :=
    analyticAt_const.add (analyticAt_const.mul (analyticAt_id.mul hmA))
  have hLin : AnalyticAt ℂ (fun z : ℂ =>
      (2 * (Real.pi : ℂ) * Complex.I * (N : ℂ) * ((r : ℕ) : ℂ)) * z) 0 := by fun_prop
  have hC : AnalyticAt ℂ (fun z : ℂ => (N : ℂ) ^ 2 * (z * L (z + p))) 0 :=
    analyticAt_const.mul (analyticAt_id.mul hsA)
  rw [he]
  change iteratedDeriv 2
    (((fun z : ℂ => 1 + (N : ℂ) * (z * U ((N : ℂ) * z))) -
      (fun z : ℂ => (2 * (Real.pi : ℂ) * Complex.I * (N : ℂ) * ((r : ℕ) : ℂ)) * z)) -
      (fun z : ℂ => (N : ℂ) ^ 2 * (z * L (z + p)))) 0 = _
  have hlin2 : iteratedDeriv 2 (fun z : ℂ =>
      (2 * (Real.pi : ℂ) * Complex.I * (N : ℂ) * ((r : ℕ) : ℂ)) * z) 0 = 0 := by
    rw [iteratedDeriv_const_mul_field]
    norm_num [iteratedDeriv_fun_id]
  rw [iteratedDeriv_sub (hA.sub hLin).contDiffAt hC.contDiffAt,
    iteratedDeriv_sub hA.contDiffAt hLin.contDiffAt, hlin2,
    iteratedDeriv_const_add (by decide : 0 < (2 : ℕ)) (1 : ℂ)]
  simp only [iteratedDeriv_const_mul_field, iteratedDeriv_fun_id]
  norm_num
  rw [second_z_mul hmA, second_z_mul hsA, hmD, hsD]
  rw [xValue_of_good N _ _ τ hg]
  have hx := ThetaWeierstrass.weierstrassP_eq_neg_deriv_logDerivative τ p
    (fun h => hp ((ThetaWeierstrass.H_zero_iff_mem_lattice τ p).mpr h))
  change (ThetaWeierstrass.periodPair τ).weierstrassP p =
    -deriv L p + ThetaWeierstrass.finitePart τ at hx
  change _ = 2 * (N : ℂ) ^ 2 * (ThetaWeierstrass.periodPair τ).weierstrassP p
  rw [hx]
  ring

/-- Forward weight-two transform at every nonzero finite torsion row. -/
theorem x_fourier_finite_good (τ : ℍ) (r s : Fin N)
    (hg : ¬ ((N : ℤ) ∣ ((r : ℕ) : ℤ) ∧ (N : ℤ) ∣ ((s : ℕ) : ℤ))) :
    xValue N (r : ℕ) (s : ℕ) τ =
      -∑ a : Fin N, ∑ b : Fin N, muValue N (a : ℕ) (b : ℕ) τ *
        character N (a : ℕ) (b : ℕ) (r : ℕ) (s : ℕ) := by
  have hd := (unitSum_germ_good N τ r s hg).iteratedDeriv_eq 2
  rw [unitSum_second, rightGood_second N τ r s hg] at hd
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  apply mul_left_cancel₀ (mul_ne_zero two_ne_zero (pow_ne_zero 2 hN))
  linear_combination -hd

end ZInQ.Contrib.HeckePrimeRationality.TorsionMuFourier
