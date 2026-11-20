import ZInQKernel.Contrib.OneProof.RC.O12Eisenstein.DivisorSum
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

/-! Weight two at infinity for a character pair (tex 9862–9864).
The analytic estimates and identifications of series are on-the-spot (c). -/

noncomputable section

namespace ZInQ.Manuscript.RC.EisForm

open O12Eisenstein UpperHalfPlane Function
open scoped Manifold

variable {m₁ m₂ : ℕ}

/-- The factor-pair convention agrees with the divisor-indexed formula. -/
theorem divisorCoeff_eq_sum_divisors {K : Type*} [CommRing K]
    (a : DirichletCharacter K m₁) (b : DirichletCharacter K m₂) (n : ℕ) :
    divisorCoeff a b n = ∑ d ∈ n.divisors,
      a ((n / d : ℕ) : ZMod m₁) * (b (d : ZMod m₂) * (d : K)) := by
  unfold divisorCoeff
  rw [← Nat.map_swap_divisorsAntidiagonal, Finset.sum_map]
  exact
    (Nat.sum_divisorsAntidiagonal (n := n)
      (fun d u : ℕ => a (u : ZMod m₁) * (b (d : ZMod m₂) * (d : K))))

theorem norm_divisorCoeff_le (a : DirichletCharacter ℂ m₁)
    (b : DirichletCharacter ℂ m₂) (n : ℕ) :
    ‖divisorCoeff a b n‖ ≤ (n : ℝ) ^ 2 := by
  classical
  rw [divisorCoeff_eq_sum_divisors]
  calc
    _ ≤ ∑ d ∈ n.divisors, ‖a ((n / d : ℕ) : ZMod m₁) * (b (d : ZMod m₂) * (d : ℂ))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _d ∈ n.divisors, (n : ℝ) := Finset.sum_le_sum fun d hd => by
      simp only [norm_mul, Complex.norm_natCast]
      calc
        _ ≤ 1 * (1 * (d : ℝ)) := by
          gcongr <;> apply DirichletCharacter.norm_le_one
        _ ≤ (n : ℝ) := by
          simp only [one_mul]
          exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2)
            (Nat.dvd_of_mem_divisors hd)
    _ ≤ _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, pow_two]
      gcongr
      exact_mod_cast Nat.card_divisors_le_self n

/-- Prescribe the constant separately from the positive normalized divisor sums. -/
def seriesCoeff (a : DirichletCharacter ℂ m₁) (b : DirichletCharacter ℂ m₂)
    (C : ℂ) (n : ℕ) : ℂ :=
  if n = 0 then C else divisorCoeff a b n

/-- The normalized analytic series on the upper half plane. -/
def series (a : DirichletCharacter ℂ m₁) (b : DirichletCharacter ℂ m₂)
    (C : ℂ) (z : ℍ) : ℂ :=
  FormalMultilinearSeries.ofScalarsSum (seriesCoeff a b C) (Periodic.qParam 1 z)

private theorem summable_seriesCoeff (a : DirichletCharacter ℂ m₁)
    (b : DirichletCharacter ℂ m₂) (C : ℂ) {r : ℂ} (hr : ‖r‖ < 1) :
    Summable fun n : ℕ => seriesCoeff a b C n * r ^ n := by
  apply (summable_nat_add_iff (k := 1)).mp
  apply Summable.of_norm_bounded
    ((summable_norm_pow_mul_geometric_of_norm_lt_one 2 hr).comp_injective (i := fun n : ℕ => n + 1)
      (fun x y h => Nat.add_right_cancel h))
  intro n
  simp only [Function.comp_apply, seriesCoeff, Nat.add_one_ne_zero, ite_false, norm_mul, norm_pow,
    Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_right (norm_divisorCoeff_le a b (n + 1)) (by positivity)

private theorem series_radius (a : DirichletCharacter ℂ m₁)
    (b : DirichletCharacter ℂ m₂) (C : ℂ) :
    1 ≤ (FormalMultilinearSeries.ofScalars ℂ (seriesCoeff a b C)).radius := by
  refine le_of_forall_lt_imp_le_of_dense fun r hr => ?_
  lift r to NNReal using hr.ne_top
  apply FormalMultilinearSeries.le_radius_of_summable
  have hnorm (n : ℕ) : ‖FormalMultilinearSeries.ofScalars ℂ (seriesCoeff a b C) n‖ =
      ‖seriesCoeff a b C n‖ := by
    rw [FormalMultilinearSeries.ofScalars,
      ← (ContinuousMultilinearMap.piFieldEquiv ℂ (Fin n) ℂ).symm.norm_map]
    simp
  simp only [hnorm]
  have h := (summable_seriesCoeff a b C (r := (r : ℝ)) (by simpa using hr)).norm
  simpa only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg r.coe_nonneg]
    using h

theorem hasSum_series (a : DirichletCharacter ℂ m₁)
    (b : DirichletCharacter ℂ m₂) (C : ℂ) (z : ℍ) :
    HasSum (fun n : ℕ => seriesCoeff a b C n • Periodic.qParam 1 z ^ n) (series a b C z) := by
  simpa only [series, FormalMultilinearSeries.ofScalars_sum_eq, smul_eq_mul] using
    (summable_seriesCoeff a b C (Periodic.norm_qParam_lt_one one_pos z.im_pos)).hasSum

theorem series_holo (a : DirichletCharacter ℂ m₁)
    (b : DirichletCharacter ℂ m₂) (C : ℂ) : MDiff (series a b C) := by
  intro z
  rw [UpperHalfPlane.mdifferentiableAt_iff]
  let p := FormalMultilinearSeries.ofScalars ℂ (seriesCoeff a b C)
  have hr : 0 < p.radius := zero_lt_one.trans_le (series_radius a b C)
  have hmem : Periodic.qParam 1 z ∈ Metric.eball (0 : ℂ) p.radius := by
    apply Metric.eball_subset_eball (series_radius a b C)
    rw [← ENNReal.coe_one, Metric.eball_coe, NNReal.coe_one, mem_ball_zero_iff]
    exact Periodic.norm_qParam_lt_one one_pos z.im_pos
  have hd := ((p.hasFPowerSeriesOnBall hr).analyticAt_of_mem hmem).differentiableAt.comp
    (z : ℂ) ((Periodic.differentiable_qParam (h := 1)) z)
  apply hd.congr_of_eventuallyEq
  filter_upwards [UpperHalfPlane.eventuallyEq_coe_comp_ofComplex z.im_pos] with w hw
  change p.sum (Periodic.qParam 1 (UpperHalfPlane.ofComplex w : ℂ)) =
    p.sum (Periodic.qParam 1 w)
  rw [show (UpperHalfPlane.ofComplex w : ℂ) = w from hw]

theorem series_periodic (a : DirichletCharacter ℂ m₁)
    (b : DirichletCharacter ℂ m₂) (C : ℂ) :
    Periodic (series a b C ∘ UpperHalfPlane.ofComplex) 1 := by
  apply UpperHalfPlane.periodic_comp_ofComplex
  intro z
  simp only [series, UpperHalfPlane.coe_vadd, Complex.ofReal_one, Periodic.qParam, div_one]
  congr 1
  rw [mul_add, mul_one, Complex.exp_add, Complex.exp_two_pi_mul_I, one_mul]

theorem series_boundedAtInfty (a : DirichletCharacter ℂ m₁)
    (b : DirichletCharacter ℂ m₂) (C : ℂ) : IsBoundedAtImInfty (series a b C) :=
  isBoundedAtImInfty_of_hasSum_qExpansion one_pos (hasSum_series a b C)

private theorem coeff_of_hasSum {h : ℝ} {f : ℍ → ℂ} {b : ℕ → ℂ} (hpos : 0 < h)
    (hp : Periodic (f ∘ UpperHalfPlane.ofComplex) h) (hh : MDiff f) (hb : IsBoundedAtImInfty f)
    (hs : ∀ z : ℍ, HasSum (fun m : ℕ => b m • Periodic.qParam h z ^ m) (f z)) (n : ℕ) :
    (qExpansion h f).coeff n = b n := by
  let f₀ : ContinuousMap ℍ ℂ := ⟨f, hh.continuous⟩
  exact (UpperHalfPlane.qExpansion_coeff_unique f₀ (c := b) hpos
    (UpperHalfPlane.analyticAt_cuspFunction_zero hpos hp hh hb) hs n).symm

theorem qExpansion_series (a : DirichletCharacter ℂ m₁)
    (b : DirichletCharacter ℂ m₂) (C : ℂ) (n : ℕ) :
    (qExpansion 1 (series a b C)).coeff n = seriesCoeff a b C n :=
  coeff_of_hasSum one_pos (series_periodic a b C) (series_holo a b C)
    (series_boundedAtInfty a b C) (hasSum_series a b C) n


end ZInQ.Manuscript.RC.EisForm
