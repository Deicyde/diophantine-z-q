import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.QExpansion.Basic
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Cusps.Basic
import Mathlib.RingTheory.PowerSeries.Expand

/-!
# Period conversion for Γ₁ modular forms

The width-N expansion of a Γ₁(N) form is the expansion of its width-one
series by the factor N. Both coefficient statements follow from actual
convergence of the width-one series and uniqueness at the positive width N.
-/

noncomputable section

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.AllLevelPeriodConversion

variable (N : ℕ) [NeZero N]

lemma qParam_one_eq_pow (τ : ℍ) :
    Function.Periodic.qParam 1 (τ : ℂ) =
      Function.Periodic.qParam (N : ℝ) (τ : ℂ) ^ N := by
  rw [Function.Periodic.qParam, Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  field_simp [hN0]

lemma width_mem_strictPeriods :
    (N : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods := by
  simp only [CongruenceSubgroup.strictPeriods_Gamma1]
  exact AddSubgroup.mem_zmultiples_iff.mpr ⟨(N : ℤ), by simp⟩

/-- The expanded width-one series actually converges to the original form. -/
lemma hasSum_expand {k : ℤ} (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (τ : ℍ) :
    HasSum (fun r : ℕ =>
      (PowerSeries.expand N (NeZero.ne N) (qExpansion 1 g)).coeff r *
        Function.Periodic.qParam (N : ℝ) τ ^ r) (g τ) := by
  have hΓ1 := TauCeti.one_mem_strictPeriods_Gamma1_map N
  have hg : HasSum (fun m : ℕ => (qExpansion 1 g).coeff m *
      Function.Periodic.qParam 1 τ ^ m) (g τ) := by
    simpa only [smul_eq_mul] using UpperHalfPlane.hasSum_qExpansion one_pos
      (SlashInvariantFormClass.periodic_comp_ofComplex g hΓ1)
      (ModularFormClass.holo g) (ModularFormClass.bdd_at_infty g) τ
  have hinj : Function.Injective (fun m : ℕ => N * m) := fun i j h =>
    Nat.eq_of_mul_eq_mul_left (NeZero.pos N) h
  apply (hinj.hasSum_iff (f := fun r : ℕ =>
    (PowerSeries.expand N (NeZero.ne N) (qExpansion 1 g)).coeff r *
      Function.Periodic.qParam (N : ℝ) τ ^ r) ?_).mp
  · change HasSum (fun m : ℕ =>
      (PowerSeries.expand N (NeZero.ne N) (qExpansion 1 g)).coeff (N * m) *
        Function.Periodic.qParam (N : ℝ) τ ^ (N * m)) (g τ)
    simpa only [PowerSeries.coeff_expand_mul, pow_mul, ← qParam_one_eq_pow N τ] using hg
  · intro r hr
    have hnd : ¬ N ∣ r := by
      rintro ⟨m, hm⟩
      exact hr ⟨m, hm.symm⟩
    rw [PowerSeries.coeff_expand_of_not_dvd N (NeZero.ne N) _ hnd, zero_mul]

/-- The complete actual period-N expansion identity. -/
theorem qExpansion_eq_expand {k : ℤ}
    (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    qExpansion (N : ℝ) g = PowerSeries.expand N (NeZero.ne N) (qExpansion 1 g) := by
  have hh : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have han := ModularFormClass.analyticAt_cuspFunction_zero g hh (width_mem_strictPeriods N)
  ext r
  symm
  exact TauCeti.UpperHalfPlane.qExpansion_coeff_unique
    (c := fun n => (PowerSeries.expand N (NeZero.ne N) (qExpansion 1 g)).coeff n)
    hh han (fun τ => by simpa only [smul_eq_mul] using hasSum_expand N g τ) r

/-- The coefficient at index N*m in period N is the coefficient at index m in period one. -/
theorem coeff_mul {k : ℤ} (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (m : ℕ) :
    (qExpansion (N : ℝ) g).coeff (N * m) = (qExpansion 1 g).coeff m := by
  rw [qExpansion_eq_expand, PowerSeries.coeff_expand_mul]

/-- All indices outside the multiples of N have zero period-N coefficients. -/
theorem coeff_eq_zero_of_not_dvd {k : ℤ}
    (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (r : ℕ) (hr : ¬ N ∣ r) :
    (qExpansion (N : ℝ) g).coeff r = 0 := by
  rw [qExpansion_eq_expand, PowerSeries.coeff_expand_of_not_dvd N (NeZero.ne N) _ hr]

/-- Rationality of the actual two expansions is equivalent. -/
theorem rational_coefficients_iff {k : ℤ}
    (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (∀ r : ℕ, ∃ q : ℚ, (qExpansion (N : ℝ) g).coeff r = q) ↔
      (∀ m : ℕ, ∃ q : ℚ, (qExpansion 1 g).coeff m = q) := by
  constructor
  · intro hg m
    simpa only [coeff_mul N g m] using hg (N * m)
  · intro hg r
    by_cases hr : N ∣ r
    · obtain ⟨m, rfl⟩ := hr
      simpa only [coeff_mul N g m] using hg m
    · exact ⟨0, by rw [coeff_eq_zero_of_not_dvd N g r hr]; norm_cast⟩

/-- Coefficients belong to any chosen rational intermediate field at both periods equivalently. -/
theorem coefficient_field_iff {k : ℤ}
    (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (K : IntermediateField ℚ ℂ) :
    (∀ r : ℕ, (qExpansion (N : ℝ) g).coeff r ∈ K) ↔
      (∀ m : ℕ, (qExpansion 1 g).coeff m ∈ K) := by
  constructor
  · intro hg m
    simpa only [coeff_mul N g m] using hg (N * m)
  · intro hg r
    by_cases hr : N ∣ r
    · obtain ⟨m, rfl⟩ := hr
      simpa only [coeff_mul N g m] using hg m
    · rw [coeff_eq_zero_of_not_dvd N g r hr]
      exact K.zero_mem

end ZInQ.Contrib.HeckePrimeRationality.AllLevelPeriodConversion
