import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionMuFourierKernel

/-!
# Actual quadratic Laurent expansion of the torsion kernel

The first three coefficients are derived from the analytic kernel unit. The
remainder is analytic and the punctured domain is genuinely zero-free.
-/

noncomputable section
set_option autoImplicit false
open Complex UpperHalfPlane Filter
open scoped Topology

namespace ZInQ.Contrib.HeckePrimeRationality.TorsionMuFourierKernel

open CompletedTheta TorsionFourierComparison TorsionWeierstrassData

variable (N : ℕ) [NeZero N]

/-- The zero label gives an identically zero unit as well as an identically zero kernel. -/
lemma kernelUnit_zero_row (τ : ℍ) : kernelUnit N 0 0 τ = 0 := by
  funext z
  simp [kernelUnit, kernelNumerator, torsionPoint, H_zero]

/-- Uniform second coefficient for all finite labels, with the actual zero convention. -/
lemma kernelUnit_second_finite (a b : Fin N) (τ : ℍ) :
    iteratedDeriv 2 (kernelUnit N (a : ℕ) (b : ℕ) τ) 0 =
      2 * (N : ℂ) * muValue N (a : ℕ) (b : ℕ) τ := by
  by_cases hg : ¬ ((N : ℤ) ∣ ((a : ℕ) : ℤ) ∧ (N : ℤ) ∣ ((b : ℕ) : ℤ))
  · exact kernelUnit_second_zero N (a : ℕ) (b : ℕ) τ hg
  · have hab : a = 0 ∧ b = 0 := by
      have h := (finite_good_iff N a b).not.mp hg
      tauto
    obtain ⟨rfl, rfl⟩ := hab
    simp only [Fin.val_zero, Nat.cast_zero, kernelUnit_zero_row, muValue_zero, mul_zero]
    change iteratedDeriv 2 (fun _ : ℂ => (0 : ℂ)) 0 = 0
    exact iteratedDeriv_fun_const_zero

/-- The actual Laurent expansion through its linear term: residue 1/N,
constant λ, linear coefficient Nμ, and an analytic quadratic remainder. -/
theorem kernel_laurent_second (a b : ℤ) (τ : ℍ)
    (hg : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b)) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧
      ∀ᶠ z in 𝓝[≠] (0 : ℂ), H τ ((N : ℂ) * z) ≠ 0 ∧
        TorsionFourierKernel.kernel N a b τ z = 1 / ((N : ℂ) * z) + lambdaValue N a b τ +
          (N : ℂ) * muValue N a b τ * z + z ^ 2 * R z := by
  obtain ⟨R, hR, he⟩ := (analyticAt_kernelUnit N a b τ).exists_eventuallyEq_sum_add_pow_mul 3
  have hTaylor : ∀ᶠ z in 𝓝 (0 : ℂ), kernelUnit N a b τ z =
      (N : ℂ)⁻¹ + lambdaValue N a b τ * z + (N : ℂ) * muValue N a b τ * z ^ 2 + z ^ 3 * R z := by
    filter_upwards [he] with z hz
    simp only [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one,
      kernelUnit_zero N a b τ hg, kernelUnit_deriv_zero N a b τ hg,
      kernelUnit_second_zero N a b τ hg, smul_eq_mul] at hz
    norm_num at hz
    convert hz using 1 <;> ring
  have hn := (differentiable_unitDenominator N τ 0).continuousAt.eventually_ne
    (unitDenominator_zero_ne N τ)
  refine ⟨R, hR, ?_⟩
  filter_upwards [hTaylor.filter_mono nhdsWithin_le_nhds,
    hn.filter_mono nhdsWithin_le_nhds, kernelUnit_germ N a b τ, self_mem_nhdsWithin] with z hz hdz hez hzne
  have hz0 : z ≠ 0 := hzne
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  refine ⟨?_, ?_⟩
  · rw [dilated_factorization]
    exact mul_ne_zero hz0 hdz
  · calc
      TorsionFourierKernel.kernel N a b τ z = kernelUnit N a b τ z / z := by
        apply (eq_div_iff hz0).mpr
        simpa only [mul_comm] using hez
      _ = _ := by
        rw [hz]
        field_simp [hz0, hN] <;> ring

end ZInQ.Contrib.HeckePrimeRationality.TorsionMuFourierKernel
