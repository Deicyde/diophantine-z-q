import TwistedLValueV005

/-!
# Critical rational Mellin periods of primitive twists

The critical values at one and two are finite character-weighted averages of
actual convergent rationally translated Mellin periods. The powers of two pi,
the inverse modulus, and the negative Fourier argument are kept explicit.
No critical-period nonvanishing or injectivity is assumed or concluded.
-/

noncomputable section

open Complex MeasureTheory Filter Matrix.SpecialLinearGroup CongruenceSubgroup
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm Topology Classical

namespace CriticalTwists

variable {N M L : ℕ} [NeZero N] [NeZero M] [NeZero L] {k : ℤ}

/-- The actual rationally translated Mellin integrand. -/
def rationalMellinIntegrand (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (a : ZMod M) (t : ℝ) : ℂ := f (((a.val : ℝ) / M) +ᵥ ofComplex (I * t))

/-- Translation and cuspidality derive convergence at every complex exponent. -/
theorem rationalMellin_convergent (hk : 0 < k) (s : ℂ)
    (hNL : N * M ∣ L) (hML : M * M ∣ L)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (a : ZMod M) :
    MellinConvergent (rationalMellinIntegrand f a) s := by
  have h := cuspMellin_convergent hk (horizontalTranslate hNL hML f a) s
  change MellinConvergent
    (fun t : ℝ => f (((a.val : ℝ) / M) +ᵥ ofComplex (I * t))) s
  simpa only [horizontalTranslate_apply] using h

/-- The translated completed L-value is its actual rational Mellin period. -/
theorem translated_completedL_eq_rationalMellin (hk : 0 < k) (s : ℂ)
    (hNL : N * M ∣ L) (hML : M * M ∣ L)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (a : ZMod M) :
    ModularForm.Λ hk (horizontalTranslate hNL hML f a) s =
      mellin (rationalMellinIntegrand f a) s := by
  rw [CuspForm.Λ_eq_mellin]
  congr 1
  funext t
  exact horizontalTranslate_apply hNL hML f a (ofComplex (I * t))

/-- A primitive twist is the exact Gauss-weighted rational Mellin average at every exponent. -/
theorem primitive_twist_L_eq_rationalMellin (hk : 0 < k) (s : ℂ)
    (ψ : DirichletCharacter ℂ M) (hψ : ψ.IsPrimitive)
    (hNL : N * M ∣ L) (hML : M * M ∣ L)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ModularForm.L hk (CuspForm.twist ψ hNL hML f) s =
      (2 / Gammaℂ s) * (M : ℂ)⁻¹ * gaussSum ψ ZMod.stdAddChar *
        ∑ a : ZMod M, ψ⁻¹ (-a) * mellin (rationalMellinIntegrand f a) s := by
  rw [primitive_twist_L_gauss_average hk s ψ hψ hNL hML f]
  simp only [ModularForm.L, translated_completedL_eq_rationalMellin, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- The weight-two critical value uses the unweighted actual rational period. -/
theorem primitive_twist_L_one_periods (hk : 0 < k)
    (ψ : DirichletCharacter ℂ M) (hψ : ψ.IsPrimitive)
    (hNL : N * M ∣ L) (hML : M * M ∣ L)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ModularForm.L hk (CuspForm.twist ψ hNL hML f) 1 =
      (2 * Real.pi : ℂ) * (M : ℂ)⁻¹ * gaussSum ψ ZMod.stdAddChar *
        ∑ a : ZMod M, ψ⁻¹ (-a) *
          ∫ t : ℝ in Set.Ioi 0, rationalMellinIntegrand f a t := by
  rw [primitive_twist_L_gauss_average hk 1 ψ hψ hNL hML f]
  simp only [L_one_eq_integral, horizontalTranslate_apply, rationalMellinIntegrand,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- The weight-three critical value uses the actual first-moment rational period. -/
theorem primitive_twist_L_two_periods (hk : 0 < k)
    (ψ : DirichletCharacter ℂ M) (hψ : ψ.IsPrimitive)
    (hNL : N * M ∣ L) (hML : M * M ∣ L)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ModularForm.L hk (CuspForm.twist ψ hNL hML f) 2 =
      (2 * Real.pi : ℂ) ^ 2 * (M : ℂ)⁻¹ * gaussSum ψ ZMod.stdAddChar *
        ∑ a : ZMod M, ψ⁻¹ (-a) *
          ∫ t : ℝ in Set.Ioi 0, (t : ℂ) * rationalMellinIntegrand f a t := by
  rw [primitive_twist_L_gauss_average hk 2 ψ hψ hNL hML f]
  simp only [L_two_eq_integral, horizontalTranslate_apply, rationalMellinIntegrand,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- The critical factor at one is actually nonzero; only the period average can vanish. -/
theorem primitive_critical_one_factor_ne_zero
    (ψ : DirichletCharacter ℂ M) (hψ : ψ.IsPrimitive) :
    (2 * Real.pi : ℂ) * (M : ℂ)⁻¹ * gaussSum ψ ZMod.stdAddChar ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    (inv_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne M)))) (primitive_gaussSum_ne_zero ψ hψ)

/-- The critical factor at two is actually nonzero; only the first-moment average can vanish. -/
theorem primitive_critical_two_factor_ne_zero
    (ψ : DirichletCharacter ℂ M) (hψ : ψ.IsPrimitive) :
    (2 * Real.pi : ℂ) ^ 2 * (M : ℂ)⁻¹ * gaussSum ψ ZMod.stdAddChar ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (mul_ne_zero two_ne_zero
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
    (inv_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne M)))) (primitive_gaussSum_ne_zero ψ hψ)

end CriticalTwists
