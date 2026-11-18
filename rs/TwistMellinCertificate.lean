import rs.CriticalTwistIntegrals

/-!
# A concrete all-complex-exponent twist Mellin certificate

The actual cusp twist and every rational translate live at the constructed
common level. The integral uses the genuine positive-axis Mellin measure and
kernel, with all cusp convergence supplied. Neither the sum nor a critical
L-value is asserted nonzero; the Eisenstein-product detector remains separate.
-/

noncomputable section
set_option autoImplicit false

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane
open Complex MeasureTheory Set ZMod HeckeRing.GL2
open scoped MatrixGroups ModularForm Pointwise

namespace ZInQ.Contrib.HeckePrimeRationality.RankinSupplier

/-- The actual common Gamma-one level has strict cusp width exactly one. -/
theorem common_level_strictWidth (N M : ℕ) :
    ((Gamma1 (N * M ^ 2)).map (mapGL ℝ)).strictWidthInfty = 1 := by
  exact Subgroup.strictWidthInfty_eq_one_of_T_mem
    (by simpa only [zpow_one] using T_zpow_mem_Gamma1 (N * M ^ 2) (1 : ℤ))

/-- The completed L-value of each actual common-level translate is its convergent rational-slash Mellin integral. -/
theorem translated_completedL_eq_mellin {N M : ℕ} [NeZero N] [NeZero M] {k : ℤ}
    (hk : 0 < k) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (a : ZMod M) (s : ℂ) :
    ModularForm.Λ hk (translatedCusp f a) s =
      mellin (imaginaryRestriction
        (⇑f ∣[k] GeneralLinearGroup.map (algebraMap ℚ ℝ) (shiftMatrix M a))) s := by
  rw [← (cusp_hasMellin hk (translatedCusp f a) s).2, translatedCusp_coe]

/-- The actual twist Mellin transform is a finite Dirichlet-Fourier combination of actual positive-rational translate Mellin transforms. -/
theorem actual_twist_hasMellin_translates {N M : ℕ} [NeZero N] [NeZero M] {k : ℤ}
    (hk : 0 < k) (ψ : DirichletCharacter ℂ M)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (s : ℂ) :
    HasMellin (imaginaryRestriction ⇑(CuspForm.twist ψ
      (original_mul_modulus_dvd_common N M) (modulus_sq_dvd_common N M) f)) s
      ((M : ℂ)⁻¹ * ∑ a : ZMod M, 𝓕 ψ a * mellin (imaginaryRestriction
        (⇑f ∣[k] GeneralLinearGroup.map (algebraMap ℚ ℝ) (shiftMatrix M a))) s) := by
  have h := actual_twist_hasMellin hk ψ f s
  simpa only [translated_completedL_eq_mellin] using h

/-- For a primitive Dirichlet character, the exact Gauss normalization has inverse-character argument -a. -/
theorem primitive_twist_hasMellin_translates {N M : ℕ} [NeZero N] [NeZero M] {k : ℤ}
    (hk : 0 < k) {ψ : DirichletCharacter ℂ M} (hψ : ψ.IsPrimitive)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (s : ℂ) :
    HasMellin (imaginaryRestriction ⇑(CuspForm.twist ψ
      (original_mul_modulus_dvd_common N M) (modulus_sq_dvd_common N M) f)) s
      ((gaussSum ψ ZMod.stdAddChar / (M : ℂ)) *
        ∑ a : ZMod M, ψ⁻¹ (-a) * mellin (imaginaryRestriction
          (⇑f ∣[k] GeneralLinearGroup.map (algebraMap ℚ ℝ) (shiftMatrix M a))) s) := by
  have h := primitive_twist_hasMellin hk hψ f s
  simpa only [translated_completedL_eq_mellin] using h

/-- The requested actual newform twist supplier, with a constructed level, literal width,
positive rational matrices, and absolute integrability for every complex exponent. -/
theorem newform_twist_mellin_certificate {N M : ℕ} [NeZero N] [NeZero M]
    (j : ℕ) (hj : j = 2 ∨ j = 3) (F : Newform N (j : ℤ))
    (ψ : DirichletCharacter ℂ M) (s : ℂ) :
    ((Gamma1 (N * M ^ 2)).map (mapGL ℝ)).strictWidthInfty = 1 ∧
      (∀ a : ZMod M, 0 < (shiftMatrix M a : Matrix (Fin 2) (Fin 2) ℚ).det) ∧
      (∀ a : ZMod M, IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ (s - 1) * imaginaryRestriction
        (⇑F.toCuspForm ∣[(j : ℤ)]
          GeneralLinearGroup.map (algebraMap ℚ ℝ) (shiftMatrix M a)) t) (Ioi 0)) ∧
      HasMellin (imaginaryRestriction ⇑(CuspForm.twist ψ
        (original_mul_modulus_dvd_common N M) (modulus_sq_dvd_common N M) F.toCuspForm)) s
        ((M : ℂ)⁻¹ * ∑ a : ZMod M, 𝓕 ψ a * mellin (imaginaryRestriction
          (⇑F.toCuspForm ∣[(j : ℤ)]
            GeneralLinearGroup.map (algebraMap ℚ ℝ) (shiftMatrix M a))) s) :=
  ⟨common_level_strictWidth N M, shiftMatrix_det_pos M,
    fun a ↦ translated_kernel_integrable (critical_weight_pos j hj) F.toCuspForm a s,
    actual_twist_hasMellin_translates (critical_weight_pos j hj) ψ F.toCuspForm s⟩

end ZInQ.Contrib.HeckePrimeRationality.RankinSupplier
