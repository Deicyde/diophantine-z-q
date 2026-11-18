import rs.TwistMellin

/-!
# Critical twisted L-values as convergent finite translate integrals

The discrete Fourier normalization of a primitive Dirichlet twist carries the
exact inverse-character argument -a and its genuine Gauss sum. The critical
Mellin kernels in weights two and three are absolutely integrable at both ends.
Their factors are computed from the actual completed L-function convention.
No claim of pointwise L-value nonvanishing or Eisenstein-product detection is made.
-/

noncomputable section
set_option autoImplicit false

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane
open Complex MeasureTheory Set ZMod HeckeRing.GL2
open scoped MatrixGroups ModularForm Pointwise

namespace ZInQ.Contrib.HeckePrimeRationality.RankinSupplier

/-- A primitive character's standard Gauss sum is genuinely nonzero, by Fourier inversion. -/
theorem primitive_gaussSum_ne_zero {M : ℕ} [NeZero M] {ψ : DirichletCharacter ℂ M}
    (hψ : ψ.IsPrimitive) : gaussSum ψ ZMod.stdAddChar ≠ 0 := by
  intro hz
  have hfun : (⇑ψ : ZMod M → ℂ) = 0 := by
    apply (ZMod.dft (N := M)).injective
    ext a
    rw [hψ.fourierTransform_eq_inv_mul_gaussSum, hz, mul_zero, map_zero]
    rfl
  have h1 := congrFun hfun (1 : ZMod M)
  have h10 : (1 : ℂ) = 0 := by simpa only [map_one, Pi.zero_apply] using h1
  exact one_ne_zero h10

/-- The computed finite Fourier coefficient prefactor for a primitive twist is nonzero. -/
theorem primitive_gauss_prefactor_ne_zero {M : ℕ} [NeZero M] {ψ : DirichletCharacter ℂ M}
    (hψ : ψ.IsPrimitive) : gaussSum ψ ZMod.stdAddChar / (M : ℂ) ≠ 0 :=
  div_ne_zero (primitive_gaussSum_ne_zero hψ) (Nat.cast_ne_zero.mpr (NeZero.ne M))

/-- The exact primitive-character Fourier normalization of the actual completed L-twist. -/
theorem primitive_twist_completedL {N M : ℕ} [NeZero N] [NeZero M] {k : ℤ}
    (hk : 0 < k) {ψ : DirichletCharacter ℂ M} (hψ : ψ.IsPrimitive)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (s : ℂ) :
    ModularForm.Λ hk (CuspForm.twist ψ
      (original_mul_modulus_dvd_common N M) (modulus_sq_dvd_common N M) f) s =
      (gaussSum ψ ZMod.stdAddChar / (M : ℂ)) *
        ∑ a : ZMod M, ψ⁻¹ (-a) * ModularForm.Λ hk (translatedCusp f a) s := by
  rw [actual_twist_completedL]
  simp_rw [hψ.fourierTransform_eq_inv_mul_gaussSum]
  calc
    (M : ℂ)⁻¹ * ∑ a : ZMod M,
        (ψ⁻¹ (-a) * gaussSum ψ ZMod.stdAddChar) * ModularForm.Λ hk (translatedCusp f a) s =
      (M : ℂ)⁻¹ * ∑ a : ZMod M, gaussSum ψ ZMod.stdAddChar *
        (ψ⁻¹ (-a) * ModularForm.Λ hk (translatedCusp f a) s) := by
          congr 1
          apply Finset.sum_congr rfl
          intro a _
          ring
    _ = _ := by
      rw [← Finset.mul_sum]
      ring

/-- The primitive twist Mellin identity comes with genuine convergence for every complex s. -/
theorem primitive_twist_hasMellin {N M : ℕ} [NeZero N] [NeZero M] {k : ℤ}
    (hk : 0 < k) {ψ : DirichletCharacter ℂ M} (hψ : ψ.IsPrimitive)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (s : ℂ) :
    HasMellin (imaginaryRestriction ⇑(CuspForm.twist ψ
      (original_mul_modulus_dvd_common N M) (modulus_sq_dvd_common N M) f)) s
      ((gaussSum ψ ZMod.stdAddChar / (M : ℂ)) *
        ∑ a : ZMod M, ψ⁻¹ (-a) * ModularForm.Λ hk (translatedCusp f a) s) := by
  have hm := cusp_hasMellin hk
    (CuspForm.twist ψ (original_mul_modulus_dvd_common N M) (modulus_sq_dvd_common N M) f) s
  exact ⟨hm.1, hm.2.trans (primitive_twist_completedL hk hψ f s)⟩

/-- The complex Mellin exponent at the critical argument is the actual integer kernel weight. -/
theorem critical_kernel_exponent (j : ℕ) (t : ℝ) :
    (t : ℂ) ^ (((j : ℂ) - 1) - 1) = (t : ℂ) ^ ((j : ℤ) - 2) := by
  have he : ((j : ℂ) - 1) - 1 = (((j : ℤ) - 2 : ℤ) : ℂ) := by
    push_cast
    ring
  rw [he, Complex.cpow_intCast]

/-- At the classical critical argument, the completed L-function is the actual convergent integer-kernel integral. -/
theorem completedL_critical_integral {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (j : ℕ) (hk : 0 < (j : ℤ)) (f : CuspForm Γ (j : ℤ)) :
    ModularForm.Λ hk f ((j : ℂ) - 1) =
      ∫ t : ℝ in Ioi 0, (t : ℂ) ^ ((j : ℤ) - 2) * imaginaryRestriction ⇑f t := by
  rw [← (cusp_hasMellin hk f ((j : ℂ) - 1)).2]
  unfold mellin
  simp only [critical_kernel_exponent, smul_eq_mul]

/-- Every translate kernel at the critical argument is integrable, even though its Dirichlet series need not converge there. -/
theorem critical_translated_kernel_integrable {N M : ℕ} [NeZero N] [NeZero M]
    (j : ℕ) (hk : 0 < (j : ℤ)) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) (j : ℤ))
    (a : ZMod M) :
    IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ ((j : ℤ) - 2) * imaginaryRestriction
      (⇑f ∣[(j : ℤ)] GeneralLinearGroup.map (algebraMap ℚ ℝ) (shiftMatrix M a)) t) (Ioi 0) := by
  simpa only [critical_kernel_exponent] using
    translated_kernel_integrable hk f a ((j : ℂ) - 1)

/-- The actual archimedean factor at the two requested critical weights is exactly the corresponding power of 2π. -/
theorem critical_archimedean_factor (j : ℕ) (hj : j = 2 ∨ j = 3) :
    (2 : ℂ) / Complex.Gammaℂ ((j : ℂ) - 1) =
      ((2 : ℂ) * Real.pi) ^ ((j : ℤ) - 1) := by
  rcases hj with rfl | rfl
  · norm_num
  · have htwo := Complex.Gammaℂ_add_one (s := (1 : ℂ)) (by norm_num : (1 : ℂ) ≠ 0)
    norm_num at htwo ⊢
    rw [htwo]
    field_simp

/-- Weights two and three are positive actual integer weights. -/
theorem critical_weight_pos (j : ℕ) (hj : j = 2 ∨ j = 3) : 0 < (j : ℤ) := by
  rcases hj with rfl | rfl <;> norm_num

/-- The actual ordinary L-value at j-1 is a finite sum of absolutely convergent positive-rational translate integrals.
This is a single-twist analytic identity, not a pairing with an Eisenstein product. -/
theorem primitive_critical_L_translate_integrals {N M : ℕ} [NeZero N] [NeZero M]
    (j : ℕ) (hj : j = 2 ∨ j = 3) (F : Newform N (j : ℤ))
    {ψ : DirichletCharacter ℂ M} (hψ : ψ.IsPrimitive) :
    ModularForm.L (critical_weight_pos j hj) (CuspForm.twist ψ
      (original_mul_modulus_dvd_common N M) (modulus_sq_dvd_common N M) F.toCuspForm)
        ((j : ℂ) - 1) =
      ((2 : ℂ) * Real.pi) ^ ((j : ℤ) - 1) *
        (gaussSum ψ ZMod.stdAddChar / (M : ℂ)) *
          ∑ a : ZMod M, ψ⁻¹ (-a) *
            ∫ t : ℝ in Ioi 0, (t : ℂ) ^ ((j : ℤ) - 2) * imaginaryRestriction
              (⇑F.toCuspForm ∣[(j : ℤ)]
                GeneralLinearGroup.map (algebraMap ℚ ℝ) (shiftMatrix M a)) t := by
  let hk := critical_weight_pos j hj
  have hi (a : ZMod M) : ModularForm.Λ hk (translatedCusp F.toCuspForm a) ((j : ℂ) - 1) =
      ∫ t : ℝ in Ioi 0, (t : ℂ) ^ ((j : ℤ) - 2) * imaginaryRestriction
        (⇑F.toCuspForm ∣[(j : ℤ)] GeneralLinearGroup.map (algebraMap ℚ ℝ) (shiftMatrix M a)) t := by
    rw [completedL_critical_integral, translatedCusp_coe]
  rw [ModularForm.L, primitive_twist_completedL]
  simp_rw [hi]
  rw [critical_archimedean_factor j hj]
  ring
  exact hψ

/-- The critical integral supplier certifies the actual twist, every actual translate, its computed normalization,
and its L-value identity without a pointwise nonvanishing or product-detector premise. -/
theorem primitive_critical_integral_certificate {N M : ℕ} [NeZero N] [NeZero M]
    (j : ℕ) (hj : j = 2 ∨ j = 3) (F : Newform N (j : ℤ))
    {ψ : DirichletCharacter ℂ M} (hψ : ψ.IsPrimitive) :
    (∀ a : ZMod M, 0 < (shiftMatrix M a : Matrix (Fin 2) (Fin 2) ℚ).det) ∧
      IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ ((j : ℤ) - 2) *
        imaginaryRestriction ⇑(CuspForm.twist ψ
          (original_mul_modulus_dvd_common N M) (modulus_sq_dvd_common N M) F.toCuspForm) t) (Ioi 0) ∧
      (∀ a : ZMod M, IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ ((j : ℤ) - 2) * imaginaryRestriction
        (⇑F.toCuspForm ∣[(j : ℤ)]
          GeneralLinearGroup.map (algebraMap ℚ ℝ) (shiftMatrix M a)) t) (Ioi 0)) ∧
      gaussSum ψ ZMod.stdAddChar / (M : ℂ) ≠ 0 ∧
      ModularForm.L (critical_weight_pos j hj) (CuspForm.twist ψ
        (original_mul_modulus_dvd_common N M) (modulus_sq_dvd_common N M) F.toCuspForm)
          ((j : ℂ) - 1) =
        ((2 : ℂ) * Real.pi) ^ ((j : ℤ) - 1) *
          (gaussSum ψ ZMod.stdAddChar / (M : ℂ)) *
            ∑ a : ZMod M, ψ⁻¹ (-a) *
              ∫ t : ℝ in Ioi 0, (t : ℂ) ^ ((j : ℤ) - 2) * imaginaryRestriction
                (⇑F.toCuspForm ∣[(j : ℤ)]
                  GeneralLinearGroup.map (algebraMap ℚ ℝ) (shiftMatrix M a)) t := by
  refine ⟨shiftMatrix_det_pos M, ?_,
    fun a ↦ critical_translated_kernel_integrable j (critical_weight_pos j hj) F.toCuspForm a,
    primitive_gauss_prefactor_ne_zero hψ, primitive_critical_L_translate_integrals j hj F hψ⟩
  have h := (cusp_hasMellin (critical_weight_pos j hj)
    (CuspForm.twist ψ (original_mul_modulus_dvd_common N M)
      (modulus_sq_dvd_common N M) F.toCuspForm) ((j : ℂ) - 1)).1
  change IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ (((j : ℂ) - 1) - 1) •
    imaginaryRestriction ⇑(CuspForm.twist ψ
      (original_mul_modulus_dvd_common N M) (modulus_sq_dvd_common N M) F.toCuspForm) t) (Ioi 0) at h
  simpa only [critical_kernel_exponent, smul_eq_mul] using h

end ZInQ.Contrib.HeckePrimeRationality.RankinSupplier
