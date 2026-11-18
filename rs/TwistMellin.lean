import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Twist.Basic
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Cusps.Basic
import Mathlib.NumberTheory.ModularForms.LFunction
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Newforms.Newform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

/-!
# Actual Mellin transforms of finite twists

The actual cusp twist is a finite Fourier sum of positive rational translates,
all represented as actual cusp forms at the constructed common level N M².
Cuspidality at both ends supplies convergence for every complex exponent before
interchanging the finite sum and the Mellin integral. The imaginary restriction
uses the same function as the completed L-function and is integrated only on
the positive real axis. This is not an Eisenstein-product detector or a
pointwise nonvanishing theorem.
-/

noncomputable section
set_option autoImplicit false

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane
open Complex MeasureTheory Set ZMod
open scoped MatrixGroups ModularForm Pointwise

namespace ZInQ.Contrib.HeckePrimeRationality.RankinSupplier

/-- The constructed common level contains the original level times the twist modulus. -/
theorem original_mul_modulus_dvd_common (N M : ℕ) : N * M ∣ N * M ^ 2 :=
  ⟨M, by ring⟩

/-- The constructed common level contains the square of the twist modulus. -/
theorem modulus_sq_dvd_common (N M : ℕ) : M * M ∣ N * M ^ 2 :=
  ⟨N, by ring⟩

/-- The actual positive rational translation by a residue divided by the twist modulus. -/
def shiftMatrix (M : ℕ) (a : ZMod M) : GL (Fin 2) ℚ :=
  GeneralLinearGroup.upperRightHom ((a.val : ℚ) / M)

/-- Every matrix in the actual finite translation family has determinant one. -/
theorem shiftMatrix_det (M : ℕ) (a : ZMod M) :
    (shiftMatrix M a : Matrix (Fin 2) (Fin 2) ℚ).det = 1 := by
  change (!![1, (a.val : ℚ) / M; 0, 1]).det = 1
  norm_num [Matrix.det_fin_two]

/-- Positivity is proved for the actual rational matrix, not supplied as an orbit premise. -/
theorem shiftMatrix_det_pos (M : ℕ) (a : ZMod M) :
    0 < (shiftMatrix M a : Matrix (Fin 2) (Fin 2) ℚ).det := by
  rw [shiftMatrix_det]
  exact one_pos

/-- The rational translation maps to the exact real translation used by the actual twist. -/
theorem shiftMatrix_map (M : ℕ) (a : ZMod M) :
    GeneralLinearGroup.map (algebraMap ℚ ℝ) (shiftMatrix M a) =
      GeneralLinearGroup.upperRightHom ((a.val : ℝ) / M) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shiftMatrix, GeneralLinearGroup.upperRightHom_apply]

/-- One actual rational translate, restricted to the actual constructed common cusp level. -/
def translatedCusp {N M : ℕ} [NeZero N] [NeZero M] {k : ℤ}
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (a : ZMod M) :
    CuspForm ((Gamma1 (N * M ^ 2)).map (mapGL ℝ)) k :=
  CuspForm.restrict
    (TauCeti.Gamma1_map_le_conjAct_upperRightHom
      (original_mul_modulus_dvd_common N M) (modulus_sq_dvd_common N M) (a.val : ℤ))
    (CuspForm.translate f (GeneralLinearGroup.upperRightHom (((a.val : ℤ) : ℝ) / M)))

/-- The actual common-level cusp form is exactly the positive rational slash of the original f. -/
theorem translatedCusp_coe {N M : ℕ} [NeZero N] [NeZero M] {k : ℤ}
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (a : ZMod M) :
    ⇑(translatedCusp f a) = ⇑f ∣[k] GeneralLinearGroup.map (algebraMap ℚ ℝ) (shiftMatrix M a) := by
  rw [translatedCusp, CuspForm.coe_restrict, CuspForm.coe_translate, shiftMatrix_map,
    Int.cast_natCast]

/-- Each actual translate evaluates at the exact horizontal rational shift, with no determinant factor. -/
theorem translatedCusp_apply {N M : ℕ} [NeZero N] [NeZero M] {k : ℤ}
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (a : ZMod M) (τ : ℍ) :
    translatedCusp f a τ = f (((a.val : ℝ) / M) +ᵥ τ) := by
  rw [congrFun (translatedCusp_coe f a) τ, shiftMatrix_map,
    TauCeti.ModularForm.slash_upperRightHom_apply]

/-- The existing actual cusp twist is the constructed finite Fourier combination at the same level. -/
theorem actual_twist_eq_sum {N M : ℕ} [NeZero N] [NeZero M] {k : ℤ}
    (Φ : ZMod M → ℂ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    CuspForm.twist Φ (original_mul_modulus_dvd_common N M) (modulus_sq_dvd_common N M) f =
      (M : ℂ)⁻¹ • ∑ a : ZMod M, 𝓕 Φ a • translatedCusp f a := by
  apply DFunLike.ext
  intro τ
  simp only [CuspForm.twist_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul,
    FunLike.coe_sum, Finset.sum_apply, translatedCusp_apply]

/-- The imaginary-axis function used by the actual completed L-function. -/
def imaginaryRestriction (f : ℍ → ℂ) : ℝ → ℂ :=
  fun t ↦ f (UpperHalfPlane.ofComplex (Complex.I * t))

/-- On the integration domain, the imaginary restriction is evaluation at the actual point i t. -/
theorem imaginaryRestriction_of_pos (f : ℍ → ℂ) {t : ℝ} (ht : 0 < t) :
    imaginaryRestriction f t = f ⟨Complex.I * t, by simpa using ht⟩ := by
  rw [imaginaryRestriction, ofComplex_apply_of_im_pos (by simpa using ht)]

/-- Actual cusps supply Mellin convergence and the completed L-value for every complex exponent. -/
theorem cusp_hasMellin {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ}
    (hk : 0 < k) (f : CuspForm Γ k) (s : ℂ) :
    HasMellin (imaginaryRestriction ⇑f) s (ModularForm.Λ hk f s) := by
  exact (CuspForm.isStrongFEPair hk f).hasMellin s

/-- A finite Mellin sum can be interchanged only after convergence of every summand is proved. -/
theorem hasMellin_finset_sum {I : Type*} (S : Finset I) (u : I → ℝ → ℂ) (z : I → ℂ) (s : ℂ)
    (hs : ∀ i ∈ S, HasMellin (u i) s (z i)) :
    HasMellin (fun t ↦ ∑ i ∈ S, u i t) s (∑ i ∈ S, z i) := by
  classical
  revert hs
  induction S using Finset.induction_on with
  | empty =>
    intro _
    simp [HasMellin, MellinConvergent, mellin]
  | @insert i S hi ih =>
    intro hs
    have hai := hs i (Finset.mem_insert_self i S)
    have has := ih (fun j hj ↦ hs j (Finset.mem_insert_of_mem hj))
    have hadd := hasMellin_add hai.1 has.1
    rw [hai.2, has.2] at hadd
    simpa only [Finset.sum_insert hi] using hadd

/-- The actual imaginary restriction commutes with the finite Fourier twist sum. -/
theorem axis_actual_twist {N M : ℕ} [NeZero N] [NeZero M] {k : ℤ}
    (Φ : ZMod M → ℂ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    imaginaryRestriction ⇑(CuspForm.twist Φ
      (original_mul_modulus_dvd_common N M) (modulus_sq_dvd_common N M) f) =
      fun t ↦ (M : ℂ)⁻¹ • ∑ a : ZMod M, 𝓕 Φ a • imaginaryRestriction ⇑(translatedCusp f a) t := by
  funext t
  simp only [imaginaryRestriction, CuspForm.twist_apply, translatedCusp_apply, smul_eq_mul]

/-- The genuine all-complex-exponent Mellin formula for the existing actual cusp twist. -/
theorem actual_twist_hasMellin {N M : ℕ} [NeZero N] [NeZero M] {k : ℤ}
    (hk : 0 < k) (Φ : ZMod M → ℂ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (s : ℂ) :
    HasMellin (imaginaryRestriction ⇑(CuspForm.twist Φ
      (original_mul_modulus_dvd_common N M) (modulus_sq_dvd_common N M) f)) s
      ((M : ℂ)⁻¹ * ∑ a : ZMod M, 𝓕 Φ a * ModularForm.Λ hk (translatedCusp f a) s) := by
  classical
  have hm (a : ZMod M) := cusp_hasMellin hk (translatedCusp f a) s
  have hc (a : ZMod M) : HasMellin
      (fun t ↦ 𝓕 Φ a • imaginaryRestriction ⇑(translatedCusp f a) t) s
      (𝓕 Φ a • ModularForm.Λ hk (translatedCusp f a) s) := by
    have h := hasMellin_const_smul (hm a).1 (𝓕 Φ a)
    rw [(hm a).2] at h
    exact h
  have hsum := hasMellin_finset_sum Finset.univ
    (fun a t ↦ 𝓕 Φ a • imaginaryRestriction ⇑(translatedCusp f a) t)
    (fun a ↦ 𝓕 Φ a • ModularForm.Λ hk (translatedCusp f a) s) s (fun a _ ↦ hc a)
  have hscaled := hasMellin_const_smul hsum.1 (M : ℂ)⁻¹
  rw [hsum.2] at hscaled
  rw [axis_actual_twist]
  simpa only [smul_eq_mul] using hscaled

/-- The actual completed L-function twist formula is valid at every complex s, not just a series half-plane. -/
theorem actual_twist_completedL {N M : ℕ} [NeZero N] [NeZero M] {k : ℤ}
    (hk : 0 < k) (Φ : ZMod M → ℂ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (s : ℂ) :
    ModularForm.Λ hk (CuspForm.twist Φ
      (original_mul_modulus_dvd_common N M) (modulus_sq_dvd_common N M) f) s =
      (M : ℂ)⁻¹ * ∑ a : ZMod M, 𝓕 Φ a * ModularForm.Λ hk (translatedCusp f a) s := by
  exact (cusp_hasMellin hk _ s).2.symm.trans (actual_twist_hasMellin hk Φ f s).2

/-- The actual ordinary L-function has the corresponding finite Fourier formula at all complex points. -/
theorem actual_twist_L {N M : ℕ} [NeZero N] [NeZero M] {k : ℤ}
    (hk : 0 < k) (Φ : ZMod M → ℂ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (s : ℂ) :
    ModularForm.L hk (CuspForm.twist Φ
      (original_mul_modulus_dvd_common N M) (modulus_sq_dvd_common N M) f) s =
      (M : ℂ)⁻¹ * ∑ a : ZMod M, 𝓕 Φ a * ModularForm.L hk (translatedCusp f a) s := by
  simp only [ModularForm.L, actual_twist_completedL]
  rw [mul_assoc, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Every actual rational-translate Mellin kernel is absolutely integrable for every fixed complex s. -/
theorem translated_kernel_integrable {N M : ℕ} [NeZero N] [NeZero M] {k : ℤ}
    (hk : 0 < k) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (a : ZMod M) (s : ℂ) :
    IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ (s - 1) *
      imaginaryRestriction (⇑f ∣[k] GeneralLinearGroup.map (algebraMap ℚ ℝ) (shiftMatrix M a)) t) (Ioi 0) := by
  have h := (cusp_hasMellin hk (translatedCusp f a) s).1
  change IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ (s - 1) • imaginaryRestriction ⇑(translatedCusp f a) t) (Ioi 0) at h
  simpa only [translatedCusp_coe, smul_eq_mul] using h

end ZInQ.Contrib.HeckePrimeRationality.RankinSupplier
