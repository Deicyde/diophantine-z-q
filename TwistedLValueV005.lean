import CriticalMellinV003
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.LFunction.Basic
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Twist.Basic
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Newforms.Newform
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Cusps.Basic

/-!
# Exact critical-value averaging for actual Dirichlet twists

The translations have rational matrices of determinant one and lie in a
common arithmetic cusp-form space. Applying the convergent Mellin functional
therefore gives finite averaging identities for the existing L-values, including
at arguments one and two. Primitive Gauss constants are proved nonzero.
These identities do not assert nonvanishing of the critical values.
-/

noncomputable section

open Complex MeasureTheory Filter Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open UpperHalfPlane hiding I
open Matrix.GeneralLinearGroup (upperRightHom)
open scoped MatrixGroups ModularForm Topology Classical

namespace CriticalTwists

variable {N M L : ℕ} [NeZero N] [NeZero M] [NeZero L] {k : ℤ}

/-- One rational horizontal translation, restricted to the common twist level. -/
def horizontalTranslate (hNL : N * M ∣ L) (hML : M * M ∣ L)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (a : ZMod M) :
    CuspForm ((Gamma1 L).map (mapGL ℝ)) k :=
  CuspForm.restrict (TauCeti.Gamma1_map_le_conjAct_upperRightHom hNL hML (a.val : ℤ))
    (CuspForm.translate f (upperRightHom (((a.val : ℤ) : ℝ) / M)))

/-- The translating matrix is rational and has positive determinant exactly one. -/
theorem horizontalTranslation_rational_matrix (a : ZMod M) :
    ∃ A : Matrix (Fin 2) (Fin 2) ℚ, A.det = 1 ∧ 0 < A.det ∧
      A.map (fun x : ℚ => (x : ℝ)) =
        (upperRightHom (((a.val : ℤ) : ℝ) / M) : Matrix (Fin 2) (Fin 2) ℝ) := by
  refine ⟨!![1, (a.val : ℚ) / M; 0, 1], ?_, ?_, ?_⟩
  · simp [Matrix.det_fin_two_of]
  · simp [Matrix.det_fin_two_of]
  · change (!![1, (a.val : ℚ) / M; 0, 1] : Matrix (Fin 2) (Fin 2) ℚ).map
        (fun x : ℚ => (x : ℝ)) = !![1, (((a.val : ℤ) : ℝ) / M); 0, 1]
    have hq : (((a.val : ℚ) / (M : ℚ) : ℚ) : ℝ) = (((a.val : ℤ) : ℝ) / M) := by
      push_cast
      rfl
    ext i j
    fin_cases i <;> fin_cases j
    · change ((1 : ℚ) : ℝ) = (1 : ℝ)
      norm_cast
    · change ((((a.val : ℚ) / M : ℚ)) : ℝ) = (((a.val : ℤ) : ℝ) / M)
      exact hq
    · change ((0 : ℚ) : ℝ) = (0 : ℝ)
      norm_cast
    · change ((1 : ℚ) : ℝ) = (1 : ℝ)
      norm_cast

/-- The restricted translated cusp form is the literal horizontal translate. -/
theorem horizontalTranslate_apply (hNL : N * M ∣ L) (hML : M * M ∣ L)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (a : ZMod M) (τ : ℍ) :
    horizontalTranslate hNL hML f a τ = f (((a.val : ℝ) / M) +ᵥ τ) := by
  simp only [horizontalTranslate, CuspForm.coe_restrict, CuspForm.coe_translate,
    TauCeti.ModularForm.slash_upperRightHom_apply, Int.cast_natCast]

/-- The coefficient multiplier varies linearly while the input cusp form is fixed. -/
def coefficientTwistLinear (hNL : N * M ∣ L) (hML : M * M ∣ L)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (ZMod M → ℂ) →ₗ[ℂ] CuspForm ((Gamma1 L).map (mapGL ℝ)) k where
  toFun Φ := CuspForm.twist Φ hNL hML f
  map_add' Φ Ψ := by
    ext τ
    simp only [FunLike.coe_add, Pi.add_apply, CuspForm.twist_apply, map_add, add_mul,
      Finset.sum_add_distrib, mul_add]
  map_smul' c Φ := by
    ext τ
    simp only [FunLike.coe_smul, CuspForm.twist_apply, map_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    ring

/-- Exact finite rational-matrix representation with coefficients independent of the point. -/
theorem twist_eq_finite_translates (Φ : ZMod M → ℂ)
    (hNL : N * M ∣ L) (hML : M * M ∣ L)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    CuspForm.twist Φ hNL hML f =
      (M : ℂ)⁻¹ • ∑ a : ZMod M, ZMod.dft Φ a • horizontalTranslate hNL hML f a := by
  ext τ
  simp only [CuspForm.twist_apply, FunLike.coe_smul, FunLike.coe_sum, Pi.smul_apply,
    Finset.sum_apply, smul_eq_mul, horizontalTranslate_apply]

/-- The existing L-value of a twist is a finite average of actual translated L-values. -/
theorem L_twist_eq_dft_average (hk : 0 < k) (s : ℂ) (Φ : ZMod M → ℂ)
    (hNL : N * M ∣ L) (hML : M * M ∣ L)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ModularForm.L hk (CuspForm.twist Φ hNL hML f) s =
      (M : ℂ)⁻¹ * ∑ a : ZMod M,
        ZMod.dft Φ a * ModularForm.L hk (horizontalTranslate hNL hML f a) s := by
  have h := congrArg (LValueLinear hk s) (twist_eq_finite_translates Φ hNL hML f)
  simpa only [map_smul, map_sum, smul_eq_mul, LValueLinear_apply] using h

/-- The actual twist followed by its existing L-value is a linear coefficient functional. -/
def twistLValueLinear (hk : 0 < k) (s : ℂ)
    (hNL : N * M ∣ L) (hML : M * M ∣ L)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : (ZMod M → ℂ) →ₗ[ℂ] ℂ :=
  (LValueLinear hk s).comp (coefficientTwistLinear hNL hML f)

/-- The coefficient functional is tied to the existing L-value, not defined by an averaging goal. -/
theorem twistLValueLinear_apply (hk : 0 < k) (s : ℂ) (Φ : ZMod M → ℂ)
    (hNL : N * M ∣ L) (hML : M * M ∣ L)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    twistLValueLinear hk s hNL hML f Φ = ModularForm.L hk (CuspForm.twist Φ hNL hML f) s := by
  exact LValueLinear_apply hk s _

/-- At every argument, even-twist values recover the actual even residue-filtered L-value. -/
theorem even_twist_L_average (hk : 0 < k) (s : ℂ) (u : ZMod M) (hu : IsUnit u)
    (hNL : N * M ∣ L) (hML : M * M ∣ L)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (M.totient : ℂ) / 2 * ModularForm.L hk
      (CuspForm.twist (residueIndicator u + residueIndicator (-u)) hNL hML f) s =
      ∑ ψ : DirichletCharacter ℂ M, if ψ.Even then ψ u⁻¹ *
        ModularForm.L hk (CuspForm.twist ψ hNL hML f) s else 0 := by
  simpa only [twistLValueLinear_apply] using
    evenCharacterAverage (twistLValueLinear hk s hNL hML f) u hu

/-- At every argument, odd-twist values recover the actual odd residue-filtered L-value. -/
theorem odd_twist_L_average (hk : 0 < k) (s : ℂ) (u : ZMod M) (hu : IsUnit u)
    (hNL : N * M ∣ L) (hML : M * M ∣ L)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (M.totient : ℂ) / 2 * ModularForm.L hk
      (CuspForm.twist (residueIndicator u - residueIndicator (-u)) hNL hML f) s =
      ∑ ψ : DirichletCharacter ℂ M, if ψ.Odd then ψ u⁻¹ *
        ModularForm.L hk (CuspForm.twist ψ hNL hML f) s else 0 := by
  simpa only [twistLValueLinear_apply] using
    oddCharacterAverage (twistLValueLinear hk s hNL hML f) u hu

/-- Fourier inversion proves that the Gauss constant of a primitive character is nonzero. -/
theorem primitive_gaussSum_ne_zero (ψ : DirichletCharacter ℂ M) (hψ : ψ.IsPrimitive) :
    gaussSum ψ ZMod.stdAddChar ≠ 0 := by
  intro hzero
  have hf : ZMod.dft (ψ : ZMod M → ℂ) = 0 := by
    ext a
    simp only [hψ.fourierTransform_eq_inv_mul_gaussSum, hzero, mul_zero, Pi.zero_apply]
  have hz : (ψ : ZMod M → ℂ) = 0 := by
    apply ZMod.dft.injective
    simpa only [map_zero] using hf
  have h1 := congrFun hz 1
  simpa using h1

/-- The exact primitive Gauss average for the existing twisted L-value. -/
theorem primitive_twist_L_gauss_average (hk : 0 < k) (s : ℂ)
    (ψ : DirichletCharacter ℂ M) (hψ : ψ.IsPrimitive)
    (hNL : N * M ∣ L) (hML : M * M ∣ L)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ModularForm.L hk (CuspForm.twist ψ hNL hML f) s =
      (M : ℂ)⁻¹ * gaussSum ψ ZMod.stdAddChar *
        ∑ a : ZMod M, ψ⁻¹ (-a) * ModularForm.L hk (horizontalTranslate hNL hML f a) s := by
  rw [L_twist_eq_dft_average hk s ψ hNL hML f]
  simp only [hψ.fourierTransform_eq_inv_mul_gaussSum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- The factor in the primitive Gauss average is actually nonzero. -/
theorem primitive_gauss_average_factor_ne_zero
    (ψ : DirichletCharacter ℂ M) (hψ : ψ.IsPrimitive) :
    (M : ℂ)⁻¹ * gaussSum ψ ZMod.stdAddChar ≠ 0 :=
  mul_ne_zero (inv_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne M)))
    (primitive_gaussSum_ne_zero ψ hψ)

/-- Every actual normalized newform has normalized twists, regardless of character parity. -/
theorem normalized_newform_twist_coeff_one (F : HeckeRing.GL2.Newform N k)
    (ψ : DirichletCharacter ℂ M) (hNL : N * M ∣ L) (hML : M * M ∣ L) :
    (qExpansion 1 (CuspForm.twist ψ hNL hML F.toCuspForm)).coeff 1 = 1 := by
  rw [CuspForm.qExpansion_twist_coeff, F.qExpansion_coeff_one]
  simp only [Nat.cast_one, map_one, mul_one]

/-- The original nebentypus is retained by the exact actual-twist construction. -/
theorem normalized_newform_twist_nebentypus (F : HeckeRing.GL2.Newform N k)
    (ψ : DirichletCharacter ℂ M) (hNL : N * M ∣ L) (hML : M * M ∣ L) :
    CuspForm.twist ψ hNL hML F.toCuspForm ∈ cuspFormCharSpace k
      (F.χ.comp (ZMod.unitsMap (dvd_of_mul_right_dvd hNL)) *
        (ψ.toUnitHom.comp (ZMod.unitsMap (dvd_of_mul_left_dvd hML))) ^ 2) :=
  CuspForm.twist_mem_cuspFormCharSpace ψ hNL hML F.mem_charSpace

end CriticalTwists
