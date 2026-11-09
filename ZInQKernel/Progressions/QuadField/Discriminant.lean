/-
Plan step 3.2: `|disc ℚ(√d)| ≤ 4|d|`, through the order `ℤ[√d]` of discriminant `4d`.
-/
import ZInQKernel.Progressions.QuadField.Basic

namespace ZInQ.Progressions

open NumberField QuadraticAlgebra

variable {d : ℤ}

/-- `ω = √d` is an algebraic integer. -/
theorem Qsqrt.isIntegral_omega : IsIntegral ℤ (ω : Qsqrt d) := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C d, Polynomial.monic_X_pow_sub_C _ (by norm_num), ?_⟩
  have h : (ω : Qsqrt d) ^ 2 = algebraMap ℚ (Qsqrt d) (d : ℚ) := by
    rw [sq, omega_mul_omega_eq_algebraMap, map_zero, zero_mul, add_zero]
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, h]
  simp

/-- The trace of `ℚ(√d)/ℚ`: `Tr (x + y√d) = 2x`. -/
theorem Qsqrt.trace_eq (z : Qsqrt d) : Algebra.trace ℚ (Qsqrt d) z = 2 * z.re := by
  rw [Algebra.trace_eq_matrix_trace (QuadraticAlgebra.basis _ _), Matrix.trace_fin_two]
  simp [Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply]
  ring

/-- The discriminant of the basis `(1, √d)` is `4d`. -/
theorem Qsqrt.discr_basis : Algebra.discr ℚ (QuadraticAlgebra.basis (d : ℚ) 0) = 4 * d := by
  rw [Algebra.discr_def, Matrix.det_fin_two]
  simp [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Qsqrt.trace_eq]
  ring

variable [Fact (¬ IsSquare (d : ℚ))]

/-- `√d` as an element of the ring of integers of `ℚ(√d)`. -/
def Qsqrt.sqrtInt : 𝓞 (Qsqrt d) := ⟨ω, Qsqrt.isIntegral_omega⟩

@[simp]
theorem Qsqrt.coe_sqrtInt : ((Qsqrt.sqrtInt : 𝓞 (Qsqrt d)) : Qsqrt d) = ω := rfl

theorem Qsqrt.sqrtInt_sq : (Qsqrt.sqrtInt : 𝓞 (Qsqrt d)) ^ 2 = (d : 𝓞 (Qsqrt d)) := by
  apply RingOfIntegers.coe_injective
  have h : (ω : Qsqrt d) ^ 2 = algebraMap ℚ (Qsqrt d) (d : ℚ) := by
    rw [sq, omega_mul_omega_eq_algebraMap, map_zero, zero_mul, add_zero]
  rw [map_pow, map_intCast]
  change (ω : Qsqrt d) ^ 2 = _
  rw [h, map_intCast]

theorem Qsqrt.ne_zero : d ≠ 0 := by
  rintro rfl
  exact Fact.out (p := ¬ IsSquare ((0 : ℤ) : ℚ)) (by simp)

/-- The discriminant `4d` of the order `ℤ[√d]` is a square multiple of `disc ℚ(√d)`. -/
theorem Qsqrt.exists_four_mul_eq_sq_mul_discr :
    ∃ m : ℤ, 4 * d = m ^ 2 * discr (Qsqrt d) := by
  classical
  let B := QuadraticAlgebra.basis (d : ℚ) 0
  let b := integralBasis (Qsqrt d)
  let e := b.indexEquiv B
  let b' := b.reindex e
  let x : Fin 2 → 𝓞 (Qsqrt d) := ![1, ⟨ω, Qsqrt.isIntegral_omega⟩]
  have hx : ∀ j, B j = algebraMap (𝓞 (Qsqrt d)) (Qsqrt d) (x j) := by
    intro j
    fin_cases j
    · simp [B, x]
    · simp [B, x]
      rfl
  let Q : Matrix (Fin 2) (Fin 2) ℤ := fun i j => (RingOfIntegers.basis (Qsqrt d)).repr (x j) (e.symm i)
  have hP : b'.toMatrix B = Q.map (algebraMap ℤ ℚ) := by
    ext i j
    rw [Module.Basis.toMatrix_apply, Module.Basis.repr_reindex_apply, hx, integralBasis_repr_apply]
    rfl
  have h1 := Algebra.discr_of_matrix_vecMul (b' : Fin 2 → Qsqrt d) (b'.toMatrix B)
  rw [Module.Basis.toMatrix_map_vecMul, Module.Basis.coe_reindex, Algebra.discr_reindex, ← coe_discr, hP,
    Qsqrt.discr_basis] at h1
  have hdet : (Q.map (algebraMap ℤ ℚ)).det = ((Q.det : ℤ) : ℚ) :=
    (RingHom.map_det (algebraMap ℤ ℚ) Q).symm
  rw [hdet] at h1
  refine ⟨Q.det, ?_⟩
  exact_mod_cast h1

/-- `|disc ℚ(√d)| ≤ 4|d|`. -/
theorem Qsqrt.abs_discr_le : |discr (Qsqrt d)| ≤ 4 * |d| := by
  obtain ⟨m, hm⟩ := Qsqrt.exists_four_mul_eq_sq_mul_discr (d := d)
  have hd0 : d ≠ 0 := Qsqrt.ne_zero
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
    exact hd0 hm
  have h1 : 1 ≤ m ^ 2 := by
    have := sq_pos_of_ne_zero hm0
    omega
  calc |discr (Qsqrt d)| ≤ m ^ 2 * |discr (Qsqrt d)| :=
        le_mul_of_one_le_left (abs_nonneg _) h1
    _ = |4 * d| := by rw [hm, abs_mul, abs_of_nonneg (sq_nonneg m)]
    _ = 4 * |d| := by rw [abs_mul]; norm_num

end ZInQ.Progressions
