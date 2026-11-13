import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Quartic characters for the congruent-number Hasse bound

This is a proof component, not an assumed Hasse bound. All characters are extended
by zero at zero, as in Mathlib's `MulChar` convention.
-/

namespace ZInQ.Contrib.Hasse

section Characters

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The complex-valued quadratic character, with value zero at zero. -/
noncomputable def eta (F : Type*) [Field F] [Fintype F] [DecidableEq F] : MulChar F ℂ :=
  (quadraticChar F).ringHomComp (Int.castRingHom ℂ)

@[simp] theorem eta_apply (x : F) : eta F x = (quadraticChar F x : ℂ) := rfl

omit [DecidableEq F] in
/-- Nontrivial quadratic characters of a finite field into `ℂ` are unique. -/
theorem quadratic_unique {χ φ : MulChar F ℂ}
    (hχ : χ.IsQuadratic) (hφ : φ.IsQuadratic) (hχ1 : χ ≠ 1) (hφ1 : φ ≠ 1) : χ = φ := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  apply (MulChar.eq_iff hg χ φ).mpr
  have hχg : χ g ≠ 1 := by
    intro h
    apply hχ1
    exact (MulChar.eq_iff hg χ 1).mpr (by simpa using h)
  have hφg : φ g ≠ 1 := by
    intro h
    apply hφ1
    exact (MulChar.eq_iff hg φ 1).mpr (by simpa using h)
  have hχ0 : χ g ≠ 0 := (g.isUnit.map χ).ne_zero
  have hφ0 : φ g ≠ 0 := (g.isUnit.map φ).ne_zero
  rcases hχ g with h | h | h
  · exact (hχ0 h).elim
  · exact (hχg h).elim
  · rcases hφ g with h' | h' | h'
    · exact (hφ0 h').elim
    · exact (hφg h').elim
    · exact h.trans h'.symm

/-- A genuine quartic character exists when the finite field has cardinality `1 mod 4`.
Its square is the actual quadratic character; this normalization is proved, not assumed. -/
theorem exists_quartic (hF : ringChar F ≠ 2) (h4 : 4 ∣ Fintype.card F - 1) :
    ∃ χ : MulChar F ℂ, orderOf χ = 4 ∧ χ ^ 2 = eta F := by
  obtain ⟨χ, hχ⟩ := MulChar.exists_mulChar_orderOf F h4 Complex.isPrimitiveRoot_I
  refine ⟨χ, hχ, quadratic_unique ?_ ?_ ?_ ?_⟩
  · apply MulChar.isQuadratic_iff_sq_eq_one.mpr
    rw [← pow_mul, show 2 * 2 = 4 by rfl, ← hχ, pow_orderOf_eq_one]
  · exact (quadraticChar_isQuadratic F).comp _
  · apply pow_ne_one_of_lt_orderOf (by norm_num)
    rw [hχ]; norm_num
  · exact (MulChar.ringHomComp_ne_one_iff Int.cast_injective).mpr
      (quadraticChar_ne_one hF)

omit [DecidableEq F] in
/-- Complex Jacobi sums of three nontrivial characters have exactly the expected norm. -/
theorem norm_jacobiSum {χ φ : MulChar F ℂ} (hχ : χ ≠ 1) (hφ : φ ≠ 1)
    (hχφ : χ * φ ≠ 1) : ‖jacobiSum χ φ‖ = Real.sqrt (Fintype.card F) := by
  have hchar : ringChar ℂ ≠ ringChar F := by
    rw [ringChar.eq ℂ 0]
    exact (FiniteField.card F (ringChar F)).choose_spec.1.ne_zero.symm
  have h := jacobiSum_mul_jacobiSum_inv hchar hχ hφ hχφ
  have hstar : star (jacobiSum χ φ) = jacobiSum χ⁻¹ φ⁻¹ := by
    simp only [jacobiSum, star_sum, star_mul, MulChar.star_apply', mul_comm]
  rw [← hstar] at h
  have hnorm : ‖jacobiSum χ φ‖ ^ 2 = (Fintype.card F : ℝ) := by
    have hr := congrArg Complex.re h
    simpa [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_pow] using hr
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ Fintype.card F by positivity),
    Real.sqrt_nonneg (Fintype.card F), norm_nonneg (jacobiSum χ φ)]

end Characters

end ZInQ.Contrib.Hasse
