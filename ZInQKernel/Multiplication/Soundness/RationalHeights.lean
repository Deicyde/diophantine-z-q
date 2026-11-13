import ZInQKernel.Hypotheses.Height

/-!
# Sum and quotient bounds for rational heights

Blueprint: `multiplication/soundness/rational-height-bounds.md`.

The rational height `ratHeight u = log max(|a|, b)` of `u = a/b` in lowest terms is Mathlib's
logarithmic height `Height.logHeight₁` on `ℚ` (`Rat.logHeight₁_eq_log_max`), whose only infinite
place has multiplicity one. The bounds are then Mathlib's `logHeight₁_sum_le`,
`logHeight₁_mul_le` and `logHeight₁_inv`.
-/

namespace ZInQ.Mult

open Height

/-- `ratHeight` is Mathlib's logarithmic height on `ℚ`. -/
theorem ratHeight_eq_logHeight₁ (u : ℚ) : ratHeight u = logHeight₁ u := by
  rw [ratHeight, Rat.logHeight₁_eq_log_max, Nat.cast_max, Nat.cast_natAbs, Int.cast_abs]

theorem ratHeight_nonneg (u : ℚ) : 0 ≤ ratHeight u := by
  rw [ratHeight_eq_logHeight₁]; exact Real.log_nonneg (one_le_mulHeight₁ u)

@[simp] theorem ratHeight_neg (u : ℚ) : ratHeight (-u) = ratHeight u := by
  simp [ratHeight_eq_logHeight₁]

@[simp] theorem ratHeight_inv (u : ℚ) : ratHeight u⁻¹ = ratHeight u := by
  simp [ratHeight_eq_logHeight₁, logHeight₁_inv]

theorem totalWeight_rat : totalWeight ℚ = 1 := by
  rw [NumberField.totalWeight_eq_finrank, Module.finrank_self]

/-- `h(x₁ + x₂ + x₃) ≤ h(x₁) + h(x₂) + h(x₃) + log 3`. -/
theorem ratHeight_add3_le (x₁ x₂ x₃ : ℚ) :
    ratHeight (x₁ + x₂ + x₃) ≤ ratHeight x₁ + ratHeight x₂ + ratHeight x₃ + Real.log 3 := by
  have h := logHeight₁_sum_le (Finset.univ : Finset (Fin 3)) ![x₁, x₂, x₃]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons, Finset.card_univ, Fintype.card_fin, totalWeight_rat,
    Nat.cast_one, one_mul] at h
  simp only [ratHeight_eq_logHeight₁]
  push_cast at h
  linarith

theorem ratHeight_mul_le (x y : ℚ) : ratHeight (x * y) ≤ ratHeight x + ratHeight y := by
  simp only [ratHeight_eq_logHeight₁]; exact logHeight₁_mul_le x y

/-- `h(x / y) ≤ h(x) + h(y)` (for `y = 0` both sides are trivially compared, as `x / 0 = 0`). -/
theorem ratHeight_div_le (x y : ℚ) : ratHeight (x / y) ≤ ratHeight x + ratHeight y := by
  rw [div_eq_mul_inv, ← ratHeight_inv y]; exact ratHeight_mul_le x y⁻¹

/-- **Sum and quotient bounds for rational heights.** -/
theorem rational_height_bounds :
    (∀ x₁ x₂ x₃ : ℚ,
      ratHeight (x₁ + x₂ + x₃) ≤ ratHeight x₁ + ratHeight x₂ + ratHeight x₃ + Real.log 3) ∧
    (∀ x y : ℚ, y ≠ 0 → ratHeight (x / y) ≤ ratHeight x + ratHeight y) ∧
    (∀ x : ℚ, ratHeight (-x) = ratHeight x ∧ 0 ≤ ratHeight x) ∧
    (∀ y : ℚ, y ≠ 0 → ratHeight y⁻¹ = ratHeight y) :=
  ⟨ratHeight_add3_le, fun x y _ => ratHeight_div_le x y,
    fun x => ⟨ratHeight_neg x, ratHeight_nonneg x⟩, fun y _ => ratHeight_inv y⟩

end ZInQ.Mult
