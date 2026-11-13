import ZInQKernel.Model.Field

/-!
# The `x`-height on `C(K₀)`

Blueprint: `model/heights/x-height.md`.

`K₀` is a number field, so it carries Mathlib's admissible family of absolute values
(`NumberField.instAdmissibleAbsValues`): the infinite places with their multiplicities and the
finite places, normalized so that the product formula holds. Mathlib's `Height.logHeight₁` is the
relative logarithmic height `∑_v n_v log max(1, |x|_v)`; the absolute height divides it by
`[K₀ : ℚ] = 2`. The `x`-height of a point of `C` is the absolute height of its abscissa, and `0` at
`O`; it is half of Mathlib's naive height `Point.naiveHeight`.
-/

namespace ZInQ

open WeierstrassCurve WeierstrassCurve.Affine Height

/-- The absolute logarithmic Weil height `h(x) = ½ ∑_v n_v log max(1, |x|_v)` on `K₀`. -/
noncomputable def hK0 (x : K0) : ℝ := logHeight₁ x / 2

/-- The `x`-height `h_x(T) = h(x(T))` for `T ≠ O`, `h_x(O) = 0`. -/
noncomputable def hx (T : curveC.toAffine.Point) : ℝ := T.naiveHeight / 2

theorem hK0_eq_logHeight₁ (x : K0) : hK0 x = logHeight₁ x / 2 := rfl

@[simp] theorem hx_zero : hx 0 = 0 := by
  simp [hx, Point.naiveHeight_eq_logHeight₁, Point.xRep_zero]

@[simp] theorem hx_some {x y : K0} (h : curveC.toAffine.Nonsingular x y) :
    hx (.some x y h) = hK0 x := by
  simp [hx, hK0, Point.naiveHeight_eq_logHeight₁, Point.xRep_some]

theorem hK0_nonneg (x : K0) : 0 ≤ hK0 x := by
  unfold hK0
  have : 0 ≤ logHeight₁ x := Real.log_nonneg (one_le_mulHeight₁ x)
  linarith

theorem hx_nonneg (T : curveC.toAffine.Point) : 0 ≤ hx T := by
  rcases T with _ | ⟨h⟩
  · simp [← Point.zero_def]
  · rw [hx_some]; exact hK0_nonneg _

@[simp] theorem hK0_zero : hK0 0 = 0 := by simp [hK0]

@[simp] theorem hK0_neg (x : K0) : hK0 (-x) = hK0 x := by simp [hK0, logHeight₁_neg]

@[simp] theorem hx_neg (T : curveC.toAffine.Point) : hx (-T) = hx T := by
  simp [hx, Point.naiveHeight_eq_logHeight, Point.xRep_neg]

/-- `hx` is half of Mathlib's naive height. -/
theorem naiveHeight_eq_two_mul_hx (T : curveC.toAffine.Point) : T.naiveHeight = 2 * hx T := by
  unfold hx; ring

end ZInQ
