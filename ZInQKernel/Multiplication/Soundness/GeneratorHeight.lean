import ZInQKernel.Model.Heights
import ZInQKernel.Multiplication.Soundness.HeightConstants

/-!
# The canonical height of multiples of `P₀`

Blueprint: `multiplication/soundness/generator-height.md`.

The canonical height on `E(K₀)` is transported from `C(K₀)` by the change of variables
`θ : E(K₀) ≃+ C(K₀)`, `(x, y) ↦ (ε⁴ x, ε⁶ y)`, which maps `P₀` to `[2]R`.
-/

namespace ZInQ.Mult

open WeierstrassCurve WeierstrassCurve.Affine

/-- `ĥ(Q) = ĥ_C(θ(Q))` for `Q ∈ E(K₀)`. -/
noncomputable def canonHeightE (Q : genCurve.toAffine.Point) : ℝ := canonHeight (theta Q)

@[simp] theorem canonHeightE_zero : canonHeightE 0 = 0 := by
  simp [canonHeightE]

/-- `ĥ([n] P₀) = n² ĥ(P₀)`. -/
theorem canonHeightE_zsmul_genP0 (n : ℤ) :
    canonHeightE (n • genP0) = (n : ℝ) ^ 2 * canonHeightE genP0 := by
  rw [canonHeightE, map_zsmul, canonHeight_zsmul, canonHeightE]

/-- `2 ĥ(P₀) ≥ log 41 - ⅓ log 392`. -/
theorem log_41_sub_le_two_canonHeightE_genP0 :
    Real.log 41 - Real.log 392 / 3 ≤ 2 * canonHeightE genP0 := by
  have := hx_le_two_canonHeight (2 • pointR)
  rw [hx_two_R] at this
  rw [canonHeightE, theta_genP0]
  linarith

/-- `2 ĥ(P₀) > 1`. -/
theorem two_canonHeight_genP0_gt_one : 1 < 2 * canonHeightE genP0 :=
  lt_of_lt_of_le one_lt_log_41_sub log_41_sub_le_two_canonHeightE_genP0

/-- `2 ĥ(Q) ≤ h(ε⁴ x(Q)) + ⅓ log 676` for `Q = (x, y) ∈ E(K₀) \ {O}`. -/
theorem two_canonHeightE_le {x y : K0} (h : genCurve.toAffine.Nonsingular x y) :
    2 * canonHeightE (.some x y h) ≤ hK0 (epsilon ^ 4 * x) + Real.log 676 / 3 := by
  have := two_canonHeight_le (theta (.some x y h))
  rw [theta_some, hx_some] at this
  rw [canonHeightE, theta_some]
  exact this

/-- **The canonical height of multiples of `P₀`.** -/
theorem generator_height :
    (∀ n : ℤ, canonHeightE (n • genP0) = (n : ℝ) ^ 2 * canonHeightE genP0) ∧
    (Real.log 41 - Real.log 392 / 3 ≤ 2 * canonHeightE genP0 ∧
      1 < Real.log 41 - Real.log 392 / 3) ∧
    ((∀ (x y : K0) (h : genCurve.toAffine.Nonsingular x y),
      2 * canonHeightE (.some x y h) ≤ hK0 (epsilon ^ 4 * x) + Real.log 676 / 3) ∧
      canonHeightE 0 = 0) :=
  ⟨canonHeightE_zsmul_genP0, ⟨log_41_sub_le_two_canonHeightE_genP0, one_lt_log_41_sub⟩,
    ⟨fun _ _ h => two_canonHeightE_le h, canonHeightE_zero⟩⟩

end ZInQ.Mult
