import ZInQKernel.Model.Field.Curve

/-!
# The local parameter `z` on multiples of the generator

Blueprint: `compiler/natural/precision/z-coordinate.md`.

For an affine point `P = (x, y)` of `E(K₀)` with `y ≠ 0`, `z(P) = -x/y`. An index `k` is
*admissible* if `[k]P₀` is affine with nonzero ordinate; for admissible `k`,
`z_k = z([k]P₀) = u_k + v_k s` and `ε_k = |u_k| + |v_k| > 0`; for admissible `a, j`,
`r(a, j) = ½ Tr (z_j / z_a)` is the rational component of `z_j / z_a`.

The functions `zPt`, `zIdx`, `epsIdx` and `rRatio` are total: they take the junk value `0` at
the identity (and `zPt` takes `-x/0 = 0` at points of order two). Only their values at
admissible indices enter the precision relation.
-/

namespace ZInQ.Compiler.Precision

open WeierstrassCurve WeierstrassCurve.Affine

/-- `z(P) = -x/y` for an affine point `P = (x, y)`; junk value `0` at `O`. -/
noncomputable def zPt : genCurve.toAffine.Point → K0
  | .zero => 0
  | .some x y _ => -x / y

@[simp] theorem zPt_zero : zPt 0 = 0 := rfl

@[simp] theorem zPt_some {x y : K0} (h : genCurve.toAffine.Nonsingular x y) :
    zPt (.some x y h) = -x / y := rfl

/-- An affine point of `E` with `y ≠ 0` has `x ≠ 0`. -/
theorem x_ne_zero_of_y_ne_zero {x y : K0} (h : genCurve.toAffine.Equation x y) (hy : y ≠ 0) :
    x ≠ 0 := by
  rintro rfl
  rw [genCurve_equation_iff] at h
  apply hy
  simpa using h

/-- `z(P) ≠ 0` for an affine point with nonzero ordinate. -/
theorem zPt_ne_zero {x y : K0} (h : genCurve.toAffine.Nonsingular x y) (hy : y ≠ 0) :
    zPt (.some x y h) ≠ 0 := by
  rw [zPt_some]
  exact div_ne_zero (neg_ne_zero.mpr (x_ne_zero_of_y_ne_zero h.1 hy)) hy

/-- `z(-P) = -z(P)`. -/
theorem zPt_neg (P : genCurve.toAffine.Point) : zPt (-P) = -zPt P := by
  cases P with
  | zero => show (0 : K0) = -0; simp
  | some x y h =>
    rw [Point.neg_some, zPt_some, zPt_some]
    have : genCurve.toAffine.negY x y = -y := by simp [Affine.negY, genCurve]
    rw [this, div_neg]

/-- An index `k` is admissible if `[k]P₀` is an affine point with nonzero ordinate. -/
def Admissible (k : ℤ) : Prop :=
  ∃ (x y : K0) (h : genCurve.toAffine.Nonsingular x y), k • genP0 = .some x y h ∧ y ≠ 0

/-- `z_k = z([k]P₀)`. -/
noncomputable def zIdx (k : ℤ) : K0 := zPt (k • genP0)

/-- `ε_k = |u_k| + |v_k|` where `z_k = u_k + v_k s`. -/
noncomputable def epsIdx (k : ℤ) : ℚ := |(zIdx k).re| + |(zIdx k).im|

/-- `r(a, j)`, the rational component of `z_j / z_a`. -/
noncomputable def rRatio (a j : ℤ) : ℚ := (zIdx j / zIdx a).re

theorem zIdx_ne_zero {k : ℤ} (hk : Admissible k) : zIdx k ≠ 0 := by
  obtain ⟨x, y, h, hP, hy⟩ := hk
  rw [zIdx, hP]
  exact zPt_ne_zero h hy

/-- `ε_k > 0` for admissible `k`. -/
theorem epsIdx_pos {k : ℤ} (hk : Admissible k) : 0 < epsIdx k := by
  have hz := zIdx_ne_zero hk
  unfold epsIdx
  rcases eq_or_ne (zIdx k).re 0 with h1 | h1
  · have h2 : (zIdx k).im ≠ 0 := fun h2 => hz (QuadraticAlgebra.ext h1 h2)
    have := abs_pos.mpr h2
    positivity
  · have := abs_pos.mpr h1
    positivity

theorem zIdx_neg (k : ℤ) : zIdx (-k) = -zIdx k := by
  rw [zIdx, zIdx, neg_zsmul, zPt_neg]

/-- `r(a, j) = ½ Tr_{K₀/ℚ}(z_j / z_a)`. -/
theorem rRatio_eq_half_trace (a j : ℤ) :
    rRatio a j = QuadraticAlgebra.trace (zIdx j / zIdx a) / 2 := by
  rw [rRatio, K0.trace_eq]; ring

end ZInQ.Compiler.Precision
