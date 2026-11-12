import Mathlib

/-!
# bp-modcurves, node MC2c (first half): points under a change of variables

Mathlib v4.35 has `VariableChange` acting on `WeierstrassCurve` but no transport of points.
For `C = (u, r, s, t)` (so `x = u²x' + r`, `y = u³y' + u²sx' + t`) the new coordinates of
`(x, y)` are `x' = (x − r)/u²`, `y' = (y − s(x − r) − t)/u³`. This file proves that the transport
preserves the equation, nonsingularity, negation and the slope.
-/

namespace BPModCurves

open WeierstrassCurve

variable {K : Type*} [Field K] (W : WeierstrassCurve K) (C : VariableChange K)

/-- New `x`-coordinate. -/
def tx (x : K) : K := (x - C.r) / (C.u : K) ^ 2

/-- New `y`-coordinate. -/
def ty (x y : K) : K := (y - C.s * (x - C.r) - C.t) / (C.u : K) ^ 3

theorem u_ne_zero : (C.u : K) ≠ 0 := C.u.ne_zero

theorem poly_transport (x y : K) :
    (ty C x y) ^ 2 + (C • W).a₁ * tx C x * ty C x y + (C • W).a₃ * ty C x y -
      ((tx C x) ^ 3 + (C • W).a₂ * (tx C x) ^ 2 + (C • W).a₄ * tx C x + (C • W).a₆) =
    (y ^ 2 + W.a₁ * x * y + W.a₃ * y - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)) /
      (C.u : K) ^ 6 := by
  have hu := u_ne_zero C
  simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆, tx, ty, Units.val_inv_eq_inv_val]
  field_simp
  ring

theorem equation_transport (x y : K) :
    (C • W).toAffine.Equation (tx C x) (ty C x y) ↔ W.toAffine.Equation x y := by
  rw [Affine.equation_iff', Affine.equation_iff']
  have := poly_transport W C x y
  simp only [WeierstrassCurve.toAffine] at this ⊢
  rw [this, div_eq_zero_iff]
  simp [u_ne_zero C]

theorem negY_transport (x y : K) :
    (C • W).toAffine.negY (tx C x) (ty C x y) = ty C x (W.toAffine.negY x y) := by
  have hu := u_ne_zero C
  simp only [Affine.negY, variableChange_a₁, variableChange_a₃, tx, ty, Units.val_inv_eq_inv_val]
  field_simp
  ring

theorem ty_inj {x y y' : K} (h : ty C x y = ty C x y') : y = y' := by
  have hu := pow_ne_zero 3 (u_ne_zero C)
  simp only [ty] at h
  rw [div_left_inj' hu] at h
  linear_combination h

theorem tx_inj {x x' : K} (h : tx C x = tx C x') : x = x' := by
  have hu := pow_ne_zero 2 (u_ne_zero C)
  simp only [tx] at h
  rw [div_left_inj' hu] at h
  linear_combination h

theorem disj_aux {A B s v w : K} (hv : v ≠ 0) (hw : w ≠ 0) :
    ((A + s * B) / v ≠ 0 ∨ B / w ≠ 0) ↔ (A ≠ 0 ∨ B ≠ 0) := by
  constructor
  · rintro (h | h)
    · by_cases hB : B = 0
      · left; intro hA; apply h; rw [hA, hB]; simp
      · right; exact hB
    · right; intro hB; apply h; rw [hB]; simp
  · rintro (h | h)
    · by_cases hB : B = 0
      · left; rw [hB, mul_zero, add_zero]; exact div_ne_zero h hv
      · right; exact div_ne_zero hB hw
    · right; exact div_ne_zero h hw

theorem nonsingular_transport (x y : K) :
    (C • W).toAffine.Nonsingular (tx C x) (ty C x y) ↔ W.toAffine.Nonsingular x y := by
  have hu := u_ne_zero C
  rw [Affine.nonsingular_iff, Affine.nonsingular_iff, equation_transport]
  have hA : (C • W).a₁ * ty C x y - (3 * tx C x ^ 2 + 2 * (C • W).a₂ * tx C x + (C • W).a₄) =
      (W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) + C.s * (2 * y + W.a₁ * x + W.a₃)) /
        (C.u : K) ^ 4 := by
    simp only [variableChange_a₁, variableChange_a₂, variableChange_a₄, tx, ty,
      Units.val_inv_eq_inv_val]
    field_simp
    ring
  have hB : ty C x y - (-ty C x y - (C • W).a₁ * tx C x - (C • W).a₃) =
      (2 * y + W.a₁ * x + W.a₃) / (C.u : K) ^ 3 := by
    simp only [variableChange_a₁, variableChange_a₃, tx, ty, Units.val_inv_eq_inv_val]
    field_simp
    ring
  simp only [WeierstrassCurve.toAffine] at hA hB ⊢
  refine and_congr_right fun _ => ?_
  have iff1 : (ty C x y ≠ -ty C x y - (C • W).a₁ * tx C x - (C • W).a₃) ↔
      (2 * y + W.a₁ * x + W.a₃) / (C.u : K) ^ 3 ≠ 0 := by rw [← hB, sub_ne_zero]
  have iff2 : (W.a₁ * y ≠ 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) ↔
      W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) ≠ 0 := sub_ne_zero.symm
  have iff3 : (y ≠ -y - W.a₁ * x - W.a₃) ↔ 2 * y + W.a₁ * x + W.a₃ ≠ 0 := by
    rw [← sub_ne_zero]; ring_nf
  rw [← sub_ne_zero, hA, iff1, iff2, iff3]
  exact disj_aux (pow_ne_zero 4 hu) (pow_ne_zero 3 hu)

end BPModCurves
