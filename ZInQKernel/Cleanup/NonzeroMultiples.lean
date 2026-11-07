import ZInQKernel.Compiler.Precision.Relation
import ZInQKernel.Multiplication.Local.FormalGroup

/-!
# Nonzero multiples of the generator

Blueprint: `model/descent/nonzero-multiples.md`.

`P₀` has infinite order (`genP0_not_isOfFinAddOrder`) and `ι` is injective (`iota_injective`),
both in `Model/Generator/InfiniteOrder.lean`. Here: for `m ≠ 0`, `[m]P₀` is affine with nonzero
abscissa and ordinate, `z([m]P₀) = -x/y` and `w([m]P₀) = 1/x` are nonzero, and the first
coordinate of `ι(m)` is `0` exactly when `m ≠ 0`. The affine part with nonzero ordinate is the
admissibility guard of the precision chapter (`Compiler.Precision.admissible_of_ne_zero`).
-/

namespace ZInQ

open WeierstrassCurve WeierstrassCurve.Affine

/-- `[m]P₀ = O` exactly when `m = 0`. -/
theorem zsmul_genP0_eq_zero_iff {m : ℤ} : m • genP0 = 0 ↔ m = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, zero_zsmul]⟩
  by_contra hm
  exact genP0_not_isOfFinAddOrder (isOfFinAddOrder_iff_zsmul_eq_zero.mpr ⟨m, hm, h⟩)

/-- For `m ≠ 0`, `[m]P₀ = (x, y)` is affine with `x ≠ 0` and `y ≠ 0`. -/
theorem zsmul_genP0_affine {m : ℤ} (hm : m ≠ 0) :
    ∃ (x y : K0) (h : genCurve.toAffine.Nonsingular x y), m • genP0 = .some x y h ∧
      x ≠ 0 ∧ y ≠ 0 := by
  obtain ⟨x, y, h, e, hy⟩ := Compiler.Precision.admissible_of_ne_zero hm
  exact ⟨x, y, h, e, Compiler.Precision.x_ne_zero_of_y_ne_zero h.1 hy, hy⟩

/-- **Nonzero multiples of the generator.** For `m ≠ 0`, `[m]P₀ = (x, y)` is affine, `x ≠ 0`,
`y ≠ 0`, and `z = -x/y` and `w = 1/x` are nonzero. -/
theorem zsmul_genP0_affine_z_w {m : ℤ} (hm : m ≠ 0) :
    ∃ (x y : K0) (h : genCurve.toAffine.Nonsingular x y), m • genP0 = .some x y h ∧
      x ≠ 0 ∧ y ≠ 0 ∧ -x / y ≠ 0 ∧ 1 / x ≠ 0 := by
  obtain ⟨x, y, h, e, hx, hy⟩ := zsmul_genP0_affine hm
  exact ⟨x, y, h, e, hx, hy, div_ne_zero (neg_ne_zero.mpr hx) hy, one_div_ne_zero hx⟩

/-- `z([m]P₀) ≠ 0` for `m ≠ 0` (the coordinate `z` of the precision chapter). -/
theorem zIdx_ne_zero_of_ne_zero {m : ℤ} (hm : m ≠ 0) : Compiler.Precision.zIdx m ≠ 0 :=
  Compiler.Precision.zIdx_ne_zero (Compiler.Precision.admissible_of_ne_zero hm)

/-- `z([m]P₀) ≠ 0` for `m ≠ 0` (the coordinate `z` of the multiplication chapter). -/
theorem mult_zCoord_zsmul_genP0_ne_zero {m : ℤ} (hm : m ≠ 0) :
    Mult.zCoord (A := -genD ^ 2) (m • genP0) ≠ 0 := by
  obtain ⟨x, y, h, e, hx, hy, hz, -⟩ := zsmul_genP0_affine_z_w hm
  rw [e]
  exact hz

/-- `w([m]P₀) ≠ 0` for `m ≠ 0` (the coordinate `w` of the multiplication chapter). -/
theorem mult_wCoord_zsmul_genP0_ne_zero {m : ℤ} (hm : m ≠ 0) :
    Mult.wCoord (A := -genD ^ 2) (m • genP0) ≠ 0 := by
  obtain ⟨x, y, h, e, hx, hy, -, hw⟩ := zsmul_genP0_affine_z_w hm
  rw [e]
  exact hw

/-- The first coordinate of `ι(m)` is `0` exactly when `m ≠ 0`. -/
theorem iota_zero_coord_iff {m : ℤ} : iota m 0 = 0 ↔ m ≠ 0 := by
  rw [iota_def, pointCode_apply_zero]
  split_ifs with h
  · simp [zsmul_genP0_eq_zero_iff.mp h]
  · simp only [true_iff]
    rintro rfl
    exact h (zero_zsmul _)

/-- The first coordinate of `ι(m)` is `1` exactly when `m = 0`. -/
theorem iota_zero_coord_eq_one_iff {m : ℤ} : iota m 0 = 1 ↔ m = 0 := by
  rw [iota_def, pointCode_apply_zero_eq_one_iff, zsmul_genP0_eq_zero_iff]

end ZInQ
