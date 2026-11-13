import ZInQKernel.Multiplication.Local.FormalGroup

/-!
# Points of `y² = x³ + A x` under a field embedding

For a ring homomorphism `f : K →+* L` of fields and `B = f(A)`, `mapPt f hB` sends
`(x, y) ↦ (f x, f y)`; it is a group homomorphism `W_A(K) → W_B(L)` (`mapPt_add`,
`mapPtHom`) commuting with `z = -x/y`. It is used to regard points of `E(K₀)` as points over a
completion `K_π`.
-/

namespace ZInQ.Mult

open WeierstrassCurve WeierstrassCurve.Affine

variable {K L : Type*} [Field K] [Field L] (f : K →+* L) {A : K} {B : L}

theorem shortCurve_map (hB : f A = B) : shortCurve B = (shortCurve A).map f := by
  subst hB; ext <;> simp [shortCurve]

theorem nonsingular_map (hB : f A = B) {x y : K} (h : (shortCurve A).toAffine.Nonsingular x y) :
    (shortCurve B).toAffine.Nonsingular (f x) (f y) := by
  rw [shortCurve_map f hB]
  exact (Affine.map_nonsingular (W := (shortCurve A).toAffine) f.injective x y).mpr h

/-- The image of a point of `y² = x³ + A x` over `K` in `y² = x³ + B x` over `L`, `B = f(A)`. -/
def mapPt (hB : f A = B) : (shortCurve A).toAffine.Point → (shortCurve B).toAffine.Point
  | 0 => 0
  | .some x y h => .some (f x) (f y) (nonsingular_map f hB h)

@[simp] theorem mapPt_zero (hB : f A = B) : mapPt f hB 0 = 0 := rfl

@[simp] theorem mapPt_some (hB : f A = B) {x y : K} (h : (shortCurve A).toAffine.Nonsingular x y) :
    mapPt f hB (.some x y h) = .some (f x) (f y) (nonsingular_map f hB h) := rfl

variable [DecidableEq K] [DecidableEq L]

theorem mapPt_add (hB : f A = B) (P Q : (shortCurve A).toAffine.Point) :
    mapPt f hB (P + Q) = mapPt f hB P + mapPt f hB Q := by
  have hW := shortCurve_map f hB
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · rw [point_zero_eq, zero_add, mapPt_zero, zero_add]
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rw [point_zero_eq, add_zero, mapPt_zero, add_zero]
  by_cases hxy : x₁ = x₂ ∧ y₁ = (shortCurve A).toAffine.negY x₂ y₂
  · rw [Point.add_of_Y_eq hxy.1 hxy.2, mapPt_zero, mapPt_some, mapPt_some,
      Point.add_of_Y_eq (congrArg f hxy.1)]
    rw [hxy.2, shortCurve_negY, shortCurve_negY, map_neg]
  · have hxy' : ¬(f x₁ = f x₂ ∧ f y₁ = (shortCurve B).toAffine.negY (f x₂) (f y₂)) := by
      rintro ⟨h1, h2⟩
      refine hxy ⟨f.injective h1, f.injective ?_⟩
      rw [h2, shortCurve_negY, shortCurve_negY, map_neg]
    rw [Point.add_some hxy, mapPt_some, mapPt_some, mapPt_some, Point.add_some hxy']
    have hs : (shortCurve B).toAffine.slope (f x₁) (f x₂) (f y₁) (f y₂) =
        f ((shortCurve A).toAffine.slope x₁ x₂ y₁ y₂) := by
      rw [hW]; exact Affine.map_slope (W := (shortCurve A).toAffine) f x₁ x₂ y₁ y₂
    simp only [Point.some.injEq]
    constructor
    · rw [hs, hW]; exact (Affine.map_addX (W' := (shortCurve A).toAffine) f _ _ _).symm
    · rw [hs, hW]; exact (Affine.map_addY (W' := (shortCurve A).toAffine) f _ _ _ _).symm

/-- `mapPt` as a group homomorphism. -/
def mapPtHom (hB : f A = B) : (shortCurve A).toAffine.Point →+ (shortCurve B).toAffine.Point where
  toFun := mapPt f hB
  map_zero' := rfl
  map_add' := mapPt_add f hB

omit [DecidableEq K] [DecidableEq L] in
theorem zCoord_mapPt (hB : f A = B) (P : (shortCurve A).toAffine.Point) :
    zCoord (mapPt f hB P) = f (zCoord P) := by
  rcases P with _ | ⟨x, y, h⟩
  · rw [point_zero_eq, mapPt_zero, zCoord_zero, zCoord_zero, map_zero]
  · simp [map_div₀]

end ZInQ.Mult
