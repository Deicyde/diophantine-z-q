import ZInQKernel.Model.Field.Curve

/-!
# Point codes

Blueprint: `model/point-codes.md`, `model/field/point-code-properties.md`.

The code of a point of `E(K₀)` is the vector in `ℚ⁵`
`code O = (1, 0, 0, 0, 0)`, `code (x, y) = (0, x₀, x₁, y₀, y₁)` with `x = x₀ + x₁ s`,
`y = y₀ + y₁ s`, and `ι(n) = code ([n] P₀)`.

`iota n` must never be evaluated: the later chapters use astronomically large indices `n`, and
all reasoning about `iota` goes through the group law. It is marked `noncomputable` so that it
cannot be `#eval`ed by accident.
-/

namespace ZInQ

open WeierstrassCurve WeierstrassCurve.Affine

/-- The code of a point of `E(K₀)` in `ℚ⁵`. -/
def pointCode : genCurve.toAffine.Point → Fin 5 → ℚ
  | .zero => ![1, 0, 0, 0, 0]
  | .some x y _ => ![0, x.re, x.im, y.re, y.im]

/-- `ι(n) = code([n] P₀)`. -/
noncomputable def iota (n : ℤ) : Fin 5 → ℚ := pointCode (n • genP0)

theorem iota_def (n : ℤ) : iota n = pointCode (n • genP0) := rfl

/-- The carrier `D = 2 E(K₀)`. -/
def carrierD : AddSubgroup genCurve.toAffine.Point :=
  (zsmulAddGroupHom (α := genCurve.toAffine.Point) 2).range

theorem mem_carrierD {P : genCurve.toAffine.Point} : P ∈ carrierD ↔ ∃ Q, 2 • Q = P := by
  simp [carrierD, zsmulAddGroupHom, two_zsmul, two_nsmul]

/-- A canonical code is the code of a point of `E(K₀)`. -/
def IsCanonicalCode (c : Fin 5 → ℚ) : Prop := ∃ P : genCurve.toAffine.Point, pointCode P = c

/-- A code of a point of the carrier `D = 2 E(K₀)`. -/
def IsCarrierCode (c : Fin 5 → ℚ) : Prop := ∃ P ∈ carrierD, pointCode P = c

/-- Negating the last two coordinates of a code. -/
def negCode (c : Fin 5 → ℚ) : Fin 5 → ℚ := ![c 0, c 1, c 2, -c 3, -c 4]

@[simp] theorem pointCode_zero : pointCode 0 = ![1, 0, 0, 0, 0] := rfl

@[simp] theorem pointCode_some {x y : K0} (h : genCurve.toAffine.Nonsingular x y) :
    pointCode (.some x y h) = ![0, x.re, x.im, y.re, y.im] := rfl

/-! ### Elementary properties of codes -/

/-- The first coordinate of a code is `1` for `O` and `0` for every affine point. -/
theorem pointCode_apply_zero (P : genCurve.toAffine.Point) :
    pointCode P 0 = if P = 0 then 1 else 0 := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · simp [Point.some_ne_zero]

theorem pointCode_apply_zero_eq_one_iff (P : genCurve.toAffine.Point) :
    pointCode P 0 = 1 ↔ P = 0 := by
  rw [pointCode_apply_zero]; split_ifs <;> simp_all

/-- Codes are injective. -/
theorem pointCode_injective : Function.Injective pointCode := by
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) h
  · rfl
  · have := congrFun h 0; simp [pointCode] at this
  · have := congrFun h 0; simp [pointCode] at this
  · have h1 := congrFun h 1
    have h2 := congrFun h 2
    have h3 := congrFun h 3
    have h4 := congrFun h 4
    simp at h1 h2 h3 h4
    simp only [Point.some.injEq]
    exact ⟨QuadraticAlgebra.ext h1 h2, QuadraticAlgebra.ext h3 h4⟩

/-- `code(-Q)` is `code(Q)` with its last two coordinates negated. -/
theorem pointCode_neg (P : genCurve.toAffine.Point) : pointCode (-P) = negCode (pointCode P) := by
  rcases P with _ | ⟨x, y, h⟩
  · ext i; fin_cases i <;> rfl
  · rw [Point.neg_some]
    ext i; fin_cases i <;> simp [negCode, pointCode, genCurve]

theorem pointCode_neg_apply (P : genCurve.toAffine.Point) (i : Fin 5) :
    pointCode (-P) i = if 3 ≤ i.val then -pointCode P i else pointCode P i := by
  rw [pointCode_neg]; fin_cases i <;> simp [negCode]

/-- `ι(0) = (1, 0, 0, 0, 0)`. -/
theorem iota_zero : iota 0 = ![1, 0, 0, 0, 0] := by
  rw [iota_def, zero_zsmul]; rfl

/-- `ι(-n)` is `ι(n)` with its last two coordinates negated. -/
theorem iota_neg (n : ℤ) : iota (-n) = negCode (iota n) := by
  rw [iota_def, iota_def, neg_zsmul, pointCode_neg]

/-- `ι(1) = (0, 1641/8, -145, -15465/4, 87483/32)`. -/
theorem iota_one : iota 1 = ![0, 1641 / 8, -145, -15465 / 4, 87483 / 32] := by
  rw [iota_def, one_zsmul]; rfl

/-- `ι(a)` and `ι(b)` are the codes of `[a]P₀` and `[b]P₀`, whose sum has code `ι(a + b)`. -/
theorem iota_add (a b : ℤ) : pointCode (a • genP0 + b • genP0) = iota (a + b) := by
  rw [iota_def, add_zsmul]

theorem iota_isCanonicalCode (n : ℤ) : IsCanonicalCode (iota n) := ⟨_, rfl⟩

/-- If `P₀` has infinite order (Proposition 3.1), distinct indices have distinct codes. -/
theorem iota_injective_of_addOrderOf_eq_zero (h : addOrderOf genP0 = 0) :
    Function.Injective iota := by
  intro a b hab
  have h1 : a • genP0 = b • genP0 := pointCode_injective hab
  have h2 : (a - b) • genP0 = 0 := by simp [sub_zsmul, h1]
  have h3 := addOrderOf_dvd_iff_zsmul_eq_zero.mpr h2
  rw [h, Nat.cast_zero, zero_dvd_iff, sub_eq_zero] at h3
  exact h3

end ZInQ
