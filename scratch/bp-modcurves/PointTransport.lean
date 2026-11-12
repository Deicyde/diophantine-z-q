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

/-- **The slope transforms as `ℓ' = (ℓ − s)/u`** (for two points on `W`, not opposite). -/
theorem slope_transport [DecidableEq K] {x₁ x₂ y₁ y₂ : K} (h₁ : W.toAffine.Equation x₁ y₁)
    (h₂ : W.toAffine.Equation x₂ y₂) (hxy : ¬(x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂)) :
    (C • W).toAffine.slope (tx C x₁) (tx C x₂) (ty C x₁ y₁) (ty C x₂ y₂) =
      (W.toAffine.slope x₁ x₂ y₁ y₂ - C.s) / (C.u : K) := by
  have hu := u_ne_zero C
  by_cases hx : x₁ = x₂
  · subst hx
    have hy : y₁ ≠ W.toAffine.negY x₁ y₂ := fun h => hxy ⟨rfl, h⟩
    have hy12 : y₁ = y₂ := (Affine.Y_eq_of_X_eq h₁ h₂ rfl).resolve_right hy
    subst hy12
    have hy' : ty C x₁ y₁ ≠ (C • W).toAffine.negY (tx C x₁) (ty C x₁ y₁) := by
      rw [negY_transport]; intro h; exact hy (ty_inj C h)
    rw [Affine.slope_of_Y_ne rfl hy', Affine.slope_of_Y_ne rfl hy]
    have hden : ty C x₁ y₁ - (C • W).toAffine.negY (tx C x₁) (ty C x₁ y₁) =
        (y₁ - W.toAffine.negY x₁ y₁) / (C.u : K) ^ 3 := by
      rw [negY_transport]; simp only [ty]; field_simp; ring
    have hnum : 3 * tx C x₁ ^ 2 + 2 * (C • W).a₂ * tx C x₁ + (C • W).a₄ -
        (C • W).a₁ * ty C x₁ y₁ =
        (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁ - C.s * (y₁ - W.toAffine.negY x₁ y₁)) /
          (C.u : K) ^ 4 := by
      simp only [variableChange_a₁, variableChange_a₂, variableChange_a₄, tx, ty, Affine.negY,
        Units.val_inv_eq_inv_val]
      field_simp
      ring
    have hd0 : y₁ - W.toAffine.negY x₁ y₁ ≠ 0 := sub_ne_zero.2 hy
    simp only [WeierstrassCurve.toAffine] at hden hnum ⊢
    rw [hden, hnum]
    field_simp
  · have hx' : tx C x₁ ≠ tx C x₂ := fun h => hx (tx_inj C h)
    rw [Affine.slope_of_X_ne hx', Affine.slope_of_X_ne hx]
    have hd0 : x₁ - x₂ ≠ 0 := sub_ne_zero.2 hx
    have e1 : tx C x₁ - tx C x₂ = (x₁ - x₂) / (C.u : K) ^ 2 := by
      simp only [tx]; field_simp; ring
    have e2 : ty C x₁ y₁ - ty C x₂ y₂ = ((y₁ - y₂) - C.s * (x₁ - x₂)) / (C.u : K) ^ 3 := by
      simp only [ty]; field_simp; ring
    rw [e1, e2]
    field_simp

/-- The transport of points along a change of variables. -/
def mapPt : W.toAffine.Point → (C • W).toAffine.Point
  | .zero => 0
  | .some x y h => .some (tx C x) (ty C x y) ((nonsingular_transport W C x y).2 h)

/-- **The transport is additive.** -/
theorem mapPt_add [DecidableEq K] (P Q : W.toAffine.Point) :
    mapPt W C (P + Q) = mapPt W C P + mapPt W C Q := by
  have hu := u_ne_zero C
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rfl
  · rfl
  · rfl
  · by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
    · rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2]
      obtain ⟨rfl, rfl⟩ := hxy
      refine (Affine.Point.add_of_Y_eq rfl ?_).symm
      rw [negY_transport]
    · have hxy' : ¬(tx C x₁ = tx C x₂ ∧
          ty C x₁ y₁ = (C • W).toAffine.negY (tx C x₂) (ty C x₂ y₂)) := by
        rintro ⟨hx, hy⟩
        have hx' := tx_inj C hx
        subst hx'
        rw [negY_transport] at hy
        exact hxy ⟨rfl, ty_inj C hy⟩
      rw [Affine.Point.add_some hxy]
      simp only [mapPt]
      rw [Affine.Point.add_some hxy', Affine.Point.some.injEq]
      have hsl := slope_transport W C h₁.1 h₂.1 hxy
      rw [hsl]
      constructor
      · simp only [Affine.addX, variableChange_a₁, variableChange_a₂, tx,
          Units.val_inv_eq_inv_val, WeierstrassCurve.toAffine]
        field_simp
        ring
      · simp only [Affine.addY, Affine.negAddY, Affine.addX, Affine.negY, variableChange_a₁,
          variableChange_a₂, variableChange_a₃, tx, ty, Units.val_inv_eq_inv_val,
          WeierstrassCurve.toAffine]
        field_simp
        ring

/-- The transport as an additive homomorphism. -/
def mapPtHom [DecidableEq K] : W.toAffine.Point →+ (C • W).toAffine.Point where
  toFun := mapPt W C
  map_zero' := rfl
  map_add' := mapPt_add W C

theorem mapPt_injective : Function.Injective (mapPt W C) := by
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) h
  · rfl
  · exact absurd h (by simp [mapPt])
  · exact absurd h (by simp [mapPt])
  · simp only [mapPt, Affine.Point.some.injEq] at h
    obtain ⟨hx, hy⟩ := h
    have hx' := tx_inj C hx
    subst hx'
    have hy' := ty_inj C hy
    subst hy'
    rfl

/-- **Orders are preserved**: a change of variables carries a point of exact order `N` to a
point of exact order `N` (needed to package Tate normal form as `Y₁(N)(K) ≃ {(b,c)}`). -/
theorem addOrderOf_mapPt [DecidableEq K] (P : W.toAffine.Point) :
    addOrderOf (mapPt W C P) = addOrderOf P :=
  addOrderOf_injective (mapPtHom W C) (mapPt_injective W C) P

/-! ### Tate normal form with the order of the point (MC2c, existence half)

`tateNF`, `exists_tateNF_coord`, `not_two_torsion`, `not_flex`, `exists_tateNF` are copied from
`TateNormalForm.lean` (scratch files cannot import each other). -/

/-- The Tate normal form `E(b, c) : y² + (1 − c)xy − by = x³ − bx²`. -/
def tateNF (b c : K) : WeierstrassCurve K := ⟨1 - c, -b, -b, 0, 0⟩

theorem tateNF_equation_zero (b c : K) : (tateNF b c).toAffine.Equation 0 0 := by
  rw [Affine.equation_iff]; simp [tateNF]

/-- **Existence of the Tate normal form**, in coordinates: if `(x₀, y₀)` lies on `W`, is not
`2`-torsion (`y₀ ≠ −y₀ − a₁x₀ − a₃`) and not a flex (`x(2P) ≠ x₀`), then a change of variables
sending `(x₀, y₀)` to `(0, 0)` takes `W` to some `E(b, c)`. -/
theorem exists_tateNF_coord [DecidableEq K] (W : WeierstrassCurve K) (x₀ y₀ : K)
    (heq : W.toAffine.Equation x₀ y₀) (h2 : y₀ ≠ W.toAffine.negY x₀ y₀)
    (h3 : W.toAffine.addX x₀ x₀ (W.toAffine.slope x₀ x₀ y₀ y₀) ≠ x₀) :
    ∃ (C : VariableChange K) (b c : K), C • W = tateNF b c ∧ C.r = x₀ ∧ C.t = y₀ := by
  rw [Affine.equation_iff] at heq
  set d := 2 * y₀ + W.a₁ * x₀ + W.a₃ with hd
  have hd0 : d ≠ 0 := by
    intro h; apply h2; simp only [Affine.negY]; linear_combination h
  set ℓ := (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄ - W.a₁ * y₀) / d with hℓ
  have hsl : W.toAffine.slope x₀ x₀ y₀ y₀ = ℓ := by
    rw [Affine.slope_of_Y_ne rfl h2]; simp only [Affine.negY, hℓ, hd]; congr 1; ring
  set A2 := W.a₂ - ℓ * W.a₁ + 3 * x₀ - ℓ ^ 2 with hA2
  have hA20 : A2 ≠ 0 := by
    intro h; apply h3; rw [hsl]; simp only [Affine.addX]; linear_combination -h
  have hu0 : d / A2 ≠ 0 := div_ne_zero hd0 hA20
  have hℓd : ℓ * d = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄ - W.a₁ * y₀ := by
    rw [hℓ]; field_simp
  clear_value d ℓ A2
  refine ⟨⟨Units.mk0 (d / A2) hu0, x₀, ℓ, y₀⟩, -(A2 / (d / A2) ^ 2),
    1 - (W.a₁ + 2 * ℓ) / (d / A2), ?_, rfl, rfl⟩
  ext
  · simp only [variableChange_a₁, tateNF, Units.val_inv_eq_inv_val, Units.val_mk0]
    ring
  · simp only [variableChange_a₂, tateNF, Units.val_inv_eq_inv_val, Units.val_mk0]
    rw [← hA2]; field_simp
  · simp only [variableChange_a₃, tateNF, Units.val_inv_eq_inv_val, Units.val_mk0]
    rw [show W.a₃ + x₀ * W.a₁ + 2 * y₀ = d by rw [hd]; ring]; field_simp
  · simp only [variableChange_a₄, tateNF, Units.val_inv_eq_inv_val, Units.val_mk0]
    rw [mul_eq_zero]; right
    linear_combination -hℓd + ℓ * hd
  · simp only [variableChange_a₆, tateNF, Units.val_inv_eq_inv_val, Units.val_mk0]
    rw [mul_eq_zero]; right
    linear_combination -heq

/-- The order hypotheses in terms of Mathlib's group of points. -/
theorem not_two_torsion [DecidableEq K] (W : WeierstrassCurve K) {x₀ y₀ : K}
    (h : W.toAffine.Nonsingular x₀ y₀)
    (h2P : (Affine.Point.some x₀ y₀ h) + (Affine.Point.some x₀ y₀ h) ≠ 0) :
    y₀ ≠ W.toAffine.negY x₀ y₀ := fun hy => h2P (Affine.Point.add_self_of_Y_eq hy)

theorem not_flex [DecidableEq K] (W : WeierstrassCurve K) {x₀ y₀ : K}
    (h : W.toAffine.Nonsingular x₀ y₀)
    (h2P : (Affine.Point.some x₀ y₀ h) + (Affine.Point.some x₀ y₀ h) ≠ 0)
    (h3P : (Affine.Point.some x₀ y₀ h) + (Affine.Point.some x₀ y₀ h) +
      (Affine.Point.some x₀ y₀ h) ≠ 0) :
    W.toAffine.addX x₀ x₀ (W.toAffine.slope x₀ x₀ y₀ y₀) ≠ x₀ := by
  intro hx
  have hy := not_two_torsion W h h2P
  set P := Affine.Point.some x₀ y₀ h
  have hPP := Affine.Point.add_self_of_Y_ne (h₁ := h) hy
  rcases (Affine.Point.X_eq_iff (h₁ := Affine.nonsingular_add h h fun hxy => hy hxy.right)
    (h₂ := h)).1 hx with e | e
  · rw [← hPP] at e
    have : P = 0 := by
      simpa using congrArg (· - P) e
    exact Affine.Point.some_ne_zero h this
  · rw [← hPP] at e
    apply h3P; rw [e, neg_add_cancel]

/-- **Existence of the Tate normal form** for a point `P` with `2P ≠ 0`, `3P ≠ 0`. -/
theorem exists_tateNF [DecidableEq K] (W : WeierstrassCurve K) {x₀ y₀ : K}
    (h : W.toAffine.Nonsingular x₀ y₀)
    (h2P : (Affine.Point.some x₀ y₀ h) + (Affine.Point.some x₀ y₀ h) ≠ 0)
    (h3P : (Affine.Point.some x₀ y₀ h) + (Affine.Point.some x₀ y₀ h) +
      (Affine.Point.some x₀ y₀ h) ≠ 0) :
    ∃ (C : VariableChange K) (b c : K), C • W = tateNF b c ∧ C.r = x₀ ∧ C.t = y₀ :=
  exists_tateNF_coord W x₀ y₀ h.1 (not_two_torsion W h h2P) (not_flex W h h2P h3P)

/-- **Moduli of `Y₁(N)` at the level of points, existence half**: a point `P` of exact order
`N ≥ 4` on `W` is carried by a change of variables to the point `(0,0)` of some `E(b,c)`, and
`(0,0)` has exact order `N` there. -/
theorem exists_tateNF_order [DecidableEq K] (W : WeierstrassCurve K) {x₀ y₀ : K}
    (h : W.toAffine.Nonsingular x₀ y₀) (N : ℕ) (hN : 4 ≤ N)
    (hP : addOrderOf (Affine.Point.some x₀ y₀ h) = N) :
    ∃ (b c : K) (h0 : (tateNF b c).toAffine.Nonsingular 0 0),
      addOrderOf (Affine.Point.some 0 0 h0) = N ∧
      ∃ C : VariableChange K, C • W = tateNF b c ∧ C.r = x₀ ∧ C.t = y₀ := by
  set P := Affine.Point.some x₀ y₀ h with hPdef
  have h2P : P + P ≠ 0 := by
    intro h2
    have : addOrderOf P ∣ 2 := addOrderOf_dvd_of_nsmul_eq_zero (by rw [two_nsmul]; exact h2)
    have := Nat.le_of_dvd (by norm_num) this; omega
  have h3P : P + P + P ≠ 0 := by
    intro h3
    have : addOrderOf P ∣ 3 := addOrderOf_dvd_of_nsmul_eq_zero (by
      rw [show (3 : ℕ) = 2 + 1 from rfl, succ_nsmul, two_nsmul]; exact h3)
    have := Nat.le_of_dvd (by norm_num) this; omega
  obtain ⟨C, b, c, hC, hr, ht⟩ := exists_tateNF W h h2P h3P
  have htx : tx C x₀ = 0 := by simp [tx, hr]
  have hty : ty C x₀ y₀ = 0 := by simp [ty, hr, ht]
  have key : ∀ W' : WeierstrassCurve K, C • W = W' →
      ∃ h0 : W'.toAffine.Nonsingular 0 0, addOrderOf (Affine.Point.some 0 0 h0) = N := by
    intro W' hW
    subst hW
    have hns : (C • W).toAffine.Nonsingular 0 0 := by
      have := (nonsingular_transport W C x₀ y₀).2 h
      rwa [htx, hty] at this
    refine ⟨hns, ?_⟩
    have e : (Affine.Point.some 0 0 hns : (C • W).toAffine.Point) = mapPt W C P := by
      simp only [hPdef, mapPt, Affine.Point.some.injEq]; exact ⟨htx.symm, hty.symm⟩
    rw [e, addOrderOf_mapPt, hP]
  obtain ⟨h0, hord⟩ := key _ hC
  exact ⟨b, c, h0, hord, C, hC, hr, ht⟩

end BPModCurves

#print axioms BPModCurves.mapPt_add
#print axioms BPModCurves.addOrderOf_mapPt
#print axioms BPModCurves.exists_tateNF_order
