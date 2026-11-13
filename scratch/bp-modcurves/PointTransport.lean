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

/-! ### MC2c: `Y₁(N)(K) ≃` Tate coordinates

`tateNF_unique`, `tateNF_Δ`, `tateNF_b_ne_zero` are copied from `TateNormalForm.lean`. -/

/-- **Uniqueness of the Tate normal form**: a change of variables fixing `(0, 0)` between two
Tate normal forms with `b ≠ 0` is the identity, and `(b, c) = (b', c')`. (`b ≠ 0` holds on
every elliptic `E(b, c)`: `b ∣ Δ(b, c)`.) -/
theorem tateNF_unique (b c b' c' : K) (hb : b ≠ 0) (C : VariableChange K)
    (hC : C • tateNF b c = tateNF b' c') (hr : C.r = 0) (ht : C.t = 0) :
    C = 1 ∧ b = b' ∧ c = c' := by
  have e1 := congrArg WeierstrassCurve.a₁ hC
  have e2 := congrArg WeierstrassCurve.a₂ hC
  have e3 := congrArg WeierstrassCurve.a₃ hC
  have e4 := congrArg WeierstrassCurve.a₄ hC
  simp only [variableChange_a₁, variableChange_a₂,
    variableChange_a₃, variableChange_a₄, tateNF, hr, ht,
    Units.val_inv_eq_inv_val] at e1 e2 e3 e4
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  have hs : C.s = 0 := by
    have : C.s * b = 0 := by
      have := e4; field_simp at this; linear_combination this
    exact (mul_eq_zero.1 this).resolve_right hb
  rw [hs] at e1 e2
  have hu1 : (C.u : K) = 1 := by
    have h23 : (C.u : K)⁻¹ ^ 2 * b = (C.u : K)⁻¹ ^ 3 * b := by
      linear_combination -e2 + e3
    field_simp at h23
    exact h23
  rw [hu1] at e1 e2
  refine ⟨?_, by linear_combination -e2, by linear_combination -e1⟩
  have hU : C.u = 1 := Units.val_eq_one.1 hu1
  rcases C with ⟨u, r, s, t⟩
  simp only at hr ht hs hU
  subst hr ht hs hU
  rfl

/-- The discriminant of the Tate normal form: `Δ(b,c) = b³(16b² − 8bc² − 20bc + b + c(c−1)³)`. -/
theorem tateNF_Δ (b c : K) : (tateNF b c).Δ =
    b ^ 3 * (16 * b ^ 2 - 8 * b * c ^ 2 - 20 * b * c + b + c * (c - 1) ^ 3) := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, tateNF]
  ring

theorem tateNF_b_ne_zero (b c : K) [(tateNF b c).IsElliptic] : b ≠ 0 := by
  intro hb
  have h := (tateNF b c).isUnit_Δ
  rw [tateNF_Δ, hb] at h
  simp at h

theorem tx_mul (C C' : VariableChange K) (x : K) : tx (C * C') x = tx C (tx C' x) := by
  have hu := u_ne_zero C
  have hu' := u_ne_zero C'
  simp only [tx, VariableChange.mul_def, Units.val_mul]
  field_simp
  ring

theorem ty_mul (C C' : VariableChange K) (x y : K) :
    ty (C * C') x y = ty C (tx C' x) (ty C' x y) := by
  have hu := u_ne_zero C
  have hu' := u_ne_zero C'
  simp only [tx, ty, VariableChange.mul_def, Units.val_mul]
  field_simp
  ring

theorem tx_one (x : K) : tx (1 : VariableChange K) x = x := by
  simp [tx, VariableChange.one_def]

theorem ty_one (x y : K) : ty (1 : VariableChange K) x y = y := by
  simp [ty, VariableChange.one_def]

theorem tx_inv (C : VariableChange K) (x : K) : tx C⁻¹ (tx C x) = x := by
  rw [← tx_mul, inv_mul_cancel, tx_one]

theorem ty_inv (C : VariableChange K) (x y : K) : ty C⁻¹ (tx C x) (ty C x y) = y := by
  rw [← ty_mul, inv_mul_cancel, ty_one]

theorem r_t_eq_zero (D : VariableChange K) (h1 : tx D 0 = 0) (h2 : ty D 0 0 = 0) :
    D.r = 0 ∧ D.t = 0 := by
  have hu := u_ne_zero D
  simp only [tx, ty, div_eq_zero_iff, pow_eq_zero_iff, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, hu, or_false, zero_sub, neg_eq_zero] at h1 h2
  rw [h1] at h2
  exact ⟨h1, by simpa using h2⟩

/-- The origin of `C • W` is the transport of `(x, y)` when `C.r = x`, `C.t = y`. -/
theorem origin_of_change [DecidableEq K] (W : WeierstrassCurve K) {x y : K}
    (h : W.toAffine.Nonsingular x y) (C : VariableChange K) (hr : C.r = x) (ht : C.t = y)
    (W' : WeierstrassCurve K) (hW : C • W = W') :
    ∃ h0 : W'.toAffine.Nonsingular 0 0,
      addOrderOf (Affine.Point.some 0 0 h0) = addOrderOf (Affine.Point.some x y h) := by
  subst hW
  have htx : tx C x = 0 := by simp [tx, hr]
  have hty : ty C x y = 0 := by simp [ty, hr, ht]
  have hns : (C • W).toAffine.Nonsingular 0 0 := by
    have := (nonsingular_transport W C x y).2 h
    rwa [htx, hty] at this
  refine ⟨hns, ?_⟩
  have e : (Affine.Point.some 0 0 hns : (C • W).toAffine.Point) =
      mapPt W C (Affine.Point.some x y h) := by
    simp only [mapPt, Affine.Point.some.injEq]; exact ⟨htx.symm, hty.symm⟩
  rw [e, addOrderOf_mapPt]

/-- **Level-`N` data**: an elliptic Weierstrass curve with an affine point of exact order `N`. -/
structure Y1Data (K : Type*) [Field K] [DecidableEq K] (N : ℕ) where
  W : WeierstrassCurve K
  ell : W.IsElliptic
  x : K
  y : K
  ns : W.toAffine.Nonsingular x y
  ord : addOrderOf (Affine.Point.some x y ns) = N

variable [DecidableEq K] {N : ℕ}

/-- Isomorphism of level-`N` data: a change of variables carrying the curve and the point. -/
def Y1Iso (p q : Y1Data K N) : Prop :=
  ∃ C : VariableChange K, C • p.W = q.W ∧ tx C p.x = q.x ∧ ty C p.x p.y = q.y

theorem y1Iso_equivalence : Equivalence (Y1Iso (K := K) (N := N)) where
  refl p := ⟨1, one_smul _ _, tx_one _, ty_one _ _⟩
  symm := by
    rintro p q ⟨C, hW, hx, hy⟩
    refine ⟨C⁻¹, ?_, ?_, ?_⟩
    · rw [← hW, inv_smul_smul]
    · rw [← hx, tx_inv]
    · rw [← hx, ← hy, ty_inv]
  trans := by
    rintro p q r ⟨C, hW, hx, hy⟩ ⟨C', hW', hx', hy'⟩
    refine ⟨C' * C, ?_, ?_, ?_⟩
    · rw [mul_smul, hW, hW']
    · rw [tx_mul, hx, hx']
    · rw [ty_mul, hx, hy, hy']

instance Y1Setoid : Setoid (Y1Data K N) := ⟨Y1Iso, y1Iso_equivalence⟩

/-- **`Y₁(N)(K)`**: level-`N` data up to isomorphism. -/
def Y1Points (K : Type*) [Field K] [DecidableEq K] (N : ℕ) := Quotient (Y1Setoid (K := K) (N := N))

/-- Tate coordinates of `Y₁(N)(K)`: `(b, c)` with `E(b,c)` elliptic and `(0,0)` of exact order `N`. -/
abbrev TateData (K : Type*) [Field K] [DecidableEq K] (N : ℕ) :=
  {bc : K × K // (tateNF bc.1 bc.2).IsElliptic ∧
    ∃ h0 : (tateNF bc.1 bc.2).toAffine.Nonsingular 0 0, addOrderOf (Affine.Point.some 0 0 h0) = N}

theorem exists_tate (hN : 4 ≤ N) (p : Y1Data K N) :
    ∃ bc : K × K, ∃ C : VariableChange K, C • p.W = tateNF bc.1 bc.2 ∧ C.r = p.x ∧ C.t = p.y := by
  obtain ⟨b, c, -, -, C, hC, hr, ht⟩ := exists_tateNF_order p.W p.ns N hN p.ord
  exact ⟨(b, c), C, hC, hr, ht⟩

/-- The Tate coordinates of a level-`N` datum. -/
noncomputable def tateOf (hN : 4 ≤ N) (p : Y1Data K N) : TateData K N := by
  refine ⟨Classical.choose (exists_tate hN p), ?_⟩
  obtain ⟨C, hC, hr, ht⟩ := Classical.choose_spec (exists_tate hN p)
  refine ⟨?_, ?_⟩
  · have := p.ell
    rw [← hC]; infer_instance
  · obtain ⟨h0, hord⟩ := origin_of_change p.W p.ns C hr ht _ hC
    exact ⟨h0, hord.trans p.ord⟩

theorem tateOf_spec (hN : 4 ≤ N) (p : Y1Data K N) :
    ∃ C : VariableChange K, C • p.W = tateNF (tateOf hN p).1.1 (tateOf hN p).1.2 ∧
      C.r = p.x ∧ C.t = p.y :=
  Classical.choose_spec (exists_tate hN p)

omit [DecidableEq K] in
/-- Two Tate normal forms related by a change of variables carrying origin to origin coincide. -/
theorem tate_eq_of_change (b c b' c' : K) [hE : (tateNF b c).IsElliptic] (D : VariableChange K)
    (hD : D • tateNF b c = tateNF b' c') (h1 : tx D 0 = 0) (h2 : ty D 0 0 = 0) :
    b = b' ∧ c = c' := by
  obtain ⟨hr, ht⟩ := r_t_eq_zero D h1 h2
  exact (tateNF_unique b c b' c' (tateNF_b_ne_zero b c) D hD hr ht).2

theorem tateOf_wd (hN : 4 ≤ N) (p q : Y1Data K N) (hpq : Y1Iso p q) :
    tateOf hN p = tateOf hN q := by
  obtain ⟨C, hW, hx, hy⟩ := hpq
  obtain ⟨Cp, hCp, hrp, htp⟩ := tateOf_spec hN p
  obtain ⟨Cq, hCq, hrq, htq⟩ := tateOf_spec hN q
  have hEp := (tateOf hN p).2.1
  set D := Cq * C * Cp⁻¹
  have hD : D • tateNF (tateOf hN p).1.1 (tateOf hN p).1.2 =
      tateNF (tateOf hN q).1.1 (tateOf hN q).1.2 := by
    rw [← hCp, ← hCq, ← hW]; simp only [D, mul_smul, inv_smul_smul]
  have hxp : tx Cp p.x = 0 := by simp [tx, hrp]
  have hyp : ty Cp p.x p.y = 0 := by simp [ty, hrp, htp]
  have hxq : tx Cq q.x = 0 := by simp [tx, hrq]
  have hyq : ty Cq q.x q.y = 0 := by simp [ty, hrq, htq]
  have e0 : tx Cp⁻¹ 0 = p.x := by have := tx_inv Cp p.x; rwa [hxp] at this
  have e0' : ty Cp⁻¹ 0 0 = p.y := by have := ty_inv Cp p.x p.y; rwa [hxp, hyp] at this
  have h1 : tx D 0 = 0 := by
    simp only [D, tx_mul]; rw [e0, hx, hxq]
  have h2 : ty D 0 0 = 0 := by
    simp only [D, ty_mul]
    rw [e0, e0', hx, hy, hyq]
  obtain ⟨eb, ec⟩ := tate_eq_of_change _ _ _ _ D hD h1 h2
  exact Subtype.ext (Prod.ext eb ec)

/-- **The moduli interpretation of `Y₁(N)` at the level of points (`N ≥ 4`)**: level-`N` data up to
change of variables are in bijection with the Tate coordinates `(b, c)` such that `E(b,c)` is
elliptic and `(0,0)` has exact order `N` (Kubert 1976, Table 3; Husemöller §4.4, UNVERIFIED). -/
noncomputable def y1PointsEquivTate (hN : 4 ≤ N) : Y1Points K N ≃ TateData K N where
  toFun := Quotient.lift (tateOf hN) (tateOf_wd hN)
  invFun bc := Quotient.mk _
    { W := tateNF bc.1.1 bc.1.2, ell := bc.2.1, x := 0, y := 0, ns := bc.2.2.choose,
      ord := bc.2.2.choose_spec }
  left_inv := by
    intro P
    induction P using Quotient.inductionOn with
    | h p =>
    apply Quotient.sound
    obtain ⟨Cp, hCp, hrp, htp⟩ := tateOf_spec hN p
    refine ⟨Cp⁻¹, ?_, ?_, ?_⟩
    · show Cp⁻¹ • tateNF (tateOf hN p).1.1 (tateOf hN p).1.2 = p.W
      rw [← hCp, inv_smul_smul]
    · show tx Cp⁻¹ 0 = p.x
      have hxp : tx Cp p.x = 0 := by simp [tx, hrp]
      have := tx_inv Cp p.x; rwa [hxp] at this
    · show ty Cp⁻¹ 0 0 = p.y
      have hxp : tx Cp p.x = 0 := by simp [tx, hrp]
      have hyp : ty Cp p.x p.y = 0 := by simp [ty, hrp, htp]
      have := ty_inv Cp p.x p.y; rwa [hxp, hyp] at this
  right_inv := by
    intro bc
    show tateOf hN _ = bc
    obtain ⟨C, hC, hr, ht⟩ := tateOf_spec hN
      { W := tateNF bc.1.1 bc.1.2, ell := bc.2.1, x := 0, y := 0, ns := bc.2.2.choose,
        ord := bc.2.2.choose_spec }
    have hE := bc.2.1
    obtain ⟨-, eb, ec⟩ := tateNF_unique bc.1.1 bc.1.2 _ _ (tateNF_b_ne_zero bc.1.1 bc.1.2) C hC hr ht
    exact (Subtype.ext (Prod.ext eb ec)).symm

end BPModCurves

#print axioms BPModCurves.mapPt_add
#print axioms BPModCurves.addOrderOf_mapPt
#print axioms BPModCurves.exists_tateNF_order
#print axioms BPModCurves.y1PointsEquivTate
