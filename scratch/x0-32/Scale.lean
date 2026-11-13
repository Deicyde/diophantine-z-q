import ZInQKernel.Contrib.TYZGenus.X0

noncomputable section
namespace ZInQ.Contrib.TYZGenus.X0

open WeierstrassCurve WeierstrassCurve.Affine

/-! ## §2.0 Scaling maps between short Weierstrass curves -/

section Scale

variable {F : Type*} [Field F] [DecidableEq F]

set_option linter.unusedSectionVars false

/-- `W, W'` are short Weierstrass curves (`a₁ = a₂ = a₃ = 0`) and `(x, y) ↦ (w²x, w³y)` maps `W`
to `W'`: `a₄' = w⁴a₄`, `a₆' = w⁶a₆`, `w ≠ 0`. -/
structure IsScale (W W' : WeierstrassCurve F) (w : F) : Prop where
  a₁ : W.a₁ = 0
  a₂ : W.a₂ = 0
  a₃ : W.a₃ = 0
  a₁' : W'.a₁ = 0
  a₂' : W'.a₂ = 0
  a₃' : W'.a₃ = 0
  a₄ : W'.a₄ = w ^ 4 * W.a₄
  a₆ : W'.a₆ = w ^ 6 * W.a₆
  ne : w ≠ 0

variable {W W' W'' : WeierstrassCurve F} {w w' : F}

theorem IsScale.nonsingular (hs : IsScale W W' w) {x y : F} (h : W.toAffine.Nonsingular x y) :
    W'.toAffine.Nonsingular (w ^ 2 * x) (w ^ 3 * y) := by
  rw [nonsingular_iff', equation_iff'] at h ⊢
  rw [hs.a₁, hs.a₂, hs.a₃] at h
  rw [hs.a₁', hs.a₂', hs.a₃', hs.a₄, hs.a₆]
  obtain ⟨he, hn⟩ := h
  have hw := hs.ne
  refine ⟨by linear_combination w ^ 6 * he, ?_⟩
  rcases hn with h | h
  · left
    intro h'
    apply h
    have : w ^ 4 * (0 * y - (3 * x ^ 2 + 2 * 0 * x + W.a₄)) = 0 := by linear_combination h'
    simpa [hw] using this
  · right
    intro h'
    apply h
    have : w ^ 3 * (y - (-y - 0 * x - 0)) = 0 := by linear_combination h'
    have := (mul_eq_zero.mp this).resolve_left (pow_ne_zero 3 hw)
    linear_combination this

/-- The scaling map `W(F) → W'(F)`, `(x, y) ↦ (w²x, w³y)`. -/
def scalePt (hs : IsScale W W' w) : W.toAffine.Point → W'.toAffine.Point
  | .zero => .zero
  | .some x y h => .some (w ^ 2 * x) (w ^ 3 * y) (hs.nonsingular h)

theorem scalePt_some (hs : IsScale W W' w) {x y : F} (h : W.toAffine.Nonsingular x y) :
    scalePt hs (.some x y h) = .some (w ^ 2 * x) (w ^ 3 * y) (hs.nonsingular h) := rfl

theorem scalePt_zero (hs : IsScale W W' w) : scalePt hs 0 = 0 := rfl

theorem IsScale.slope (hs : IsScale W W' w) (x₁ x₂ y₁ y₂ : F) :
    W'.toAffine.slope (w ^ 2 * x₁) (w ^ 2 * x₂) (w ^ 3 * y₁) (w ^ 3 * y₂) =
      w * W.toAffine.slope x₁ x₂ y₁ y₂ := by
  have hw := hs.ne
  by_cases hx : x₁ = x₂
  · have hx' : w ^ 2 * x₁ = w ^ 2 * x₂ := by rw [hx]
    by_cases hy : y₁ = W.toAffine.negY x₂ y₂
    · have hy' : w ^ 3 * y₁ = W'.toAffine.negY (w ^ 2 * x₂) (w ^ 3 * y₂) := by
        simp only [negY, hs.a₁, hs.a₃, hs.a₁', hs.a₃'] at hy ⊢
        rw [hy]; ring
      rw [slope_of_Y_eq hx hy, slope_of_Y_eq hx' hy', mul_zero]
    · have hy' : w ^ 3 * y₁ ≠ W'.toAffine.negY (w ^ 2 * x₂) (w ^ 3 * y₂) := by
        simp only [negY, hs.a₁, hs.a₃, hs.a₁', hs.a₃'] at hy ⊢
        intro h
        apply hy
        have : w ^ 3 * (y₁ - (-y₂ - 0 * x₂ - 0)) = 0 := by linear_combination h
        have := (mul_eq_zero.mp this).resolve_left (pow_ne_zero 3 hw)
        linear_combination this
      rw [slope_of_Y_ne hx hy, slope_of_Y_ne hx' hy']
      simp only [negY, hs.a₁, hs.a₂, hs.a₃, hs.a₁', hs.a₂', hs.a₃', hs.a₄]
      have key : ∀ N D : F, (w ^ 4 * N) / (w ^ 3 * D) = w * (N / D) := by
        intro N D
        rw [mul_div_mul_comm]
        congr 1
        field_simp
      rw [← key]
      congr 1 <;> ring
  · have hx' : w ^ 2 * x₁ ≠ w ^ 2 * x₂ := fun h => hx (mul_left_cancel₀ (pow_ne_zero 2 hw) h)
    rw [slope_of_X_ne hx, slope_of_X_ne hx']
    have : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
    field_simp

/-- **Scaling maps are additive.** -/
theorem scalePt_add (hs : IsScale W W' w) (P Q : W.toAffine.Point) :
    scalePt hs (P + Q) = scalePt hs P + scalePt hs Q := by
  have hw := hs.ne
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rfl
  · rfl
  · rfl
  · by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
    · have hxy' : w ^ 2 * x₁ = w ^ 2 * x₂ ∧
          w ^ 3 * y₁ = W'.toAffine.negY (w ^ 2 * x₂) (w ^ 3 * y₂) := by
        refine ⟨by rw [hxy.1], ?_⟩
        have := hxy.2
        simp only [negY, hs.a₁, hs.a₃, hs.a₁', hs.a₃'] at this ⊢
        rw [this]; ring
      rw [Point.add_of_Y_eq hxy.1 hxy.2, scalePt_some, scalePt_some,
        Point.add_of_Y_eq hxy'.1 hxy'.2]
      rfl
    · have hxy' : ¬(w ^ 2 * x₁ = w ^ 2 * x₂ ∧
          w ^ 3 * y₁ = W'.toAffine.negY (w ^ 2 * x₂) (w ^ 3 * y₂)) := by
        rintro ⟨h1, h2⟩
        apply hxy
        refine ⟨mul_left_cancel₀ (pow_ne_zero 2 hw) h1, ?_⟩
        simp only [negY, hs.a₁, hs.a₃, hs.a₁', hs.a₃'] at h2 ⊢
        have : w ^ 3 * (y₁ - (-y₂ - 0 * x₂ - 0)) = 0 := by linear_combination h2
        have := (mul_eq_zero.mp this).resolve_left (pow_ne_zero 3 hw)
        linear_combination this
      rw [Point.add_some hxy, scalePt_some, scalePt_some, scalePt_some, Point.add_some hxy',
        Point.some.injEq]
      have hsl := hs.slope x₁ x₂ y₁ y₂
      constructor
      · simp only [addX, hs.a₁, hs.a₂, hs.a₁', hs.a₂']
        rw [hsl]
        ring
      · simp only [addY, negAddY, addX, negY, hs.a₁, hs.a₂, hs.a₃, hs.a₁', hs.a₂', hs.a₃']
        rw [hsl]
        ring

/-- The scaling map as an additive homomorphism. -/
def scaleHom (hs : IsScale W W' w) : W.toAffine.Point →+ W'.toAffine.Point :=
  AddMonoidHom.mk' (scalePt hs) (scalePt_add hs)

theorem IsScale.comp (hs : IsScale W W' w) (hs' : IsScale W' W'' w') :
    IsScale W W'' (w' * w) where
  a₁ := hs.a₁
  a₂ := hs.a₂
  a₃ := hs.a₃
  a₁' := hs'.a₁'
  a₂' := hs'.a₂'
  a₃' := hs'.a₃'
  a₄ := by rw [hs'.a₄, hs.a₄]; ring
  a₆ := by rw [hs'.a₆, hs.a₆]; ring
  ne := mul_ne_zero hs'.ne hs.ne

theorem scalePt_comp (hs : IsScale W W' w) (hs' : IsScale W' W'' w') (P : W.toAffine.Point) :
    scalePt hs' (scalePt hs P) = scalePt (hs.comp hs') P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · simp only [scalePt_some, Point.some.injEq]
    constructor <;> ring

theorem scalePt_one (hs : IsScale W W 1) (P : W.toAffine.Point) : scalePt hs P = P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · simp [scalePt_some]

theorem scalePt_eq_of_eq (hs : IsScale W W' w) (hs' : IsScale W W' w') (he : w = w')
    (P : W.toAffine.Point) : scalePt hs P = scalePt hs' P := by
  subst he; rfl

end Scale

/-! ## §2.1 `X₀(32) = A` and `C₁` over `ℚ̄` -/

open ZInQ.Contrib.TYZDecomp.CurveA

/-- `C₁` over `ℚ̄`. -/
abbrev curveC1bar : WeierstrassCurve Qbar := curveC1.baseChange Qbar

/-- `C₁(ℚ̄)`. -/
abbrev PtC1 : Type := curveC1bar.toAffine.Point

@[simp] theorem curveC1bar_a₁ : curveC1bar.a₁ = 0 := by
  simp [curveC1bar, curveC1, shortCurve, WeierstrassCurve.baseChange]
@[simp] theorem curveC1bar_a₂ : curveC1bar.a₂ = 0 := by
  simp [curveC1bar, curveC1, shortCurve, WeierstrassCurve.baseChange]
@[simp] theorem curveC1bar_a₃ : curveC1bar.a₃ = 0 := by
  simp [curveC1bar, curveC1, shortCurve, WeierstrassCurve.baseChange]
@[simp] theorem curveC1bar_a₄ : curveC1bar.a₄ = -1 := by
  simp [curveC1bar, curveC1, shortCurve, WeierstrassCurve.baseChange]
@[simp] theorem curveC1bar_a₆ : curveC1bar.a₆ = 0 := by
  simp [curveC1bar, curveC1, shortCurve, WeierstrassCurve.baseChange]

theorem iQ_pow_four : iQ ^ 4 = 1 := by
  have h := iQ_sq
  calc iQ ^ 4 = (iQ ^ 2) ^ 2 := by ring
    _ = 1 := by rw [h]; norm_num

/-- `(x, y) ↦ (w²x, w³y)` with `w = (1 + i)/2` maps `A : y² = x³ + 4x` to `C₁ : y² = x³ − x`
(`w⁴ = −1/4`). -/
theorem isScale_iota : IsScale curveAbar curveC1bar ((1 + iQ) / 2) where
  a₁ := curveAbar_a₁
  a₂ := curveAbar_a₂
  a₃ := curveAbar_a₃
  a₁' := curveC1bar_a₁
  a₂' := curveC1bar_a₂
  a₃' := curveC1bar_a₃
  a₄ := by
    rw [curveC1bar_a₄, curveAbar_a₄]
    linear_combination (-(5 : Qbar) / 4 - iQ - 1 / 4 * iQ ^ 2) * iQ_sq
  a₆ := by rw [curveC1bar_a₆, curveAbar_a₆, mul_zero]
  ne := by
    intro h
    have h1 : iQ = -1 := by linear_combination 2 * h
    have := iQ_sq
    rw [h1] at this
    norm_num at this

/-- `(x, y) ↦ (w²x, w³y)` with `w = 1 − i` maps `C₁` to `A` (`w⁴ = −4`). -/
theorem isScale_iotaInv : IsScale curveC1bar curveAbar (1 - iQ) where
  a₁ := curveC1bar_a₁
  a₂ := curveC1bar_a₂
  a₃ := curveC1bar_a₃
  a₁' := curveAbar_a₁
  a₂' := curveAbar_a₂
  a₃' := curveAbar_a₃
  a₄ := by
    rw [curveC1bar_a₄, curveAbar_a₄]
    linear_combination (5 - 4 * iQ + iQ ^ 2) * iQ_sq
  a₆ := by rw [curveC1bar_a₆, curveAbar_a₆, mul_zero]
  ne := by
    intro h
    have h1 : iQ = 1 := by linear_combination -h
    have := iQ_sq
    rw [h1] at this
    norm_num at this

/-- **`A ≅ C₁` over `ℚ(i)`**: `ι(x, y) = (ix/2, (i − 1)y/4)`, an additive bijection
`A(ℚ̄) → C₁(ℚ̄)` with coefficients in `ℚ(i)`. -/
def iota : PtA →+ PtC1 := scaleHom isScale_iota

/-- The inverse of `ι`: `(x, y) ↦ (−2ix, −(2 + 2i)y)`. -/
def iotaInv : PtC1 →+ PtA := scaleHom isScale_iotaInv

theorem iota_some {x y : Qbar} (h : curveAbar.toAffine.Nonsingular x y) :
    iota (.some x y h) = .some (((1 + iQ) / 2) ^ 2 * x) (((1 + iQ) / 2) ^ 3 * y)
      (isScale_iota.nonsingular h) := rfl

theorem iotaInv_some {x y : Qbar} (h : curveC1bar.toAffine.Nonsingular x y) :
    iotaInv (.some x y h) = .some ((1 - iQ) ^ 2 * x) ((1 - iQ) ^ 3 * y)
      (isScale_iotaInv.nonsingular h) := rfl

theorem iotaInv_iota (P : PtA) : iotaInv (iota P) = P := by
  change scalePt isScale_iotaInv (scalePt isScale_iota P) = P
  rw [scalePt_comp]
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · simp only [scalePt_some, WeierstrassCurve.Affine.Point.some.injEq]
    constructor
    · linear_combination x * (-(3 : Qbar) / 4 + 1 / 4 * iQ ^ 2) * iQ_sq
    · linear_combination y * (-(7 : Qbar) / 8 + 1 / 2 * iQ ^ 2 - 1 / 8 * iQ ^ 4) * iQ_sq

theorem iota_iotaInv (Q : PtC1) : iota (iotaInv Q) = Q := by
  change scalePt isScale_iota (scalePt isScale_iotaInv Q) = Q
  rw [scalePt_comp]
  rcases Q with _ | ⟨x, y, h⟩
  · rfl
  · simp only [scalePt_some, WeierstrassCurve.Affine.Point.some.injEq]
    constructor
    · linear_combination x * (-(3 : Qbar) / 4 + 1 / 4 * iQ ^ 2) * iQ_sq
    · linear_combination y * (-(7 : Qbar) / 8 + 1 / 2 * iQ ^ 2 - 1 / 8 * iQ ^ 4) * iQ_sq

/-! ## §2.2 The `2`-isogenies `φ : A → C₁`, `ψ : C₁ → A` -/

/-- **`φ = ι ∘ (1 + [i]) : A → C₁`**, a `2`-isogeny with kernel `{O, (0, 0)}`; over `ℚ` it is
`(x, y) ↦ (y²/4x², y(x² − 4)/8x²)` (`phi_some`). -/
def phi : PtA →+ PtC1 := iota.comp (AddMonoidHom.id PtA + iHom)

/-- **`ψ = (1 − [i]) ∘ ι⁻¹ : C₁ → A`**, the dual `2`-isogeny; over `ℚ` it is
`(x, y) ↦ (y²/x², y(x² + 1)/x²)` (`psi_some`). -/
def psi : PtC1 →+ PtA := (AddMonoidHom.id PtA - iHom).comp iotaInv

theorem phi_apply (P : PtA) : phi P = iota (P + iPt P) := rfl

theorem psi_apply (Q : PtC1) : psi Q = iotaInv Q - iPt (iotaInv Q) := rfl

/-- **`ψ ∘ φ = [2]`.** -/
theorem psi_phi (P : PtA) : psi (phi P) = 2 • P := by
  rw [psi_apply, phi_apply, iotaInv_iota]
  have h1 : iPt (P + iPt P) = iPt P + iPt (iPt P) := iPt_add _ _
  rw [h1, iPt_iPt, two_nsmul]
  abel

/-- **`φ ∘ ψ = [2]`.** -/
theorem phi_psi (Q : PtC1) : phi (psi Q) = 2 • Q := by
  rw [phi_apply, psi_apply]
  have h1 : iPt (iotaInv Q - iPt (iotaInv Q)) = iPt (iotaInv Q) - iPt (iPt (iotaInv Q)) :=
    map_sub iHom _ _
  rw [h1, iPt_iPt]
  have h2 : iotaInv Q - iPt (iotaInv Q) + (iPt (iotaInv Q) - -iotaInv Q) = 2 • iotaInv Q := by
    rw [two_nsmul]; abel
  rw [h2, map_nsmul, iota_iotaInv]


theorem iQ_pow3 : iQ ^ 3 = -iQ := by linear_combination iQ * iQ_sq
theorem iQ_pow4 : iQ ^ 4 = 1 := by linear_combination (iQ ^ 2 - 1) * iQ_sq
theorem iQ_pow5 : iQ ^ 5 = iQ := by linear_combination (iQ ^ 3 - iQ) * iQ_sq
theorem iQ_pow6 : iQ ^ 6 = -1 := by linear_combination (iQ ^ 4 - iQ ^ 2 + 1) * iQ_sq
theorem iQ_pow7 : iQ ^ 7 = -iQ := by linear_combination (iQ ^ 5 - iQ ^ 3 + iQ) * iQ_sq
theorem iQ_pow8 : iQ ^ 8 = 1 := by linear_combination (iQ ^ 6 - iQ ^ 4 + iQ ^ 2 - 1) * iQ_sq

theorem two_ne_zero' : (2 : Qbar) ≠ 0 := two_ne_zero

open WeierstrassCurve.Affine in
/-- **`φ` over `ℚ`**: `φ(x, y) = (y²/4x², y(x² − 4)/8x²)` for `x ≠ 0`. -/
theorem phi_some {x y : Qbar} (h : curveAbar.toAffine.Nonsingular x y) (hx : x ≠ 0) :
    ∃ h' : curveC1bar.toAffine.Nonsingular (y ^ 2 / (4 * x ^ 2)) (y * (x ^ 2 - 4) / (8 * x ^ 2)),
      phi (.some x y h) = .some _ _ h' := by
  have hx' : x ≠ -x := by
    intro h0; apply hx; linear_combination h0 / 2
  have he := (nonsingular_iff' _ _).mp h |>.1
  rw [equation_iff'] at he
  simp only [curveAbar_a₁, curveAbar_a₂, curveAbar_a₃, curveAbar_a₄, curveAbar_a₆] at he
  rw [phi_apply, iPt_some, Point.add_of_X_ne hx', iota_some]
  have hsl : curveAbar.toAffine.slope x (-x) y (iQ * y) = (y - iQ * y) / (x - -x) :=
    slope_of_X_ne hx'
  have e1 : ((1 + iQ) / 2) ^ 2 * curveAbar.toAffine.addX x (-x)
      (curveAbar.toAffine.slope x (-x) y (iQ * y)) = y ^ 2 / (4 * x ^ 2) := by
    rw [hsl]
    simp only [addX, curveAbar_a₁, curveAbar_a₂]
    field_simp
    ring_nf
    simp only [iQ_sq, iQ_pow3, iQ_pow4, iQ_pow5, iQ_pow6]
    ring_nf
  have e2 : ((1 + iQ) / 2) ^ 3 * curveAbar.toAffine.addY x (-x) y
      (curveAbar.toAffine.slope x (-x) y (iQ * y)) = y * (x ^ 2 - 4) / (8 * x ^ 2) := by
    rw [hsl]
    simp only [addY, negAddY, negY, addX, curveAbar_a₁, curveAbar_a₂, curveAbar_a₃]
    field_simp
    ring_nf
    simp only [iQ_sq, iQ_pow3, iQ_pow4, iQ_pow5, iQ_pow6, iQ_pow7, iQ_pow8]
    ring_nf
    linear_combination (-64 * y) * he
  refine ⟨by
    rw [← e1, ← e2]
    exact isScale_iota.nonsingular (nonsingular_add h (nonsingular_iPt h) fun hxy => hx' hxy.1),
    ?_⟩
  simp only [Point.some.injEq]
  exact ⟨e1, e2⟩


open WeierstrassCurve.Affine in
/-- **`ψ` over `ℚ`**: `ψ(x, y) = (y²/x², y(x² + 1)/x²)` for `x ≠ 0`. -/
theorem psi_some {x y : Qbar} (h : curveC1bar.toAffine.Nonsingular x y) (hx : x ≠ 0) :
    ∃ h' : curveAbar.toAffine.Nonsingular (y ^ 2 / x ^ 2) (y * (x ^ 2 + 1) / x ^ 2),
      psi (.some x y h) = .some _ _ h' := by
  have he := (nonsingular_iff' _ _).mp h |>.1
  rw [equation_iff'] at he
  simp only [curveC1bar_a₁, curveC1bar_a₂, curveC1bar_a₃, curveC1bar_a₄, curveC1bar_a₆] at he
  have hv : (1 - iQ) ^ 2 ≠ 0 := pow_ne_zero 2 isScale_iotaInv.ne
  have hv2 : (1 - iQ) ^ 2 = -2 * iQ := by linear_combination iQ_sq
  have hv3 : (1 - iQ) ^ 3 = -2 - 2 * iQ := by linear_combination (3 - iQ) * iQ_sq
  have hi0 := iQ_ne_zero
  set X := (1 - iQ) ^ 2 * x with hX
  set Y := (1 - iQ) ^ 3 * y with hY
  rw [hv2] at hX
  rw [hv3] at hY
  have hX0 : X ≠ 0 := mul_ne_zero hv hx
  have hx' : X ≠ -X := by
    intro h0; apply hX0; linear_combination h0 / 2
  have hR : curveAbar.toAffine.Nonsingular X Y := isScale_iotaInv.nonsingular h
  rw [psi_apply, iotaInv_some, sub_eq_add_neg, iPt_some, Point.neg_some]
  have hnegY : curveAbar.toAffine.negY (-X) (iQ * Y) = -(iQ * Y) := by
    simp only [negY, curveAbar_a₁, curveAbar_a₃]; ring
  have hsl : curveAbar.toAffine.slope X (-X) Y (curveAbar.toAffine.negY (-X) (iQ * Y)) =
      (Y + iQ * Y) / (X - -X) := by
    rw [slope_of_X_ne hx', hnegY, sub_neg_eq_add]
  rw [Point.add_of_X_ne hx']
  have e1 : curveAbar.toAffine.addX X (-X)
      (curveAbar.toAffine.slope X (-X) Y (curveAbar.toAffine.negY (-X) (iQ * Y))) =
      y ^ 2 / x ^ 2 := by
    rw [hsl]
    simp only [addX, curveAbar_a₁, curveAbar_a₂, hX, hY]
    field_simp
    ring_nf
    simp only [iQ_sq, iQ_pow3, iQ_pow4, iQ_pow5, iQ_pow6, iQ_pow7, iQ_pow8]
    ring_nf
    done
  have e2 : curveAbar.toAffine.addY X (-X) Y
      (curveAbar.toAffine.slope X (-X) Y (curveAbar.toAffine.negY (-X) (iQ * Y))) =
      y * (x ^ 2 + 1) / x ^ 2 := by
    rw [hsl]
    simp only [addY, negAddY, negY, addX, curveAbar_a₁, curveAbar_a₂, curveAbar_a₃, hX, hY]
    field_simp
    ring_nf
    simp only [iQ_sq, iQ_pow3, iQ_pow4, iQ_pow5, iQ_pow6, iQ_pow7, iQ_pow8]
    ring_nf
    linear_combination (-8 * iQ * y) * he
  refine ⟨by
    rw [← e1, ← e2]
    exact nonsingular_add hR ((nonsingular_neg ..).mpr (nonsingular_iPt hR)) fun hxy => hx' hxy.1, ?_⟩
  simp only [Point.some.injEq]
  exact ⟨e1, e2⟩

end ZInQ.Contrib.TYZGenus.X0
