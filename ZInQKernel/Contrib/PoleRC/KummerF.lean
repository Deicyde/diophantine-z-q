import ZInQKernel.Contrib.PoleRC.KummerM

/-!
# The complete 2-descent of `E_ℓ` over an arbitrary field (characteristic not 2 or 3)

`KummerM.lean` and `DescentM.lean` do this over `ℚ`; the proofs are field-generic except for a
few order-theoretic steps, which are replaced here by the hypotheses `2 ≠ 0`, `3 ≠ 0` in `F`.
Used in `LocalGood.lean` with `F = 𝔽_p`.

* `curveF ℓ : y² = x(x − ℓ)(x + 3ℓ)` over `F`; nonsingular for `ℓ ≠ 0` (`Δ = 2304ℓ⁶`).
* `kumF ℓ e`: the Kummer map at the root `e` (Silverman X.1.4; S12 lines 233–241: the class of
  `x − e`, replaced at `(e, 0)` by `f'(e) = ∏_{j ≠ i}(e − e_j)`, and `1` at `O`); `kumF_add`: a
  homomorphism. `deltaF ℓ = (kumF ℓ (−3ℓ), kumF ℓ ℓ)`: S12's coordinates `(x + 3ℓ, x − ℓ)`.
* `exists_two_nsmul_eq_F`: the halving lemma; `deltaF_ker`: `ker δ = 2E(F)` (S12 line 241:
  "The Kummer map is an injection of `E(k)/2E(k)`").
* `four_le_card_ker_two`: the four points `O, (0, 0), (ℓ, 0), (−3ℓ, 0)` of `E(F)[2]`.
-/

namespace ZInQ.Manuscript.PoleRC

open WeierstrassCurve WeierstrassCurve.Affine ZInQ.Descent Polynomial

variable {F : Type*} [Field F]

/-- `E_ℓ : y² = x(x − ℓ)(x + 3ℓ) = x³ + 2ℓx² − 3ℓ²x` over a field `F`. -/
def curveF (ℓ : F) : WeierstrassCurve F := ⟨0, 2 * ℓ, 0, -3 * ℓ ^ 2, 0⟩

variable {ℓ : F}

theorem curveF_equation_iff (x y : F) :
    (curveF ℓ).toAffine.Equation x y ↔ y ^ 2 = x ^ 3 + 2 * ℓ * x ^ 2 - 3 * ℓ ^ 2 * x := by
  rw [Affine.equation_iff]
  simp only [curveF]
  constructor <;> intro h <;> linear_combination h

@[simp] theorem curveF_a₁ : (curveF ℓ).a₁ = 0 := rfl
@[simp] theorem curveF_a₂ : (curveF ℓ).a₂ = 2 * ℓ := rfl
@[simp] theorem curveF_a₃ : (curveF ℓ).a₃ = 0 := rfl
@[simp] theorem curveF_a₄ : (curveF ℓ).a₄ = -3 * ℓ ^ 2 := rfl
@[simp] theorem curveF_a₆ : (curveF ℓ).a₆ = 0 := rfl

theorem curveF_negY (x y : F) : (curveF ℓ).toAffine.negY x y = -y := by
  simp [Affine.negY, curveF]

theorem curveF_Δ : (curveF ℓ).Δ = 2304 * ℓ ^ 6 := by
  simp only [curveF, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]; ring

theorem curveF_Δ_ne_zero (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hℓ : ℓ ≠ 0) :
    (curveF ℓ).Δ ≠ 0 := by
  rw [curveF_Δ, show (2304 : F) = 2 ^ 8 * 3 ^ 2 by norm_num]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)) (pow_ne_zero _ hℓ)

theorem curveF_nonsingular (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hℓ : ℓ ≠ 0) {x y : F}
    (h : (curveF ℓ).toAffine.Equation x y) : (curveF ℓ).toAffine.Nonsingular x y :=
  (equation_iff_nonsingular_of_Δ_ne_zero (curveF_Δ_ne_zero h2 h3 hℓ)).mp h

/-- `e` is a root of `x³ + 2ℓx² − 3ℓ²x`. -/
def IsRootF (ℓ e : F) : Prop := e ^ 3 + 2 * ℓ * e ^ 2 - 3 * ℓ ^ 2 * e = 0

/-- `f'(e) = 3e² + 4ℓe − 3ℓ²`. -/
def fdF (ℓ e : F) : F := 3 * e ^ 2 + 4 * ℓ * e - 3 * ℓ ^ 2

theorem isRootF_neg3 (ℓ : F) : IsRootF ℓ (-3 * ℓ) := by unfold IsRootF; ring
theorem isRootF_ell (ℓ : F) : IsRootF ℓ ℓ := by unfold IsRootF; ring
theorem isRootF_zero (ℓ : F) : IsRootF ℓ 0 := by unfold IsRootF; ring

theorem isRootF_cases {e : F} (he : IsRootF ℓ e) : e = 0 ∨ e = ℓ ∨ e = -3 * ℓ := by
  have h : e * (e - ℓ) * (e + 3 * ℓ) = 0 := by unfold IsRootF at he; linear_combination he
  rcases mul_eq_zero.mp h with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (by linear_combination h))
  · exact Or.inr (Or.inr (by linear_combination h))

theorem fdF_ne_zero (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hℓ : ℓ ≠ 0) {e : F}
    (he : IsRootF ℓ e) : fdF ℓ e ≠ 0 := by
  unfold fdF
  rcases isRootF_cases he with h | h | h <;> rw [h]
  · rw [show 3 * (0 : F) ^ 2 + 4 * ℓ * 0 - 3 * ℓ ^ 2 = -3 * ℓ ^ 2 by ring]
    exact mul_ne_zero (neg_ne_zero.mpr h3) (pow_ne_zero 2 hℓ)
  · rw [show 3 * ℓ ^ 2 + 4 * ℓ * ℓ - 3 * ℓ ^ 2 = 2 * 2 * ℓ ^ 2 by ring]
    exact mul_ne_zero (mul_ne_zero h2 h2) (pow_ne_zero 2 hℓ)
  · rw [show 3 * (-3 * ℓ) ^ 2 + 4 * ℓ * (-3 * ℓ) - 3 * ℓ ^ 2 = 2 * 2 * 3 * ℓ ^ 2 by ring]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero h2 h2) h3) (pow_ne_zero 2 hℓ)

theorem fdF_neg3 : fdF ℓ (-3 * ℓ) = 12 * ℓ ^ 2 := by unfold fdF; ring
theorem fdF_ell : fdF ℓ ℓ = 4 * ℓ ^ 2 := by unfold fdF; ring

variable [DecidableEq F]

/-- **The Kummer map of `E_ℓ` at the root `e`**, over `F`. -/
noncomputable def kumF (ℓ e : F) : (curveF ℓ).toAffine.Point → SqClass F
  | 0 => 1
  | .some x _ _ => if x = e then sqc (fdF ℓ e) else sqc (x - e)

@[simp] theorem kumF_zero (e : F) : kumF ℓ e 0 = 1 := rfl

theorem kumF_some {e x y : F} (h : (curveF ℓ).toAffine.Nonsingular x y) :
    kumF ℓ e (.some x y h) = if x = e then sqc (fdF ℓ e) else sqc (x - e) := rfl

theorem kumF_some_of_ne {e x y : F} (h : (curveF ℓ).toAffine.Nonsingular x y) (hx : x ≠ e) :
    kumF ℓ e (.some x y h) = sqc (x - e) := by
  simp [kumF_some, hx]

theorem kumF_some_eq {e x y : F} (h : (curveF ℓ).toAffine.Nonsingular x y) (hx : x = e) :
    kumF ℓ e (.some x y h) = sqc (fdF ℓ e) := by
  simp [kumF_some, hx]

theorem kumF_neg (e : F) (P : (curveF ℓ).toAffine.Point) : kumF ℓ e (-P) = kumF ℓ e P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rfl

theorem y_eq_zero_of_rootF {e x y : F} (h : (curveF ℓ).toAffine.Nonsingular x y)
    (he : IsRootF ℓ e) (hx : x = e) : y = 0 := by
  have := (curveF_equation_iff x y).mp h.1
  rw [hx] at this
  unfold IsRootF at he
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by rw [this, he])

theorem rootF_equation {e : F} (he : IsRootF ℓ e) : (curveF ℓ).toAffine.Equation e 0 := by
  rw [curveF_equation_iff]; unfold IsRootF at he; linear_combination -he

section Root

variable (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hℓ : ℓ ≠ 0) {e : F} (he : IsRootF ℓ e)
include h2 h3 hℓ he

/-- The two-torsion point `(e, 0)`. -/
noncomputable def tPtF : (curveF ℓ).toAffine.Point :=
  .some e 0 (curveF_nonsingular h2 h3 hℓ (rootF_equation he))

theorem some_eq_tPtF {x y : F} (h : (curveF ℓ).toAffine.Nonsingular x y) (hx : x = e) :
    Point.some x y h = tPtF h2 h3 hℓ he := by
  have hy := y_eq_zero_of_rootF h he hx
  subst hx hy; rfl

theorem kumF_tPtF : kumF ℓ e (tPtF h2 h3 hℓ he) = sqc (fdF ℓ e) := kumF_some_eq _ rfl

theorem add_tPtF_x {x y : F} (h : (curveF ℓ).toAffine.Nonsingular x y) (hx : x ≠ e) :
    ∃ y' h', Point.some x y h + tPtF h2 h3 hℓ he = .some (e + fdF ℓ e / (x - e)) y' h' := by
  unfold tPtF
  rw [Point.add_of_X_ne hx]
  have hxe : x - e ≠ 0 := sub_ne_zero.mpr hx
  have ex : (curveF ℓ).toAffine.addX x e ((curveF ℓ).toAffine.slope x e y 0) =
      e + fdF ℓ e / (x - e) := by
    have hq := (curveF_equation_iff x y).mp h.1
    rw [Affine.slope_of_X_ne hx]
    simp only [Affine.addX, curveF, fdF, sub_zero, zero_mul, add_zero]
    unfold IsRootF at he
    field_simp
    linear_combination hq + he
  have hn := nonsingular_add h (curveF_nonsingular h2 h3 hℓ (rootF_equation he))
    (fun hxy => hx hxy.left)
  rw [ex] at hn
  exact ⟨_, hn, by simp only [Point.some.injEq]; exact ⟨ex, trivial⟩⟩

theorem kumF_add_tPtF (P : (curveF ℓ).toAffine.Point) :
    kumF ℓ e (P + tPtF h2 h3 hℓ he) = kumF ℓ e P * sqc (fdF ℓ e) := by
  have hc := fdF_ne_zero h2 h3 hℓ he
  rcases P with _ | ⟨x, y, h⟩
  · rw [show (Point.zero : (curveF ℓ).toAffine.Point) = 0 from rfl, zero_add, kumF_tPtF,
      kumF_zero, one_mul]
  · by_cases hx : x = e
    · rw [some_eq_tPtF h2 h3 hℓ he h hx]
      unfold tPtF
      rw [Point.add_self_of_Y_eq (by simp [curveF_negY]), kumF_some_eq _ rfl]
      simp [SqClass.mul_self]
    · obtain ⟨y', h', eq⟩ := add_tPtF_x h2 h3 hℓ he h hx
      have hxe : x - e ≠ 0 := sub_ne_zero.mpr hx
      have hne : e + fdF ℓ e / (x - e) ≠ e := by
        intro h0
        have : fdF ℓ e / (x - e) = 0 := by linear_combination h0
        exact div_ne_zero hc hxe this
      rw [eq, kumF_some_of_ne _ hne, kumF_some_of_ne _ hx, add_sub_cancel_left,
        sqc_div hc hxe, mul_comm]

omit h2 h3 hℓ in
/-- **The chord-tangent identity at the root `e`.** -/
theorem mul_addX_sub_eq_F {x₁ x₂ y₁ y₂ : F} (h₁ : (curveF ℓ).toAffine.Nonsingular x₁ y₁)
    (h₂ : (curveF ℓ).toAffine.Nonsingular x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (curveF ℓ).toAffine.negY x₂ y₂)) :
    (x₁ - e) * (x₂ - e) *
        ((curveF ℓ).toAffine.addX x₁ x₂ ((curveF ℓ).toAffine.slope x₁ x₂ y₁ y₂) - e) =
      (y₁ - (curveF ℓ).toAffine.slope x₁ x₂ y₁ y₂ * (x₁ - e)) ^ 2 := by
  have key := congrArg (Polynomial.eval e) (Affine.addPolynomial_slope h₁.1 h₂.1 hxy)
  rw [Affine.addPolynomial_eq] at key
  simp only [Cubic.toPoly, eval_neg, eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_sub,
    curveF_a₁, curveF_a₂, curveF_a₃, curveF_a₄, curveF_a₆] at key
  unfold IsRootF at he
  linear_combination -key - he

/-- **The Kummer map at a root is a homomorphism** (Silverman X.1.4). -/
theorem kumF_add (P Q : (curveF ℓ).toAffine.Point) :
    kumF ℓ e (P + Q) = kumF ℓ e P * kumF ℓ e Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · show kumF ℓ e (0 + _) = kumF ℓ e 0 * _
    rw [zero_add, kumF_zero, one_mul]
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · show kumF ℓ e (_ + 0) = _ * kumF ℓ e 0
    rw [add_zero, kumF_zero, mul_one]
  by_cases hx₁ : x₁ = e
  · rw [some_eq_tPtF h2 h3 hℓ he h₁ hx₁, add_comm, kumF_add_tPtF, kumF_tPtF, mul_comm]
  by_cases hx₂ : x₂ = e
  · rw [some_eq_tPtF h2 h3 hℓ he h₂ hx₂, kumF_add_tPtF, kumF_tPtF]
  by_cases hxy : x₁ = x₂ ∧ y₁ = (curveF ℓ).toAffine.negY x₂ y₂
  · rw [Point.add_of_Y_eq hxy.1 hxy.2, kumF_zero, kumF_some_of_ne _ hx₁,
      kumF_some_of_ne _ hx₂, hxy.1, SqClass.mul_self]
  have key := mul_addX_sub_eq_F he h₁ h₂ hxy
  rw [Point.add_some hxy]
  by_cases hx₃ : (curveF ℓ).toAffine.addX x₁ x₂ ((curveF ℓ).toAffine.slope x₁ x₂ y₁ y₂) = e
  · have hPQ : Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ = tPtF h2 h3 hℓ he := by
      rw [Point.add_some hxy]; exact some_eq_tPtF h2 h3 hℓ he _ hx₃
    have hQ : Point.some x₂ y₂ h₂ = -Point.some x₁ y₁ h₁ + tPtF h2 h3 hℓ he := by
      rw [← hPQ]; abel
    rw [some_eq_tPtF h2 h3 hℓ he _ hx₃, hQ, kumF_add_tPtF, kumF_neg, kumF_tPtF,
      ← mul_assoc, SqClass.mul_self, one_mul]
  · rw [kumF_some_of_ne _ hx₁, kumF_some_of_ne _ hx₂, kumF_some_of_ne _ hx₃]
    have h1 : x₁ - e ≠ 0 := sub_ne_zero.mpr hx₁
    have h2' : x₂ - e ≠ 0 := sub_ne_zero.mpr hx₂
    have hν : y₁ - (curveF ℓ).toAffine.slope x₁ x₂ y₁ y₂ * (x₁ - e) ≠ 0 := by
      intro h0
      rw [h0] at key
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_eq_zero] at key
      exact hx₃ (by
        rcases key with (k | k) | k
        · exact absurd k h1
        · exact absurd k h2'
        · exact sub_eq_zero.mp k)
    have : (curveF ℓ).toAffine.addX x₁ x₂ ((curveF ℓ).toAffine.slope x₁ x₂ y₁ y₂) - e =
        (x₁ - e) * (x₂ - e) * ((y₁ - (curveF ℓ).toAffine.slope x₁ x₂ y₁ y₂ * (x₁ - e)) /
          ((x₁ - e) * (x₂ - e))) ^ 2 := by
      have hx12 : (x₁ - e) * (x₂ - e) ≠ 0 := mul_ne_zero h1 h2'
      rw [div_pow, ← key]
      field_simp
    rw [this, sqc_mul_sq _ (div_ne_zero hν (mul_ne_zero h1 h2')), sqc_mul h1 h2']

end Root

/-! ### The complete 2-descent map -/

section Delta

variable (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hℓ : ℓ ≠ 0)
include h2 h3 hℓ

/-- The complete 2-descent map in the coordinates `(x + 3ℓ, x − ℓ)` (S12 line 252). -/
noncomputable def deltaF (ℓ : F) (P : (curveF ℓ).toAffine.Point) : SqClass F × SqClass F :=
  (kumF ℓ (-3 * ℓ) P, kumF ℓ ℓ P)

omit h2 h3 hℓ in
theorem deltaF_def (P : (curveF ℓ).toAffine.Point) :
    deltaF ℓ P = (kumF ℓ (-3 * ℓ) P, kumF ℓ ℓ P) := rfl

theorem deltaF_add (P Q : (curveF ℓ).toAffine.Point) :
    deltaF ℓ (P + Q) = deltaF ℓ P * deltaF ℓ Q := by
  simp only [deltaF, kumF_add h2 h3 hℓ (isRootF_neg3 ℓ), kumF_add h2 h3 hℓ (isRootF_ell ℓ),
    Prod.mk_mul_mk]

/-- The complete 2-descent map as a homomorphism. -/
noncomputable def deltaHomF : (curveF ℓ).toAffine.Point →+ Additive (SqClass F × SqClass F) where
  toFun P := Additive.ofMul (deltaF ℓ P)
  map_zero' := rfl
  map_add' P Q := by rw [deltaF_add h2 h3 hℓ]; rfl

theorem deltaF_two_nsmul (P : (curveF ℓ).toAffine.Point) : deltaF ℓ (2 • P) = 1 := by
  rw [two_nsmul, deltaF_add h2 h3 hℓ]
  ext <;> simp [SqClass.mul_self]

omit h2 h3 hℓ in
/-- Two points with the same abscissa are equal or opposite. -/
theorem some_eq_or_eq_neg_F {x y X Y : F} (h : (curveF ℓ).toAffine.Nonsingular x y)
    (h' : (curveF ℓ).toAffine.Nonsingular X Y) (hX : X = x) :
    Point.some x y h = .some X Y h' ∨ Point.some x y h = -Point.some X Y h' := by
  have e₁ := (curveF_equation_iff x y).mp h.1
  have e₂ := (curveF_equation_iff X Y).mp h'.1
  subst hX
  have : (y - Y) * (y + Y) = 0 := by linear_combination e₁ - e₂
  rcases mul_eq_zero.mp this with h0 | h0
  · left; simp only [Point.some.injEq, true_and]; linear_combination h0
  · right; simp only [Point.neg_some, Point.some.injEq, curveF_negY, true_and]
    linear_combination h0

/-- **The halving lemma.** If `x = r₁²`, `x − ℓ = r₂²`, `x + 3ℓ = r₃²`, then `(x, y) ∈ 2E_ℓ(F)`;
the half has abscissa `x + r₁r₂ + r₁r₃ + r₂r₃` (as in `DescentM.lean`, over `F`). -/
theorem exists_two_nsmul_eq_F {x y : F} (h : (curveF ℓ).toAffine.Nonsingular x y)
    {r₁ r₂ r₃ : F} (h₁ : x = r₁ ^ 2) (h₂ : x - ℓ = r₂ ^ 2) (h₃ : x + 3 * ℓ = r₃ ^ 2) :
    ∃ Q : (curveF ℓ).toAffine.Point, 2 • Q = .some x y h := by
  subst h₁
  have u : r₁ ^ 2 - ℓ = r₂ ^ 2 := h₂
  have v : r₁ ^ 2 + 3 * ℓ = r₃ ^ 2 := h₃
  set x' := r₁ ^ 2 + r₁ * r₂ + r₁ * r₃ + r₂ * r₃ with hx'
  set y' := (r₁ + r₂) * (r₁ + r₃) * (r₂ + r₃) with hy'
  have hQ : (curveF ℓ).toAffine.Equation x' y' := by
    rw [curveF_equation_iff, hx', hy']
    linear_combination (-((r₁ + r₂) * (r₁ + r₃)) * ((r₁ + r₃) * (r₂ + r₃))) * u +
      (-((r₁ + r₂) * (r₁ + r₃)) * ((r₁ + r₂) * (r₂ + r₃)) -
        ((r₁ + r₂) * (r₁ + r₃)) * (r₁ ^ 2 - ℓ - r₂ ^ 2)) * v
  have hy0 : y' ≠ 0 := by
    have h12 : r₁ + r₂ ≠ 0 := by
      intro h0; apply hℓ
      have : r₁ = -r₂ := by linear_combination h0
      rw [this] at u; linear_combination -u
    have h13 : r₁ + r₃ ≠ 0 := by
      intro h0
      have : r₁ = -r₃ := by linear_combination h0
      rw [this] at v
      exact mul_ne_zero h3 hℓ (by linear_combination v)
    have h23 : r₂ + r₃ ≠ 0 := by
      intro h0
      have : r₂ = -r₃ := by linear_combination h0
      rw [this] at u
      exact mul_ne_zero (mul_ne_zero h2 h2) hℓ (by linear_combination v - u)
    exact mul_ne_zero (mul_ne_zero h12 h13) h23
  have hyy : y' - -y' ≠ 0 := by
    rw [sub_neg_eq_add, ← two_mul]; exact mul_ne_zero h2 hy0
  have hyn : y' ≠ (curveF ℓ).toAffine.negY x' y' := by
    rw [curveF_negY]; intro h0; apply hyy; rw [← h0]; ring
  have hsl : (curveF ℓ).toAffine.slope x' x' y' y' = r₁ + r₂ + r₃ := by
    rw [Affine.slope_of_Y_ne rfl hyn, curveF_negY, div_eq_iff hyy]
    simp only [curveF_a₁, curveF_a₂, curveF_a₄, zero_mul, sub_zero]
    rw [hx', hy']
    linear_combination (((r₁ + r₂) * (r₁ + r₃)) + ((r₁ + r₃) * (r₂ + r₃))) * u +
      (((r₁ + r₂) * (r₁ + r₃)) + ((r₁ + r₂) * (r₂ + r₃)) + (r₁ ^ 2 - ℓ - r₂ ^ 2)) * v
  have hX : (curveF ℓ).toAffine.addX x' x' ((curveF ℓ).toAffine.slope x' x' y' y') = r₁ ^ 2 := by
    rw [hsl]
    simp only [Affine.addX, curveF_a₁, curveF_a₂, zero_mul, add_zero]
    rw [hx']
    linear_combination -u - v
  have hQn : (curveF ℓ).toAffine.Nonsingular x' y' := curveF_nonsingular h2 h3 hℓ hQ
  set Q : (curveF ℓ).toAffine.Point := .some x' y' hQn
  have h2Q : 2 • Q = Point.some _ _ (nonsingular_add hQn hQn fun hxy => hyn hxy.right) := by
    rw [two_nsmul]; exact Point.add_self_of_Y_ne hyn
  rcases some_eq_or_eq_neg_F h _ hX with e | e
  · exact ⟨Q, by rw [h2Q, e]⟩
  · exact ⟨-Q, by rw [two_nsmul, ← neg_add, ← two_nsmul, h2Q, e]⟩

omit h2 h3 hℓ in
theorem isSquare_of_sqc_eq_one {z : F} (h : sqc z = 1) : ∃ r : F, z = r ^ 2 := by
  by_cases hz : z = 0
  · exact ⟨0, by rw [hz]; ring⟩
  · obtain ⟨r, hr⟩ := (sqc_eq_one_iff hz).mp h
    exact ⟨r, by rw [hr]; ring⟩

/-- **`δ(P) = 1` gives `P ∈ 2E_ℓ(F)`** (the injectivity of `E(F)/2E(F) →` Kummer classes,
Silverman X.1.4), over any field with `2, 3 ≠ 0`. -/
theorem exists_two_nsmul_of_deltaF_eq_one (P : (curveF ℓ).toAffine.Point)
    (h1 : deltaF ℓ P = 1) : ∃ Q, 2 • Q = P := by
  rcases P with _ | ⟨x, y, h⟩
  · exact ⟨0, by simp; rfl⟩
  have hf := congrArg Prod.fst h1
  have hs := congrArg Prod.snd h1
  simp only [deltaF, Prod.fst_one, Prod.snd_one, kumF_some] at hf hs
  have heq : y ^ 2 = x * (x - ℓ) * (x + 3 * ℓ) := by
    have := (curveF_equation_iff x y).mp h.1; rw [this]; ring
  have h3ℓ : -3 * ℓ ≠ ℓ := by
    intro h0; exact mul_ne_zero (mul_ne_zero h2 h2) hℓ (by linear_combination -h0)
  by_cases hx3 : x = -3 * ℓ
  · -- `(−3ℓ, 0)`: `3` and `−ℓ` are squares, `x = −3ℓ = 3 · (−ℓ)`
    rw [if_pos hx3, fdF_neg3,
      show (12 : F) * ℓ ^ 2 = 3 * (2 * ℓ) ^ 2 by ring, sqc_mul_sq _ (mul_ne_zero h2 hℓ)] at hf
    rw [if_neg (by rw [hx3]; exact h3ℓ)] at hs
    obtain ⟨s, hs'⟩ := isSquare_of_sqc_eq_one hf
    obtain ⟨t, ht⟩ := isSquare_of_sqc_eq_one hs
    refine exists_two_nsmul_eq_F h2 h3 hℓ h (r₁ := s * t / 2) (r₂ := t) (r₃ := 0) ?_ ?_ ?_
    · rw [hx3]
      have : x - ℓ = -4 * ℓ := by rw [hx3]; ring
      field_simp
      rw [← hs', show (2 : F) ^ 2 = 4 by norm_num]
      linear_combination (-3 : F) * (ht.symm.trans this) + 0 * hs'
    · exact ht
    · rw [hx3]; ring
  by_cases hx1 : x = ℓ
  · -- `(ℓ, 0)`: `ℓ` is a square
    rw [if_neg hx3] at hf
    rw [if_pos hx1] at hs
    rw [hx1, show ℓ - -3 * ℓ = ℓ * 2 ^ 2 by ring, sqc_mul_sq _ h2] at hf
    obtain ⟨s, hs'⟩ := isSquare_of_sqc_eq_one hf
    exact exists_two_nsmul_eq_F h2 h3 hℓ h (r₁ := s) (r₂ := 0) (r₃ := 2 * s)
      (by rw [hx1, hs']) (by rw [hx1]; ring) (by rw [hx1, hs']; ring)
  rw [if_neg hx3, show x - -3 * ℓ = x + 3 * ℓ by ring] at hf
  rw [if_neg hx1] at hs
  obtain ⟨r₃, hr₃⟩ := isSquare_of_sqc_eq_one hf
  obtain ⟨r₂, hr₂⟩ := isSquare_of_sqc_eq_one hs
  by_cases hx0 : x = 0
  · -- `(0, 0)`
    exact exists_two_nsmul_eq_F h2 h3 hℓ h (r₁ := 0) (by rw [hx0]; ring) hr₂ hr₃
  have hr0 : r₂ * r₃ ≠ 0 := by
    intro h0
    have hxa : x + 3 * ℓ ≠ 0 := fun h0 => hx3 (by linear_combination h0)
    have hxb : x - ℓ ≠ 0 := sub_ne_zero.mpr hx1
    apply mul_ne_zero hxb hxa
    rw [hr₂, hr₃]; linear_combination (r₂ * r₃) * h0
  exact exists_two_nsmul_eq_F h2 h3 hℓ h (r₁ := y / (r₂ * r₃))
    (by rw [div_pow, eq_div_iff (pow_ne_zero 2 hr0), heq, hr₂, hr₃]; ring) hr₂ hr₃

/-- **`ker δ = 2E_ℓ(F)`.** -/
theorem deltaHomF_ker :
    (deltaHomF h2 h3 hℓ).ker = (nsmulAddMonoidHom 2 : (curveF ℓ).toAffine.Point →+ _).range := by
  ext P
  rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_range]
  simp only [nsmulAddMonoidHom_apply]
  constructor
  · intro h
    exact exists_two_nsmul_of_deltaF_eq_one h2 h3 hℓ P (congrArg Additive.toMul h)
  · rintro ⟨Q, rfl⟩
    exact congrArg Additive.ofMul (deltaF_two_nsmul h2 h3 hℓ Q)

/-- **Four points of `E_ℓ(F)[2]`**: `O`, `(0, 0)`, `(ℓ, 0)`, `(−3ℓ, 0)`. -/
theorem four_le_card_ker_two [Finite (curveF ℓ).toAffine.Point] :
    4 ≤ Nat.card (nsmulAddMonoidHom 2 : (curveF ℓ).toAffine.Point →+ _).ker := by
  set T₀ := tPtF h2 h3 hℓ (isRootF_zero ℓ)
  set T₁ := tPtF h2 h3 hℓ (isRootF_ell ℓ)
  set T₂ := tPtF h2 h3 hℓ (isRootF_neg3 ℓ)
  have htor : ∀ {e : F} (he : IsRootF ℓ e), 2 • tPtF h2 h3 hℓ he = 0 := by
    intro e he
    unfold tPtF
    rw [two_nsmul, Point.add_self_of_Y_eq (by simp [curveF_negY])]
  have hx : ∀ {e e' : F} (he : IsRootF ℓ e) (he' : IsRootF ℓ e'),
      tPtF h2 h3 hℓ he = tPtF h2 h3 hℓ he' → e = e' := by
    intro e e' he he' h
    unfold tPtF at h
    simp only [Point.some.injEq] at h
    exact h.1
  have hz : ∀ {e : F} (he : IsRootF ℓ e), (0 : (curveF ℓ).toAffine.Point) ≠ tPtF h2 h3 hℓ he := by
    intro e he h
    unfold tPtF at h
    exact Point.some_ne_zero _ h.symm
  have hsub : ({0, T₀, T₁, T₂} : Set (curveF ℓ).toAffine.Point) ⊆
      ((nsmulAddMonoidHom 2 : (curveF ℓ).toAffine.Point →+ _).ker : Set _) := by
    intro P hP
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hP
    simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply]
    rcases hP with rfl | rfl | rfl | rfl
    · exact nsmul_zero 2
    · exact htor _
    · exact htor _
    · exact htor _
  have h4 : ({0, T₀, T₁, T₂} : Set (curveF ℓ).toAffine.Point).ncard = 4 := by
    have h01 : (0 : F) ≠ ℓ := fun h => hℓ h.symm
    have h03 : (0 : F) ≠ -3 * ℓ := fun h => mul_ne_zero (neg_ne_zero.mpr h3) hℓ h.symm
    have h13 : ℓ ≠ -3 * ℓ := fun h =>
      mul_ne_zero (mul_ne_zero h2 h2) hℓ (by linear_combination h)
    rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair]
    · exact fun h => h13 (hx _ _ h)
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨fun h => h01 (hx _ _ h), fun h => h03 (hx _ _ h)⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hz _, hz _, hz _⟩
  rw [← h4, ← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
  exact Set.ncard_le_ncard hsub (Set.toFinite _)

end Delta

end ZInQ.Manuscript.PoleRC
