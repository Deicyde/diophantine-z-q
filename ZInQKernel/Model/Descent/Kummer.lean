import ZInQKernel.Model.Field.ShortWeierstrass

/-!
# Two-isogenies and the Kummer map

Blueprint: `model/descent/kummer-map.md`, `model/descent/kummer-homomorphism.md`,
`model/descent/kummer-kernel.md`, `model/descent/isogeny-doubling.md`.

For a field `K` and `b ∈ K` with `E_b : y² = x³ + b x` elliptic (`shortCurve b`; ellipticity
means `-64 b³ ≠ 0`, so `2 ≠ 0` and `b ≠ 0` in `K`):

* `SqClass K = Kˣ / Kˣ²`, written multiplicatively, and `sqc x` the class of `x ≠ 0`
  (`sqc 0 = 1` by convention);
* the Kummer map `kummer b : E_b(K) → Kˣ/Kˣ²`, `O ↦ 1`, `(0,0) ↦ b`, `(x, y) ↦ x` (`x ≠ 0`);
  it is a homomorphism (`kummerHom`);
* the two-isogeny `phi : E_b(K) → E_{b'}(K)` for `b' = -4 b`,
  `O, (0,0) ↦ O`, `(x, y) ↦ (y²/x², y (b - x²)/x²)`;
* the rescaling `rescale : E_{b''}(K) ≃+ E_b(K)` for `b'' = 16 b`, `(x, y) ↦ (x/4, y/8)`.

The target curves of `phi` and `rescale` are given by an equation `b' = -4 b`, `b'' = 16 b`
rather than by the literal coefficient, so that compositions need no casts.

The main results: `kummer_add` (homomorphism), `kummer_eq_one_iff` (the kernel of the Kummer
map of `E_{-4b}` is the image of `φ_b`), and `rescale_phi_phi` (`λ_b ∘ φ_{-4b} ∘ φ_b = [2]`).
-/

namespace ZInQ

open WeierstrassCurve WeierstrassCurve.Affine

namespace Descent

variable {K : Type*} [Field K]

/-! ### Square classes -/

/-- The group `Kˣ / Kˣ²` of square classes. -/
def SqClass (K : Type*) [Field K] : Type _ := Kˣ ⧸ (powMonoidHom 2 : Kˣ →* Kˣ).range

instance : CommGroup (SqClass K) := QuotientGroup.Quotient.commGroup _

/-- The quotient map `Kˣ → Kˣ/Kˣ²`. -/
def SqClass.mk : Kˣ →* SqClass K := QuotientGroup.mk' _

theorem SqClass.mk_eq_one_iff (u : Kˣ) :
    SqClass.mk u = 1 ↔ u ∈ (powMonoidHom 2 : Kˣ →* Kˣ).range :=
  QuotientGroup.eq_one_iff u

theorem SqClass.mk_surjective : Function.Surjective (SqClass.mk (K := K)) :=
  QuotientGroup.mk'_surjective _

@[elab_as_elim]
theorem SqClass.induction_on {p : SqClass K → Prop} (c : SqClass K) (H : ∀ u, p (SqClass.mk u)) :
    p c := by
  obtain ⟨u, rfl⟩ := SqClass.mk_surjective c; exact H u

open Classical in
/-- The square class of `x ∈ K`, with the convention `sqc 0 = 1`. -/
noncomputable def sqc (x : K) : SqClass K :=
  if hx : x = 0 then 1 else SqClass.mk (Units.mk0 x hx)

@[simp] theorem sqc_zero : sqc (0 : K) = 1 := by simp [sqc]

theorem sqc_of_ne_zero {x : K} (hx : x ≠ 0) : sqc x = SqClass.mk (Units.mk0 x hx) := by
  simp [sqc, hx]

theorem sqc_units (u : Kˣ) : sqc (u : K) = SqClass.mk u := by
  rw [sqc_of_ne_zero u.ne_zero]; congr 1; ext; rfl

@[simp] theorem sqc_one : sqc (1 : K) = 1 := by
  rw [sqc_of_ne_zero one_ne_zero, SqClass.mk_eq_one_iff]
  exact ⟨1, by ext; simp⟩

theorem sqc_mul {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) : sqc (x * y) = sqc x * sqc y := by
  rw [sqc_of_ne_zero hx, sqc_of_ne_zero hy, sqc_of_ne_zero (mul_ne_zero hx hy), ← map_mul]
  congr 1
  exact Units.ext rfl

/-- Every square class has order dividing two. -/
theorem SqClass.mul_self (c : SqClass K) : c * c = 1 := by
  induction c using SqClass.induction_on with
  | H u =>
    rw [← map_mul, SqClass.mk_eq_one_iff]
    exact ⟨u, by simp [pow_two]⟩

theorem SqClass.inv_eq (c : SqClass K) : c⁻¹ = c :=
  inv_eq_of_mul_eq_one_right (SqClass.mul_self c)

theorem SqClass.pow_two (c : SqClass K) : c ^ 2 = 1 := by
  rw [_root_.pow_two, SqClass.mul_self]

theorem sqc_sq (z : K) : sqc (z ^ 2) = 1 := by
  by_cases hz : z = 0
  · simp [hz]
  · rw [pow_two, sqc_mul hz hz, SqClass.mul_self]

theorem sqc_mul_sq (x : K) {z : K} (hz : z ≠ 0) : sqc (x * z ^ 2) = sqc x := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [sqc_mul hx (pow_ne_zero 2 hz), sqc_sq, mul_one]

theorem sqc_inv (x : K) : sqc x⁻¹ = sqc x := by
  by_cases hx : x = 0
  · simp [hx]
  · have : x⁻¹ = x * x⁻¹ ^ 2 := by field_simp
    rw [this, sqc_mul_sq x (inv_ne_zero hx)]

theorem sqc_div {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) : sqc (x / y) = sqc x * sqc y := by
  rw [div_eq_mul_inv, sqc_mul hx (inv_ne_zero hy), sqc_inv]

theorem sqc_neg_sq (z : K) {x : K} (hz : z ≠ 0) : sqc (z ^ 2 * x) = sqc x := by
  rw [mul_comm, sqc_mul_sq x hz]

/-- For `x ≠ 0`, `sqc x = 1` iff `x` is a square. -/
theorem sqc_eq_one_iff {x : K} (hx : x ≠ 0) : sqc x = 1 ↔ IsSquare x := by
  rw [sqc_of_ne_zero hx, SqClass.mk_eq_one_iff, MonoidHom.mem_range]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u, ?_⟩
    have := congrArg Units.val hu
    simpa [pow_two] using this.symm
  · rintro ⟨r, rfl⟩
    have hr : r ≠ 0 := by rintro rfl; simp at hx
    exact ⟨Units.mk0 r hr, by ext; simp [pow_two]⟩

theorem sqc_eq_one_iff_exists {x : K} (hx : x ≠ 0) : sqc x = 1 ↔ ∃ w, w ≠ 0 ∧ x = w ^ 2 := by
  rw [sqc_eq_one_iff hx]
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨r, by rintro rfl; simp at hx, by ring⟩
  · rintro ⟨w, -, rfl⟩
    exact ⟨w, by ring⟩

/-- Two nonzero elements have the same class iff their quotient is a square. -/
theorem sqc_eq_sqc_iff {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    sqc x = sqc y ↔ ∃ w, w ≠ 0 ∧ x = y * w ^ 2 := by
  constructor
  · intro h
    have h1 : sqc (x / y) = 1 := by rw [sqc_div hx hy, h, SqClass.mul_self]
    obtain ⟨w, hw, hw'⟩ := (sqc_eq_one_iff_exists (div_ne_zero hx hy)).mp h1
    exact ⟨w, hw, by rw [← hw']; field_simp⟩
  · rintro ⟨w, hw, rfl⟩
    exact sqc_mul_sq y hw

/-- Every square class is the class of a nonzero element. -/
theorem SqClass.exists_eq_sqc (c : SqClass K) : ∃ x : K, x ≠ 0 ∧ sqc x = c := by
  induction c using SqClass.induction_on with
  | H u => exact ⟨u, u.ne_zero, sqc_units u⟩

/-! ### Ellipticity of `y² = x³ + b x` -/

section Elliptic

variable {b : K}

theorem two_ne_zero_of_isElliptic [h : (shortCurve b).IsElliptic] : (2 : K) ≠ 0 := by
  intro h2
  have hΔ := h.isUnit.ne_zero
  rw [shortCurve_Δ] at hΔ
  apply hΔ
  have : (64 : K) = 2 * 32 := by norm_num
  rw [this, h2]; ring

theorem four_ne_zero_of_isElliptic [(shortCurve b).IsElliptic] : (4 : K) ≠ 0 := by
  have h2 := two_ne_zero_of_isElliptic (b := b)
  rw [show (4 : K) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2

theorem eight_ne_zero_of_isElliptic [(shortCurve b).IsElliptic] : (8 : K) ≠ 0 := by
  have h2 := two_ne_zero_of_isElliptic (b := b)
  rw [show (8 : K) = 2 * 2 * 2 by norm_num]; exact mul_ne_zero (mul_ne_zero h2 h2) h2

theorem ne_zero_of_isElliptic [h : (shortCurve b).IsElliptic] : b ≠ 0 := by
  rintro rfl
  have hΔ := h.isUnit.ne_zero
  rw [shortCurve_Δ] at hΔ
  simp at hΔ

theorem shortCurve_isElliptic_of_eq {b' : K} [(shortCurve b).IsElliptic] {c : K} (hc : c ≠ 0)
    (h : b' = c * b) : (shortCurve b').IsElliptic := by
  have : NeZero (2 : K) := ⟨two_ne_zero_of_isElliptic (b := b)⟩
  exact shortCurve_isElliptic (by rw [h]; exact mul_ne_zero hc ne_zero_of_isElliptic)

end Elliptic

/-! ### The Kummer map -/

section Kummer

variable [DecidableEq K] (b : K)

/-- The Kummer map `α_b : E_b(K) → Kˣ/Kˣ²`: `O ↦ 1`, `(0, 0) ↦ b`, `(x, y) ↦ x` for `x ≠ 0`. -/
noncomputable def kummer : (shortCurve b).toAffine.Point → SqClass K
  | 0 => 1
  | .some x _ _ => if x = 0 then sqc b else sqc x

@[simp] theorem kummer_zero : kummer b 0 = 1 := rfl

theorem kummer_some {x y : K} (h : (shortCurve b).toAffine.Nonsingular x y) :
    kummer b (.some x y h) = if x = 0 then sqc b else sqc x := rfl

theorem kummer_some_of_ne {x y : K} (h : (shortCurve b).toAffine.Nonsingular x y) (hx : x ≠ 0) :
    kummer b (.some x y h) = sqc x := by
  simp [kummer_some, hx]

theorem kummer_some_zero {y : K} (h : (shortCurve b).toAffine.Nonsingular 0 y) :
    kummer b (.some 0 y h) = sqc b := by
  simp [kummer_some]

theorem kummer_neg (P : (shortCurve b).toAffine.Point) : kummer b (-P) = kummer b P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rfl

variable {b}

/-- The two-torsion point `(0, 0)` of `E_b`. -/
def tZero [(shortCurve b).IsElliptic] : (shortCurve b).toAffine.Point :=
  Point.mk (W' := (shortCurve b).toAffine) (x := 0) (y := 0) (by
    rw [shortCurve_equation_iff]; ring)

theorem tZero_def [(shortCurve b).IsElliptic] :
    ∃ h, (tZero : (shortCurve b).toAffine.Point) = .some 0 0 h := ⟨_, rfl⟩

@[simp] theorem kummer_tZero [(shortCurve b).IsElliptic] : kummer b tZero = sqc b :=
  kummer_some_zero b _

theorem eq_zero_of_x_eq_zero {x y : K} (h : (shortCurve b).toAffine.Nonsingular x y)
    (hx : x = 0) : y = 0 := by
  have := (shortCurve_equation_iff b x y).mp h.1
  rw [hx] at this
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by rw [this]; ring)

theorem some_eq_tZero [(shortCurve b).IsElliptic] {x y : K}
    (h : (shortCurve b).toAffine.Nonsingular x y) (hx : x = 0) : Point.some x y h = tZero := by
  have hy := eq_zero_of_x_eq_zero h hx
  subst hx hy; rfl

variable [hE : (shortCurve b).IsElliptic]

/-- `(x, y) + (0, 0) = (b / x, -b y / x²)` for `x ≠ 0`; only the abscissa is needed. -/
theorem add_tZero_x {x y : K} (h : (shortCurve b).toAffine.Nonsingular x y) (hx : x ≠ 0) :
    ∃ y' h', Point.some x y h + tZero = .some (b / x) y' h' := by
  obtain ⟨h0, ht⟩ := tZero_def (b := b)
  rw [ht, Point.add_of_X_ne hx]
  have e : (shortCurve b).toAffine.addX x 0 ((shortCurve b).toAffine.slope x 0 y 0) = b / x := by
      have he := (shortCurve_equation_iff b x y).mp h.1
      rw [Affine.slope_of_X_ne hx]
      simp only [Affine.addX, shortCurve_a₁, shortCurve_a₂, sub_zero, zero_mul, add_zero]
      rw [eq_div_iff hx]
      field_simp
      linear_combination he
  have hn := nonsingular_add h h0 (fun hxy => hx hxy.left)
  rw [e] at hn
  exact ⟨_, hn, by simp only [Point.some.injEq]; exact ⟨e, trivial⟩⟩

theorem kummer_add_tZero (P : (shortCurve b).toAffine.Point) :
    kummer b (P + tZero) = kummer b P * sqc b := by
  have hb : b ≠ 0 := ne_zero_of_isElliptic
  rcases P with _ | ⟨x, y, h⟩
  · rw [show (Point.zero : (shortCurve b).toAffine.Point) = 0 from rfl, zero_add, kummer_tZero,
      kummer_zero, one_mul]
  · by_cases hx : x = 0
    · rw [some_eq_tZero h hx]
      obtain ⟨h0, ht⟩ := tZero_def (b := b)
      rw [ht, Point.add_self_of_Y_eq (by simp), kummer_some_zero]
      simp [SqClass.mul_self]
    · obtain ⟨y', h', e⟩ := add_tZero_x h hx
      rw [e, kummer_some_of_ne _ _ (div_ne_zero hb hx), kummer_some_of_ne _ _ hx, sqc_div hb hx,
        mul_comm]

/-- The key identity for the chord-tangent law: if `(x₁, y₁) + (x₂, y₂)` is affine with slope
`ℓ`, then `x₁ x₂ x₃ = (y₁ - ℓ x₁)²`. -/
theorem mul_addX_eq {x₁ x₂ y₁ y₂ : K} (h₁ : (shortCurve b).toAffine.Nonsingular x₁ y₁)
    (h₂ : (shortCurve b).toAffine.Nonsingular x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (shortCurve b).toAffine.negY x₂ y₂)) :
    x₁ * x₂ * (shortCurve b).toAffine.addX x₁ x₂ ((shortCurve b).toAffine.slope x₁ x₂ y₁ y₂) =
      (y₁ - (shortCurve b).toAffine.slope x₁ x₂ y₁ y₂ * x₁) ^ 2 := by
  have e₁ := (shortCurve_equation_iff b x₁ y₁).mp h₁.1
  have e₂ := (shortCurve_equation_iff b x₂ y₂).mp h₂.1
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_isElliptic (b := b)
  simp only [Affine.addX, shortCurve_a₁, shortCurve_a₂, zero_mul, add_zero, sub_zero]
  by_cases hx : x₁ = x₂
  · subst hx
    have hy : y₁ ≠ -y₂ := by rw [shortCurve_negY] at hxy; exact fun h => hxy ⟨rfl, h⟩
    have hyy : y₁ = y₂ := by
      have : (y₁ - y₂) * (y₁ + y₂) = 0 := by linear_combination e₁ - e₂
      rcases mul_eq_zero.mp this with h | h
      · exact sub_eq_zero.mp h
      · exact absurd (eq_neg_of_add_eq_zero_left h) hy
    subst hyy
    have hy0 : y₁ - -y₁ ≠ 0 := by
      intro h0; apply hy
      have : (2 : K) * y₁ = 0 := by linear_combination h0
      rw [(mul_eq_zero.mp this).resolve_left h2, neg_zero]
    set ℓ := (shortCurve b).toAffine.slope x₁ x₁ y₁ y₁ with hℓdef
    have hℓ : ℓ * (y₁ - -y₁) = 3 * x₁ ^ 2 + b := by
      rw [hℓdef, Affine.slope_of_Y_ne rfl (by rwa [shortCurve_negY])]
      simp only [shortCurve_negY, shortCurve_a₁, shortCurve_a₂, shortCurve_a₄, mul_zero, add_zero,
        sub_zero, zero_mul]
      exact div_mul_cancel₀ _ hy0
    apply mul_right_cancel₀ (pow_ne_zero 2 hy0)
    linear_combination (x₁ ^ 2 * (ℓ * (y₁ - -y₁) + (3 * x₁ ^ 2 + b)) +
        x₁ * (4 * y₁ ^ 2 - (ℓ * (y₁ - -y₁) + (3 * x₁ ^ 2 + b)) * x₁)) * hℓ +
      (-(8 * x₁ ^ 3) - 4 * (y₁ ^ 2 + (x₁ ^ 3 + b * x₁) - (3 * x₁ ^ 2 + b) * x₁)) * e₁
  · set ℓ := (shortCurve b).toAffine.slope x₁ x₂ y₁ y₂ with hℓdef
    have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
    have hℓ : ℓ * (x₁ - x₂) = y₁ - y₂ := by
      rw [hℓdef, Affine.slope_of_X_ne hx]; field_simp
    apply mul_right_cancel₀ (pow_ne_zero 2 hd)
    linear_combination (x₁ * x₂ * (ℓ * (x₁ - x₂) + (y₁ - y₂)) +
        x₁ * (2 * y₁ * (x₁ - x₂) - (ℓ * (x₁ - x₂) + (y₁ - y₂)) * x₁)) * hℓ +
      x₂ * (x₁ - x₂) * e₁ - x₁ * (x₁ - x₂) * e₂

/-- **The Kummer map is a homomorphism**: `α_b(P + Q) = α_b(P) α_b(Q)`. -/
theorem kummer_add (P Q : (shortCurve b).toAffine.Point) :
    kummer b (P + Q) = kummer b P * kummer b Q := by
  have hb : b ≠ 0 := ne_zero_of_isElliptic
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · show kummer b (0 + _) = kummer b 0 * _
    rw [zero_add, kummer_zero, one_mul]
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · show kummer b (_ + 0) = _ * kummer b 0
    rw [add_zero, kummer_zero, mul_one]
  by_cases hx₁ : x₁ = 0
  · rw [some_eq_tZero h₁ hx₁, add_comm, kummer_add_tZero, kummer_tZero, mul_comm]
  by_cases hx₂ : x₂ = 0
  · rw [some_eq_tZero h₂ hx₂, kummer_add_tZero, kummer_tZero]
  by_cases hxy : x₁ = x₂ ∧ y₁ = (shortCurve b).toAffine.negY x₂ y₂
  · rw [Point.add_of_Y_eq hxy.1 hxy.2, kummer_zero, kummer_some_of_ne _ _ hx₁,
      kummer_some_of_ne _ _ hx₂, hxy.1, SqClass.mul_self]
  have key := mul_addX_eq h₁ h₂ hxy
  rw [Point.add_some hxy]
  set ℓ := (shortCurve b).toAffine.slope x₁ x₂ y₁ y₂
  set x₃ := (shortCurve b).toAffine.addX x₁ x₂ ℓ
  by_cases hx₃ : x₃ = 0
  · -- `P + Q = (0, 0)`, so `Q = -P + (0, 0)`
    have hPQ : Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ = tZero := by
      rw [Point.add_some hxy]; exact some_eq_tZero _ hx₃
    have hQ : Point.some x₂ y₂ h₂ = -Point.some x₁ y₁ h₁ + tZero := by
      rw [← hPQ]; abel
    rw [some_eq_tZero _ hx₃, hQ, kummer_add_tZero, kummer_neg, kummer_tZero, ← mul_assoc,
      SqClass.mul_self, one_mul]
  · rw [kummer_some_of_ne _ _ hx₁, kummer_some_of_ne _ _ hx₂, kummer_some_of_ne _ _ hx₃]
    set ν := y₁ - ℓ * x₁
    have hν : ν ≠ 0 := by
      intro h0
      rw [h0] at key
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_eq_zero] at key
      tauto
    have : x₃ = x₁ * x₂ * (ν / (x₁ * x₂)) ^ 2 := by
      have hx12 : x₁ * x₂ ≠ 0 := mul_ne_zero hx₁ hx₂
      rw [div_pow, ← key]
      field_simp
    rw [this, sqc_mul_sq _ (div_ne_zero hν (mul_ne_zero hx₁ hx₂)), sqc_mul hx₁ hx₂]

/-- The Kummer map as a homomorphism `E_b(K) →+ Additive (Kˣ/Kˣ²)`. -/
noncomputable def kummerHom : (shortCurve b).toAffine.Point →+ Additive (SqClass K) where
  toFun P := Additive.ofMul (kummer b P)
  map_zero' := rfl
  map_add' P Q := by rw [kummer_add]; rfl

@[simp] theorem kummerHom_apply (P : (shortCurve b).toAffine.Point) :
    Additive.toMul (kummerHom P) = kummer b P := rfl

theorem kummer_nsmul (n : ℕ) (P : (shortCurve b).toAffine.Point) :
    kummer b (n • P) = kummer b P ^ n := by
  have := map_nsmul (kummerHom (b := b)) n P
  exact congrArg Additive.toMul this

theorem kummer_zsmul (n : ℤ) (P : (shortCurve b).toAffine.Point) :
    kummer b (n • P) = kummer b P ^ n := by
  have := map_zsmul (kummerHom (b := b)) n P
  exact congrArg Additive.toMul this

theorem kummer_two_nsmul (P : (shortCurve b).toAffine.Point) : kummer b (2 • P) = 1 := by
  rw [kummer_nsmul, SqClass.pow_two]

end Kummer

/-! ### The two-isogeny -/

section Isogeny

variable [DecidableEq K] {b b' : K}

theorem phi_equation {x y : K} (h : (shortCurve b).toAffine.Equation x y) (hx : x ≠ 0)
    (hb' : b' = -4 * b) :
    (shortCurve b').toAffine.Equation (y ^ 2 / x ^ 2) (y * (b - x ^ 2) / x ^ 2) := by
  have he := (shortCurve_equation_iff b x y).mp h
  rw [shortCurve_equation_iff, hb']
  have hb : b = (y ^ 2 - x ^ 3) / x := by field_simp; linear_combination -he
  rw [hb]
  field_simp
  ring

variable [(shortCurve b).IsElliptic] [(shortCurve b').IsElliptic]

/-- The two-isogeny `φ_b : E_b → E_{b'}`, `b' = -4 b`: `O, (0, 0) ↦ O` and
`(x, y) ↦ (y²/x², y (b - x²)/x²)` for `x ≠ 0`. -/
noncomputable def phi (hb' : b' = -4 * b) :
    (shortCurve b).toAffine.Point → (shortCurve b').toAffine.Point
  | 0 => 0
  | .some x _ h => if hx : x = 0 then 0 else Point.mk (phi_equation h.1 hx hb')

variable (hb' : b' = -4 * b)

@[simp] theorem phi_zero : phi hb' 0 = 0 := rfl

theorem phi_some_of_eq_zero {x y : K} (h : (shortCurve b).toAffine.Nonsingular x y) (hx : x = 0) :
    phi hb' (.some x y h) = 0 := by
  simp [phi, hx]

theorem phi_some {x y : K} (h : (shortCurve b).toAffine.Nonsingular x y) (hx : x ≠ 0) :
    phi hb' (.some x y h) = Point.mk (phi_equation h.1 hx hb') := by
  simp [phi, hx]

/-- **The image of a two-isogeny is the kernel of the Kummer map**: for `Q ∈ E_{-4b}(K)`,
`α_{-4b}(Q) = 1 ↔ Q ∈ φ_b(E_b(K))`. -/
theorem kummer_eq_one_iff (Q : (shortCurve b').toAffine.Point) :
    kummer b' Q = 1 ↔ Q ∈ Set.range (phi hb') := by
  have hb : b ≠ 0 := ne_zero_of_isElliptic
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_isElliptic (b := b)
  have h4 : (4 : K) ≠ 0 := four_ne_zero_of_isElliptic (b := b)
  constructor
  · intro hQ
    rcases Q with _ | ⟨X, Y, hXY⟩
    · exact ⟨0, rfl⟩
    have he := (shortCurve_equation_iff b' X Y).mp hXY.1
    by_cases hX : X = 0
    · -- `Q = (0, 0)` and `-4 b = t²`
      simp only [kummer_some, hX, ↓reduceIte] at hQ
      have hb'0 : b' ≠ 0 := by rw [hb']; exact mul_ne_zero (neg_ne_zero.mpr h4) hb
      obtain ⟨t, ht, htb⟩ := (sqc_eq_one_iff_exists hb'0).mp hQ
      have hP : (shortCurve b).toAffine.Equation (t / 2) 0 := by
        rw [shortCurve_equation_iff]
        have : b = -(t ^ 2) / 4 := by
          field_simp; linear_combination -htb + hb'
        rw [this]; field_simp; ring
      refine ⟨Point.mk hP, ?_⟩
      rw [Point.mk, phi_some _ _ (div_ne_zero ht h2)]
      have hY : Y = 0 := eq_zero_of_x_eq_zero hXY hX
      simp only [Point.mk, Point.some.injEq, hX, hY]
      constructor <;> ring
    · rw [kummer_some_of_ne _ _ hX] at hQ
      obtain ⟨w, hw, rfl⟩ := (sqc_eq_one_iff_exists hX).mp hQ
      -- `x = (w² - Y/w)/2`, `y = w x`
      have hbw : b = (w ^ 6 - Y ^ 2) / (4 * w ^ 2) := by
        rw [hb'] at he; field_simp; linear_combination he
      set x := (w ^ 2 - Y / w) / 2 with hx
      have hx0 : x ≠ 0 := by
        intro h0
        apply hb
        have : x * ((w ^ 2 + Y / w) / 2) = b := by
          rw [hx, hbw]; field_simp; ring
        rw [← this, h0, zero_mul]
      have hP : (shortCurve b).toAffine.Equation x (w * x) := by
        rw [shortCurve_equation_iff, hbw, hx]
        field_simp
        ring
      have hx' : x = (w ^ 3 - Y) / (2 * w) := by rw [hx]; field_simp
      have hwY : w ^ 3 - Y ≠ 0 := by
        intro h0; apply hx0; rw [hx', h0, zero_div]
      refine ⟨Point.mk hP, ?_⟩
      rw [Point.mk, phi_some _ _ hx0]
      simp only [Point.mk, Point.some.injEq]
      constructor
      · field_simp
      · rw [hbw, hx']
        field_simp
        ring
  · rintro ⟨P, rfl⟩
    rcases P with _ | ⟨x, y, h⟩
    · rfl
    by_cases hx : x = 0
    · rw [phi_some_of_eq_zero _ _ hx]; rfl
    rw [phi_some _ _ hx, Point.mk]
    by_cases hy : y = 0
    · -- `φ(x, 0) = (0, 0)` and `-4b = (2x)²`
      have he := (shortCurve_equation_iff b x y).mp h.1
      simp only [hy, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
        zero_mul]
      rw [kummer_some_zero]
      have : b' = (2 * x) ^ 2 := by
        rw [hb']
        have : x * (x ^ 2 + b) = 0 := by rw [hy] at he; linear_combination -he
        have := (mul_eq_zero.mp this).resolve_left hx
        linear_combination -4 * this
      rw [this, sqc_sq]
    · rw [kummer_some_of_ne _ _ (div_ne_zero (pow_ne_zero 2 hy) (pow_ne_zero 2 hx)), ← div_pow,
        sqc_sq]

end Isogeny

/-! ### The rescaling and the doubling formula -/

section Rescale

variable [DecidableEq K] {b b'' : K} [(shortCurve b).IsElliptic] [(shortCurve b'').IsElliptic]

/-- The rescaling `λ_b : E_{b''}(K) ≃+ E_b(K)`, `b'' = 16 b`, `(x, y) ↦ (x/4, y/8)`. -/
noncomputable def rescale (hb'' : b'' = 16 * b) :
    (shortCurve b'').toAffine.Point ≃+ (shortCurve b).toAffine.Point :=
  (scaleEquiv (A := b) (B := b'') (u := 2) (two_ne_zero_of_isElliptic (b := b))
    (by rw [hb'']; norm_num)).symm

theorem rescale_some (hb'' : b'' = 16 * b) {x y : K}
    (h : (shortCurve b'').toAffine.Nonsingular x y) :
    ∃ h', rescale hb'' (.some x y h) = .some (x / 4) (y / 8) h' := by
  obtain ⟨h', e⟩ := scaleEquiv_symm_some (A := b) (B := b'') (u := 2)
    (two_ne_zero_of_isElliptic (b := b)) (by rw [hb'']; norm_num) h
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_isElliptic (b := b)
  have ex : (2 : K)⁻¹ ^ 2 * x = x / 4 := by rw [inv_pow, ← div_eq_inv_mul]; norm_num
  have ey : (2 : K)⁻¹ ^ 3 * y = y / 8 := by rw [inv_pow, ← div_eq_inv_mul]; norm_num
  rw [ex, ey] at h'
  refine ⟨h', ?_⟩
  rw [rescale, e]
  simp only [Point.some.injEq]
  exact ⟨ex, ey⟩

theorem kummer_rescale (hb'' : b'' = 16 * b) (P : (shortCurve b'').toAffine.Point) :
    kummer b (rescale hb'' P) = kummer b'' P := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_isElliptic (b := b)
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  obtain ⟨h', e⟩ := rescale_some hb'' h
  rw [e]
  by_cases hx : x = 0
  · have : x / 4 = 0 := by rw [hx, zero_div]
    subst hx
    simp only [kummer_some, zero_div, ↓reduceIte]
    rw [hb'',
      show (16 : K) * b = 4 ^ 2 * b by norm_num, sqc_neg_sq _ (by
        rw [show (4 : K) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2)]
  · have : x / 4 ≠ 0 := div_ne_zero hx (by rw [show (4 : K) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2)
    rw [kummer_some_of_ne _ _ this, kummer_some_of_ne _ _ hx,
      show x / 4 = x * (1 / 2) ^ 2 by rw [div_pow, div_eq_mul_inv]; norm_num, sqc_mul_sq _ (by simpa using h2)]

variable {b' : K} [(shortCurve b').IsElliptic]

/-- **The composite of the two-isogenies is doubling**: `λ_b (φ_{-4b} (φ_b P)) = [2] P`. -/
theorem rescale_phi_phi (hb' : b' = -4 * b) (hb'' : b'' = -4 * b')
    (P : (shortCurve b).toAffine.Point) :
    rescale (by rw [hb'', hb']; ring) (phi hb'' (phi hb' P)) = 2 • P := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_isElliptic (b := b)
  have hb0 : b ≠ 0 := ne_zero_of_isElliptic
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  by_cases hx : x = 0
  · have hy := eq_zero_of_x_eq_zero h hx
    rw [phi_some_of_eq_zero _ _ hx, phi_zero, map_zero, eq_comm,
      @shortCurve_two_nsmul_some_eq_zero_iff K _ _ ⟨h2⟩ b x y h]
    exact hy
  by_cases hy : y = 0
  · rw [phi_some _ _ hx, Point.mk, phi_some_of_eq_zero _ _ (by rw [hy]; ring), map_zero, eq_comm,
      @shortCurve_two_nsmul_some_eq_zero_iff K _ _ ⟨h2⟩ b x y h]
    exact hy
  have h4 : (4 : K) ≠ 0 := four_ne_zero_of_isElliptic (b := b)
  have h8 : (8 : K) ≠ 0 := eight_ne_zero_of_isElliptic (b := b)
  have hyy : y - -y ≠ 0 := by
    intro h0; apply hy
    have : (2 : K) * y = 0 := by linear_combination h0
    exact (mul_eq_zero.mp this).resolve_left h2
  have hy' : y ≠ (shortCurve b).toAffine.negY x y := by
    rw [shortCurve_negY]; intro h0; apply hyy; rw [← h0]; ring
  have hX : y ^ 2 / x ^ 2 ≠ 0 := div_ne_zero (pow_ne_zero 2 hy) (pow_ne_zero 2 hx)
  rw [phi_some _ _ hx, Point.mk, phi_some _ _ hX, Point.mk]
  obtain ⟨h', e⟩ := rescale_some (b := b) (by rw [hb'', hb']; ring)
    (equation_iff_nonsingular.mp (phi_equation (phi_equation h.1 hx hb') hX hb''))
  rw [e, two_nsmul, Point.add_self_of_Y_ne hy']
  simp only [Point.some.injEq]
  rw [Affine.slope_of_Y_ne rfl hy']
  have he := (shortCurve_equation_iff b x y).mp h.1
  have hbx : b = (y ^ 2 - x ^ 3) / x := by field_simp; linear_combination -he
  simp only [Affine.addX, Affine.addY, Affine.negAddY, shortCurve_negY, shortCurve_a₁,
    shortCurve_a₂, shortCurve_a₄, mul_zero, zero_mul, add_zero, sub_zero]
  rw [hb', hbx, show y - -y = 2 * y by ring]
  constructor
  · field_simp
    ring
  · field_simp
    ring

end Rescale

/-! ### Kummer maps and scalings -/

section Scale

variable [DecidableEq K] {A B u : K} [(shortCurve A).IsElliptic] [(shortCurve B).IsElliptic]

/-- The scaling `(x, y) ↦ (u² x, u³ y)`, `B = u⁴ A`, preserves the Kummer map: abscissas are
multiplied by a square and `B ≡ A` modulo squares. -/
theorem kummer_scaleEquiv (hu : u ≠ 0) (hB : B = u ^ 4 * A) (P : (shortCurve A).toAffine.Point) :
    kummer B (scaleEquiv hu hB P) = kummer A P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  rw [scaleEquiv_some]
  by_cases hx : x = 0
  · subst hx
    simp only [kummer_some, mul_zero, ↓reduceIte]
    rw [hB, show u ^ 4 * A = A * (u ^ 2) ^ 2 by ring, sqc_mul_sq _ (pow_ne_zero 2 hu)]
  · have : u ^ 2 * x ≠ 0 := mul_ne_zero (pow_ne_zero 2 hu) hx
    rw [kummer_some_of_ne _ _ this, kummer_some_of_ne _ _ hx, mul_comm, sqc_mul_sq _ hu]

end Scale

end Descent

end ZInQ
