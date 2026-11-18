import ZInQKernel.Contrib.OneProof.PoleS12.GoodF.KummerF

/-!
# The complete 2-descent of `y² = x(x − ℓ)(x + 3ℓ)` over a field with `2, 3 ≠ 0`

Generalized copy of round 1's `DescentM.lean` (over `ℚ`): the descent map `deltaM`, the halving
lemma, and (new) `ker δ ⊆ 2E` with no hypothesis on `ℓ` (`deltaM_eq_one_imp`), and the passage
from a point to `LocM` (`locM_of_deltaM`).
-/

namespace ZInQ.Manuscript.PoleS12.GoodF

open WeierstrassCurve WeierstrassCurve.Affine ZInQ.Descent Polynomial ZInQ.Manuscript.PoleRC

open scoped Classical

variable {F : Type*} [Field F] {ℓ : F}

theorem isRootM_neg3 (ℓ : F) : IsRootM ℓ (-3 * ℓ) := by unfold IsRootM; ring
theorem isRootM_ell (ℓ : F) : IsRootM ℓ ℓ := by unfold IsRootM; ring
theorem isRootM_zero (ℓ : F) : IsRootM ℓ 0 := by unfold IsRootM; ring

/-- The complete 2-descent map of `E_ℓ` in the coordinates `(x + 3ℓ, x − ℓ)`. -/
noncomputable def deltaM (ℓ : F) (P : (curveF ℓ).toAffine.Point) : SqClass F × SqClass F :=
  (kum ℓ (-3 * ℓ) P, kum ℓ ℓ P)

theorem deltaM_add (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hℓ : ℓ ≠ 0) (P Q : (curveF ℓ).toAffine.Point) :
    deltaM ℓ (P + Q) = deltaM ℓ P * deltaM ℓ Q := by
  simp only [deltaM, kum_add h2 h3 hℓ (isRootM_neg3 ℓ), kum_add h2 h3 hℓ (isRootM_ell ℓ), Prod.mk_mul_mk]

/-- The complete 2-descent map as a homomorphism. -/
noncomputable def deltaHomM (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hℓ : ℓ ≠ 0) :
    (curveF ℓ).toAffine.Point →+ Additive (SqClass F × SqClass F) where
  toFun P := Additive.ofMul (deltaM ℓ P)
  map_zero' := rfl
  map_add' P Q := by rw [deltaM_add h2 h3 hℓ]; rfl

theorem deltaM_two_nsmul (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hℓ : ℓ ≠ 0) (P : (curveF ℓ).toAffine.Point) :
    deltaM ℓ (2 • P) = 1 := by
  rw [two_nsmul, deltaM_add h2 h3 hℓ]
  ext <;> simp [SqClass.mul_self]

theorem two_nsmul_some_eq_zero_iff (h2 : (2 : F) ≠ 0) {x y : F}
    (h : (curveF ℓ).toAffine.Nonsingular x y) : 2 • Point.some x y h = 0 ↔ y = 0 := by
  rw [two_nsmul, add_eq_zero_iff_eq_neg, Point.neg_some, Point.some.injEq, curve_negY]
  constructor
  · rintro ⟨-, h'⟩
    have : (2 : F) * y = 0 := by linear_combination h'
    exact (mul_eq_zero.mp this).resolve_left h2
  · intro h'; exact ⟨rfl, by rw [h']; ring⟩

/-- Two points with the same abscissa are equal or opposite. -/
theorem some_eq_or_eq_neg_M {x y X Y : F} (h : (curveF ℓ).toAffine.Nonsingular x y)
    (h' : (curveF ℓ).toAffine.Nonsingular X Y) (hX : X = x) :
    Point.some x y h = .some X Y h' ∨ Point.some x y h = -Point.some X Y h' := by
  have e₁ := (curve_equation_iff x y).mp h.1
  have e₂ := (curve_equation_iff X Y).mp h'.1
  subst hX
  have : (y - Y) * (y + Y) = 0 := by linear_combination e₁ - e₂
  rcases mul_eq_zero.mp this with h0 | h0
  · left; simp only [Point.some.injEq, true_and]; linear_combination h0
  · right; simp only [Point.neg_some, Point.some.injEq, curve_negY, true_and]
    linear_combination h0

/-- **The halving lemma.** If `x = r₁²`, `x − ℓ = r₂²`, `x + 3ℓ = r₃²` (`ℓ ≠ 0`), then
`(x, y) ∈ 2E_ℓ(ℚ)`; the half is `x' = x + r₁r₂ + r₁r₃ + r₂r₃`,
`y' = (r₁ + r₂)(r₁ + r₃)(r₂ + r₃)`, with tangent slope `r₁ + r₂ + r₃`. -/
theorem exists_two_nsmul_eq_M (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hℓ : ℓ ≠ 0) {x y : F} (h : (curveF ℓ).toAffine.Nonsingular x y)
    {r₁ r₂ r₃ : F} (h₁ : x = r₁ ^ 2) (h₂ : x - ℓ = r₂ ^ 2) (h₃ : x + 3 * ℓ = r₃ ^ 2) :
    ∃ Q : (curveF ℓ).toAffine.Point, 2 • Q = .some x y h := by
  subst h₁
  have u : r₁ ^ 2 - ℓ = r₂ ^ 2 := h₂
  have v : r₁ ^ 2 + 3 * ℓ = r₃ ^ 2 := h₃
  set x' := r₁ ^ 2 + r₁ * r₂ + r₁ * r₃ + r₂ * r₃ with hx'
  set y' := (r₁ + r₂) * (r₁ + r₃) * (r₂ + r₃) with hy'
  have hQ : (curveF ℓ).toAffine.Equation x' y' := by
    rw [curve_equation_iff, hx', hy']
    linear_combination (-((r₁ + r₂) * (r₁ + r₃)) * ((r₁ + r₃) * (r₂ + r₃))) * u +
      (-((r₁ + r₂) * (r₁ + r₃)) * ((r₁ + r₂) * (r₂ + r₃)) -
        ((r₁ + r₂) * (r₁ + r₃)) * (r₁ ^ 2 - ℓ - r₂ ^ 2)) * v
  have hy0 : y' ≠ 0 := by
    have h12 : r₁ + r₂ ≠ 0 := by
      intro h0; apply hℓ
      have : r₁ = -r₂ := by linear_combination h0
      rw [this] at u; linear_combination -u
    have h13 : r₁ + r₃ ≠ 0 := by
      intro h0; apply hℓ
      have : r₁ = -r₃ := by linear_combination h0
      rw [this] at v
      have : (3 : F) * ℓ = 0 := by linear_combination v
      exact (mul_eq_zero.mp this).resolve_left h3
    have h23 : r₂ + r₃ ≠ 0 := by
      intro h0; apply hℓ
      have : r₂ = -r₃ := by linear_combination h0
      rw [this] at u
      have : (2 : F) ^ 2 * ℓ = 0 := by linear_combination v - u
      exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero 2 h2)
    exact mul_ne_zero (mul_ne_zero h12 h13) h23
  have hyn : y' ≠ (curveF ℓ).toAffine.negY x' y' := by
    rw [curve_negY]; intro h0; apply hy0
    have : (2 : F) * y' = 0 := by linear_combination h0
    exact (mul_eq_zero.mp this).resolve_left h2
  have hyy : y' - -y' ≠ 0 := by
    intro h0; apply hy0
    have : (2 : F) * y' = 0 := by linear_combination h0
    exact (mul_eq_zero.mp this).resolve_left h2
  have hsl : (curveF ℓ).toAffine.slope x' x' y' y' = r₁ + r₂ + r₃ := by
    rw [Affine.slope_of_Y_ne rfl hyn, curve_negY, div_eq_iff hyy]
    simp only [curveF_a₁, curveF_a₂, curveF_a₄, zero_mul, sub_zero]
    rw [hx', hy']
    linear_combination (((r₁ + r₂) * (r₁ + r₃)) + ((r₁ + r₃) * (r₂ + r₃))) * u +
      (((r₁ + r₂) * (r₁ + r₃)) + ((r₁ + r₂) * (r₂ + r₃)) + (r₁ ^ 2 - ℓ - r₂ ^ 2)) * v
  have hX : (curveF ℓ).toAffine.addX x' x' ((curveF ℓ).toAffine.slope x' x' y' y') = r₁ ^ 2 := by
    rw [hsl]
    simp only [Affine.addX, curveF_a₁, curveF_a₂, zero_mul, add_zero]
    rw [hx']
    linear_combination -u - v
  have hQn : (curveF ℓ).toAffine.Nonsingular x' y' := curve_nonsingular h2 h3 hℓ hQ
  set Q : (curveF ℓ).toAffine.Point := .some x' y' hQn
  have h2Q : 2 • Q = Point.some _ _ (nonsingular_add hQn hQn fun hxy => hyn hxy.right) := by
    rw [two_nsmul]; exact Point.add_self_of_Y_ne hyn
  rcases some_eq_or_eq_neg_M h _ hX with e | e
  · exact ⟨Q, by rw [h2Q, e]⟩
  · exact ⟨-Q, by rw [two_nsmul, ← neg_add, ← two_nsmul, h2Q, e]⟩

theorem fd_neg3 : fd ℓ (-3 * ℓ) = 12 * ℓ ^ 2 := by unfold fd; ring
theorem fd_ell : fd ℓ ℓ = 4 * ℓ ^ 2 := by unfold fd; ring

/-- **`ker δ ⊆ 2E`** over any field with `2, 3 ≠ 0`, with no hypothesis on `ℓ` (the root cases
are halved too). -/
theorem deltaM_eq_one_imp (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hℓ : ℓ ≠ 0)
    (P : (curveF ℓ).toAffine.Point) (h1 : deltaM ℓ P = 1) : ∃ Q, 2 • Q = P := by
  rcases P with _ | ⟨x, y, h⟩
  · exact ⟨0, by simp; rfl⟩
  have hf := congrArg Prod.fst h1
  have hs := congrArg Prod.snd h1
  simp only [deltaM, Prod.fst_one, Prod.snd_one, kum_some] at hf hs
  have heq : y ^ 2 = x * (x - ℓ) * (x + 3 * ℓ) := by
    have := (curve_equation_iff x y).mp h.1; rw [this]; ring
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 ^ 2 by norm_num]; exact pow_ne_zero 2 h2
  have h4ℓ : (4 : F) * ℓ ≠ 0 := mul_ne_zero h4 hℓ
  have h3ℓ : (3 : F) * ℓ ≠ 0 := mul_ne_zero h3 hℓ
  by_cases hx3 : x = -3 * ℓ
  · have hxl : x ≠ ℓ := fun h' => h4ℓ (by linear_combination hx3 - h')
    rw [if_pos hx3, fd_neg3, show (12 : F) * ℓ ^ 2 = 3 * (2 * ℓ) ^ 2 by ring,
      sqc_mul_sq _ (mul_ne_zero h2 hℓ)] at hf
    rw [if_neg hxl] at hs
    obtain ⟨s, hs0, hs'⟩ := (sqc_eq_one_iff_exists h3).mp hf
    obtain ⟨t, ht0, ht'⟩ := (sqc_eq_one_iff_exists (by
      intro h0; apply h4ℓ; linear_combination hx3 - h0)).mp hs
    exact exists_two_nsmul_eq_M h2 h3 hℓ h (r₁ := s * t / 2) (r₂ := t) (r₃ := 0)
      (by rw [show (s * t / 2) ^ 2 = s ^ 2 * t ^ 2 / 4 by rw [div_pow, mul_pow]; norm_num, eq_div_iff h4]
          linear_combination hx3 + 3 * ht' + t ^ 2 * hs')
      ht' (by rw [hx3]; ring)
  by_cases hx1 : x = ℓ
  · rw [if_neg hx3] at hf
    obtain ⟨s, hs0, hs'⟩ := (sqc_eq_one_iff_exists (by
      intro h0; apply h4ℓ; linear_combination h0 - hx1)).mp hf
    exact exists_two_nsmul_eq_M h2 h3 hℓ h (r₁ := s / 2) (r₂ := 0) (r₃ := s)
      (by rw [show (s / 2) ^ 2 = s ^ 2 / 4 by rw [div_pow]; norm_num, eq_div_iff h4]
          linear_combination hs' + 3 * hx1)
      (by rw [hx1]; ring) (by linear_combination hs')
  rw [if_neg hx3] at hf
  rw [if_neg hx1] at hs
  have hxa : x + 3 * ℓ ≠ 0 := fun h0 => hx3 (by linear_combination h0)
  have hxb : x - ℓ ≠ 0 := sub_ne_zero.mpr hx1
  have hf' : sqc (x + 3 * ℓ) = 1 := by rw [show x + 3 * ℓ = x - -3 * ℓ by ring]; exact hf
  obtain ⟨r₃, hr30, hr₃⟩ := (sqc_eq_one_iff_exists hxa).mp hf'
  obtain ⟨r₂, hr20, hr₂⟩ := (sqc_eq_one_iff_exists hxb).mp hs
  by_cases hx0 : x = 0
  · exact exists_two_nsmul_eq_M h2 h3 hℓ h (r₁ := 0) (r₂ := r₂) (r₃ := r₃)
      (by rw [hx0]; ring) hr₂ hr₃
  have hr0 : r₂ * r₃ ≠ 0 := mul_ne_zero hr20 hr30
  exact exists_two_nsmul_eq_M h2 h3 hℓ h (r₁ := y / (r₂ * r₃))
    (by rw [div_pow, eq_div_iff (pow_ne_zero 2 hr0), heq, hr₂, hr₃]; ring) hr₂ hr₃

theorem isSquare_div_of_sqc_eq {u a : F} (ha : a ≠ 0) (h : u = 0 ∨ sqc u = sqc a) :
    IsSquare (u / a) := by
  rcases h with h | h
  · rw [h, zero_div]; exact ⟨0, by ring⟩
  · by_cases hu : u = 0
    · rw [hu, zero_div]; exact ⟨0, by ring⟩
    · have : sqc (u / a) = 1 := by rw [sqc_div hu ha, h, SqClass.mul_self]
      exact (sqc_eq_one_iff (div_ne_zero hu ha)).mp this

theorem sqc_mul_eq_of {u v x w : F} (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (h : u * v = x * w ^ 2) : sqc u * sqc v = sqc x := by
  rw [← sqc_mul hu hv, h, sqc_mul_sq _ hw]

/-- A rational point whose Kummer classes are those of `a, b` gives `LocM F ℓ a b`. -/
theorem locM_of_deltaM (hF2 : (2 : F) ≠ 0) (hF3 : (3 : F) ≠ 0) (hℓ : ℓ ≠ 0) {a b : F} (ha : a ≠ 0) (hb : b ≠ 0)
    (P : (curveF ℓ).toAffine.Point) (h1 : sqc a = (deltaM ℓ P).1)
    (h2 : sqc b = (deltaM ℓ P).2) : LocM F ℓ a b := by
  rcases P with _ | ⟨x, y, h⟩
  · left
    simp only [deltaM, kum_zero] at h1 h2
    exact ⟨(sqc_eq_one_iff ha).mp (h1.trans rfl), (sqc_eq_one_iff hb).mp (h2.trans rfl)⟩
  right
  refine ⟨x, ?_⟩
  simp only [deltaM, kum_some] at h1 h2
  have heq : y ^ 2 = x * (x - ℓ) * (x + 3 * ℓ) := by
    have := (curve_equation_iff x y).mp h.1; rw [this]; ring
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 ^ 2 by norm_num]; exact pow_ne_zero 2 hF2
  have h12 : (12 : F) ≠ 0 := by
    rw [show (12 : F) = 2 ^ 2 * 3 by norm_num]; exact mul_ne_zero (pow_ne_zero 2 hF2) hF3
  have h4ℓ : (4 : F) * ℓ ≠ 0 := mul_ne_zero h4 hℓ
  have h3ℓ : ℓ ≠ -3 * ℓ := fun h' => h4ℓ (by linear_combination h')
  by_cases hx3 : x = -3 * ℓ
  · rw [if_pos hx3] at h1
    rw [if_neg (by rw [hx3]; exact h3ℓ.symm)] at h2
    subst hx3
    refine ⟨isSquare_div_of_sqc_eq ha (Or.inl (by ring)), isSquare_div_of_sqc_eq hb
      (Or.inr h2.symm), isSquare_div_of_sqc_eq hab (Or.inr ?_)⟩
    rw [sqc_mul ha hb, h1, h2, fd_neg3]
    exact (sqc_mul_eq_of (mul_ne_zero h12 (pow_ne_zero 2 hℓ))
      (by intro h0; apply h4ℓ; linear_combination -h0)
      h4ℓ (by ring)).symm
  by_cases hx1 : x = ℓ
  · rw [if_neg hx3] at h1
    rw [if_pos hx1] at h2
    subst hx1
    refine ⟨isSquare_div_of_sqc_eq ha (Or.inr ?_), isSquare_div_of_sqc_eq hb (Or.inl (by ring)),
      isSquare_div_of_sqc_eq hab (Or.inr ?_)⟩
    · rw [h1]; congr 1; ring
    · rw [sqc_mul ha hb, h1, h2, fd_ell]
      exact (sqc_mul_eq_of (by intro h0; apply h4ℓ; linear_combination h0)
        (mul_ne_zero h4 (pow_ne_zero 2 hℓ))
        h4ℓ (by ring)).symm
  rw [if_neg hx3] at h1
  rw [if_neg hx1] at h2
  have hxa : x - -3 * ℓ = x + 3 * ℓ := by ring
  rw [hxa] at h1
  refine ⟨isSquare_div_of_sqc_eq ha (Or.inr h1.symm), isSquare_div_of_sqc_eq hb (Or.inr h2.symm),
    isSquare_div_of_sqc_eq hab ?_⟩
  by_cases hx0 : x = 0
  · exact Or.inl hx0
  right
  have hxa' : x + 3 * ℓ ≠ 0 := fun h0 => hx3 (by linear_combination h0)
  have hxb : x - ℓ ≠ 0 := sub_ne_zero.mpr hx1
  have hy : y ≠ 0 := by
    intro h0; rw [h0] at heq
    have : x * (x - ℓ) * (x + 3 * ℓ) = 0 := by linear_combination -heq
    simp only [mul_eq_zero] at this
    tauto
  rw [sqc_mul ha hb, h1, h2]
  exact (sqc_mul_eq_of hxa' hxb (div_ne_zero hy hx0) (by
    field_simp; linear_combination -heq)).symm

theorem ker_two_nsmul_eq_F (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hℓ : ℓ ≠ 0) :
    (((nsmulAddMonoidHom 2 : (curveF ℓ).toAffine.Point →+ _).ker :
        AddSubgroup _) : Set (curveF ℓ).toAffine.Point) =
      {0, tPt h2 h3 hℓ (isRootM_zero ℓ), tPt h2 h3 hℓ (isRootM_ell ℓ), tPt h2 h3 hℓ (isRootM_neg3 ℓ)} := by
  ext P
  simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  rcases P with _ | ⟨x, y, h⟩
  · exact iff_of_true (nsmul_zero 2) (Or.inl rfl)
  rw [two_nsmul_some_eq_zero_iff h2]
  constructor
  · intro hy
    have e := (curve_equation_iff x y).mp h.1
    rw [hy] at e
    have : x * (x - ℓ) * (x + 3 * ℓ) = 0 := by linear_combination -e
    right
    rcases mul_eq_zero.mp this with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · left; exact some_eq_tPt h2 h3 hℓ (isRootM_zero ℓ) h h''
      · right; left; exact some_eq_tPt h2 h3 hℓ (isRootM_ell ℓ) h (sub_eq_zero.mp h'')
    · right; right
      exact some_eq_tPt h2 h3 hℓ (isRootM_neg3 ℓ) h (by linear_combination h')
  · rintro (h0 | h0 | h0 | h0)
    · exact absurd h0 (by simp)
    all_goals
      unfold tPt at h0
      simp only [Point.some.injEq] at h0
      exact h0.2

theorem card_ker_two_nsmul_eq_four_F (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hℓ : ℓ ≠ 0) :
    Nat.card (nsmulAddMonoidHom 2 : (curveF ℓ).toAffine.Point →+ _).ker = 4 := by
  have hx : ∀ {e e' : F} (he : IsRootM ℓ e) (he' : IsRootM ℓ e'),
      tPt h2 h3 hℓ he = tPt h2 h3 hℓ he' → e = e' := by
    intro e e' he he' h
    unfold tPt at h
    simp only [Point.some.injEq] at h
    exact h.1
  have hz : ∀ {e : F} (he : IsRootM ℓ e), (0 : (curveF ℓ).toAffine.Point) ≠ tPt h2 h3 hℓ he := by
    intro e he h
    unfold tPt at h
    exact Point.some_ne_zero _ h.symm
  have h4ℓ : (4 : F) * ℓ ≠ 0 :=
    mul_ne_zero (by rw [show (4 : F) = 2 ^ 2 by norm_num]; exact pow_ne_zero 2 h2) hℓ
  have h3ℓ : (3 : F) * ℓ ≠ 0 := mul_ne_zero h3 hℓ
  rw [← SetLike.coe_sort_coe, ker_two_nsmul_eq_F h2 h3 hℓ, Nat.card_coe_set_eq]
  rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair]
  · intro h; have := hx _ _ h; apply h4ℓ; linear_combination this
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => hℓ (hx _ _ h).symm, fun h => h3ℓ (by linear_combination hx _ _ h)⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hz _, hz _, hz _⟩


/-! ### Over a finite field: the Kummer map is onto, so every pair is a local class -/

section Finite

variable [Fintype F]

/-- The points over a finite field form a finite set. -/
theorem finite_points (ℓ : F) : Finite (curveF ℓ).toAffine.Point := by
  refine Finite.of_injective (β := Option (F × F))
    (fun P => match P with
      | .zero => none
      | .some x y _ => some (x, y)) ?_
  intro P Q h
  rcases P with _ | ⟨x, y, hP⟩ <;> rcases Q with _ | ⟨x', y', hQ⟩
  · rfl
  · simp at h
  · simp at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl

/-- `#(G/2G) = #G[2]` for a finite abelian group. -/
theorem card_quotient_two_eq {G : Type*} [AddCommGroup G] [Finite G] :
    Nat.card (G ⧸ (nsmulAddMonoidHom 2 : G →+ G).range) =
      Nat.card (nsmulAddMonoidHom 2 : G →+ G).ker := by
  have e1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
    (nsmulAddMonoidHom 2 : G →+ G).range
  have e2 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
    (nsmulAddMonoidHom 2 : G →+ G).ker
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange _).toEquiv] at e2
  have hpos : 0 < Nat.card (nsmulAddMonoidHom 2 : G →+ G).range := Nat.card_pos
  have : Nat.card (G ⧸ (nsmulAddMonoidHom 2 : G →+ G).range) *
      Nat.card (nsmulAddMonoidHom 2 : G →+ G).range =
      Nat.card (nsmulAddMonoidHom 2 : G →+ G).ker *
      Nat.card (nsmulAddMonoidHom 2 : G →+ G).range := by
    rw [← e1, e2, mul_comm]
  exact Nat.eq_of_mul_eq_mul_right hpos this

/-- In a finite field of odd characteristic, the square classes are `1` and the class of a fixed
nonsquare. -/
theorem sqc_eq_one_or (hc : ringChar F ≠ 2) {g : F} (hg : ¬ IsSquare g) (c : SqClass F) :
    c = 1 ∨ c = sqc g := by
  obtain ⟨x, hx, rfl⟩ := SqClass.exists_eq_sqc c
  have hg0 : g ≠ 0 := by rintro rfl; exact hg ⟨0, by ring⟩
  by_cases hsx : IsSquare x
  · exact Or.inl ((sqc_eq_one_iff hx).mpr hsx)
  · right
    have hm : quadraticChar F (x * g) = 1 := by
      rw [map_mul, quadraticChar_neg_one_iff_not_isSquare.mpr hsx,
        quadraticChar_neg_one_iff_not_isSquare.mpr hg]
      norm_num
    obtain ⟨r, hr⟩ := (quadraticChar_one_iff_isSquare (mul_ne_zero hx hg0)).mp hm
    have hr0 : r ≠ 0 := by
      rintro rfl; rw [mul_zero] at hr; exact mul_ne_zero hx hg0 hr
    refine (sqc_eq_sqc_iff hx hg0).mpr ⟨r / g, div_ne_zero hr0 hg0, ?_⟩
    rw [div_pow, ← mul_div_assoc, eq_div_iff (pow_ne_zero 2 hg0)]
    linear_combination g * hr

/-- **Every pair of nonzero elements of a finite field of characteristic `≠ 2, 3` is a local
Kummer class of `y² = x(x − ℓ)(x + 3ℓ)`** (`ℓ ≠ 0`): the Kummer map `E(F) → (F*/F*²)²` has
kernel `2E(F)`, so its image has `#E(F)[2] = 4` elements, the whole target. -/
theorem locM_finite (hc : ringChar F ≠ 2) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hℓ : ℓ ≠ 0)
    {α β : F} (hα : α ≠ 0) (hβ : β ≠ 0) : LocM F ℓ α β := by
  haveI := finite_points ℓ
  obtain ⟨g, hg⟩ := FiniteField.exists_nonsquare hc
  set δ := deltaHomM h2 h3 hℓ
  -- `ker δ = 2E`
  have hker : δ.ker = (nsmulAddMonoidHom 2 : (curveF ℓ).toAffine.Point →+ _).range := by
    ext P
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_range]
    simp only [nsmulAddMonoidHom_apply]
    constructor
    · intro h; exact deltaM_eq_one_imp h2 h3 hℓ P (congrArg Additive.toMul h)
    · rintro ⟨Q, rfl⟩; exact congrArg Additive.ofMul (deltaM_two_nsmul h2 h3 hℓ Q)
  -- `#range δ = 4`
  have hrange : Nat.card δ.range = 4 := by
    rw [← Nat.card_congr (QuotientAddGroup.quotientKerEquivRange δ).toEquiv, hker,
      card_quotient_two_eq, card_ker_two_nsmul_eq_four_F h2 h3 hℓ]
  -- the target has at most four elements
  have hsurj : Function.Surjective (fun b : Bool => if b then sqc g else (1 : SqClass F)) := by
    intro c
    rcases sqc_eq_one_or hc hg c with h | h
    · exact ⟨false, by simp [h]⟩
    · exact ⟨true, by simp [h]⟩
  haveI : Finite (SqClass F) := Finite.of_surjective _ hsurj
  have hcard2 : Nat.card (SqClass F) ≤ 2 := by
    have := Nat.card_le_card_of_surjective _ hsurj
    simpa using this
  have hcardT : Nat.card (Additive (SqClass F × SqClass F)) ≤ 4 := by
    show Nat.card (SqClass F × SqClass F) ≤ 4
    rw [Nat.card_prod]
    nlinarith [Nat.zero_le (Nat.card (SqClass F))]
  have htop : δ.range = ⊤ := by
    refine AddSubgroup.eq_top_of_card_eq _ (le_antisymm ?_ ?_)
    · haveI : Finite (Additive (SqClass F × SqClass F)) :=
        inferInstanceAs (Finite (SqClass F × SqClass F))
      exact Nat.card_le_card_of_injective _ Subtype.val_injective
    · rw [hrange]; exact hcardT
  obtain ⟨P, hP⟩ : Additive.ofMul (sqc α, sqc β) ∈ δ.range := by rw [htop]; trivial
  have hP' : deltaM ℓ P = (sqc α, sqc β) := congrArg Additive.toMul hP
  exact locM_of_deltaM h2 h3 hℓ hα hβ P (by rw [hP']) (by rw [hP'])

end Finite

end ZInQ.Manuscript.PoleS12.GoodF
