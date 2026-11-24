import ZInQKernel.Contrib.PoleRC.KummerM
import ZInQKernel.RouteK.Rank.RK9

/-!
# The complete 2-descent of `E_ℓ` and the proof of `DescentGlueM`

* `deltaM ℓ P = (kum ℓ (−3ℓ) P, kum ℓ ℓ P)`: the Kummer map in the manuscript's coordinates
  `(x + 3ℓ, x − ℓ)`; a homomorphism (`deltaHomM`).
* `exists_two_nsmul_eq_M` (halving): if `x`, `x − ℓ`, `x + 3ℓ` are squares, `(x, y) ∈ 2E_ℓ(ℚ)`.
* `deltaM_eq_one_iff`: for `ℓ > 0` not a square, `ker δ = 2E_ℓ(ℚ)`.
* `selRepM_mem_selM`: the squarefree representatives of `δ(P)` lie in `SelM ℓ`.
* `card_ker_two_nsmul_eq_four_M`: `#E_ℓ(ℚ)[2] = 4`.
* `descentGlueM`: **`DescentGlueM` holds** (counting as Route K's RK9,
  `RouteK.Rank.loc_of_mem_sel2_of_infinite_order`).
-/

namespace ZInQ.Manuscript.PoleRC

open WeierstrassCurve WeierstrassCurve.Affine ZInQ.Descent ZInQ.RouteK.Rank

variable {ℓ : ℚ}

theorem isRootM_neg3 (ℓ : ℚ) : IsRootM ℓ (-3 * ℓ) := by unfold IsRootM; ring
theorem isRootM_ell (ℓ : ℚ) : IsRootM ℓ ℓ := by unfold IsRootM; ring
theorem isRootM_zero (ℓ : ℚ) : IsRootM ℓ 0 := by unfold IsRootM; ring

/-- The complete 2-descent map of `E_ℓ` in the coordinates `(x + 3ℓ, x − ℓ)`. -/
noncomputable def deltaM (ℓ : ℚ) (P : (curve ℓ).toAffine.Point) : SqClass ℚ × SqClass ℚ :=
  (kum ℓ (-3 * ℓ) P, kum ℓ ℓ P)

theorem deltaM_add (hℓ : ℓ ≠ 0) (P Q : (curve ℓ).toAffine.Point) :
    deltaM ℓ (P + Q) = deltaM ℓ P * deltaM ℓ Q := by
  simp only [deltaM, kum_add hℓ (isRootM_neg3 ℓ), kum_add hℓ (isRootM_ell ℓ), Prod.mk_mul_mk]

/-- The complete 2-descent map as a homomorphism. -/
noncomputable def deltaHomM (hℓ : ℓ ≠ 0) :
    (curve ℓ).toAffine.Point →+ Additive (SqClass ℚ × SqClass ℚ) where
  toFun P := Additive.ofMul (deltaM ℓ P)
  map_zero' := rfl
  map_add' P Q := by rw [deltaM_add hℓ]; rfl

theorem deltaM_two_nsmul (hℓ : ℓ ≠ 0) (P : (curve ℓ).toAffine.Point) :
    deltaM ℓ (2 • P) = 1 := by
  rw [two_nsmul, deltaM_add hℓ]
  ext <;> simp [SqClass.mul_self]

theorem two_nsmul_some_eq_zero_iff {x y : ℚ} (h : (curve ℓ).toAffine.Nonsingular x y) :
    2 • Point.some x y h = 0 ↔ y = 0 := by
  rw [two_nsmul, add_eq_zero_iff_eq_neg, Point.neg_some, Point.some.injEq, curve_negY]
  constructor
  · rintro ⟨-, h'⟩; linarith
  · intro h'; exact ⟨rfl, by rw [h']; ring⟩

/-- Two points with the same abscissa are equal or opposite. -/
theorem some_eq_or_eq_neg_M {x y X Y : ℚ} (h : (curve ℓ).toAffine.Nonsingular x y)
    (h' : (curve ℓ).toAffine.Nonsingular X Y) (hX : X = x) :
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
theorem exists_two_nsmul_eq_M (hℓ : ℓ ≠ 0) {x y : ℚ} (h : (curve ℓ).toAffine.Nonsingular x y)
    {r₁ r₂ r₃ : ℚ} (h₁ : x = r₁ ^ 2) (h₂ : x - ℓ = r₂ ^ 2) (h₃ : x + 3 * ℓ = r₃ ^ 2) :
    ∃ Q : (curve ℓ).toAffine.Point, 2 • Q = .some x y h := by
  subst h₁
  have u : r₁ ^ 2 - ℓ = r₂ ^ 2 := h₂
  have v : r₁ ^ 2 + 3 * ℓ = r₃ ^ 2 := h₃
  set x' := r₁ ^ 2 + r₁ * r₂ + r₁ * r₃ + r₂ * r₃ with hx'
  set y' := (r₁ + r₂) * (r₁ + r₃) * (r₂ + r₃) with hy'
  have hQ : (curve ℓ).toAffine.Equation x' y' := by
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
      rw [this] at v; linear_combination v / 3
    have h23 : r₂ + r₃ ≠ 0 := by
      intro h0; apply hℓ
      have : r₂ = -r₃ := by linear_combination h0
      rw [this] at u; linear_combination (v - u) / 4
    exact mul_ne_zero (mul_ne_zero h12 h13) h23
  have hyn : y' ≠ (curve ℓ).toAffine.negY x' y' := by
    rw [curve_negY]; intro h0; apply hy0; linarith
  have hyy : y' - -y' ≠ 0 := by intro h0; apply hy0; linarith
  have hsl : (curve ℓ).toAffine.slope x' x' y' y' = r₁ + r₂ + r₃ := by
    rw [Affine.slope_of_Y_ne rfl hyn, curve_negY, div_eq_iff hyy]
    simp only [curve_a₁, curve_a₂, curve_a₄, zero_mul, sub_zero]
    rw [hx', hy']
    linear_combination (((r₁ + r₂) * (r₁ + r₃)) + ((r₁ + r₃) * (r₂ + r₃))) * u +
      (((r₁ + r₂) * (r₁ + r₃)) + ((r₁ + r₂) * (r₂ + r₃)) + (r₁ ^ 2 - ℓ - r₂ ^ 2)) * v
  have hX : (curve ℓ).toAffine.addX x' x' ((curve ℓ).toAffine.slope x' x' y' y') = r₁ ^ 2 := by
    rw [hsl]
    simp only [Affine.addX, curve_a₁, curve_a₂, zero_mul, add_zero]
    rw [hx']
    linear_combination -u - v
  have hQn : (curve ℓ).toAffine.Nonsingular x' y' := curve_nonsingular hℓ hQ
  set Q : (curve ℓ).toAffine.Point := .some x' y' hQn
  have h2Q : 2 • Q = Point.some _ _ (nonsingular_add hQn hQn fun hxy => hyn hxy.right) := by
    rw [two_nsmul]; exact Point.add_self_of_Y_ne hyn
  rcases some_eq_or_eq_neg_M h _ hX with e | e
  · exact ⟨Q, by rw [h2Q, e]⟩
  · exact ⟨-Q, by rw [two_nsmul, ← neg_add, ← two_nsmul, h2Q, e]⟩

theorem not_isSquare_three_rat : ¬ IsSquare (3 : ℚ) := by
  rw [show (3 : ℚ) = ((3 : ℕ) : ℚ) by norm_num, Rat.isSquare_natCast_iff]
  rintro ⟨r, hr⟩
  have : r ≤ 1 ∨ 2 ≤ r := by omega
  rcases this with h | h
  · interval_cases r <;> omega
  · nlinarith

theorem fd_neg3 : fd ℓ (-3 * ℓ) = 12 * ℓ ^ 2 := by unfold fd; ring
theorem fd_ell : fd ℓ ℓ = 4 * ℓ ^ 2 := by unfold fd; ring

theorem sqc_ne_one_of_not_isSquare {q : ℚ} (hq : q ≠ 0) (h : ¬ IsSquare q) : sqc q ≠ 1 :=
  fun h1 => h ((sqc_eq_one_iff hq).mp h1)

/-- **`ker δ = 2E_ℓ(ℚ)`** for `ℓ > 0` not a square. -/
theorem deltaM_eq_one_iff (hℓ : 0 < ℓ) (hns : ¬ IsSquare ℓ) (P : (curve ℓ).toAffine.Point) :
    deltaM ℓ P = 1 ↔ ∃ Q, 2 • Q = P := by
  have hℓ0 : ℓ ≠ 0 := hℓ.ne'
  constructor
  swap
  · rintro ⟨Q, rfl⟩; exact deltaM_two_nsmul hℓ0 Q
  intro h1
  rcases P with _ | ⟨x, y, h⟩
  · exact ⟨0, by simp; rfl⟩
  have hf := congrArg Prod.fst h1
  have hs := congrArg Prod.snd h1
  simp only [deltaM, Prod.fst_one, Prod.snd_one, kum_some] at hf hs
  have heq : y ^ 2 = x * (x - ℓ) * (x + 3 * ℓ) := by
    have := (curve_equation_iff x y).mp h.1; rw [this]; ring
  by_cases hx3 : x = -3 * ℓ
  · exfalso
    simp only [hx3, ↓reduceIte, fd] at hf
    rw [show 3 * (-3 * ℓ) ^ 2 + 4 * ℓ * (-3 * ℓ) - 3 * ℓ ^ 2 = 3 * (2 * ℓ) ^ 2 by ring,
      sqc_mul_sq _ (mul_ne_zero two_ne_zero hℓ0)] at hf
    exact sqc_ne_one_of_not_isSquare (by norm_num) not_isSquare_three_rat hf
  by_cases hx1 : x = ℓ
  · exfalso
    simp only [hx1, ↓reduceIte, show ℓ ≠ -3 * ℓ from fun h => hℓ0 (by linarith)] at hf
    rw [show ℓ - -3 * ℓ = ℓ * 2 ^ 2 by ring, sqc_mul_sq _ (by norm_num)] at hf
    exact sqc_ne_one_of_not_isSquare hℓ0 hns hf
  simp only [hx3, ↓reduceIte, sub_neg_eq_add] at hf
  simp only [hx1, ↓reduceIte] at hs
  have hxa : x + 3 * ℓ ≠ 0 := fun h0 => hx3 (by linarith)
  have hxb : x - ℓ ≠ 0 := sub_ne_zero.mpr hx1
  have hf' : sqc (x + 3 * ℓ) = 1 := by rw [show x + 3 * ℓ = x - -3 * ℓ by ring]; exact hf
  obtain ⟨r₃, hr₃⟩ := (sqc_eq_one_iff hxa).mp hf'
  obtain ⟨r₂, hr₂⟩ := (sqc_eq_one_iff hxb).mp hs
  by_cases hx0 : x = 0
  · exfalso
    rw [hx0] at hr₂
    have : (0 : ℚ) ≤ r₂ * r₂ := mul_self_nonneg _
    linarith
  have hr0 : r₂ * r₃ ≠ 0 := by
    intro h0
    apply mul_ne_zero hxb hxa
    rw [hr₂, hr₃]; linear_combination (r₂ * r₃) * h0
  exact exists_two_nsmul_eq_M hℓ0 h (r₁ := y / (r₂ * r₃))
    (by rw [div_pow, eq_div_iff (pow_ne_zero 2 hr0), heq, hr₂, hr₃]; ring)
    (by rw [hr₂]; ring) (by rw [hr₃]; ring)

/-! ### The image lies in `SelM ℓ` -/

theorem isSquare_div_of_sqc_eq {u a : ℚ} (ha : a ≠ 0) (h : u = 0 ∨ sqc u = sqc a) :
    IsSquare (u / a) := by
  rcases h with h | h
  · rw [h, zero_div]; exact ⟨0, by ring⟩
  · by_cases hu : u = 0
    · rw [hu, zero_div]; exact ⟨0, by ring⟩
    · have : sqc (u / a) = 1 := by rw [sqc_div hu ha, h, SqClass.mul_self]
      exact (sqc_eq_one_iff (div_ne_zero hu ha)).mp this

theorem sqc_mul_eq_of {u v x w : ℚ} (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (h : u * v = x * w ^ 2) : sqc u * sqc v = sqc x := by
  rw [← sqc_mul hu hv, h, sqc_mul_sq _ hw]

/-- A rational point whose Kummer classes are those of `a, b` gives `LocM ℚ ℓ a b`. -/
theorem locM_of_deltaM (hℓ : ℓ ≠ 0) {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0)
    (P : (curve ℓ).toAffine.Point) (h1 : sqc a = (deltaM ℓ P).1)
    (h2 : sqc b = (deltaM ℓ P).2) : LocM ℚ ℓ a b := by
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
  have h3ℓ : ℓ ≠ -3 * ℓ := fun h' => hℓ (by linarith)
  by_cases hx3 : x = -3 * ℓ
  · rw [if_pos hx3] at h1
    rw [if_neg (by rw [hx3]; exact h3ℓ.symm)] at h2
    subst hx3
    refine ⟨isSquare_div_of_sqc_eq ha (Or.inl (by ring)), isSquare_div_of_sqc_eq hb
      (Or.inr h2.symm), isSquare_div_of_sqc_eq hab (Or.inr ?_)⟩
    rw [sqc_mul ha hb, h1, h2, fd_neg3]
    exact (sqc_mul_eq_of (mul_ne_zero (by norm_num) (pow_ne_zero 2 hℓ))
      (by intro h0; apply hℓ; linarith)
      (mul_ne_zero (by norm_num : (4 : ℚ) ≠ 0) hℓ) (by ring)).symm
  by_cases hx1 : x = ℓ
  · rw [if_neg hx3] at h1
    rw [if_pos hx1] at h2
    subst hx1
    refine ⟨isSquare_div_of_sqc_eq ha (Or.inr ?_), isSquare_div_of_sqc_eq hb (Or.inl (by ring)),
      isSquare_div_of_sqc_eq hab (Or.inr ?_)⟩
    · rw [h1]; congr 1; ring
    · rw [sqc_mul ha hb, h1, h2, fd_ell]
      exact (sqc_mul_eq_of (by intro h0; apply hℓ; linarith)
        (mul_ne_zero (by norm_num) (pow_ne_zero 2 hℓ))
        (mul_ne_zero (by norm_num : (4 : ℚ) ≠ 0) hℓ) (by ring)).symm
  rw [if_neg hx3] at h1
  rw [if_neg hx1] at h2
  have hxa : x - -3 * ℓ = x + 3 * ℓ := by ring
  rw [hxa] at h1
  refine ⟨isSquare_div_of_sqc_eq ha (Or.inr h1.symm), isSquare_div_of_sqc_eq hb (Or.inr h2.symm),
    isSquare_div_of_sqc_eq hab ?_⟩
  by_cases hx0 : x = 0
  · exact Or.inl hx0
  right
  have hxa' : x + 3 * ℓ ≠ 0 := fun h0 => hx3 (by linarith)
  have hxb : x - ℓ ≠ 0 := sub_ne_zero.mpr hx1
  have hy : y ≠ 0 := by
    intro h0; rw [h0] at heq
    have : x * (x - ℓ) * (x + 3 * ℓ) = 0 := by linarith [heq]
    simp only [mul_eq_zero] at this
    tauto
  rw [sqc_mul ha hb, h1, h2]
  exact (sqc_mul_eq_of hxa' hxb (div_ne_zero hy hx0) (by
    field_simp; linear_combination -heq)).symm

/-- `LocM` transfers along a ring homomorphism of fields. -/
theorem locM_map {K L : Type*} [Field K] [Field L] (f : K →+* L) {ℓ a b : K}
    (h : LocM K ℓ a b) : LocM L (f ℓ) (f a) (f b) := by
  have hsq : ∀ z : K, IsSquare z → IsSquare (f z) := fun z ⟨r, hr⟩ => ⟨f r, by rw [hr, map_mul]⟩
  rcases h with ⟨h1, h2⟩ | ⟨x, h1, h2, h3⟩
  · exact Or.inl ⟨hsq _ h1, hsq _ h2⟩
  · refine Or.inr ⟨f x, ?_, ?_, ?_⟩
    · have := hsq _ h1; simpa [map_div₀, map_add, map_mul, map_ofNat] using this
    · have := hsq _ h2; simpa [map_div₀, map_sub] using this
    · have := hsq _ h3; simpa [map_div₀, map_mul] using this

theorem locM_cast_of_rat {L : Type*} [Field L] [CharZero L] {ℓ : ℕ} {a b : ℤ}
    (h : LocM ℚ ℓ a b) : LocM L ℓ a b := by
  have := locM_map (Rat.castHom L) h
  simpa using this

/-- The squarefree representatives of `δ(P)`. -/
noncomputable def selRepM (ℓ : ℕ) (P : (curve (ℓ : ℚ)).toAffine.Point) : ℤ × ℤ :=
  (sqfRep (deltaM ℓ P).1, sqfRep (deltaM ℓ P).2)

theorem locM_selRepM {ℓ : ℕ} (hℓ : ℓ ≠ 0) (P : (curve (ℓ : ℚ)).toAffine.Point) :
    LocM ℚ ℓ ((selRepM ℓ P).1 : ℚ) ((selRepM ℓ P).2 : ℚ) :=
  locM_of_deltaM (by exact_mod_cast hℓ) (sqfRep_ne_zero _) (sqfRep_ne_zero _) P
    (sqc_sqfRep _) (sqc_sqfRep _)

/-- **The image of the complete 2-descent map lies in `SelM ℓ`.** -/
theorem selRepM_mem_selM {ℓ : ℕ} (hℓ : ℓ ≠ 0) (P : (curve (ℓ : ℚ)).toAffine.Point) :
    selRepM ℓ P ∈ SelM ℓ := by
  have h := locM_selRepM hℓ P
  exact ⟨sqfRep_squarefree _, sqfRep_squarefree _, locM_cast_of_rat h,
    fun p _ => locM_cast_of_rat h⟩

/-! ### `#E_ℓ(ℚ)[2] = 4` -/

theorem ker_two_nsmul_eq_M (hℓ : ℓ ≠ 0) :
    (((nsmulAddMonoidHom 2 : (curve ℓ).toAffine.Point →+ _).ker :
        AddSubgroup _) : Set (curve ℓ).toAffine.Point) =
      {0, tPt hℓ (isRootM_zero ℓ), tPt hℓ (isRootM_ell ℓ), tPt hℓ (isRootM_neg3 ℓ)} := by
  ext P
  simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  rcases P with _ | ⟨x, y, h⟩
  · exact iff_of_true (nsmul_zero 2) (Or.inl rfl)
  rw [two_nsmul_some_eq_zero_iff]
  constructor
  · intro hy
    have e := (curve_equation_iff x y).mp h.1
    rw [hy] at e
    have : x * (x - ℓ) * (x + 3 * ℓ) = 0 := by linear_combination -e
    right
    rcases mul_eq_zero.mp this with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · left; exact some_eq_tPt hℓ (isRootM_zero ℓ) h h''
      · right; left; exact some_eq_tPt hℓ (isRootM_ell ℓ) h (sub_eq_zero.mp h'')
    · right; right
      exact some_eq_tPt hℓ (isRootM_neg3 ℓ) h (by linear_combination h')
  · rintro (h0 | h0 | h0 | h0)
    · exact absurd h0 (by simp)
    all_goals
      unfold tPt at h0
      simp only [Point.some.injEq] at h0
      exact h0.2

theorem card_ker_two_nsmul_eq_four_M (hℓ : ℓ ≠ 0) :
    Nat.card (nsmulAddMonoidHom 2 : (curve ℓ).toAffine.Point →+ _).ker = 4 := by
  have hx : ∀ {e e' : ℚ} (he : IsRootM ℓ e) (he' : IsRootM ℓ e'),
      tPt hℓ he = tPt hℓ he' → e = e' := by
    intro e e' he he' h
    unfold tPt at h
    simp only [Point.some.injEq] at h
    exact h.1
  have hz : ∀ {e : ℚ} (he : IsRootM ℓ e), (0 : (curve ℓ).toAffine.Point) ≠ tPt hℓ he := by
    intro e he h
    unfold tPt at h
    exact Point.some_ne_zero _ h.symm
  rw [← SetLike.coe_sort_coe, ker_two_nsmul_eq_M hℓ, Nat.card_coe_set_eq]
  rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair]
  · intro h; have := hx _ _ h; apply hℓ; linarith
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => hℓ (hx _ _ h).symm, fun h => hℓ (by linarith [hx _ _ h])⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hz _, hz _, hz _⟩

/-! ### The count: `DescentGlueM` -/

theorem deltaHomM_ker_eq (hℓ : 0 < ℓ) (hns : ¬ IsSquare ℓ) :
    (deltaHomM hℓ.ne').ker =
      (nsmulAddMonoidHom 2 : (curve ℓ).toAffine.Point →+ _).range := by
  ext P
  rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_range]
  simp only [nsmulAddMonoidHom_apply]
  rw [← deltaM_eq_one_iff hℓ hns P]
  constructor
  · intro h; exact congrArg Additive.toMul h
  · intro h; exact congrArg Additive.ofMul h

theorem not_isSquare_of_mod_four {ℓ : ℕ} (h : ℓ % 4 = 3) : ¬ IsSquare (ℓ : ℚ) := by
  rw [Rat.isSquare_natCast_iff]
  rintro ⟨r, rfl⟩
  have : r % 4 = 0 ∨ r % 4 = 1 ∨ r % 4 = 2 ∨ r % 4 = 3 := by omega
  rw [Nat.mul_mod] at h
  rcases this with h' | h' | h' | h' <;> rw [h'] at h <;> norm_num at h

theorem card_quotient_two_eq_ncard_range_selRepM {ℓ : ℕ} (hℓ : 0 < ℓ) (h4 : ℓ % 4 = 3) :
    Nat.card ((curve (ℓ : ℚ)).toAffine.Point ⧸
        (nsmulAddMonoidHom 2 : (curve (ℓ : ℚ)).toAffine.Point →+ _).range) =
      (Set.range (selRepM ℓ)).ncard := by
  have hℓ' : (0 : ℚ) < ℓ := by exact_mod_cast hℓ
  set δ := deltaHomM hℓ'.ne'
  rw [← deltaHomM_ker_eq hℓ' (not_isSquare_of_mod_four h4),
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange δ).toEquiv]
  have hsel : Set.range (selRepM ℓ) = repPair '' Set.range δ := by
    rw [← Set.range_comp]; rfl
  rw [hsel, Set.ncard_image_of_injective _ repPair_injective, ← Nat.card_coe_set_eq,
    ← AddMonoidHom.coe_range, SetLike.coe_sort_coe]

/-- **`DescentGlueM` holds.** -/
theorem descentGlueM : DescentGlueM := by
  intro ℓ hℓ _hsf h12 hfg hinf h8
  have hℓ0 : ℓ ≠ 0 := hℓ.ne'
  have hℓq : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ0
  set S := Set.range (selRepM ℓ)
  have hS : S ⊆ SelM ℓ := by rintro _ ⟨P, rfl⟩; exact selRepM_mem_selM hℓ0 P
  have hfin : (SelM ℓ).Finite := Set.finite_of_ncard_ne_zero (by rw [h8]; norm_num)
  have hSfin : S.Finite := hfin.subset hS
  have hSpos : S.ncard ≠ 0 := (Set.ncard_pos hSfin).mpr ⟨_, 0, rfl⟩ |>.ne'
  have hcard := card_quotient_two_eq_ncard_range_selRepM hℓ (by omega)
  have : Finite ((curve (ℓ : ℚ)).toAffine.Point ⧸
      (nsmulAddMonoidHom 2 : (curve (ℓ : ℚ)).toAffine.Point →+ _).range) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact hSpos)
  have h8le := eight_le_card_quotient_two (card_ker_two_nsmul_eq_four_M hℓq) hinf
  rw [hcard] at h8le
  have hSeq : S = SelM ℓ := Set.eq_of_subset_of_ncard_le hS (by rw [h8]; exact h8le) hfin
  intro ab hab
  rw [← hSeq] at hab
  obtain ⟨P, rfl⟩ := hab
  exact locM_selRepM hℓ0 P

end ZInQ.Manuscript.PoleRC
