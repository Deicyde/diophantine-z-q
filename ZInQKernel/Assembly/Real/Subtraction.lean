import ZInQKernel.Model.Field.ShortWeierstrass

/-!
# Compactness and continuity of subtraction on a real curve

Blueprint: `assembly/approximation/real-subtraction.md`.

For `e ≠ 0`, `E_e(ℝ)` is the group of real points of `y² = x³ - e²x` (`realCurve e`, the short
Weierstrass curve `shortCurve (-e²)`). Mathlib has no topology on elliptic curve points; the
article's sequential notion of convergence `P_m → Q` is the predicate `TendstoPt P Q`, stated for
any Weierstrass curve over `ℝ`. We prove

1. every sequence has a convergent subsequence (`exists_subseq_tendstoPt`);
2. if `P_m → Q` and `P'_m → Q` then `P'_m - P_m → O` (`tendstoPt_sub_zero`).
-/

namespace ZInQ.Assembly

open WeierstrassCurve WeierstrassCurve.Affine Filter Topology

/-- The real curve `E_e : y² = x³ - e²x`. -/
noncomputable abbrev realCurve (e : ℝ) : WeierstrassCurve ℝ := shortCurve (-e ^ 2)

namespace RealCurve

section General

variable {W : WeierstrassCurve ℝ}

/-- The abscissa of a point; the junk value at `O` is `0`. -/
def ptX : W.toAffine.Point → ℝ
  | .zero => 0
  | .some x _ _ => x

/-- The ordinate of a point; the junk value at `O` is `0`. -/
def ptY : W.toAffine.Point → ℝ
  | .zero => 0
  | .some _ y _ => y

@[simp] theorem ptX_zero : ptX (0 : W.toAffine.Point) = 0 := rfl
@[simp] theorem ptY_zero : ptY (0 : W.toAffine.Point) = 0 := rfl
@[simp] theorem ptX_some {x y : ℝ} (h : W.toAffine.Nonsingular x y) : ptX (.some x y h) = x := rfl
@[simp] theorem ptY_some {x y : ℝ} (h : W.toAffine.Nonsingular x y) : ptY (.some x y h) = y := rfl

/-- **Convergence of a sequence of points.** `TendstoPt P Q` (`P_m → Q`) means:
* if `Q = (x_Q, y_Q)` is affine: `P_m` is affine for all large `m`, `x(P_m) → x_Q` and
  `y(P_m) → y_Q`;
* if `Q = O`: for every `M`, for all large `m`, either `P_m = O` or `P_m` is affine with
  `x(P_m) > M`. -/
def TendstoPt (P : ℕ → W.toAffine.Point) : W.toAffine.Point → Prop
  | .zero => ∀ M : ℝ, ∀ᶠ m in atTop, P m = 0 ∨ M < ptX (P m)
  | .some x₀ y₀ _ => (∀ᶠ m in atTop, P m ≠ 0) ∧
      Tendsto (fun m => ptX (P m)) atTop (𝓝 x₀) ∧ Tendsto (fun m => ptY (P m)) atTop (𝓝 y₀)

theorem tendstoPt_zero_iff {P : ℕ → W.toAffine.Point} :
    TendstoPt P 0 ↔ ∀ M : ℝ, ∀ᶠ m in atTop, P m = 0 ∨ M < ptX (P m) := Iff.rfl

theorem tendstoPt_some_iff {P : ℕ → W.toAffine.Point} {x₀ y₀ : ℝ}
    {h₀ : W.toAffine.Nonsingular x₀ y₀} :
    TendstoPt P (.some x₀ y₀ h₀) ↔ (∀ᶠ m in atTop, P m ≠ 0) ∧
      Tendsto (fun m => ptX (P m)) atTop (𝓝 x₀) ∧ Tendsto (fun m => ptY (P m)) atTop (𝓝 y₀) :=
  Iff.rfl

theorem eq_some_of_ne_zero {P : W.toAffine.Point} (hP : P ≠ 0) :
    ∃ h, P = .some (ptX P) (ptY P) h := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y h => exact ⟨h, rfl⟩

end General

/-! ### The curve `y² = x³ - e²x` -/

variable {e : ℝ}

theorem equation_iff (e x y : ℝ) :
    (realCurve e).toAffine.Equation x y ↔ y ^ 2 = x ^ 3 - e ^ 2 * x := by
  rw [shortCurve_equation_iff]; constructor <;> intro h <;> linarith

theorem isElliptic (he : e ≠ 0) : (realCurve e).IsElliptic :=
  shortCurve_isElliptic (neg_ne_zero.mpr (pow_ne_zero 2 he))

theorem nonsingular_of_equation (he : e ≠ 0) {x y : ℝ} (h : (realCurve e).toAffine.Equation x y) :
    (realCurve e).toAffine.Nonsingular x y := by
  have := isElliptic he
  exact equation_iff_nonsingular.mp h

/-- The equation at the coordinates of an affine point. -/
theorem sq_ptY {P : (realCurve e).toAffine.Point} (hP : P ≠ 0) :
    ptY P ^ 2 = ptX P ^ 3 - e ^ 2 * ptX P := by
  obtain ⟨h, -⟩ := eq_some_of_ne_zero hP
  exact (equation_iff _ _ _).mp h.1

/-- Real points have `x ≥ -|e|`. -/
theorem neg_abs_le_of_sq {x y : ℝ} (h : y ^ 2 = x ^ 3 - e ^ 2 * x) : -|e| ≤ x := by
  by_contra hx
  push Not at hx
  have hx0 : x < 0 := lt_of_lt_of_le hx (by linarith [abs_nonneg e])
  have hsq : e ^ 2 < x ^ 2 := by
    rw [← sq_abs e]; nlinarith [abs_nonneg e]
  have : x * (x ^ 2 - e ^ 2) < 0 := mul_neg_of_neg_of_pos hx0 (by linarith)
  nlinarith [sq_nonneg y]

/-- The derivative of `x³ - e²x` does not vanish at a root. -/
theorem deriv_ne_zero_of_root (he : e ≠ 0) {c : ℝ} (hc : c ^ 3 - e ^ 2 * c = 0) :
    3 * c ^ 2 - e ^ 2 ≠ 0 := by
  have he2 : 0 < e ^ 2 := by positivity
  intro h
  have h1 : c * (c ^ 2 - e ^ 2) = 0 := by linear_combination hc
  rcases mul_eq_zero.mp h1 with h0 | h0
  · subst h0; linarith
  · have : c ^ 2 = e ^ 2 := by linarith
    linarith

/-! ### The difference of two affine points -/

/-- The difference `P' - P` of two affine points of `y² = x³ + Ax` is `O`, or affine with
abscissa `ℓ² - x' - x`, where either `x' ≠ x` and `ℓ (x' - x) = y' + y` (chord), or `x' = x`,
`y' = -y ≠ y` and `ℓ (-2y) = 3x² + A` (tangent). -/
theorem sub_some_cases {A x y x' y' : ℝ} (h : (shortCurve A).toAffine.Nonsingular x y)
    (h' : (shortCurve A).toAffine.Nonsingular x' y') :
    Point.some x' y' h' - Point.some x y h = 0 ∨
      ∃ (X Y : ℝ) (hXY : (shortCurve A).toAffine.Nonsingular X Y),
        Point.some x' y' h' - Point.some x y h = .some X Y hXY ∧ ∃ ℓ : ℝ, X = ℓ ^ 2 - x' - x ∧
          ((x' ≠ x ∧ ℓ * (x' - x) = y' + y) ∨
            (x' = x ∧ y' = -y ∧ y ≠ 0 ∧ ℓ * (-2 * y) = 3 * x ^ 2 + A)) := by
  rw [sub_eq_add_neg, Point.neg_some]
  by_cases hxy : x' = x ∧ y' = (shortCurve A).toAffine.negY x ((shortCurve A).toAffine.negY x y)
  · exact Or.inl (Point.add_of_Y_eq hxy.1 hxy.2)
  refine Or.inr ⟨_, _, _, Point.add_some hxy, (shortCurve A).toAffine.slope x' x y'
    ((shortCurve A).toAffine.negY x y), by simp, ?_⟩
  have e1 := (shortCurve_equation_iff _ _ _).mp h.1
  have e2 := (shortCurve_equation_iff _ _ _).mp h'.1
  rw [negY_negY] at hxy
  by_cases hx : x' = x
  · subst hx
    have hy : y' ≠ y := fun hy => hxy ⟨rfl, hy⟩
    have hy' : y' = -y := by
      have : (y' - y) * (y' + y) = 0 := by linear_combination e2 - e1
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd (by linarith) hy
      · linarith
    have hy0 : y ≠ 0 := by rintro rfl; exact hy (by simpa using hy')
    refine Or.inr ⟨rfl, hy', hy0, ?_⟩
    rw [slope_of_Y_ne rfl (by rwa [negY_negY]), shortCurve_negY]
    simp only [shortCurve_a₁, shortCurve_a₂, shortCurve_a₄]
    rw [hy', show -y - - -y = -2 * y by ring]
    rw [div_mul_cancel₀ _ (mul_ne_zero (by norm_num : (-2 : ℝ) ≠ 0) hy0)]; ring
  · refine Or.inl ⟨hx, ?_⟩
    rw [slope_of_X_ne hx, shortCurve_negY]
    field_simp [sub_ne_zero.mpr hx]
    ring

/-! ### Real analysis -/

/-- If `N_m → c ≠ 0` and `D_m → 0`, then every solution `ℓ` of `ℓ D_m = N_m` is eventually
large. -/
theorem eventually_lt_abs_of_mul_eq {N D : ℕ → ℝ} {c : ℝ} (hN : Tendsto N atTop (𝓝 c))
    (hc : c ≠ 0) (hD : Tendsto D atTop (𝓝 0)) (K : ℝ) :
    ∀ᶠ m in atTop, ∀ ℓ : ℝ, ℓ * D m = N m → K < |ℓ| := by
  set K' := max K 1
  have hK' : 0 < K' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hc' : 0 < |c| := abs_pos.mpr hc
  have h1 : ∀ᶠ m in atTop, |c| / 2 < |N m| :=
    ((continuous_abs.tendsto c).comp hN).eventually (lt_mem_nhds (by linarith))
  have h2 : ∀ᶠ m in atTop, |D m| < |c| / (2 * K') := by
    have := ((continuous_abs.tendsto 0).comp hD).eventually
      (gt_mem_nhds (show |(0 : ℝ)| < |c| / (2 * K') by rw [abs_zero]; positivity))
    exact this
  filter_upwards [h1, h2] with m hm1 hm2 ℓ hℓ
  refine lt_of_le_of_lt (le_max_left K 1) ?_
  by_contra hle
  push Not at hle
  have habs : |ℓ| * |D m| = |N m| := by rw [← abs_mul, hℓ]
  have : |ℓ| * |D m| ≤ K' * |D m| := mul_le_mul_of_nonneg_right hle (abs_nonneg _)
  have h3 : K' * |D m| < K' * (|c| / (2 * K')) := mul_lt_mul_of_pos_left hm2 hK'
  have h4 : K' * (|c| / (2 * K')) = |c| / 2 := by field_simp
  linarith

/-- If `|ℓ| > K ≥ 1` with `K ≥ |M| + |b| + 1`, then `ℓ² > M + b`. -/
theorem lt_sq_of_lt_abs {ℓ M b : ℝ} (h : |M| + |b| + 1 < |ℓ|) : M + b < ℓ ^ 2 := by
  have h1 : 1 < |ℓ| := by linarith [abs_nonneg M, abs_nonneg b]
  have : |ℓ| < |ℓ| ^ 2 := by nlinarith
  rw [sq_abs] at this
  linarith [le_abs_self M, le_abs_self b]

/-- **Continuity of subtraction at an affine point.** -/
theorem tendstoPt_sub_zero_of_some (he : e ≠ 0) {P P' : ℕ → (realCurve e).toAffine.Point}
    {x₀ y₀ : ℝ} {h₀ : (realCurve e).toAffine.Nonsingular x₀ y₀}
    (hP : TendstoPt P (.some x₀ y₀ h₀)) (hP' : TendstoPt P' (.some x₀ y₀ h₀)) :
    TendstoPt (fun m => P' m - P m) 0 := by
  obtain ⟨hne, hx, hy⟩ := hP
  obtain ⟨hne', hx', hy'⟩ := hP'
  have e₀ := (equation_iff _ _ _).mp h₀.1
  intro M
  set K := |M| + |2 * x₀ + 1| + 1
  have hsum : ∀ᶠ m in atTop, ptX (P' m) + ptX (P m) < 2 * x₀ + 1 :=
    (hx'.add hx).eventually (gt_mem_nhds (by linarith))
  -- the main estimate: `P' m - P m` is `O` or has a large slope
  have key : ∀ᶠ m in atTop, P' m - P m = 0 ∨
      ∃ (X Y : ℝ) (hXY : (realCurve e).toAffine.Nonsingular X Y), P' m - P m = .some X Y hXY ∧
        ∃ ℓ : ℝ, X = ℓ ^ 2 - ptX (P' m) - ptX (P m) ∧ K < |ℓ| := by
    by_cases hy₀ : y₀ = 0
    · -- `Q = (c, 0)` is a root of `x³ - e²x`
      have hc : 3 * x₀ ^ 2 - e ^ 2 ≠ 0 :=
        deriv_ne_zero_of_root he (by rw [← e₀, hy₀]; ring)
      have hT : ∀ᶠ m in atTop, ∀ ℓ : ℝ, ℓ * (-2 * ptY (P m)) = 3 * ptX (P m) ^ 2 + -e ^ 2 →
          K < |ℓ| :=
        eventually_lt_abs_of_mul_eq (((hx.pow 2).const_mul 3).add_const _) (by simpa [sub_eq_add_neg] using hc)
          (by simpa [hy₀] using hy.const_mul (-2)) K
      have hg : Tendsto (fun m => ptX (P' m) ^ 2 + ptX (P m) * ptX (P' m) + ptX (P m) ^ 2 - e ^ 2)
          atTop (𝓝 (3 * x₀ ^ 2 - e ^ 2)) := by
        have := (((hx'.pow 2).add (hx.mul hx')).add (hx.pow 2)).sub_const (e ^ 2)
        convert this using 2; ring
      have hC := eventually_lt_abs_of_mul_eq hg hc (by simpa [hy₀] using hy'.sub hy) K
      filter_upwards [hne, hne', hT, hC, hg.eventually_ne hc] with m h1 h2 hT hC hg0
      obtain ⟨hs, hsP⟩ := eq_some_of_ne_zero h1
      obtain ⟨hs', hsP'⟩ := eq_some_of_ne_zero h2
      have q1 := sq_ptY h1
      have q2 := sq_ptY h2
      rw [hsP, hsP']
      rcases sub_some_cases hs hs' with h0 | ⟨X, Y, hXY, hD, ℓ, hX, hcase⟩
      · exact Or.inl h0
      refine Or.inr ⟨X, Y, hXY, hD, ℓ, hX, ?_⟩
      rcases hcase with ⟨hxne, hℓ⟩ | ⟨-, -, -, hℓ⟩
      · apply hC ℓ
        have hxs : ptX (P' m) - ptX (P m) ≠ 0 := sub_ne_zero.mpr hxne
        apply mul_left_cancel₀ hxs
        linear_combination (ptY (P' m) - ptY (P m)) * hℓ + q2 - q1
      · exact hT ℓ hℓ
    · -- `Q = (c, d)` with `d ≠ 0`
      have hN : Tendsto (fun m => ptY (P' m) + ptY (P m)) atTop (𝓝 (2 * y₀)) := by
        convert hy'.add hy using 2; ring
      have h2y : 2 * y₀ ≠ 0 := mul_ne_zero two_ne_zero hy₀
      have hC := eventually_lt_abs_of_mul_eq hN h2y (by simpa using hx'.sub hx) K
      filter_upwards [hne, hne', hC, hN.eventually_ne h2y] with m h1 h2 hC hN0
      obtain ⟨hs, hsP⟩ := eq_some_of_ne_zero h1
      obtain ⟨hs', hsP'⟩ := eq_some_of_ne_zero h2
      rw [hsP, hsP']
      rcases sub_some_cases hs hs' with h0 | ⟨X, Y, hXY, hD, ℓ, hX, hcase⟩
      · exact Or.inl h0
      refine Or.inr ⟨X, Y, hXY, hD, ℓ, hX, ?_⟩
      rcases hcase with ⟨-, hℓ⟩ | ⟨-, hyy, -, -⟩
      · exact hC ℓ hℓ
      · exact absurd (by rw [hyy]; ring) hN0
  filter_upwards [key, hsum] with m hk hs
  rcases hk with h0 | ⟨X, Y, hXY, hD, ℓ, hX, hℓ⟩
  · exact Or.inl h0
  right
  simp only [hD, ptX_some, hX]
  have := lt_sq_of_lt_abs (b := 2 * x₀ + 1) hℓ
  linarith

/-- The point `T = (0, 0)`. -/
theorem nonsingular_T (he : e ≠ 0) : (realCurve e).toAffine.Nonsingular 0 0 :=
  nonsingular_of_equation he ((equation_iff _ _ _).mpr (by ring))

/-- Adding `T = (0, 0)` to an affine point with `x ≠ 0` gives abscissa `-e²/x`. -/
theorem add_T_some (he : e ≠ 0) {x y : ℝ} (h : (realCurve e).toAffine.Nonsingular x y)
    (hx : x ≠ 0) : ∃ (X Y : ℝ) (hXY : (realCurve e).toAffine.Nonsingular X Y),
      Point.some x y h + Point.some 0 0 (nonsingular_T he) = .some X Y hXY ∧ X * x = -e ^ 2 := by
  have hxy : ¬(x = 0 ∧ y = (realCurve e).toAffine.negY 0 0) := fun h => hx h.1
  refine ⟨_, _, _, Point.add_some hxy, ?_⟩
  have e1 := (equation_iff _ _ _).mp h.1
  rw [slope_of_X_ne hx]
  simp only [addX, shortCurve_a₁, shortCurve_a₂, sub_zero, zero_mul, add_zero]
  rw [div_pow, sub_mul, e1]
  field_simp
  ring

/-- Near `O`, translation by `T` lands near `T`. -/
theorem tendstoPt_add_T (he : e ≠ 0) {P : ℕ → (realCurve e).toAffine.Point}
    (hP : TendstoPt P 0) :
    TendstoPt (fun m => P m + .some 0 0 (nonsingular_T he)) (.some 0 0 (nonsingular_T he)) := by
  have he2 : 0 < e ^ 2 := by positivity
  -- for `ε > 0`, eventually `P m = O` or `P m + T` is affine with small coordinates
  have main : ∀ ε > 0, ∀ᶠ m in atTop, P m + .some 0 0 (nonsingular_T he) ≠ 0 ∧
      |ptX (P m + .some 0 0 (nonsingular_T he))| < ε ∧
      |ptY (P m + .some 0 0 (nonsingular_T he))| < ε := by
    intro ε hε
    filter_upwards [hP (max 0 (max (e ^ 2 / ε) (e ^ 2 * e ^ 2 / ε ^ 2)))] with m hm
    rcases hm with h0 | hlt
    · simp only [h0, zero_add, ptX_some, ptY_some, abs_zero]
      exact ⟨Point.some_ne_zero _, hε, hε⟩
    have hM0 := le_max_left 0 (max (e ^ 2 / ε) (e ^ 2 * e ^ 2 / ε ^ 2))
    have hM1 := le_trans (le_max_left _ _) (le_max_right 0 (max (e ^ 2 / ε) (e ^ 2 * e ^ 2 / ε ^ 2)))
    have hM2 := le_trans (le_max_right _ _) (le_max_right 0 (max (e ^ 2 / ε) (e ^ 2 * e ^ 2 / ε ^ 2)))
    have hne : P m ≠ 0 := by rintro h; rw [h, ptX_zero] at hlt; linarith
    obtain ⟨hs, hsP⟩ := eq_some_of_ne_zero hne
    set x := ptX (P m)
    have hx0 : 0 < x := by linarith
    obtain ⟨X, Y, hXY, hadd, hX⟩ := add_T_some he hs hx0.ne'
    rw [hsP, hadd]
    simp only [ptX_some, ptY_some]
    have eY := (equation_iff _ _ _).mp hXY.1
    have hXe : X = -e ^ 2 / x := by field_simp; linarith
    have hXabs : |X| = e ^ 2 / x := by
      rw [hXe, neg_div, abs_neg, abs_of_pos (by positivity)]
    have h1 : e ^ 2 / x < ε := by
      rw [div_lt_iff₀ hx0]; rw [div_le_iff₀ hε] at hM1; nlinarith
    refine ⟨Point.some_ne_zero _, hXabs ▸ h1, ?_⟩
    apply abs_lt_of_sq_lt_sq _ hε.le
    have hY : Y ^ 2 = e ^ 2 * e ^ 2 / x - e ^ 2 * (e ^ 2) ^ 2 / x ^ 3 := by
      rw [eY, hXe]; field_simp; ring
    have hle : Y ^ 2 ≤ e ^ 2 * e ^ 2 / x := by
      rw [hY]; have : 0 ≤ e ^ 2 * (e ^ 2) ^ 2 / x ^ 3 := by positivity
      linarith
    refine lt_of_le_of_lt hle ?_
    rw [div_lt_iff₀ hx0]
    rw [div_le_iff₀ (by positivity)] at hM2
    nlinarith [mul_lt_mul_of_pos_right hlt (pow_pos hε 2)]
  refine ⟨(main 1 one_pos).mono fun m h => h.1, ?_, ?_⟩
  · rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [main ε hε] with m hm
    simpa [Real.dist_eq] using hm.2.1
  · rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [main ε hε] with m hm
    simpa [Real.dist_eq] using hm.2.2

/-- **Continuity of subtraction** (part 2 of the article): if `P_m → Q` and `P'_m → Q`, then
`P'_m - P_m → O`. -/
theorem tendstoPt_sub_zero (he : e ≠ 0) {P P' : ℕ → (realCurve e).toAffine.Point}
    {Q : (realCurve e).toAffine.Point} (h : TendstoPt P Q) (h' : TendstoPt P' Q) :
    TendstoPt (fun m => P' m - P m) 0 := by
  cases Q with
  | zero =>
    have := tendstoPt_sub_zero_of_some he (tendstoPt_add_T he h) (tendstoPt_add_T he h')
    simpa only [add_sub_add_right_eq_sub] using this
  | some x₀ y₀ h₀ => exact tendstoPt_sub_zero_of_some he h h'

/-- **Sequential compactness** (part 1 of the article): every sequence in `E_e(ℝ)` has a
subsequence converging to a point of `E_e(ℝ)`. -/
theorem exists_subseq_tendstoPt (he : e ≠ 0) (P : ℕ → (realCurve e).toAffine.Point) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Q, TendstoPt (P ∘ φ) Q := by
  by_cases hO : ∀ M : ℝ, ∃ᶠ m in atTop, P m = 0 ∨ M < ptX (P m)
  · obtain ⟨φ, hφ, hgood⟩ := extraction_forall_of_frequently
      (P := fun n m => P m = 0 ∨ (n : ℝ) < ptX (P m)) fun n => hO n
    refine ⟨φ, hφ, 0, fun M => ?_⟩
    filter_upwards [eventually_ge_atTop ⌈M⌉₊] with n hn
    rcases hgood n with h0 | hlt
    · exact Or.inl h0
    · right
      have : M ≤ (n : ℝ) := le_trans (Nat.le_ceil M) (by exact_mod_cast hn)
      simp only [Function.comp]
      linarith
  push Not at hO
  obtain ⟨M, hM⟩ := hO
  obtain ⟨N, hN⟩ := eventually_atTop.mp hM
  set R := |M| + |e|
  set B := R ^ 3 + e ^ 2 * R + 1
  set u : ℕ → ℝ × ℝ := fun k => (ptX (P (k + N)), ptY (P (k + N)))
  have hmem : ∀ k, u k ∈ Set.Icc (-R) R ×ˢ Set.Icc (-B) B := by
    intro k
    have hk := hN (k + N) (by omega)
    obtain ⟨hne, hle⟩ := hk
    have q := sq_ptY hne
    set x := ptX (P (k + N))
    set y := ptY (P (k + N))
    have hlo := neg_abs_le_of_sq q
    have hxR : |x| ≤ R := by
      rw [abs_le]; constructor <;> linarith [abs_nonneg M, abs_nonneg e, le_abs_self M]
    have hR0 : 0 ≤ R := by positivity
    have hy2 : y ^ 2 ≤ R ^ 3 + e ^ 2 * R := by
      have h3 : x ^ 3 ≤ R ^ 3 :=
        le_trans (le_abs_self _) (by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg x) hxR 3)
      have h4 : -(e ^ 2 * x) ≤ e ^ 2 * R := by
        have := mul_le_mul_of_nonneg_left (neg_le_abs x) (sq_nonneg e)
        nlinarith [mul_le_mul_of_nonneg_left hxR (sq_nonneg e)]
      linarith
    have hyB : |y| ≤ B := by
      nlinarith [sq_abs y, sq_nonneg (|y| - 1), abs_nonneg y]
    refine ⟨⟨by linarith [abs_le.mp hxR], (abs_le.mp hxR).2⟩, abs_le.mp hyB⟩
  obtain ⟨⟨a, b⟩, -, ψ, hψ, hlim⟩ := (isCompact_Icc.prod isCompact_Icc).tendsto_subseq hmem
  have hC : IsClosed {p : ℝ × ℝ | p.2 ^ 2 = p.1 ^ 3 - e ^ 2 * p.1} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  have hab : (a, b) ∈ {p : ℝ × ℝ | p.2 ^ 2 = p.1 ^ 3 - e ^ 2 * p.1} :=
    hC.mem_of_tendsto hlim (Eventually.of_forall fun k =>
      sq_ptY (by exact (hN (ψ k + N) (by omega)).1))
  refine ⟨fun k => ψ k + N, fun i j hij => by simp only; have := hψ hij; omega,
    .some a b (nonsingular_of_equation he ((equation_iff _ _ _).mpr hab)), ?_, ?_, ?_⟩
  · exact Eventually.of_forall fun k => by
      exact (hN (ψ k + N) (by omega)).1
  · exact (continuous_fst.tendsto _).comp hlim
  · exact (continuous_snd.tendsto _).comp hlim

end RealCurve

end ZInQ.Assembly
