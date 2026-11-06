import ZInQKernel.Model.Heights.XHeight
import ZInQ.ModelDuplicationBounds

/-!
# The duplication forms on `C` and their archimedean sizes

Blueprint: `model/heights/duplication-forms.md`, `model/heights/duplication-archimedean.md`.

`F₂(a, b) = (a² + δ² b²)²` and `G₂(a, b) = 4 a b (a² - δ² b²)`. For `T = (x, y) ∈ C(K₀)` with
`y ≠ 0` and `x = a / b` (`a, b ∈ ℤ[s]`, `b ≠ 0`): `G₂(a, b) ≠ 0` and `x([2]T) = F₂(a, b) / G₂(a, b)`;
if `y = 0` then `[2]T = O`. At either real embedding,
`max(|σa|, |σb|)⁴ ≤ max(|σF₂|, |σG₂|) ≤ 676 max(|σa|, |σb|)⁴`.
-/

namespace ZInQ

open WeierstrassCurve WeierstrassCurve.Affine

/-- `F(d; a, b) = (a² + d² b²)²`. -/
def dupF {R : Type*} [CommRing R] (d a b : R) : R := (a ^ 2 + d ^ 2 * b ^ 2) ^ 2

/-- `G(d; a, b) = 4 a b (a² - d² b²)`. -/
def dupG {R : Type*} [CommRing R] (d a b : R) : R := 4 * a * b * (a ^ 2 - d ^ 2 * b ^ 2)

theorem map_dupF {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (d a b : R) :
    f (dupF d a b) = dupF (f d) (f a) (f b) := by simp [dupF]

theorem map_dupG {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (d a b : R) :
    f (dupG d a b) = dupG (f d) (f a) (f b) := by
  simp only [dupG, map_mul, map_sub, map_pow]; rw [map_ofNat]

/-- The duplication form `F₂(a, b) = (a² + δ² b²)²` on `ℤ[s]`. -/
def F2 (a b : Zs) : Zs := dupF deltaZ a b

/-- The duplication form `G₂(a, b) = 4 a b (a² - δ² b²)` on `ℤ[s]`. -/
def G2 (a b : Zs) : Zs := dupG deltaZ a b

theorem toK0_F2 (a b : Zs) : Zs.toK0 (F2 a b) = dupF delta (Zs.toK0 a) (Zs.toK0 b) := by
  rw [F2, map_dupF, toK0_deltaZ]

theorem toK0_G2 (a b : Zs) : Zs.toK0 (G2 a b) = dupG delta (Zs.toK0 a) (Zs.toK0 b) := by
  rw [G2, map_dupG, toK0_deltaZ]

/-- The tangent computation: if `y² = x³ - D x` and `y ≠ 0`, then
`((3x² - D)/(2y))² - 2x = (x² + D)² / (4 x (x² - D))`. -/
theorem tangent_x_formula {K : Type*} [Field K] [CharZero K] {x y D : K}
    (he : y ^ 2 = x ^ 3 - D * x) (hy : y ≠ 0) :
    ((3 * x ^ 2 - D) / (2 * y)) ^ 2 - 2 * x = (x ^ 2 + D) ^ 2 / (4 * x * (x ^ 2 - D)) := by
  have hx : x ≠ 0 := by rintro rfl; apply hy; simpa using he
  have hxD : x ^ 2 - D ≠ 0 := by
    intro h; apply hy; have : y ^ 2 = x * (x ^ 2 - D) := by rw [he]; ring
    rw [h, mul_zero] at this; exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  have h4 : (4 : K) * x * (x ^ 2 - D) ≠ 0 := by
    apply mul_ne_zero (mul_ne_zero (by norm_num) hx) hxD
  rw [div_pow, eq_div_iff h4, sub_mul, div_mul_eq_mul_div, mul_pow,
    show (2 : K) ^ 2 * y ^ 2 = 4 * x * (x ^ 2 - D) by rw [he]; ring]
  rw [mul_div_assoc, div_self h4]
  have : (2 : K) * x * (4 * x * (x ^ 2 - D)) = 8 * x * (x ^ 3 - D * x) := by ring
  rw [this]; ring

/-- Points of `C` with `y ≠ 0` have `x ≠ 0` and `x² ≠ δ²`. -/
theorem curveC_x_ne_of_y_ne {x y : K0} (h : curveC.toAffine.Equation x y) (hy : y ≠ 0) :
    x ≠ 0 ∧ x ^ 2 - delta ^ 2 ≠ 0 := by
  have he := (curveC_equation_iff x y).mp h
  constructor
  · rintro rfl; apply hy; simpa using he
  · intro h; apply hy; have : y ^ 2 = x * (x ^ 2 - delta ^ 2) := by rw [he]; ring
    rw [h, mul_zero] at this; exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this

/-- The duplication formula on `C` in terms of the abscissa. -/
theorem curveC_two_smul_some {x y : K0} (h : curveC.toAffine.Nonsingular x y) (hy : y ≠ 0) :
    ∃ y' h', 2 • Point.some x y h =
      Point.some ((x ^ 2 + delta ^ 2) ^ 2 / (4 * x * (x ^ 2 - delta ^ 2))) y' h' := by
  have hY : y ≠ curveC.toAffine.negY x y := by
    rw [curveC, shortCurve_negY]
    intro h'; apply hy; linear_combination h' / 2
  rw [two_nsmul, Point.add_self_of_Y_ne hY]
  have hX : curveC.toAffine.addX x x (curveC.toAffine.slope x x y y) =
      (x ^ 2 + delta ^ 2) ^ 2 / (4 * x * (x ^ 2 - delta ^ 2)) := by
    rw [Affine.slope_of_Y_ne rfl hY, Affine.addX]
    simp only [curveC, shortCurve_negY, shortCurve_a₁, shortCurve_a₂, shortCurve_a₄]
    rw [← tangent_x_formula ((curveC_equation_iff x y).mp h.1) hy]
    ring
  refine ⟨_, hX ▸ nonsingular_add h h fun hxy => hY hxy.right, ?_⟩
  simp only [Point.some.injEq]
  exact ⟨hX, trivial⟩

/-- **Duplication forms.** For `T = (x, y) ∈ C(K₀)` with `y ≠ 0` and `x = a / b`
(`a, b ∈ ℤ[s]`, `b ≠ 0`): `G₂(a, b) ≠ 0` and `[2]T = (F₂(a, b) / G₂(a, b), y')` for some `y'`
(in particular `[2]T ≠ O`). -/
theorem x_two_smul_C {x y : K0} (h : curveC.toAffine.Nonsingular x y) (hy : y ≠ 0)
    {a b : Zs} (hb : b ≠ 0) (hx : x = Zs.toK0 a / Zs.toK0 b) :
    G2 a b ≠ 0 ∧ ∃ y' h', 2 • Point.some x y h =
      Point.some (Zs.toK0 (F2 a b) / Zs.toK0 (G2 a b)) y' h' := by
  obtain ⟨hx0, hxd⟩ := curveC_x_ne_of_y_ne h.1 hy
  have hB : Zs.toK0 b ≠ 0 := by
    rw [Ne, ← map_zero Zs.toK0]; exact fun h => hb (Zs.toK0_injective h)
  have hA : Zs.toK0 a ≠ 0 := by
    rintro hA; apply hx0; rw [hx, hA, zero_div]
  have hAB : (Zs.toK0 a) ^ 2 - delta ^ 2 * (Zs.toK0 b) ^ 2 ≠ 0 := by
    intro h'; apply hxd; rw [hx, div_pow]; field_simp; linear_combination h'
  have hG : Zs.toK0 (G2 a b) ≠ 0 := by
    rw [toK0_G2, dupG]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hA) hB) hAB
  refine ⟨fun h0 => hG (by rw [h0, map_zero]), ?_⟩
  obtain ⟨y', h', e⟩ := curveC_two_smul_some h hy
  have : (x ^ 2 + delta ^ 2) ^ 2 / (4 * x * (x ^ 2 - delta ^ 2)) =
      Zs.toK0 (F2 a b) / Zs.toK0 (G2 a b) := by
    rw [toK0_F2, toK0_G2, dupF, dupG, hx]
    rw [div_eq_div_iff (by rw [← hx]; exact mul_ne_zero (mul_ne_zero (by norm_num) hx0) hxd)
      (by rw [toK0_G2, dupG] at hG; exact hG)]
    field_simp
  exact ⟨y', this ▸ h', by rw [e]; simp only [Point.some.injEq]; exact ⟨this, trivial⟩⟩

/-- If `y = 0` then `[2]T = O`. -/
theorem two_smul_C_of_y_eq_zero {x y : K0} (h : curveC.toAffine.Nonsingular x y) (hy : y = 0) :
    2 • Point.some x y h = 0 := by
  rw [two_nsmul]
  apply Point.add_self_of_Y_eq
  rw [curveC, shortCurve_negY, hy, neg_zero]

/-! ### Archimedean bounds -/

/-- **Archimedean bounds** (real form, upstream `ModelDuplication.duplication_bounds`):
for `1 ≤ Δ ≤ 5`, `M = max(|a|, |b|)`: `M⁴ ≤ max(|F|, |G|) ≤ 676 M⁴`. -/
theorem duplication_archimedean (Δ a b : ℝ) (h1 : 1 ≤ Δ) (h5 : Δ ≤ 5) :
    max |a| |b| ^ 4 ≤ max |dupF Δ a b| |dupG Δ a b| ∧
      max |dupF Δ a b| |dupG Δ a b| ≤ 676 * max |a| |b| ^ 4 := by
  obtain ⟨h₁, h₂, -⟩ := ZInQ.ModelDuplication.duplication_bounds a b Δ h1 h5
  exact ⟨h₁, h₂⟩

theorem sqrt_two_lt_two : Real.sqrt 2 < 2 := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

theorem embPlus_delta : K0.embPlus delta = 3 - Real.sqrt 2 := by
  rw [K0.embPlus_apply]; simp [delta]; ring

theorem embMinus_delta : K0.embMinus delta = 3 + Real.sqrt 2 := by
  rw [K0.embMinus_apply]; simp [delta]

theorem embPlus_delta_mem : 1 ≤ K0.embPlus delta ∧ K0.embPlus delta ≤ 5 := by
  rw [embPlus_delta]; have := sqrt_two_lt_two; have := Real.sqrt_nonneg 2
  constructor <;> linarith

theorem embMinus_delta_mem : 1 ≤ K0.embMinus delta ∧ K0.embMinus delta ≤ 5 := by
  rw [embMinus_delta]; have := sqrt_two_lt_two; have := Real.sqrt_nonneg 2
  constructor <;> linarith

/-- The archimedean bounds at the real embeddings `σ₊`, `σ₋` of `K₀`. -/
theorem duplication_bounds_emb (σ : K0 →+* ℝ) (hσ : σ = K0.embPlus ∨ σ = K0.embMinus)
    (a b : K0) :
    max |σ a| |σ b| ^ 4 ≤ max |σ (dupF delta a b)| |σ (dupG delta a b)| ∧
      max |σ (dupF delta a b)| |σ (dupG delta a b)| ≤ 676 * max |σ a| |σ b| ^ 4 := by
  rw [map_dupF, map_dupG]
  have hd : 1 ≤ σ delta ∧ σ delta ≤ 5 := by
    rcases hσ with rfl | rfl
    · exact embPlus_delta_mem
    · exact embMinus_delta_mem
  exact duplication_archimedean _ _ _ hd.1 hd.2

end ZInQ
