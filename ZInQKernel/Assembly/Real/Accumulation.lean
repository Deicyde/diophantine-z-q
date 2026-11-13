import ZInQKernel.Assembly.Real.Subtraction
import ZInQKernel.Model.Field.Curve

/-!
# Multiples of the generator approach the identity at both real places

Blueprint: `assembly/approximation/real-accumulation.md`.

The real embeddings `σ₊, σ₋ : K₀ → ℝ` (`s ↦ ±√2`) are model-field's `K0.embPlus` and
`K0.embMinus`. A field homomorphism `f : F → K` maps `y² = x³ + Ax` to `y² = x³ + f(A)x` and
induces a group homomorphism on points (`mapShortPt`); for `σ = σ±` the target is the real curve
`y² = x³ - e²x` with `e = σ(d) ≠ 0`. Compactness and continuity of subtraction on the real curves
give `k ≥ 1` with both `σ₊([k]P₀)` and `σ₋([k]P₀)` near `O`.

That `P₀` has infinite order (the torsion part of the generator certificate) is taken as the
explicit hypothesis `¬ IsOfFinAddOrder genP0`, as in `ZInQ.iota_eq_psi`; it is proved
(`ZInQ.genP0_not_isOfFinAddOrder`), and the unconditional form is
`exists_multiple_large_unconditional` (`Cleanup/FixedPointCodes.lean`).
-/

namespace ZInQ.Assembly

open WeierstrassCurve WeierstrassCurve.Affine Filter Topology

/-! ### Points under a field homomorphism -/

section MapShort

variable {F K : Type*} [Field F] [Field K] [DecidableEq F] [DecidableEq K]

theorem shortCurve_map (f : F →+* K) (A : F) : (shortCurve A).map f = shortCurve (f A) := by
  ext <;> simp [shortCurve, WeierstrassCurve.map]

theorem nonsingular_mapShort (f : F →+* K) {A : F} {B : K} (hB : f A = B) {x y : F}
    (h : (shortCurve A).toAffine.Nonsingular x y) :
    (shortCurve B).toAffine.Nonsingular (f x) (f y) := by
  have := ((shortCurve A).toAffine.map_nonsingular f.injective x y).mpr h
  have hW : (shortCurve A).toAffine.map f = (shortCurve B).toAffine :=
    (shortCurve_map f A).trans (by rw [hB])
  rwa [hW] at this

/-- The map on points of `y² = x³ + Ax` induced by `f : F →+* K`, with target
`y² = x³ + Bx`, `B = f(A)`. -/
def mapShortPtFun (f : F →+* K) {A : F} {B : K} (hB : f A = B) :
    (shortCurve A).toAffine.Point → (shortCurve B).toAffine.Point
  | .zero => 0
  | .some x y h => .some (f x) (f y) (nonsingular_mapShort f hB h)

theorem mapShortPtFun_add (f : F →+* K) {A : F} {B : K} (hB : f A = B)
    (P Q : (shortCurve A).toAffine.Point) :
    mapShortPtFun f hB (P + Q) = mapShortPtFun f hB P + mapShortPtFun f hB Q := by
  have hW : (shortCurve A).map f = shortCurve B := by rw [shortCurve_map, hB]
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rfl
  · rfl
  · rfl
  by_cases hxy : x₁ = x₂ ∧ y₁ = (shortCurve A).toAffine.negY x₂ y₂
  · rw [Point.add_of_Y_eq hxy.1 hxy.2]
    simp only [mapShortPtFun]
    rw [Point.add_of_Y_eq (congrArg f hxy.1)
      (by rw [hxy.2, shortCurve_negY, shortCurve_negY, map_neg])]
  · have hxy' : ¬(f x₁ = f x₂ ∧ f y₁ = (shortCurve B).toAffine.negY (f x₂) (f y₂)) := by
      rintro ⟨h1, h2⟩
      apply hxy
      rw [shortCurve_negY] at h2 ⊢
      exact ⟨f.injective h1, f.injective (by rw [h2, map_neg])⟩
    rw [Point.add_some hxy]
    simp only [mapShortPtFun]
    rw [Point.add_some hxy', Point.some.injEq, ← hW, map_slope, map_addX, map_addY]
    exact ⟨rfl, rfl⟩

/-- The group homomorphism `E_A(F) → E_B(K)`, `(x, y) ↦ (f x, f y)`, `O ↦ O`. -/
def mapShortPt (f : F →+* K) {A : F} {B : K} (hB : f A = B) :
    (shortCurve A).toAffine.Point →+ (shortCurve B).toAffine.Point :=
  AddMonoidHom.mk' (mapShortPtFun f hB) (mapShortPtFun_add f hB)

@[simp] theorem mapShortPt_zero (f : F →+* K) {A : F} {B : K} (hB : f A = B) :
    mapShortPt f hB 0 = 0 := rfl

@[simp] theorem mapShortPt_some (f : F →+* K) {A : F} {B : K} (hB : f A = B) {x y : F}
    (h : (shortCurve A).toAffine.Nonsingular x y) :
    mapShortPt f hB (.some x y h) = .some (f x) (f y) (nonsingular_mapShort f hB h) := rfl

end MapShort

/-! ### Subsequences -/

namespace RealCurve

theorem TendstoPt.comp_strictMono {W : WeierstrassCurve ℝ} {P : ℕ → W.toAffine.Point}
    {Q : W.toAffine.Point} (hP : TendstoPt P Q) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    TendstoPt (P ∘ φ) Q := by
  have hφt := hφ.tendsto_atTop
  cases Q with
  | zero => exact fun M => hφt.eventually (hP M)
  | some x₀ y₀ h₀ =>
    obtain ⟨h1, h2, h3⟩ := hP
    exact ⟨hφt.eventually h1, h2.comp hφt, h3.comp hφt⟩

end RealCurve

/-! ### The real places of `E` -/

open RealCurve

/-- `σ(-d²) = -σ(d)²`. -/
theorem map_genA (σ : K0 →+* ℝ) : σ (-genD ^ 2) = -σ genD ^ 2 := by
  rw [map_neg, map_pow]

theorem map_genD_ne_zero (σ : K0 →+* ℝ) : σ genD ≠ 0 :=
  (map_ne_zero σ).mpr genD_ne_zero

/-- The homomorphism `E(K₀) → E_{σ(d)}(ℝ)` induced by a real embedding `σ`. -/
noncomputable def realPt (σ : K0 →+* ℝ) : genCurve.toAffine.Point →+ (realCurve (σ genD)).toAffine.Point :=
  mapShortPt (A := -genD ^ 2) σ (map_genA σ)

theorem realPt_some (σ : K0 →+* ℝ) {x y : K0} (h : genCurve.toAffine.Nonsingular x y) :
    ∃ h', realPt σ (.some x y h) = .some (σ x) (σ y) h' := ⟨_, rfl⟩

/-- Positive multiples of `P₀` come close to `O` at the two real places together, along some
pair of indices: for every `M` there is `k ≥ 1` with `σ±([k]P₀) = O` or `x(σ±([k]P₀)) > M`. -/
theorem exists_nsmul_near_zero (M : ℝ) : ∃ k : ℕ, 1 ≤ k ∧
    (realPt K0.embPlus (k • genP0) = 0 ∨ M < ptX (realPt K0.embPlus (k • genP0))) ∧
    (realPt K0.embMinus (k • genP0) = 0 ∨ M < ptX (realPt K0.embMinus (k • genP0))) := by
  set uP : ℕ → _ := fun k => realPt K0.embPlus ((k + 1) • genP0)
  set uM : ℕ → _ := fun k => realPt K0.embMinus ((k + 1) • genP0)
  obtain ⟨φ₁, hφ₁, QP, hQP⟩ := exists_subseq_tendstoPt (map_genD_ne_zero K0.embPlus) uP
  obtain ⟨φ₂, hφ₂, QM, hQM⟩ := exists_subseq_tendstoPt (map_genD_ne_zero K0.embMinus) (uM ∘ φ₁)
  set φ := φ₁ ∘ φ₂
  have hφ : StrictMono φ := hφ₁.comp hφ₂
  have hPP : TendstoPt (uP ∘ φ) QP := hQP.comp_strictMono hφ₂
  have hPM : TendstoPt (uM ∘ φ) QM := hQM
  have hs : StrictMono (fun i : ℕ => i + 1) := fun a b h => by simp only; omega
  have hDP := tendstoPt_sub_zero (map_genD_ne_zero K0.embPlus) hPP (hPP.comp_strictMono hs)
  have hDM := tendstoPt_sub_zero (map_genD_ne_zero K0.embMinus) hPM (hPM.comp_strictMono hs)
  obtain ⟨i, hiP, hiM⟩ := ((hDP M).and (hDM M)).exists
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt (hφ (Nat.lt_succ_self i))
  have hdiff : ∀ σ : K0 →+* ℝ, realPt σ ((φ (i + 1) + 1) • genP0) - realPt σ ((φ i + 1) • genP0) =
      realPt σ ((k + 1) • genP0) := by
    intro σ
    rw [← map_sub, hk, show φ i + k + 1 + 1 = (k + 1) + (φ i + 1) by ring, add_nsmul,
      add_sub_cancel_right]
  refine ⟨k + 1, by omega, ?_, ?_⟩
  · simpa only [Function.comp, uP, hdiff] using hiP
  · simpa only [Function.comp, uM, hdiff] using hiM

/-- **Multiples of the generator approach the identity at both real places.** For every
`M ∈ ℝ` there is `k ≥ 1` such that `[k]P₀ = (x_k, y_k)` is affine with `σ₊(x_k) > M` and
`σ₋(x_k) > M`. The infinite order of `P₀` is an explicit hypothesis. -/
theorem exists_multiple_large (hP0 : ¬ IsOfFinAddOrder genP0) (M : ℝ) :
    ∃ k : ℕ, 1 ≤ k ∧ ∃ (x y : K0) (h : genCurve.toAffine.Nonsingular x y),
      (k : ℤ) • genP0 = .some x y h ∧ M < K0.embPlus x ∧ M < K0.embMinus x := by
  obtain ⟨k, hk, hP, hM⟩ := exists_nsmul_near_zero M
  have hne : k • genP0 ≠ 0 := fun h0 =>
    hP0 (isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨k, by omega, h0⟩)
  refine ⟨k, hk, ?_⟩
  rw [natCast_zsmul]
  generalize k • genP0 = Q at hP hM hne
  cases Q with
  | zero => exact absurd rfl hne
  | some x y h =>
    refine ⟨x, y, h, rfl, ?_, ?_⟩
    · rcases hP with h0 | hlt
      · exact absurd h0 (Point.some_ne_zero _)
      · exact hlt
    · rcases hM with h0 | hlt
      · exact absurd h0 (Point.some_ne_zero _)
      · exact hlt

end ZInQ.Assembly
