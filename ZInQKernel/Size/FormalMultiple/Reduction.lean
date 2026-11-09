import ZInQKernel.Size.FormalMultiple.Residue
import ZInQKernel.Model.Descent.Reduction
import ZInQKernel.Multiplication.Local.Valuations
import ZInQKernel.Multiplication.Local.FormalGroup

/-!
# Reduction on the nonsingular part

Blueprint: `size/formal-multiple/reduction-homomorphism.md`.

Let `π` be a prime of `ℤ[s]` with `π ∤ 2`, `k` a field and `ρ : ℤ[s] →+* k` a ring
homomorphism with kernel `(π)` (for the article: `k = ℤ[s]/(π)` and `ρ` the quotient map;
`resK π ρ` is then the residue map of `𝒪_π = ℤ[s]_(π)`). Let `A ∈ K₀` be integral at `π`,
`W : y² = x³ + A x` and `W̃ : y² = x³ + Ā x` over `k`, `Ā = ρ(A)`. Mathlib's `Point` of `W̃` is
the group of nonsingular points `W̃_ns(k)` with `O`. Put

* `W₁(π) = {O} ∪ {(x, y) : x ∉ 𝒪_π}` (`InE1`, the subgroup `E1sub`);
* `W₀(π) = W₁(π) ∪ {(x, y) : x ∈ 𝒪_π, (x̄, ȳ) nonsingular on W̃}` (`InE0`, the subgroup `E0sub`);
* `red : W₀(π) → W̃_ns(k)`, `O` on `W₁(π)` and `(x, y) ↦ (x̄, ȳ)` otherwise (`redK`).

Then `W₀(π)` is a subgroup and `red` a homomorphism (`reductionHom`) with kernel `W₁(π)`
(`ker_reductionHom`); if `Ā ≠ 0`, `W₀(π) = W(K₀)` (`E0_eq_top_of_good`). Consequently
`[m · ord(red Q)] Q ∈ W₁(π)` for `Q ∈ W₀(π)` (`zsmul_addOrderOf_mem_E1`).

The proof generalizes the model chapter's `ZInQ.red_add` (residue degree one, good
reduction): the integrality of the chord slope does not use nonsingularity of the reductions,
the case of opposite reductions uses only the nonsingularity of the reduced point, and the
kernel `W₁(π)` is the formal neighbourhood `ZInQ.Mult.formalNbhd` at `v_π`.
-/

namespace ZInQ.Size

open WeierstrassCurve WeierstrassCurve.Affine

variable {k : Type*} [Field k]

/-! ### The sets and the map -/

section Defs

variable (π : Zs) (ρ : Zs →+* k) (A : K0) (Ab : k)

/-- Membership in `W₁(π)`: `O`, or an affine point with `x ∉ 𝒪_π`. -/
def InE1 : (shortCurve A).toAffine.Point → Prop
  | 0 => True
  | .some x _ _ => ¬VGe π 0 x

/-- Membership in `W₀(π)`: a point of `W₁(π)`, or an affine point with `x ∈ 𝒪_π` whose
reduction is a nonsingular point of `W̃`. -/
def InE0 : (shortCurve A).toAffine.Point → Prop
  | 0 => True
  | .some x y _ => ¬VGe π 0 x ∨
      (VGe π 0 x ∧ (shortCurve Ab).toAffine.Nonsingular (resK π ρ x) (resK π ρ y))

open Classical in
/-- The reduction map: `O` off the integral points with nonsingular reduction, and
`(x, y) ↦ (x̄, ȳ)` on them. -/
noncomputable def redK : (shortCurve A).toAffine.Point → (shortCurve Ab).toAffine.Point
  | 0 => 0
  | .some x y _ =>
    if h : VGe π 0 x ∧ (shortCurve Ab).toAffine.Nonsingular (resK π ρ x) (resK π ρ y) then
      .some _ _ h.2
    else 0

@[simp] theorem redK_zero : redK π ρ A Ab 0 = 0 := rfl

@[simp] theorem inE0_zero : InE0 π ρ A Ab 0 := trivial

@[simp] theorem inE1_zero : InE1 π A 0 := trivial

variable {π ρ A Ab}

theorem redK_some_of_ns {x y : K0} (h : (shortCurve A).toAffine.Nonsingular x y)
    (hx : VGe π 0 x) (hns : (shortCurve Ab).toAffine.Nonsingular (resK π ρ x) (resK π ρ y)) :
    redK π ρ A Ab (.some x y h) = .some _ _ hns := by
  simp [redK, hx, hns]

theorem redK_some_of_not_vge {x y : K0} (h : (shortCurve A).toAffine.Nonsingular x y)
    (hx : ¬VGe π 0 x) : redK π ρ A Ab (.some x y h) = 0 := by
  simp [redK, hx]

theorem redK_some_of_not_ns {x y : K0} (h : (shortCurve A).toAffine.Nonsingular x y)
    (hns : ¬(shortCurve Ab).toAffine.Nonsingular (resK π ρ x) (resK π ρ y)) :
    redK π ρ A Ab (.some x y h) = 0 := by
  simp only [redK]
  split_ifs with h'
  · exact absurd h'.2 hns
  · rfl

theorem inE1_some_iff {x y : K0} (h : (shortCurve A).toAffine.Nonsingular x y) :
    InE1 π A (.some x y h) ↔ ¬VGe π 0 x := Iff.rfl

theorem inE0_of_inE1 {P : (shortCurve A).toAffine.Point} (hP : InE1 π A P) :
    InE0 π ρ A Ab P := by
  rcases P with _ | ⟨x, y, h⟩
  · trivial
  · exact Or.inl hP

end Defs

/-! ### Basic properties -/

variable {π : Zs} (hπ : Prime π) (ρ : Zs →+* k) (hρ : ∀ a, ρ a = 0 ↔ π ∣ a) {A : K0}
  (hA : VGe π 0 A) {Ab : k} (hAb : resK π ρ A = Ab)

include hρ in
theorem two_ne_zero_of_not_dvd (h2 : ¬π ∣ 2) : (2 : k) ≠ 0 := by
  intro h; apply h2; rw [← hρ, map_ofNat]; exact h

include hπ hρ hA hAb in
theorem redK_equation {x y : K0} (h : (shortCurve A).toAffine.Equation x y) (hx : VGe π 0 x) :
    (shortCurve Ab).toAffine.Equation (resK π ρ x) (resK π ρ y) := by
  have e := (shortCurve_equation_iff A x y).mp h
  have hy := vge_y_of_vge_x hπ hA e hx
  rw [shortCurve_equation_iff, ← hAb, ← resK_pow hπ ρ hρ hy, ← resK_pow hπ ρ hρ hx,
    ← resK_mul hπ ρ hρ hA hx,
    ← resK_add hπ ρ hρ (hx.pow0 hπ 3) (hA.mul hπ hx |>.mono (by simp)), e]

/-- For a point of `W₀(π)`, the reduction is `O` exactly on `W₁(π)`. -/
theorem redK_eq_zero_iff {P : (shortCurve A).toAffine.Point} (hP : InE0 π ρ A Ab P) :
    redK π ρ A Ab P = 0 ↔ InE1 π A P := by
  rcases P with _ | ⟨x, y, h⟩
  · exact ⟨fun _ => trivial, fun _ => rfl⟩
  rcases hP with hx | ⟨hx, hns⟩
  · exact ⟨fun _ => hx, fun _ => redK_some_of_not_vge h hx⟩
  · rw [redK_some_of_ns h hx hns, inE1_some_iff]
    exact ⟨fun h0 => absurd h0 (Point.some_ne_zero _), fun h1 => absurd hx h1⟩

include hπ hρ hA in
theorem inE0_neg {P : (shortCurve A).toAffine.Point} (hP : InE0 π ρ A Ab P) :
    InE0 π ρ A Ab (-P) := by
  rcases P with _ | ⟨x, y, h⟩
  · trivial
  rw [Point.neg_some]
  rcases hP with hx | ⟨hx, hns⟩
  · exact Or.inl hx
  · have hy := vge_y_of_vge_x hπ hA ((shortCurve_equation_iff A x y).mp h.1) hx
    refine Or.inr ⟨hx, ?_⟩
    rw [shortCurve_negY, resK_neg hπ ρ hρ hy, ← shortCurve_negY Ab]
    exact (nonsingular_neg _ _).mpr hns

include hπ hρ hA in
theorem redK_neg (P : (shortCurve A).toAffine.Point) :
    redK π ρ A Ab (-P) = -redK π ρ A Ab P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  rw [Point.neg_some]
  by_cases hx : VGe π 0 x
  · have hy := vge_y_of_vge_x hπ hA ((shortCurve_equation_iff A x y).mp h.1) hx
    have hr : resK π ρ ((shortCurve A).toAffine.negY x y) =
        (shortCurve Ab).toAffine.negY (resK π ρ x) (resK π ρ y) := by
      rw [shortCurve_negY, shortCurve_negY, resK_neg hπ ρ hρ hy]
    by_cases hns : (shortCurve Ab).toAffine.Nonsingular (resK π ρ x) (resK π ρ y)
    · have hns' : (shortCurve Ab).toAffine.Nonsingular (resK π ρ x)
          (resK π ρ ((shortCurve A).toAffine.negY x y)) := by
        rw [hr]; exact (nonsingular_neg _ _).mpr hns
      rw [redK_some_of_ns _ hx hns', redK_some_of_ns h hx hns, Point.neg_some]
      simp only [Point.some.injEq, true_and]
      exact hr
    · have hns' : ¬(shortCurve Ab).toAffine.Nonsingular (resK π ρ x)
          (resK π ρ ((shortCurve A).toAffine.negY x y)) := by
        rw [hr, nonsingular_neg]; exact hns
      rw [redK_some_of_not_ns _ hns', redK_some_of_not_ns h hns]; rfl
  · rw [redK_some_of_not_vge _ hx, redK_some_of_not_vge h hx]; rfl

/-! ### The kernel `W₁(π)` is the formal neighbourhood -/

include hA in
theorem vP_A_nonneg : 0 ≤ Mult.vP π hπ A := by
  have := (Mult.le_vP_iff hπ A 0).mpr hA
  simpa using this

theorem not_vge_iff_vP_neg {x : K0} : ¬VGe π 0 x ↔ Mult.vP π hπ x < 0 := by
  rw [← not_le]
  have := Mult.le_vP_iff hπ x 0
  simp only [WithTop.coe_zero] at this
  rw [this]; rfl

theorem inE1_iff_mem_W1 (P : (shortCurve A).toAffine.Point) :
    InE1 π A P ↔ P ∈ Mult.W1 (Mult.vP π hπ) A := by
  rcases P with _ | ⟨x, y, h⟩
  · exact ⟨fun _ => Mult.zero_mem_W1 _, fun _ => trivial⟩
  · rw [inE1_some_iff, Mult.some_mem_W1_iff]; exact not_vge_iff_vP_neg hπ

include hπ hA in
theorem inE1_add {P Q : (shortCurve A).toAffine.Point} (hP : InE1 π A P) (hQ : InE1 π A Q) :
    InE1 π A (P + Q) := by
  have hA' := vP_A_nonneg hπ hA
  rw [inE1_iff_mem_W1 hπ] at hP hQ ⊢
  rw [← Mult.mem_formalNbhd_iff hA'] at hP hQ ⊢
  exact (Mult.formalNbhd A hA').add_mem hP hQ

include hπ hA in
theorem inE1_neg {P : (shortCurve A).toAffine.Point} (hP : InE1 π A P) : InE1 π A (-P) := by
  have hA' := vP_A_nonneg hπ hA
  rw [inE1_iff_mem_W1 hπ] at hP ⊢
  rw [← Mult.mem_formalNbhd_iff hA'] at hP ⊢
  exact (Mult.formalNbhd A hA').neg_mem hP

/-- The subgroup `W₁(π) = {O} ∪ {(x, y) : x ∉ 𝒪_π}`. -/
def E1sub : AddSubgroup (shortCurve A).toAffine.Point where
  carrier := {P | InE1 π A P}
  zero_mem' := trivial
  add_mem' hP hQ := inE1_add hπ hA hP hQ
  neg_mem' hP := inE1_neg hπ hA hP

theorem mem_E1sub_iff (P : (shortCurve A).toAffine.Point) :
    P ∈ E1sub hπ hA ↔ InE1 π A P := Iff.rfl

/-- `W₁(π)` is the formal neighbourhood of the multiplication chapter at `v_π`. -/
theorem E1sub_eq_formalNbhd : E1sub hπ hA = Mult.formalNbhd A (vP_A_nonneg hπ hA) := by
  ext P
  rw [mem_E1sub_iff, Mult.mem_formalNbhd_iff, inE1_iff_mem_W1 hπ]

/-! ### Integral chords -/

variable [DecidableEq k]

include hπ hρ hA hAb in
/-- **Integral chords**: if `x₁, x₂ ∈ 𝒪_π` and the reductions are not opposite, the sum is
affine with integral abscissa, and its coordinates reduce to the chord-and-tangent formulas
applied to the reductions (no nonsingularity of the reductions is needed). -/
theorem int_add {x₁ y₁ x₂ y₂ : K0} (h₁ : (shortCurve A).toAffine.Nonsingular x₁ y₁)
    (h₂ : (shortCurve A).toAffine.Nonsingular x₂ y₂) (hx₁ : VGe π 0 x₁) (hx₂ : VGe π 0 x₂)
    (hopp : ¬(resK π ρ x₁ = resK π ρ x₂ ∧ resK π ρ y₁ = -resK π ρ y₂)) :
    ∃ x₃ y₃ h₃, Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ = Point.some x₃ y₃ h₃ ∧
      VGe π 0 x₃ ∧
      resK π ρ x₃ = (shortCurve Ab).toAffine.addX (resK π ρ x₁) (resK π ρ x₂)
        ((shortCurve Ab).toAffine.slope (resK π ρ x₁) (resK π ρ x₂) (resK π ρ y₁)
          (resK π ρ y₂)) ∧
      resK π ρ y₃ = (shortCurve Ab).toAffine.addY (resK π ρ x₁) (resK π ρ x₂) (resK π ρ y₁)
        ((shortCurve Ab).toAffine.slope (resK π ρ x₁) (resK π ρ x₂) (resK π ρ y₁)
          (resK π ρ y₂)) := by
  have hy₁ := vge_y_of_vge_x hπ hA ((shortCurve_equation_iff A x₁ y₁).mp h₁.1) hx₁
  have hy₂ := vge_y_of_vge_x hπ hA ((shortCurve_equation_iff A x₂ y₂).mp h₂.1) hx₂
  have hopp' : ¬(resK π ρ x₁ = resK π ρ x₂ ∧
      resK π ρ y₁ = (shortCurve Ab).toAffine.negY (resK π ρ x₂) (resK π ρ y₂)) := by
    rwa [shortCurve_negY]
  have hxy : ¬(x₁ = x₂ ∧ y₁ = (shortCurve A).toAffine.negY x₂ y₂) := by
    rintro ⟨rfl, h⟩
    rw [shortCurve_negY] at h
    exact hopp ⟨rfl, by rw [h, resK_neg hπ ρ hρ hy₂]⟩
  -- the slope is integral and reduces to the slope over `k`
  obtain ⟨hℓ, hres⟩ : VGe π 0 ((shortCurve A).toAffine.slope x₁ x₂ y₁ y₂) ∧
      resK π ρ ((shortCurve A).toAffine.slope x₁ x₂ y₁ y₂) =
        (shortCurve Ab).toAffine.slope (resK π ρ x₁) (resK π ρ x₂) (resK π ρ y₁)
          (resK π ρ y₂) := by
    by_cases hX : resK π ρ x₁ = resK π ρ x₂
    · have hYY : resK π ρ y₁ = resK π ρ y₂ := by
        rcases Y_eq_of_X_eq (redK_equation hπ ρ hρ hA hAb h₁.1 hx₁)
          (redK_equation hπ ρ hρ hA hAb h₂.1 hx₂) hX with h | h
        · exact h
        · exact absurd ⟨hX, h⟩ hopp'
      have hY0 : resK π ρ y₁ + resK π ρ y₂ ≠ 0 := by
        intro h0; apply hopp; exact ⟨hX, by linear_combination h0⟩
      have hsum0 : y₁ + y₂ ≠ 0 := by
        intro h0; apply hY0; rw [← resK_add hπ ρ hρ hy₁ hy₂, h0, resK_zero hπ ρ hρ]
      have hvsum : vp π (y₁ + y₂) = 0 :=
        (vp_eq_zero_of_resK_ne_zero hπ ρ hρ (hy₁.add hπ hy₂)
          (by rw [resK_add hπ ρ hρ hy₁ hy₂]; exact hY0)).2
      have hmul := slope_mul_add h₁.1 h₂.1 hxy
      have hℓeq : (shortCurve A).toAffine.slope x₁ x₂ y₁ y₂ =
          (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + A) / (y₁ + y₂) := by
        rw [eq_div_iff hsum0]; exact hmul
      have hN : VGe π 0 (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + A) :=
        (((hx₁.pow0 hπ 2).add hπ ((hx₁.mul hπ hx₂).mono (by simp))).add hπ
          (hx₂.pow0 hπ 2)).add hπ hA
      refine ⟨?_, ?_⟩
      · rw [hℓeq]; have := hN.div hπ hsum0; rwa [hvsum, sub_zero] at this
      · have hY' : resK π ρ y₁ ≠ (shortCurve Ab).toAffine.negY (resK π ρ x₁) (resK π ρ y₁) := by
          rw [shortCurve_negY]; intro h0; apply hY0; rw [← hYY]; linear_combination h0
        rw [hℓeq, resK_div hπ ρ hρ hN (hy₁.add hπ hy₂) hvsum hsum0, ← hX, ← hYY,
          Affine.slope_of_Y_ne rfl hY', resK_add hπ ρ hρ (((hx₁.pow0 hπ 2).add hπ
            ((hx₁.mul hπ hx₂).mono (by simp))).add hπ (hx₂.pow0 hπ 2)) hA,
          resK_add hπ ρ hρ ((hx₁.pow0 hπ 2).add hπ ((hx₁.mul hπ hx₂).mono (by simp)))
            (hx₂.pow0 hπ 2),
          resK_add hπ ρ hρ (hx₁.pow0 hπ 2) ((hx₁.mul hπ hx₂).mono (by simp)),
          resK_mul hπ ρ hρ hx₁ hx₂, resK_pow hπ ρ hρ hx₁, resK_pow hπ ρ hρ hx₂, hAb,
          resK_add hπ ρ hρ hy₁ hy₂, ← hX, ← hYY]
        simp only [shortCurve_negY, shortCurve_a₁, shortCurve_a₂, shortCurve_a₄, zero_mul,
          mul_zero, add_zero, sub_zero]
        ring_nf
    · have hx : x₁ ≠ x₂ := by rintro rfl; exact hX rfl
      have hd0 : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
      have hvd : vp π (x₁ - x₂) = 0 :=
        (vp_eq_zero_of_resK_ne_zero hπ ρ hρ (hx₁.sub hπ hx₂)
          (by rw [resK_sub hπ ρ hρ hx₁ hx₂]; exact sub_ne_zero.mpr hX)).2
      rw [Affine.slope_of_X_ne hx, Affine.slope_of_X_ne hX]
      refine ⟨?_, ?_⟩
      · have := (hy₁.sub hπ hy₂).div hπ hd0; rwa [hvd, sub_zero] at this
      · rw [resK_div hπ ρ hρ (hy₁.sub hπ hy₂) (hx₁.sub hπ hx₂) hvd hd0,
          resK_sub hπ ρ hρ hy₁ hy₂, resK_sub hπ ρ hρ hx₁ hx₂]
  set ℓ := (shortCurve A).toAffine.slope x₁ x₂ y₁ y₂ with hℓdef
  have hx₃ : VGe π 0 ((shortCurve A).toAffine.addX x₁ x₂ ℓ) := by
    rw [Affine.addX, shortCurve_a₁, shortCurve_a₂, zero_mul, add_zero, sub_zero]
    exact ((hℓ.pow0 hπ 2).sub hπ hx₁).sub hπ hx₂
  have eX : resK π ρ ((shortCurve A).toAffine.addX x₁ x₂ ℓ) =
      (shortCurve Ab).toAffine.addX (resK π ρ x₁) (resK π ρ x₂)
        ((shortCurve Ab).toAffine.slope (resK π ρ x₁) (resK π ρ x₂) (resK π ρ y₁)
          (resK π ρ y₂)) := by
    simp only [Affine.addX, shortCurve_a₁, shortCurve_a₂, zero_mul, add_zero, sub_zero]
    rw [resK_sub hπ ρ hρ ((hℓ.pow0 hπ 2).sub hπ hx₁) hx₂, resK_sub hπ ρ hρ (hℓ.pow0 hπ 2) hx₁,
      resK_pow hπ ρ hρ hℓ, hres]
  refine ⟨_, _, _, Point.add_some hxy, hx₃, eX, ?_⟩
  simp only [Affine.addY, Affine.negAddY, shortCurve_negY]
  rw [resK_neg hπ ρ hρ ((hℓ.mul hπ (hx₃.sub hπ hx₁)).add hπ hy₁ |>.mono (by simp)),
    resK_add hπ ρ hρ ((hℓ.mul hπ (hx₃.sub hπ hx₁)).mono (by simp)) hy₁,
    resK_mul hπ ρ hρ hℓ (hx₃.sub hπ hx₁), resK_sub hπ ρ hρ hx₃ hx₁, eX, hres]

include hπ hρ hA hAb in
/-- **Opposite reductions**: if `red P₁ = -red P₂` for points with integral abscissas and
nonsingular reduction, then `P₁ + P₂` is `O` or lies in `W₁(π)`. -/
theorem add_of_red_opp (h2 : (2 : k) ≠ 0) {x₁ y₁ x₂ y₂ : K0}
    (h₁ : (shortCurve A).toAffine.Nonsingular x₁ y₁)
    (h₂ : (shortCurve A).toAffine.Nonsingular x₂ y₂) (hx₁ : VGe π 0 x₁) (hx₂ : VGe π 0 x₂)
    (hns₁ : (shortCurve Ab).toAffine.Nonsingular (resK π ρ x₁) (resK π ρ y₁))
    (hX : resK π ρ x₁ = resK π ρ x₂) (hY : resK π ρ y₁ = -resK π ρ y₂) :
    InE1 π A (Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂) := by
  have hy₁ := vge_y_of_vge_x hπ hA ((shortCurve_equation_iff A x₁ y₁).mp h₁.1) hx₁
  have hy₂ := vge_y_of_vge_x hπ hA ((shortCurve_equation_iff A x₂ y₂).mp h₂.1) hx₂
  by_cases hxy : x₁ = x₂ ∧ y₁ = (shortCurve A).toAffine.negY x₂ y₂
  · rw [Point.add_of_Y_eq hxy.1 hxy.2]; trivial
  rw [Point.add_some hxy]
  show ¬VGe π 0 _
  rw [Affine.addX, shortCurve_a₁, shortCurve_a₂, zero_mul, add_zero, sub_zero]
  set ℓ := (shortCurve A).toAffine.slope x₁ x₂ y₁ y₂
  have hmul := slope_mul_add h₁.1 h₂.1 hxy
  have hsum : VGe π 1 (y₁ + y₂) := by
    rw [← resK_eq_zero_iff hπ ρ hρ (hy₁.add hπ hy₂), resK_add hπ ρ hρ hy₁ hy₂, hY,
      neg_add_cancel]
  have hN : VGe π 0 (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + A) :=
    (((hx₁.pow0 hπ 2).add hπ ((hx₁.mul hπ hx₂).mono (by simp))).add hπ (hx₂.pow0 hπ 2)).add hπ hA
  have hresN : resK π ρ (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + A) = 3 * resK π ρ x₁ ^ 2 + Ab := by
    rw [resK_add hπ ρ hρ (((hx₁.pow0 hπ 2).add hπ ((hx₁.mul hπ hx₂).mono (by simp))).add hπ
      (hx₂.pow0 hπ 2)) hA, resK_add hπ ρ hρ ((hx₁.pow0 hπ 2).add hπ ((hx₁.mul hπ hx₂).mono
      (by simp))) (hx₂.pow0 hπ 2), resK_add hπ ρ hρ (hx₁.pow0 hπ 2) ((hx₁.mul hπ hx₂).mono
      (by simp)), resK_mul hπ ρ hρ hx₁ hx₂, resK_pow hπ ρ hρ hx₁, resK_pow hπ ρ hρ hx₂, hAb,
      ← hX]
    ring
  obtain ⟨hℓ0, hvℓ⟩ : ℓ ≠ 0 ∧ vp π ℓ ≤ -1 := by
    by_cases hr : resK π ρ (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + A) = 0
    · -- `3 X₁² + Ā = 0`, so `Y₁ ≠ 0` by nonsingularity of the reduced point
      rw [hresN] at hr
      have hns := (nonsingular_iff _ _).mp hns₁
      simp only [shortCurve_a₁, shortCurve_a₂, shortCurve_a₃, shortCurve_a₄, zero_mul, mul_zero,
        add_zero, sub_zero] at hns
      have hY₁ : resK π ρ y₁ ≠ 0 := by
        rcases hns.2 with h | h
        · exact absurd (by rw [hr]) h
        · intro h0; apply h; rw [h0, neg_zero]
      by_cases hx : x₁ = x₂
      · exfalso
        have hyy : y₁ = y₂ := by
          rcases Y_eq_of_X_eq h₁.1 h₂.1 hx with h | h
          · exact h
          · exact absurd ⟨hx, h⟩ hxy
        rw [hyy] at hY
        apply hY₁
        rw [hyy]
        have : (2 : k) * resK π ρ y₂ = 0 := by linear_combination hY
        exact (mul_eq_zero.mp this).resolve_left h2
      · have hsl : ℓ * (x₁ - x₂) = y₁ - y₂ := by
          simp only [ℓ]; rw [Affine.slope_of_X_ne hx, div_mul_cancel₀ _ (sub_ne_zero.mpr hx)]
        have hd : VGe π 1 (x₁ - x₂) := by
          rw [← resK_eq_zero_iff hπ ρ hρ (hx₁.sub hπ hx₂), resK_sub hπ ρ hρ hx₁ hx₂, hX,
            sub_self]
        have hres : resK π ρ (y₁ - y₂) ≠ 0 := by
          rw [resK_sub hπ ρ hρ hy₁ hy₂]
          intro h0; apply hY₁
          have : (2 : k) * resK π ρ y₁ = 0 := by linear_combination h0 + hY
          exact (mul_eq_zero.mp this).resolve_left h2
        obtain ⟨hyy0, hvyy⟩ := vp_eq_zero_of_resK_ne_zero hπ ρ hρ (hy₁.sub hπ hy₂) hres
        exact vp_le_neg_one_of_mul hπ hsl hyy0 hvyy hd
    · obtain ⟨hN0, hvN⟩ := vp_eq_zero_of_resK_ne_zero hπ ρ hρ hN hr
      exact vp_le_neg_one_of_mul hπ hmul hN0 hvN hsum
  exact not_vge_addX hπ hA hℓ0 hvℓ hx₁ hx₂

include hπ hρ hA hAb in
/-- **Translation by the kernel**: if `P₁ ∈ W₁(π)` is affine and `x₂ ∈ 𝒪_π`, then
`P₁ + P₂` has integral abscissa and the same reduced coordinates as `P₂`. -/
theorem add_kernel {x₁ y₁ x₂ y₂ : K0} (h₁ : (shortCurve A).toAffine.Nonsingular x₁ y₁)
    (h₂ : (shortCurve A).toAffine.Nonsingular x₂ y₂) (hx₁ : ¬VGe π 0 x₁) (hx₂ : VGe π 0 x₂) :
    ∃ x₃ y₃ h₃, Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ = Point.some x₃ y₃ h₃ ∧
      VGe π 0 x₃ ∧ resK π ρ x₃ = resK π ρ x₂ ∧ resK π ρ y₃ = resK π ρ y₂ := by
  have hxy : ¬(x₁ = x₂ ∧ y₁ = (shortCurve A).toAffine.negY x₂ y₂) := by
    rintro ⟨rfl, -⟩; exact hx₁ hx₂
  obtain ⟨x₃, y₃, h₃, hs⟩ : ∃ x₃ y₃ h₃,
      Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ = Point.some x₃ y₃ h₃ :=
    ⟨_, _, _, Point.add_some hxy⟩
  have hP₂ : Point.some x₂ y₂ h₂ = Point.some x₃ y₃ h₃ + -Point.some x₁ y₁ h₁ := by
    rw [← hs]; abel
  have hP₁ : Point.some x₁ y₁ h₁ = Point.some x₃ y₃ h₃ + -Point.some x₂ y₂ h₂ := by
    rw [← hs]; abel
  rw [Point.neg_some] at hP₁ hP₂
  -- the sum is integral
  have hx₃ : VGe π 0 x₃ := by
    by_contra hx₃
    have := inE1_add hπ hA (P := Point.some x₃ y₃ h₃)
      (Q := Point.some x₁ _ ((nonsingular_neg ..).mpr h₁)) hx₃ hx₁
    rw [← hP₂] at this
    exact this hx₂
  refine ⟨x₃, y₃, h₃, hs, hx₃, ?_⟩
  -- the reduced coordinates agree
  have hy₂ := vge_y_of_vge_x hπ hA ((shortCurve_equation_iff A x₂ y₂).mp h₂.1) hx₂
  by_contra hne
  have hopp : ¬(resK π ρ x₃ = resK π ρ x₂ ∧
      resK π ρ y₃ = -resK π ρ ((shortCurve A).toAffine.negY x₂ y₂)) := by
    rintro ⟨hX, hY⟩
    apply hne
    refine ⟨hX, ?_⟩
    rw [hY, shortCurve_negY, resK_neg hπ ρ hρ hy₂, neg_neg]
  obtain ⟨x', y', h', hs', hx', -⟩ := int_add hπ ρ hρ hA hAb h₃
    ((nonsingular_neg ..).mpr h₂) hx₃ hx₂ hopp
  rw [← hP₁, Point.some.injEq] at hs'
  exact hx₁ (hs'.1 ▸ hx')

include hπ hρ hA hAb in
/-- **Reduction is additive on `W₀(π)`**, and `W₀(π)` is closed under addition. -/
theorem inE0_add_redK_add (h2 : (2 : k) ≠ 0) {P Q : (shortCurve A).toAffine.Point}
    (hP : InE0 π ρ A Ab P) (hQ : InE0 π ρ A Ab Q) :
    InE0 π ρ A Ab (P + Q) ∧ redK π ρ A Ab (P + Q) = redK π ρ A Ab P + redK π ρ A Ab Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · show InE0 π ρ A Ab (0 + Q) ∧ redK π ρ A Ab (0 + Q) = redK π ρ A Ab 0 + _
    rw [zero_add, redK_zero, zero_add]; exact ⟨hQ, rfl⟩
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · show InE0 π ρ A Ab (_ + 0) ∧ redK π ρ A Ab (_ + 0) = _ + redK π ρ A Ab 0
    rw [add_zero, redK_zero, add_zero]; exact ⟨hP, rfl⟩
  rcases hP with hx₁ | ⟨hx₁, hns₁⟩ <;> rcases hQ with hx₂ | ⟨hx₂, hns₂⟩
  · -- both in the kernel
    have h := inE1_add hπ hA (P := Point.some x₁ y₁ h₁) (Q := Point.some x₂ y₂ h₂) hx₁ hx₂
    refine ⟨inE0_of_inE1 h, ?_⟩
    rw [(redK_eq_zero_iff ρ (inE0_of_inE1 h)).mpr h, redK_some_of_not_vge _ hx₁,
      redK_some_of_not_vge _ hx₂, add_zero]
  · -- kernel plus integral
    obtain ⟨x₃, y₃, h₃, hs, hx₃, hX, hY⟩ := add_kernel hπ ρ hρ hA hAb h₁ h₂ hx₁ hx₂
    have hns₃ : (shortCurve Ab).toAffine.Nonsingular (resK π ρ x₃) (resK π ρ y₃) := by
      rw [hX, hY]; exact hns₂
    rw [hs, redK_some_of_ns _ hx₃ hns₃, redK_some_of_not_vge _ hx₁, redK_some_of_ns _ hx₂ hns₂,
      zero_add]
    exact ⟨Or.inr ⟨hx₃, hns₃⟩, by simp only [Point.some.injEq]; exact ⟨hX, hY⟩⟩
  · -- integral plus kernel
    obtain ⟨x₃, y₃, h₃, hs, hx₃, hX, hY⟩ := add_kernel hπ ρ hρ hA hAb h₂ h₁ hx₂ hx₁
    have hns₃ : (shortCurve Ab).toAffine.Nonsingular (resK π ρ x₃) (resK π ρ y₃) := by
      rw [hX, hY]; exact hns₁
    rw [add_comm, hs, redK_some_of_ns _ hx₃ hns₃, redK_some_of_not_vge _ hx₂,
      redK_some_of_ns _ hx₁ hns₁, add_zero]
    exact ⟨Or.inr ⟨hx₃, hns₃⟩, by simp only [Point.some.injEq]; exact ⟨hX, hY⟩⟩
  · -- both integral with nonsingular reductions
    by_cases hopp : resK π ρ x₁ = resK π ρ x₂ ∧ resK π ρ y₁ = -resK π ρ y₂
    · have h := add_of_red_opp hπ ρ hρ hA hAb h2 h₁ h₂ hx₁ hx₂ hns₁ hopp.1 hopp.2
      refine ⟨inE0_of_inE1 h, ?_⟩
      rw [(redK_eq_zero_iff ρ (inE0_of_inE1 h)).mpr h, redK_some_of_ns _ hx₁ hns₁,
        redK_some_of_ns _ hx₂ hns₂]
      exact (Point.add_of_Y_eq hopp.1 (by rw [shortCurve_negY]; exact hopp.2)).symm
    · obtain ⟨x₃, y₃, h₃, hs, hx₃, hX, hY⟩ := int_add hπ ρ hρ hA hAb h₁ h₂ hx₁ hx₂ hopp
      have hopp' : ¬(resK π ρ x₁ = resK π ρ x₂ ∧
          resK π ρ y₁ = (shortCurve Ab).toAffine.negY (resK π ρ x₂) (resK π ρ y₂)) := by
        rwa [shortCurve_negY]
      have hns₃ : (shortCurve Ab).toAffine.Nonsingular (resK π ρ x₃) (resK π ρ y₃) := by
        rw [hX, hY]; exact nonsingular_add hns₁ hns₂ hopp'
      rw [hs, redK_some_of_ns _ hx₃ hns₃, redK_some_of_ns _ hx₁ hns₁,
        redK_some_of_ns _ hx₂ hns₂, Point.add_some hopp']
      exact ⟨Or.inr ⟨hx₃, hns₃⟩, by simp only [Point.some.injEq]; exact ⟨hX, hY⟩⟩

/-! ### The subgroup `W₀(π)` and the homomorphism -/

variable (h2 : ¬π ∣ 2)

/-- The subgroup `W₀(π)` of points with nonsingular reduction. -/
def E0sub : AddSubgroup (shortCurve A).toAffine.Point where
  carrier := {P | InE0 π ρ A Ab P}
  zero_mem' := trivial
  add_mem' hP hQ :=
    (inE0_add_redK_add hπ ρ hρ hA hAb (two_ne_zero_of_not_dvd ρ hρ h2) hP hQ).1
  neg_mem' hP := inE0_neg hπ ρ hρ hA hP

theorem mem_E0sub_iff (P : (shortCurve A).toAffine.Point) :
    P ∈ E0sub hπ ρ hρ hA hAb h2 ↔ InE0 π ρ A Ab P := Iff.rfl

theorem E1sub_le_E0sub : E1sub hπ hA ≤ E0sub hπ ρ hρ hA hAb h2 :=
  fun _ hP => inE0_of_inE1 hP

/-- **Reduction on the nonsingular part**, `red : W₀(π) →+ W̃_ns(k)`. -/
noncomputable def reductionHom :
    E0sub hπ ρ hρ hA hAb h2 →+ (shortCurve Ab).toAffine.Point where
  toFun P := redK π ρ A Ab P
  map_zero' := rfl
  map_add' P Q :=
    (inE0_add_redK_add hπ ρ hρ hA hAb (two_ne_zero_of_not_dvd ρ hρ h2) P.2 Q.2).2

@[simp] theorem reductionHom_apply (P : E0sub hπ ρ hρ hA hAb h2) :
    reductionHom hπ ρ hρ hA hAb h2 P = redK π ρ A Ab P := rfl

/-- **The kernel of reduction is `W₁(π)`.** -/
theorem ker_reductionHom :
    (reductionHom hπ ρ hρ hA hAb h2).ker = (E1sub hπ hA).addSubgroupOf (E0sub hπ ρ hρ hA hAb h2) := by
  ext P
  rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, reductionHom_apply, mem_E1sub_iff]
  exact redK_eq_zero_iff ρ P.2

omit h2 [DecidableEq k] in
include hπ hρ hA hAb in
/-- **Good reduction**: if `Ā ≠ 0` (and `2 ≠ 0` in `k`), every integral point has
nonsingular reduction, so every point lies in `W₀(π)`. -/
theorem inE0_of_good (h2 : (2 : k) ≠ 0) (hAb0 : Ab ≠ 0) (P : (shortCurve A).toAffine.Point) :
    InE0 π ρ A Ab P := by
  have : NeZero (2 : k) := ⟨h2⟩
  have := shortCurve_isElliptic hAb0
  rcases P with _ | ⟨x, y, h⟩
  · trivial
  by_cases hx : VGe π 0 x
  · exact Or.inr ⟨hx, equation_iff_nonsingular.mp (redK_equation hπ ρ hρ hA hAb h.1 hx)⟩
  · exact Or.inl hx

/-- **Good reduction**: if `Ā ≠ 0`, then `W₀(π) = W(K₀)`. -/
theorem E0_eq_top_of_good (hAb0 : Ab ≠ 0) : E0sub hπ ρ hρ hA hAb h2 = ⊤ := by
  ext P
  simp only [AddSubgroup.mem_top, iff_true]
  exact inE0_of_good hπ ρ hρ hA hAb (two_ne_zero_of_not_dvd ρ hρ h2) hAb0 P

/-- **Consequence**: for `Q ∈ W₀(π)` with `n` the order of `red Q`, `[m n] Q ∈ W₁(π)` for every
integer `m` (if the order is infinite, `n = 0` and the statement is trivial). -/
theorem zsmul_addOrderOf_mem_E1 {Q : (shortCurve A).toAffine.Point}
    (hQ : Q ∈ E0sub hπ ρ hρ hA hAb h2) (m : ℤ) :
    (m * addOrderOf (redK π ρ A Ab Q) : ℤ) • Q ∈ E1sub hπ hA := by
  have hn : (addOrderOf (redK π ρ A Ab Q)) • (⟨Q, hQ⟩ : E0sub hπ ρ hρ hA hAb h2) ∈
      (reductionHom hπ ρ hρ hA hAb h2).ker := by
    rw [AddMonoidHom.mem_ker, map_nsmul, reductionHom_apply]
    exact addOrderOf_nsmul_eq_zero _
  rw [ker_reductionHom, AddSubgroup.mem_addSubgroupOf] at hn
  have : ((addOrderOf (redK π ρ A Ab Q)) • Q) ∈ E1sub hπ hA := by simpa using hn
  rw [mul_zsmul, natCast_zsmul]
  exact (E1sub hπ hA).zsmul_mem this m

end ZInQ.Size

/-! ### The article's residue field and the model chapter's special case -/

namespace ZInQ.Size

open WeierstrassCurve WeierstrassCurve.Affine

/-- The quotient map `ℤ[s] → ℤ[s]/(π)` has kernel `(π)`: the article's residue field is an
instance of the pair `(k, ρ)`. -/
theorem quotient_mk_eq_zero_iff (π : Zs) (a : Zs) :
    Ideal.Quotient.mk (Ideal.span {π}) a = 0 ↔ π ∣ a := by
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

/-- Membership in `W₁(π)` spelled out: `Q = O`, or `Q = (x, y)` with `x ≠ 0` and
`v_π(x) < 0`. -/
theorem mem_E1sub_iff_vp {π : Zs} (hπ : Prime π) {A : K0} (hA : VGe π 0 A)
    (Q : (shortCurve A).toAffine.Point) :
    Q ∈ E1sub hπ hA ↔ Q = 0 ∨ ∃ x y h, Q = Point.some x y h ∧ x ≠ 0 ∧ vp π x < 0 := by
  rcases Q with _ | ⟨x, y, h⟩
  · exact ⟨fun _ => Or.inl rfl, fun _ => trivial⟩
  rw [mem_E1sub_iff, inE1_some_iff, VGe]
  constructor
  · intro hx
    push Not at hx
    exact Or.inr ⟨x, y, h, rfl, hx.1, hx.2⟩
  · rintro (h0 | ⟨x', y', h', he, hx0, hx⟩)
    · exact absurd h0 (Point.some_ne_zero _)
    · rw [Point.some.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      push Not
      exact ⟨hx0, hx⟩

theorem res_eq_resK {p : ℕ} [Fact p.Prime] (π : Zs) (ρ : Zs →+* ZMod p) (x : K0) :
    ZInQ.res π ρ x = resK π ρ x := rfl

/-- The model chapter's reduction map `ZInQ.red` (residue degree one, good reduction) is the
special case `k = 𝔽_p` of `redK`. -/
theorem red_eq_redK {p : ℕ} [Fact p.Prime] {π : Zs} (hπ : Prime π) (ρ : Zs →+* ZMod p)
    (hρ : ∀ a, ρ a = 0 ↔ π ∣ a) {A : K0} (hA : VGe π 0 A) {Ab : ZMod p}
    (hAb : ZInQ.res π ρ A = Ab) [(shortCurve Ab).IsElliptic]
    (P : (shortCurve A).toAffine.Point) : ZInQ.red hπ ρ hρ hA hAb P = redK π ρ A Ab P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  by_cases hx : VGe π 0 x
  · have hns : (shortCurve Ab).toAffine.Nonsingular (resK π ρ x) (resK π ρ y) :=
      equation_iff_nonsingular.mp (ZInQ.red_equation hπ ρ hρ hA hAb h.1 hx)
    rw [ZInQ.red_some_of_vge hπ ρ hρ hA hAb h hx, redK_some_of_ns h hx hns]
    rfl
  · rw [ZInQ.red_some_of_not_vge hπ ρ hρ hA hAb h hx, redK_some_of_not_vge h hx]

end ZInQ.Size
