import ZInQKernel.Model.Descent.KernelReduction

/-!
# Reduction modulo a prime of degree one

Blueprint: `model/descent/reduction-torsion.md`.

Let `π` be a prime of `ℤ[s]`, `ρ : ℤ[s] → 𝔽_p` a ring homomorphism with kernel `(π)` (`p` an odd
prime), `W : y² = x³ + A x` over `K₀` with `A` integral at `π`, and `W̃ : y² = x³ + Ā x` over
`𝔽_p` with `Ā = res A ≠ 0`. The reduction map `red : W(K₀) → W̃(𝔽_p)` sends `O` and the points
with `v_π(x) < 0` to `O`, and `(x, y)` with `x` integral to `(res x, res y)`.

1. `red_add`: `red` is a group homomorphism (`redHom`).
2. `eq_zero_of_red_eq_zero`: a point of finite order prime to `p` in the kernel of `red` is `O`.

The proof of 1 is the classical case analysis: for integral `P₁, P₂` either the reduced points
are opposite and `P₁ + P₂` is `O` or in the kernel (the slope has negative valuation), or the
slope is integral and reduces to the slope over `𝔽_p`; the kernel is closed under addition
(`kernel_add`), and `red` is constant on its cosets. Part 2 is `nsmul_ne_zero_of_not_vge`.
-/

namespace ZInQ

open WeierstrassCurve WeierstrassCurve.Affine

variable {p : ℕ} [Fact p.Prime] {π : Zs} (hπ : Prime π) (ρ : Zs →+* ZMod p)
  (hρ : ∀ a, ρ a = 0 ↔ π ∣ a) {A : K0} (hA : VGe π 0 A) {Ab : ZMod p}
  (hAb : res π ρ A = Ab)

section Basic

include hπ

theorem VGe.pow0 {x : K0} (hx : VGe π 0 x) (n : ℕ) : VGe π 0 (x ^ n) :=
  (hx.pow hπ n).mono (by simp)

include hA

theorem vge_y_of_vge_x {x y : K0} (e : y ^ 2 = x ^ 3 + A * x) (hx : VGe π 0 x) :
    VGe π 0 y := by
  by_cases hy : y = 0
  · exact Or.inl hy
  have h2 : VGe π 0 (y ^ 2) := by
    rw [e]; exact (hx.pow0 hπ 3).add hπ ((hA.mul hπ hx).mono (by simp))
  rw [vge_iff (pow_ne_zero 2 hy), vp_pow hπ] at h2
  rw [vge_iff hy]; push_cast at h2; omega

include hρ hAb

theorem red_equation {x y : K0} (h : (shortCurve A).toAffine.Equation x y) (hx : VGe π 0 x) :
    (shortCurve Ab).toAffine.Equation (res π ρ x) (res π ρ y) := by
  have e := (shortCurve_equation_iff A x y).mp h
  have hy := vge_y_of_vge_x hπ hA e hx
  rw [shortCurve_equation_iff, ← hAb, ← res_pow hπ ρ hρ hy, ← res_pow hπ ρ hρ hx,
    ← res_mul hπ ρ hρ hA hx, ← res_add hπ ρ hρ (hx.pow0 hπ 3) (hA.mul hπ hx |>.mono (by simp)), e]

end Basic

variable [(shortCurve Ab).IsElliptic]

open Classical in
/-- The reduction map `W(K₀) → W̃(𝔽_p)`. -/
noncomputable def red : (shortCurve A).toAffine.Point → (shortCurve Ab).toAffine.Point
  | 0 => 0
  | .some x y h => if hx : VGe π 0 x then Point.mk (red_equation hπ ρ hρ hA hAb h.1 hx) else 0

@[simp] theorem red_zero : red hπ ρ hρ hA hAb 0 = 0 := rfl

theorem red_some_of_vge {x y : K0} (h : (shortCurve A).toAffine.Nonsingular x y)
    (hx : VGe π 0 x) :
    red hπ ρ hρ hA hAb (.some x y h) = Point.mk (red_equation hπ ρ hρ hA hAb h.1 hx) := by
  simp [red, hx]

theorem red_some_of_not_vge {x y : K0} (h : (shortCurve A).toAffine.Nonsingular x y)
    (hx : ¬VGe π 0 x) : red hπ ρ hρ hA hAb (.some x y h) = 0 := by
  simp [red, hx]

include hπ hA hρ hAb in
theorem red_neg (P : (shortCurve A).toAffine.Point) :
    red hπ ρ hρ hA hAb (-P) = -red hπ ρ hρ hA hAb P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  by_cases hx : VGe π 0 x
  · have hy := vge_y_of_vge_x hπ hA ((shortCurve_equation_iff A x y).mp h.1) hx
    rw [Point.neg_some, red_some_of_vge hπ ρ hρ hA hAb _ hx, red_some_of_vge hπ ρ hρ hA hAb _ hx,
      Point.mk, Point.mk, Point.neg_some]
    simp only [Point.some.injEq, shortCurve_negY, true_and]
    exact res_neg hπ ρ hρ hy
  · rw [Point.neg_some, red_some_of_not_vge hπ ρ hρ hA hAb _ hx,
      red_some_of_not_vge hπ ρ hρ hA hAb _ hx, neg_zero]

variable [(shortCurve A).IsElliptic]

include hπ hA hρ hAb in
/-- If the chord slope is integral and reduces to the slope over `𝔽_p`, reduction commutes
with the sum. -/
theorem red_add_of_slope {x₁ y₁ x₂ y₂ : K0} (h₁ : (shortCurve A).toAffine.Nonsingular x₁ y₁)
    (h₂ : (shortCurve A).toAffine.Nonsingular x₂ y₂) (hx₁ : VGe π 0 x₁) (hx₂ : VGe π 0 x₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (shortCurve A).toAffine.negY x₂ y₂))
    (hℓ : VGe π 0 ((shortCurve A).toAffine.slope x₁ x₂ y₁ y₂))
    (hxy' : ¬(res π ρ x₁ = res π ρ x₂ ∧
      res π ρ y₁ = (shortCurve Ab).toAffine.negY (res π ρ x₂) (res π ρ y₂)))
    (hres : res π ρ ((shortCurve A).toAffine.slope x₁ x₂ y₁ y₂) =
      (shortCurve Ab).toAffine.slope (res π ρ x₁) (res π ρ x₂) (res π ρ y₁) (res π ρ y₂)) :
    red hπ ρ hρ hA hAb (.some x₁ y₁ h₁ + .some x₂ y₂ h₂) =
      red hπ ρ hρ hA hAb (.some x₁ y₁ h₁) + red hπ ρ hρ hA hAb (.some x₂ y₂ h₂) := by
  have hy₁ := vge_y_of_vge_x hπ hA ((shortCurve_equation_iff A x₁ y₁).mp h₁.1) hx₁
  set ℓ := (shortCurve A).toAffine.slope x₁ x₂ y₁ y₂ with hℓdef
  have hx₃ : VGe π 0 ((shortCurve A).toAffine.addX x₁ x₂ ℓ) := by
    rw [Affine.addX, shortCurve_a₁, shortCurve_a₂, zero_mul, add_zero, sub_zero]
    exact ((hℓ.pow0 hπ 2).sub hπ hx₁).sub hπ hx₂
  rw [Point.add_some hxy, red_some_of_vge hπ ρ hρ hA hAb _ hx₃, red_some_of_vge hπ ρ hρ hA hAb _ hx₁,
    red_some_of_vge hπ ρ hρ hA hAb _ hx₂, Point.mk, Point.mk, Point.mk, Point.add_some hxy']
  simp only [Point.some.injEq]
  have eX : res π ρ ((shortCurve A).toAffine.addX x₁ x₂ ℓ) =
      (shortCurve Ab).toAffine.addX (res π ρ x₁) (res π ρ x₂)
        ((shortCurve Ab).toAffine.slope (res π ρ x₁) (res π ρ x₂) (res π ρ y₁) (res π ρ y₂)) := by
    simp only [Affine.addX, shortCurve_a₁, shortCurve_a₂, zero_mul, add_zero, sub_zero]
    rw [res_sub hπ ρ hρ ((hℓ.pow0 hπ 2).sub hπ hx₁) hx₂, res_sub hπ ρ hρ (hℓ.pow0 hπ 2) hx₁,
      res_pow hπ ρ hρ hℓ, hres]
  refine ⟨eX, ?_⟩
  simp only [Affine.addY, Affine.negAddY, shortCurve_negY, shortCurve_a₁, shortCurve_a₃, zero_mul,
    sub_zero]
  rw [res_neg hπ ρ hρ ((hℓ.mul hπ (hx₃.sub hπ hx₁)).add hπ hy₁ |>.mono (by simp)),
    res_add hπ ρ hρ ((hℓ.mul hπ (hx₃.sub hπ hx₁)).mono (by simp)) hy₁,
    res_mul hπ ρ hρ hℓ (hx₃.sub hπ hx₁), res_sub hπ ρ hρ hx₃ hx₁, eX, hres]

omit [(shortCurve A).IsElliptic] [(shortCurve Ab).IsElliptic] in
/-- `ℓ (y₁ + y₂) = x₁² + x₁ x₂ + x₂² + A` for the slope `ℓ` of a chord or tangent. -/
theorem slope_mul_add {x₁ y₁ x₂ y₂ : K0} (h₁ : (shortCurve A).toAffine.Equation x₁ y₁)
    (h₂ : (shortCurve A).toAffine.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (shortCurve A).toAffine.negY x₂ y₂)) :
    (shortCurve A).toAffine.slope x₁ x₂ y₁ y₂ * (y₁ + y₂) = x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + A := by
  have e₁ := (shortCurve_equation_iff A x₁ y₁).mp h₁
  have e₂ := (shortCurve_equation_iff A x₂ y₂).mp h₂
  by_cases hx : x₁ = x₂
  · subst hx
    have hyy : y₁ = y₂ := by
      rcases Y_eq_of_X_eq h₁ h₂ rfl with h | h
      · exact h
      · exact absurd ⟨rfl, h⟩ hxy
    subst hyy
    have hy' : y₁ ≠ (shortCurve A).toAffine.negY x₁ y₁ := fun h => hxy ⟨rfl, h⟩
    rw [Affine.slope_of_Y_ne rfl hy']
    have hy0 : y₁ - (shortCurve A).toAffine.negY x₁ y₁ ≠ 0 := sub_ne_zero.mpr hy'
    simp only [shortCurve_negY, shortCurve_a₁, shortCurve_a₂, shortCurve_a₄] at hy0 ⊢
    rw [div_mul_eq_mul_div, div_eq_iff hy0]
    ring
  · rw [Affine.slope_of_X_ne hx, div_mul_eq_mul_div, div_eq_iff (sub_ne_zero.mpr hx)]
    linear_combination e₁ - e₂

include hπ in
omit [(shortCurve A).IsElliptic] [(shortCurve Ab).IsElliptic] in
/-- If `ℓ d = N` with `v(N) = 0` and `v(d) ≥ 1`, then `v(ℓ) ≤ -1`. -/
theorem vp_le_neg_one_of_mul {ℓ d N : K0} (h : ℓ * d = N) (hN : N ≠ 0) (hvN : vp π N = 0)
    (hd : VGe π 1 d) : ℓ ≠ 0 ∧ vp π ℓ ≤ -1 := by
  have hℓ : ℓ ≠ 0 := by rintro rfl; rw [zero_mul] at h; exact hN h.symm
  have hd0 : d ≠ 0 := by rintro rfl; rw [mul_zero] at h; exact hN h.symm
  refine ⟨hℓ, ?_⟩
  have := congrArg (vp π) h
  rw [vp_mul hπ hℓ hd0, hvN] at this
  rw [vge_iff hd0] at hd
  omega

include hπ hA in
omit [(shortCurve A).IsElliptic] [(shortCurve Ab).IsElliptic] in
/-- If the slope has negative valuation, the abscissa `ℓ² - x₁ - x₂` is not integral. -/
theorem not_vge_addX {ℓ x₁ x₂ : K0} (hℓ : ℓ ≠ 0) (hvℓ : vp π ℓ ≤ -1) (hx₁ : VGe π 0 x₁)
    (hx₂ : VGe π 0 x₂) : ¬VGe π 0 (ℓ ^ 2 - x₁ - x₂) := by
  have hv2 : vp π (ℓ ^ 2) = 2 * vp π ℓ := by rw [vp_pow hπ]; norm_num
  have heq : ℓ ^ 2 - x₁ - x₂ = ℓ ^ 2 + -(x₁ + x₂) := by ring
  have hsmall : VGe π (vp π (ℓ ^ 2) + 1) (-(x₁ + x₂)) :=
    ((hx₁.add hπ hx₂).neg hπ).mono (by omega)
  rw [heq, vge_iff (add_ne_zero_of_vge hπ (pow_ne_zero 2 hℓ) hsmall),
    vp_add_eq_of_vge hπ (pow_ne_zero 2 hℓ) hsmall]
  omega

include hπ hA hρ hAb in
/-- **Opposite reductions**: if `red P₁ = -red P₂` for integral `P₁, P₂`, then `P₁ + P₂` is `O`
or lies in the kernel of reduction. -/
theorem add_of_red_opp {x₁ y₁ x₂ y₂ : K0} (h₁ : (shortCurve A).toAffine.Nonsingular x₁ y₁)
    (h₂ : (shortCurve A).toAffine.Nonsingular x₂ y₂) (hx₁ : VGe π 0 x₁) (hx₂ : VGe π 0 x₂)
    (hX : res π ρ x₁ = res π ρ x₂) (hY : res π ρ y₁ = -res π ρ y₂) :
    Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ = 0 ∨
      ∃ x₃ y₃ h₃, Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ = Point.some x₃ y₃ h₃ ∧
        ¬VGe π 0 x₃ := by
  have hy₁ := vge_y_of_vge_x hπ hA ((shortCurve_equation_iff A x₁ y₁).mp h₁.1) hx₁
  have hy₂ := vge_y_of_vge_x hπ hA ((shortCurve_equation_iff A x₂ y₂).mp h₂.1) hx₂
  have h2 : (2 : ZMod p) ≠ 0 := Descent.two_ne_zero_of_isElliptic (b := Ab)
  by_cases hxy : x₁ = x₂ ∧ y₁ = (shortCurve A).toAffine.negY x₂ y₂
  · left; exact Point.add_of_Y_eq hxy.1 hxy.2
  right
  rw [Point.add_some hxy]
  refine ⟨_, _, _, rfl, ?_⟩
  rw [Affine.addX, shortCurve_a₁, shortCurve_a₂, zero_mul, add_zero, sub_zero]
  set ℓ := (shortCurve A).toAffine.slope x₁ x₂ y₁ y₂
  have hmul := slope_mul_add h₁.1 h₂.1 hxy
  have hsum : VGe π 1 (y₁ + y₂) := by
    rw [← res_eq_zero_iff hπ ρ hρ (hy₁.add hπ hy₂), res_add hπ ρ hρ hy₁ hy₂, hY, neg_add_cancel]
  have hN : VGe π 0 (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + A) :=
    (((hx₁.pow0 hπ 2).add hπ ((hx₁.mul hπ hx₂).mono (by simp))).add hπ (hx₂.pow0 hπ 2)).add hπ hA
  have hresN : res π ρ (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + A) = 3 * res π ρ x₁ ^ 2 + Ab := by
    rw [res_add hπ ρ hρ (((hx₁.pow0 hπ 2).add hπ ((hx₁.mul hπ hx₂).mono (by simp))).add hπ
      (hx₂.pow0 hπ 2)) hA, res_add hπ ρ hρ ((hx₁.pow0 hπ 2).add hπ ((hx₁.mul hπ hx₂).mono
      (by simp))) (hx₂.pow0 hπ 2), res_add hπ ρ hρ (hx₁.pow0 hπ 2) ((hx₁.mul hπ hx₂).mono
      (by simp)), res_mul hπ ρ hρ hx₁ hx₂, res_pow hπ ρ hρ hx₁, res_pow hπ ρ hρ hx₂, hAb, ← hX]
    ring
  obtain ⟨hℓ0, hvℓ⟩ : ℓ ≠ 0 ∧ vp π ℓ ≤ -1 := by
    by_cases hr : res π ρ (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + A) = 0
    · -- `3 X₁² + Ā = 0`, so `Y₁ ≠ 0` by nonsingularity of the reduced point
      rw [hresN] at hr
      have hns := (nonsingular_iff _ _).mp
        (equation_iff_nonsingular.mp (red_equation hπ ρ hρ hA hAb h₁.1 hx₁))
      simp only [shortCurve_a₁, shortCurve_a₂, shortCurve_a₃, shortCurve_a₄, zero_mul, mul_zero,
        add_zero, sub_zero] at hns
      have hY₁ : res π ρ y₁ ≠ 0 := by
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
        have : (2 : ZMod p) * res π ρ y₂ = 0 := by linear_combination hY
        exact (mul_eq_zero.mp this).resolve_left h2
      · have hsl : ℓ * (x₁ - x₂) = y₁ - y₂ := by
          simp only [ℓ]; rw [Affine.slope_of_X_ne hx, div_mul_cancel₀ _ (sub_ne_zero.mpr hx)]
        have hd : VGe π 1 (x₁ - x₂) := by
          rw [← res_eq_zero_iff hπ ρ hρ (hx₁.sub hπ hx₂), res_sub hπ ρ hρ hx₁ hx₂, hX, sub_self]
        have hres : res π ρ (y₁ - y₂) ≠ 0 := by
          rw [res_sub hπ ρ hρ hy₁ hy₂]
          intro h0; apply hY₁
          have : (2 : ZMod p) * res π ρ y₁ = 0 := by linear_combination h0 + hY
          exact (mul_eq_zero.mp this).resolve_left h2
        have hyy0 : y₁ - y₂ ≠ 0 := by intro h0; apply hres; rw [h0, res_zero hπ ρ hρ]
        have hvyy : vp π (y₁ - y₂) = 0 := by
          have := (res_eq_zero_iff hπ ρ hρ (hy₁.sub hπ hy₂)).not.mp hres
          rw [vge_iff hyy0] at this
          have h0 := (vge_iff hyy0).mp (hy₁.sub hπ hy₂)
          omega
        exact vp_le_neg_one_of_mul hπ hsl hyy0 hvyy hd
    · have hN0 : x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + A ≠ 0 := by
        intro h0; apply hr; rw [h0, res_zero hπ ρ hρ]
      have hvN : vp π (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + A) = 0 := by
        have := (res_eq_zero_iff hπ ρ hρ hN).not.mp hr
        rw [vge_iff hN0] at this
        have h0 := (vge_iff hN0).mp hN
        omega
      exact vp_le_neg_one_of_mul hπ hmul hN0 hvN hsum
  exact not_vge_addX hπ hA hℓ0 hvℓ hx₁ hx₂

include hπ hA hρ hAb in
/-- **Non-opposite reductions**: for integral `P₁, P₂` with `red P₁ ≠ -red P₂`, the sum is
integral and `red (P₁ + P₂) = red P₁ + red P₂`. -/
theorem red_add_of_not_opp {x₁ y₁ x₂ y₂ : K0} (h₁ : (shortCurve A).toAffine.Nonsingular x₁ y₁)
    (h₂ : (shortCurve A).toAffine.Nonsingular x₂ y₂) (hx₁ : VGe π 0 x₁) (hx₂ : VGe π 0 x₂)
    (hopp : ¬(res π ρ x₁ = res π ρ x₂ ∧ res π ρ y₁ = -res π ρ y₂)) :
    (∃ x₃ y₃ h₃, Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ = Point.some x₃ y₃ h₃ ∧
        VGe π 0 x₃) ∧
      red hπ ρ hρ hA hAb (.some x₁ y₁ h₁ + .some x₂ y₂ h₂) =
        red hπ ρ hρ hA hAb (.some x₁ y₁ h₁) + red hπ ρ hρ hA hAb (.some x₂ y₂ h₂) := by
  have hy₁ := vge_y_of_vge_x hπ hA ((shortCurve_equation_iff A x₁ y₁).mp h₁.1) hx₁
  have hy₂ := vge_y_of_vge_x hπ hA ((shortCurve_equation_iff A x₂ y₂).mp h₂.1) hx₂
  have h2 : (2 : ZMod p) ≠ 0 := Descent.two_ne_zero_of_isElliptic (b := Ab)
  have hopp' : ¬(res π ρ x₁ = res π ρ x₂ ∧
      res π ρ y₁ = (shortCurve Ab).toAffine.negY (res π ρ x₂) (res π ρ y₂)) := by
    rwa [shortCurve_negY]
  have hxy : ¬(x₁ = x₂ ∧ y₁ = (shortCurve A).toAffine.negY x₂ y₂) := by
    rintro ⟨rfl, h⟩
    rw [shortCurve_negY] at h
    exact hopp ⟨rfl, by rw [h, res_neg hπ ρ hρ hy₂]⟩
  -- the slope is integral and reduces to the slope over `𝔽_p`
  obtain ⟨hℓ, hres⟩ : VGe π 0 ((shortCurve A).toAffine.slope x₁ x₂ y₁ y₂) ∧
      res π ρ ((shortCurve A).toAffine.slope x₁ x₂ y₁ y₂) =
        (shortCurve Ab).toAffine.slope (res π ρ x₁) (res π ρ x₂) (res π ρ y₁) (res π ρ y₂) := by
    by_cases hX : res π ρ x₁ = res π ρ x₂
    · -- the reduced points coincide and are not two-torsion
      have hYY : res π ρ y₁ = res π ρ y₂ := by
        rcases Y_eq_of_X_eq (red_equation hπ ρ hρ hA hAb h₁.1 hx₁)
          (red_equation hπ ρ hρ hA hAb h₂.1 hx₂) hX with h | h
        · exact h
        · exact absurd ⟨hX, h⟩ hopp'
      have hY0 : res π ρ y₁ + res π ρ y₂ ≠ 0 := by
        intro h0; apply hopp; exact ⟨hX, by linear_combination h0⟩
      have hsum0 : y₁ + y₂ ≠ 0 := by
        intro h0; apply hY0; rw [← res_add hπ ρ hρ hy₁ hy₂, h0, res_zero hπ ρ hρ]
      have hvsum : vp π (y₁ + y₂) = 0 := by
        have := (res_eq_zero_iff hπ ρ hρ (hy₁.add hπ hy₂)).not.mp
          (by rw [res_add hπ ρ hρ hy₁ hy₂]; exact hY0)
        rw [vge_iff hsum0] at this
        have h0 := (vge_iff hsum0).mp (hy₁.add hπ hy₂)
        omega
      have hmul := slope_mul_add h₁.1 h₂.1 hxy
      have hℓeq : (shortCurve A).toAffine.slope x₁ x₂ y₁ y₂ =
          (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + A) / (y₁ + y₂) := by
        rw [eq_div_iff hsum0]; exact hmul
      have hN : VGe π 0 (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + A) :=
        (((hx₁.pow0 hπ 2).add hπ ((hx₁.mul hπ hx₂).mono (by simp))).add hπ
          (hx₂.pow0 hπ 2)).add hπ hA
      refine ⟨?_, ?_⟩
      · rw [hℓeq]; have := hN.div hπ hsum0; rwa [hvsum, sub_zero] at this
      · have hY' : res π ρ y₁ ≠ (shortCurve Ab).toAffine.negY (res π ρ x₁) (res π ρ y₁) := by
          rw [shortCurve_negY]; intro h0; apply hY0; rw [← hYY]; linear_combination h0
        rw [hℓeq, res_div hπ ρ hρ hN (hy₁.add hπ hy₂) hvsum hsum0, ← hX, ← hYY,
          Affine.slope_of_Y_ne rfl hY', res_add hπ ρ hρ (((hx₁.pow0 hπ 2).add hπ
            ((hx₁.mul hπ hx₂).mono (by simp))).add hπ (hx₂.pow0 hπ 2)) hA,
          res_add hπ ρ hρ ((hx₁.pow0 hπ 2).add hπ ((hx₁.mul hπ hx₂).mono (by simp)))
            (hx₂.pow0 hπ 2), res_add hπ ρ hρ (hx₁.pow0 hπ 2) ((hx₁.mul hπ hx₂).mono (by simp)),
          res_mul hπ ρ hρ hx₁ hx₂, res_pow hπ ρ hρ hx₁, res_pow hπ ρ hρ hx₂, hAb,
          res_add hπ ρ hρ hy₁ hy₂, ← hX, ← hYY]
        simp only [shortCurve_negY, shortCurve_a₁, shortCurve_a₂, shortCurve_a₄, zero_mul,
          mul_zero, add_zero, sub_zero]
        ring_nf
    · -- distinct reduced abscissas
      have hx : x₁ ≠ x₂ := by rintro rfl; exact hX rfl
      have hd0 : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
      have hvd : vp π (x₁ - x₂) = 0 := by
        have := (res_eq_zero_iff hπ ρ hρ (hx₁.sub hπ hx₂)).not.mp
          (by rw [res_sub hπ ρ hρ hx₁ hx₂]; exact sub_ne_zero.mpr hX)
        rw [vge_iff hd0] at this
        have h0 := (vge_iff hd0).mp (hx₁.sub hπ hx₂)
        omega
      rw [Affine.slope_of_X_ne hx, Affine.slope_of_X_ne hX]
      refine ⟨?_, ?_⟩
      · have := (hy₁.sub hπ hy₂).div hπ hd0; rwa [hvd, sub_zero] at this
      · rw [res_div hπ ρ hρ (hy₁.sub hπ hy₂) (hx₁.sub hπ hx₂) hvd hd0, res_sub hπ ρ hρ hy₁ hy₂,
          res_sub hπ ρ hρ hx₁ hx₂]
  refine ⟨⟨_, _, _, Point.add_some hxy, ?_⟩,
    red_add_of_slope hπ ρ hρ hA hAb h₁ h₂ hx₁ hx₂ hxy hℓ hopp' hres⟩
  rw [Affine.addX, shortCurve_a₁, shortCurve_a₂, zero_mul, add_zero, sub_zero]
  exact ((hℓ.pow0 hπ 2).sub hπ hx₁).sub hπ hx₂

include hπ hA in
omit [(shortCurve Ab).IsElliptic] [(shortCurve A).IsElliptic] in
/-- Formal-group bounds for a point of the kernel of reduction. -/
theorem kernel_bounds {x y : K0} (h : (shortCurve A).toAffine.Nonsingular x y)
    (hx : ¬VGe π 0 x) :
    ∃ n : ℤ, 1 ≤ n ∧ y ≠ 0 ∧ VGe π n (x / y) ∧ VGe π (3 * n) (1 / y) := by
  obtain ⟨n, hn, hx0, hy0, hvx, hvy⟩ :=
    level_of_not_vge hπ hA ((shortCurve_equation_iff A x y).mp h.1) hx
  refine ⟨n, hn, hy0, VGe.of_vp_eq (div_ne_zero hx0 hy0) ?_,
    VGe.of_vp_eq (one_div_ne_zero hy0) ?_⟩
  · rw [vp_div hπ hx0 hy0, hvx, hvy]; ring
  · rw [one_div, vp_inv hπ, hvy]; ring

include hπ hA in
omit [(shortCurve Ab).IsElliptic] [(shortCurve A).IsElliptic] in
theorem not_vge_of_bounds {x y : K0} (h : (shortCurve A).toAffine.Nonsingular x y) {m : ℤ}
    (hm : 1 ≤ m) (hy : y ≠ 0) (hw : VGe π (3 * m) (1 / y)) : ¬VGe π 0 x := by
  intro hx
  have hy' := vge_y_of_vge_x hπ hA ((shortCurve_equation_iff A x y).mp h.1) hx
  rw [vge_iff (one_div_ne_zero hy), one_div, vp_inv hπ] at hw
  rw [vge_iff hy] at hy'
  omega

include hπ hA in
omit [(shortCurve Ab).IsElliptic] in
/-- The kernel of reduction is closed under addition. -/
theorem kernel_add_kernel {x₁ y₁ x₂ y₂ : K0} (h₁ : (shortCurve A).toAffine.Nonsingular x₁ y₁)
    (h₂ : (shortCurve A).toAffine.Nonsingular x₂ y₂) (hx₁ : ¬VGe π 0 x₁) (hx₂ : ¬VGe π 0 x₂)
    (hne : Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ ≠ 0) :
    ∃ x₃ y₃ h₃, Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ = Point.some x₃ y₃ h₃ ∧
      ¬VGe π 0 x₃ := by
  obtain ⟨n₁, hn₁, hy₁, ht₁, hw₁⟩ := kernel_bounds hπ hA h₁ hx₁
  obtain ⟨n₂, hn₂, hy₂, ht₂, hw₂⟩ := kernel_bounds hπ hA h₂ hx₂
  set m := min n₁ n₂
  have hm : 1 ≤ m := le_min hn₁ hn₂
  obtain ⟨x₃, y₃, h₃, hs, hy₃, -, hw₃, -⟩ := kernel_add hπ hA hm h₁ h₂ hy₁ hy₂
    (ht₁.mono (min_le_left _ _)) (ht₂.mono (min_le_right _ _))
    (hw₁.mono (by omega)) (hw₂.mono (by omega)) hne
  exact ⟨x₃, y₃, h₃, hs, not_vge_of_bounds hπ hA h₃ hm hy₃ hw₃⟩

include hπ hA hρ hAb in
/-- Reduction is constant on cosets of the kernel: if `P₁` is in the kernel and `P₂` is
integral, then `P₁ + P₂` is integral with the same reduction as `P₂`. -/
theorem red_add_kernel {x₁ y₁ x₂ y₂ : K0} (h₁ : (shortCurve A).toAffine.Nonsingular x₁ y₁)
    (h₂ : (shortCurve A).toAffine.Nonsingular x₂ y₂) (hx₁ : ¬VGe π 0 x₁) (hx₂ : VGe π 0 x₂) :
    red hπ ρ hρ hA hAb (.some x₁ y₁ h₁ + .some x₂ y₂ h₂) = red hπ ρ hρ hA hAb (.some x₂ y₂ h₂) := by
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
    have hne : Point.some x₃ y₃ h₃ + Point.some x₁ _ ((nonsingular_neg ..).mpr h₁) ≠ 0 := by
      rw [← hP₂]; exact Point.some_ne_zero _
    obtain ⟨x', y', h', hs', hx'⟩ := kernel_add_kernel hπ hA h₃ _ hx₃ hx₁ hne
    rw [← hP₂, Point.some.injEq] at hs'
    exact hx' (hs'.1 ▸ hx₂)
  rw [hs]
  -- the reductions agree
  by_contra hne
  have hy₂ := vge_y_of_vge_x hπ hA ((shortCurve_equation_iff A x₂ y₂).mp h₂.1) hx₂
  have hopp : ¬(res π ρ x₃ = res π ρ x₂ ∧
      res π ρ y₃ = -res π ρ ((shortCurve A).toAffine.negY x₂ y₂)) := by
    rintro ⟨hX, hY⟩
    apply hne
    rw [red_some_of_vge hπ ρ hρ hA hAb _ hx₃, red_some_of_vge hπ ρ hρ hA hAb _ hx₂, Point.mk,
      Point.mk, Point.some.injEq]
    refine ⟨hX, ?_⟩
    rw [hY, shortCurve_negY, res_neg hπ ρ hρ hy₂, neg_neg]
  obtain ⟨⟨x', y', h', hs', hx'⟩, -⟩ := red_add_of_not_opp hπ ρ hρ hA hAb h₃
    ((nonsingular_neg ..).mpr h₂) hx₃ hx₂ hopp
  rw [← hP₁, Point.some.injEq] at hs'
  exact hx₁ (hs'.1 ▸ hx')

include hπ hA hρ hAb in
/-- **Reduction is a group homomorphism.** -/
theorem red_add (P Q : (shortCurve A).toAffine.Point) :
    red hπ ρ hρ hA hAb (P + Q) = red hπ ρ hρ hA hAb P + red hπ ρ hρ hA hAb Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · show red hπ ρ hρ hA hAb (0 + Q) = red hπ ρ hρ hA hAb 0 + _
    rw [zero_add, red_zero, zero_add]
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · show red hπ ρ hρ hA hAb (_ + 0) = _ + red hπ ρ hρ hA hAb 0
    rw [add_zero, red_zero, add_zero]
  by_cases hx₁ : VGe π 0 x₁ <;> by_cases hx₂ : VGe π 0 x₂
  · by_cases hopp : res π ρ x₁ = res π ρ x₂ ∧ res π ρ y₁ = -res π ρ y₂
    · have hrhs : red hπ ρ hρ hA hAb (.some x₁ y₁ h₁) + red hπ ρ hρ hA hAb (.some x₂ y₂ h₂) = 0 := by
        rw [red_some_of_vge hπ ρ hρ hA hAb _ hx₁, red_some_of_vge hπ ρ hρ hA hAb _ hx₂, Point.mk,
          Point.mk]
        exact Point.add_of_Y_eq hopp.1 (by rw [shortCurve_negY]; exact hopp.2)
      rw [hrhs]
      rcases add_of_red_opp hπ ρ hρ hA hAb h₁ h₂ hx₁ hx₂ hopp.1 hopp.2 with h0 | ⟨x₃, y₃, h₃, hs, hx₃⟩
      · rw [h0, red_zero]
      · rw [hs, red_some_of_not_vge hπ ρ hρ hA hAb _ hx₃]
    · exact (red_add_of_not_opp hπ ρ hρ hA hAb h₁ h₂ hx₁ hx₂ hopp).2
  · rw [add_comm, red_add_kernel hπ ρ hρ hA hAb h₂ h₁ hx₂ hx₁,
      red_some_of_not_vge hπ ρ hρ hA hAb _ hx₂, add_zero]
  · rw [red_add_kernel hπ ρ hρ hA hAb h₁ h₂ hx₁ hx₂, red_some_of_not_vge hπ ρ hρ hA hAb _ hx₁,
      zero_add]
  · rw [red_some_of_not_vge hπ ρ hρ hA hAb _ hx₁, red_some_of_not_vge hπ ρ hρ hA hAb _ hx₂,
      add_zero]
    by_cases hne : Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ = 0
    · rw [hne, red_zero]
    · obtain ⟨x₃, y₃, h₃, hs, hx₃⟩ := kernel_add_kernel hπ hA h₁ h₂ hx₁ hx₂ hne
      rw [hs, red_some_of_not_vge hπ ρ hρ hA hAb _ hx₃]

/-- The reduction homomorphism `W(K₀) →+ W̃(𝔽_p)`. -/
noncomputable def redHom : (shortCurve A).toAffine.Point →+ (shortCurve Ab).toAffine.Point where
  toFun := red hπ ρ hρ hA hAb
  map_zero' := rfl
  map_add' := red_add hπ ρ hρ hA hAb

@[simp] theorem redHom_apply (P : (shortCurve A).toAffine.Point) :
    redHom hπ ρ hρ hA hAb P = red hπ ρ hρ hA hAb P := rfl

include hπ hA hρ hAb in
/-- **Reduction is injective on prime-to-`p` torsion**: a point of finite order prime to `p`
(here: `n • T = 0` with `π ∤ n`) whose reduction is `O` is `O`. -/
theorem eq_zero_of_red_eq_zero {T : (shortCurve A).toAffine.Point} {n : ℕ}
    (hn : ¬π ∣ (n : Zs)) (hT : n • T = 0) (hred : red hπ ρ hρ hA hAb T = 0) : T = 0 := by
  rcases T with _ | ⟨x, y, h⟩
  · rfl
  by_cases hx : VGe π 0 x
  · rw [red_some_of_vge hπ ρ hρ hA hAb _ hx] at hred
    exact absurd hred (Point.some_ne_zero _)
  · exact absurd hT (nsmul_ne_zero_of_not_vge hπ hA h hx hn)

include hρ in
omit [(shortCurve Ab).IsElliptic] [(shortCurve A).IsElliptic] in
theorem dvd_natCast_iff (n : ℕ) : π ∣ (n : Zs) ↔ p ∣ n := by
  rw [← hρ, map_natCast, ZMod.natCast_eq_zero_iff]

include hπ hA hρ hAb in
/-- If `T` has order `n` prime to `p`, then `red T` has order `n`; hence `n ∣ #W̃(𝔽_p)`. -/
theorem addOrderOf_red {T : (shortCurve A).toAffine.Point} (hT : IsOfFinAddOrder T)
    (hp : ¬p ∣ addOrderOf T) : addOrderOf (red hπ ρ hρ hA hAb T) = addOrderOf T := by
  have key : ∀ k : ℕ, k • red hπ ρ hρ hA hAb T = 0 ↔ k • T = 0 := by
    intro k
    rw [← redHom_apply, ← map_nsmul, redHom_apply]
    constructor
    · intro h
      -- `k • T` has order dividing `addOrderOf T`, prime to `p`
      have hk : addOrderOf T • (k • T) = 0 := by
        rw [smul_comm, addOrderOf_nsmul_eq_zero, smul_zero]
      exact eq_zero_of_red_eq_zero hπ ρ hρ hA hAb (by rwa [dvd_natCast_iff ρ hρ]) hk h
    · intro h; rw [h, red_zero]
  exact addOrderOf_eq_addOrderOf_iff.mpr key

include hπ hA hρ hAb in
/-- Reduction is injective on every finite subgroup of order prime to `p`. -/
theorem red_injOn_of_coprime (H : AddSubgroup (shortCurve A).toAffine.Point) [Finite H]
    (hH : ¬p ∣ Nat.card H) : Set.InjOn (red hπ ρ hρ hA hAb) H := by
  intro P hP Q hQ hPQ
  have hsub : P - Q ∈ H := H.sub_mem hP hQ
  have hcard : Nat.card H • (P - Q) = 0 := by
    have := card_nsmul_eq_zero' (G := H) (x := ⟨P - Q, hsub⟩)
    exact congrArg Subtype.val this
  have hred : red hπ ρ hρ hA hAb (P - Q) = 0 := by
    rw [← redHom_apply, map_sub, redHom_apply, redHom_apply, hPQ, sub_self]
  exact sub_eq_zero.mp (eq_zero_of_red_eq_zero hπ ρ hρ hA hAb
    (by rwa [dvd_natCast_iff ρ hρ]) hcard hred)

include hπ hA hρ hAb in
/-- The order of a finite subgroup of order prime to `p` divides `#W̃(𝔽_p)`. -/
theorem card_dvd_of_coprime (H : AddSubgroup (shortCurve A).toAffine.Point) [Finite H]
    (hH : ¬p ∣ Nat.card H) [Finite (shortCurve Ab).toAffine.Point] :
    Nat.card H ∣ Nat.card (shortCurve Ab).toAffine.Point := by
  have hinj := red_injOn_of_coprime hπ ρ hρ hA hAb H hH
  have : Nat.card (H.map (redHom hπ ρ hρ hA hAb)) = Nat.card H := by
    change Nat.card ((H.map (redHom hπ ρ hρ hA hAb) : Set (shortCurve Ab).toAffine.Point)) =
      Nat.card ((H : Set (shortCurve A).toAffine.Point))
    rw [AddSubgroup.coe_map]
    exact Nat.card_image_of_injOn (f := redHom hπ ρ hρ hA hAb) hinj
  rw [← this]
  exact AddSubgroup.card_addSubgroup_dvd_card _

end ZInQ
