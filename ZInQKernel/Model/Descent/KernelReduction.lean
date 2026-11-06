import ZInQKernel.Model.Descent.Residue
import ZInQKernel.Model.Descent.Kummer

/-!
# The kernel of reduction has no torsion prime to `p`

Part of `model/descent/reduction-torsion.md` (part 2).

Let `π` be a prime of `ℤ[s]` and `W : y² = x³ + A x` over `K₀` with `A` integral at `π`. For a
point `(x, y)` with `v_π(x) < 0` put `t = x / y`, `w = 1 / y` (the formal-group parameters);
then `v_π(x) = -2n`, `v_π(t) = n`, `v_π(w) = 3n` with `n ≥ 1`, and `w = t³ + A t w²`.

*Addition estimate* (`kernel_add`): if `v(tᵢ) ≥ m ≥ 1` and `v(wᵢ) ≥ 3m` for `P₁, P₂` and
`P₁ + P₂ ≠ O`, then the same holds for `P₁ + P₂` and `v(t(P₁ + P₂) - t₁ - t₂) ≥ m + 1`. The line
through `P₁, P₂` is `λ x + ν y = 1` with `v(λ) ≥ 2m`, `v(ν) ≥ 3m`; Vieta's relations for the
three abscissas give `t₁ + t₂ - t(P₁ + P₂) = -2Aλν / (1 + Aλ²)`.

*Consequence* (`nsmul_ne_zero_of_not_vge`): `t(kP) ≡ k t(P) (mod π^{n+1})` for all `k ≥ 1`, so
`q P ≠ O` whenever `π ∤ q`.
-/

namespace ZInQ

open WeierstrassCurve WeierstrassCurve.Affine Polynomial

/-! ### Algebra of the chord -/

section Algebra

variable {K : Type*} [Field K] [DecidableEq K]

/-- Vieta's relations for the abscissas `x₁, x₂, x₃` of the three points on the line through
`(x₁, y₁)`, `(x₂, y₂)` on `y² = x³ + A x`, with `c = y₁ - ℓ x₁`. -/
theorem vieta_shortCurve {A x₁ x₂ y₁ y₂ : K} (h₁ : (shortCurve A).toAffine.Equation x₁ y₁)
    (h₂ : (shortCurve A).toAffine.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (shortCurve A).toAffine.negY x₂ y₂)) {ℓ : K}
    (hℓ : (shortCurve A).toAffine.slope x₁ x₂ y₁ y₂ = ℓ) :
    x₁ * x₂ + x₁ * (ℓ ^ 2 - x₁ - x₂) + x₂ * (ℓ ^ 2 - x₁ - x₂) = A - 2 * ℓ * (y₁ - ℓ * x₁) ∧
      x₁ * x₂ * (ℓ ^ 2 - x₁ - x₂) = (y₁ - ℓ * x₁) ^ 2 := by
  have h := addPolynomial_slope h₁ h₂ hxy
  rw [addPolynomial_eq, neg_inj, Cubic.prod_X_sub_C_eq, Cubic.toPoly_injective, hℓ] at h
  simp only [Cubic.mk.injEq] at h
  obtain ⟨-, -, hc, hd⟩ := h
  simp only [shortCurve_a₁, shortCurve_a₂, shortCurve_a₃, shortCurve_a₄, shortCurve_a₆,
    Affine.addX, zero_mul, add_zero, sub_zero, neg_zero, zero_sub] at hc hd
  constructor
  · linear_combination -hc
  · linear_combination hd

/-- The `t`-coordinate identity: with `yᵢ = ℓ xᵢ + c` (`i = 1, 2`), `-y₃ = ℓ x₃ + c` and
Vieta's relations, `x₁/y₁ + x₂/y₂ - x₃/y₃ = 2Aℓ / (Aℓ² + c²)`. -/
theorem sum_t_identity {A x₁ x₂ x₃ y₁ y₂ y₃ ℓ c : K} (V1 : x₁ + x₂ + x₃ = ℓ ^ 2)
    (V2 : x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = A - 2 * ℓ * c) (V3 : x₁ * x₂ * x₃ = c ^ 2)
    (hy₁ : y₁ = ℓ * x₁ + c) (hy₂ : y₂ = ℓ * x₂ + c) (hy₃ : -y₃ = ℓ * x₃ + c)
    (h₁ : y₁ ≠ 0) (h₂ : y₂ ≠ 0) (h₃ : y₃ ≠ 0) (hD : A * ℓ ^ 2 + c ^ 2 ≠ 0) :
    x₁ / y₁ + x₂ / y₂ - x₃ / y₃ = 2 * A * ℓ / (A * ℓ ^ 2 + c ^ 2) := by
  have h₃' : -y₃ ≠ 0 := neg_ne_zero.mpr h₃
  rw [show x₁ / y₁ + x₂ / y₂ - x₃ / y₃ = x₁ / y₁ + x₂ / y₂ + x₃ / -y₃ by rw [div_neg]; ring]
  rw [div_add_div _ _ h₁ h₂, div_add_div _ _ (mul_ne_zero h₁ h₂) h₃',
    div_eq_div_iff (mul_ne_zero (mul_ne_zero h₁ h₂) h₃') hD, hy₁, hy₂, hy₃]
  linear_combination (c ^ 4 - A * ℓ ^ 2 * c ^ 2) * V1 + (2 * ℓ * c ^ 3) * V2 +
    (A * ℓ ^ 4 + 3 * ℓ ^ 2 * c ^ 2) * V3

/-- The formal-group equation `w = t³ + A t w²` for `t = x / y`, `w = 1 / y`. -/
theorem tw_equation {A x y : K} (hy : y ≠ 0) (h : y ^ 2 = x ^ 3 + A * x) :
    1 / y = (x / y) ^ 3 + A * (x / y) * (1 / y) ^ 2 := by
  have e : (x / y) ^ 3 + A * (x / y) * (1 / y) ^ 2 = (x ^ 3 + A * x) / y ^ 3 := by
    field_simp
  rw [e, ← h]
  field_simp

end Algebra

/-! ### Valuation estimates -/

section Valuation

variable {π : Zs} (hπ : Prime π) {A : K0} (hA : VGe π 0 A)
include hπ hA

/-- The slope `λ` of the chord in the `(t, w)`-plane has `v(λ) ≥ 2m`. -/
theorem vge_chord_slope {m : ℤ} (hm : 1 ≤ m) {t₁ t₂ w₁ w₂ : K0}
    (e₁ : w₁ = t₁ ^ 3 + A * t₁ * w₁ ^ 2) (e₂ : w₂ = t₂ ^ 3 + A * t₂ * w₂ ^ 2) (ht : t₁ ≠ t₂)
    (ht₁ : VGe π m t₁) (ht₂ : VGe π m t₂) (hw₁ : VGe π (3 * m) w₁) (hw₂ : VGe π (3 * m) w₂) :
    VGe π (2 * m) ((w₂ - w₁) / (t₂ - t₁)) := by
  have hD1 : VGe π 1 (-(A * t₁ * (w₁ + w₂))) :=
    (((hA.mul hπ ht₁).mul hπ (hw₁.add hπ hw₂)).mono (by omega)).neg hπ
  have hDv : vp π (1 + -(A * t₁ * (w₁ + w₂))) = 0 := vp_one_add hπ hD1
  have hD0 : 1 + -(A * t₁ * (w₁ + w₂)) ≠ 0 := one_add_ne_zero hπ hD1
  have key : (w₂ - w₁) / (t₂ - t₁) =
      (t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2 + A * w₂ ^ 2) / (1 + -(A * t₁ * (w₁ + w₂))) := by
    rw [div_eq_div_iff (sub_ne_zero.mpr ht.symm) hD0]
    linear_combination e₂ - e₁
  rw [key]
  have hN : VGe π (2 * m) (t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2 + A * w₂ ^ 2) := by
    refine (((ht₁.pow hπ 2).mono (by push_cast; omega)).add hπ
      ((ht₁.mul hπ ht₂).mono (by omega))).add hπ ((ht₂.pow hπ 2).mono (by push_cast; omega))
      |>.add hπ ?_
    exact (hA.mul hπ (hw₂.pow hπ 2)).mono (by push_cast; omega)
  have := hN.div hπ hD0
  rwa [hDv, sub_zero] at this

/-- The slope `λ` of the tangent in the `(t, w)`-plane has `v(λ) ≥ 2m`. -/
theorem vge_tangent_slope {m : ℤ} (hm : 1 ≤ m) {t w : K0} (ht : VGe π m t)
    (hw : VGe π (3 * m) w) :
    vp π (1 + -(2 * A * t * w)) = 0 ∧ 1 + -(2 * A * t * w) ≠ 0 ∧
      VGe π (2 * m) ((3 * t ^ 2 + A * w ^ 2) / (1 + -(2 * A * t * w))) := by
  have hD1 : VGe π 1 (-(2 * A * t * w)) :=
    ((((vge_ofNat hπ 2).mul hπ hA).mul hπ ht).mul hπ hw |>.mono (by omega)).neg hπ
  have hDv := vp_one_add hπ hD1
  have hD0 := one_add_ne_zero hπ hD1
  refine ⟨hDv, hD0, ?_⟩
  have hN : VGe π (2 * m) (3 * t ^ 2 + A * w ^ 2) :=
    (((vge_ofNat hπ 3).mul hπ (ht.pow hπ 2)).mono (by push_cast; omega)).add hπ
      ((hA.mul hπ (hw.pow hπ 2)).mono (by push_cast; omega))
  have := hN.div hπ hD0
  rwa [hDv, sub_zero] at this

/-- In the kernel of reduction, distinct abscissas have distinct `t = x / y`. -/
theorem t_ne_of_x_ne {m : ℤ} (hm : 1 ≤ m) {x₁ y₁ x₂ y₂ : K0} (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0)
    (e₁ : y₁ ^ 2 = x₁ ^ 3 + A * x₁) (e₂ : y₂ ^ 2 = x₂ ^ 3 + A * x₂)
    (ht₁ : VGe π m (x₁ / y₁)) (hw₁ : VGe π (3 * m) (1 / y₁)) (hw₂ : VGe π (3 * m) (1 / y₂))
    (hx : x₁ ≠ x₂) : x₁ / y₁ ≠ x₂ / y₂ := by
  intro ht
  have f₁ := tw_equation hy₁ e₁
  have f₂ := tw_equation hy₂ e₂
  rw [← ht] at f₂
  have hD1 : VGe π 1 (-(A * (x₁ / y₁) * (1 / y₁ + 1 / y₂))) :=
    (((hA.mul hπ ht₁).mul hπ (hw₁.add hπ hw₂)).mono (by omega)).neg hπ
  have hD0 := one_add_ne_zero hπ hD1
  have hprod : (1 / y₁ - 1 / y₂) * (1 + -(A * (x₁ / y₁) * (1 / y₁ + 1 / y₂))) = 0 := by
    linear_combination f₁ - f₂
  have hw : 1 / y₁ = 1 / y₂ := sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hD0)
  have hy : y₁ = y₂ := by
    have := congrArg (fun z => 1 / z) hw; simpa using this
  apply hx
  rw [← hy] at ht
  have := congrArg (· * y₁) ht
  simpa [div_mul_cancel₀ _ hy₁] using this

/-- The tangent at a point of the kernel of reduction is `λ x + ν y = 1` with `v(λ) ≥ 2m`,
`v(ν) ≥ 3m`. -/
theorem kernel_tangent_line {m : ℤ} (hm : 1 ≤ m) {x y : K0} (hy : y ≠ 0)
    (e : y ^ 2 = x ^ 3 + A * x) (ht : VGe π m (x / y)) (hw : VGe π (3 * m) (1 / y)) :
    ∃ lam ν : K0, VGe π (2 * m) lam ∧ VGe π (3 * m) ν ∧ ν ≠ 0 ∧
      (3 * x ^ 2 + A) / (y - -y) = -lam / ν ∧ y = (3 * x ^ 2 + A) / (y - -y) * x + 1 / ν := by
  have h2 : (2 : K0) ≠ 0 := two_ne_zero
  obtain ⟨hDv, hD0, hlam⟩ := vge_tangent_slope hπ hA hm ht hw
  have hD : (1 : K0) + -(2 * A * (x / y) * (1 / y)) = (y ^ 2 - 2 * A * x) / y ^ 2 := by
    field_simp; ring
  rw [hD] at hD0 hlam
  have hD0' : y ^ 2 - 2 * A * x ≠ 0 := by
    intro h0; apply hD0; rw [h0, zero_div]
  have hlam' : (3 * (x / y) ^ 2 + A * (1 / y) ^ 2) / ((y ^ 2 - 2 * A * x) / y ^ 2) =
      (3 * x ^ 2 + A) / (y ^ 2 - 2 * A * x) := by
    field_simp
  rw [hlam'] at hlam
  have hν : 1 / y - (3 * x ^ 2 + A) / (y ^ 2 - 2 * A * x) * (x / y) =
      -2 * y / (y ^ 2 - 2 * A * x) := by
    rw [div_mul_div_comm, div_sub_div _ _ hy (mul_ne_zero hD0' hy), div_eq_div_iff
      (mul_ne_zero hy (mul_ne_zero hD0' hy)) hD0']
    linear_combination (3 * y * (y ^ 2 - 2 * A * x)) * e
  have hνvge : VGe π (3 * m) (-2 * y / (y ^ 2 - 2 * A * x)) := by
    rw [← hν]; exact hw.sub hπ ((hlam.mul hπ ht).mono (by omega))
  have hyy : y - -y = 2 * y := by ring
  rw [hyy]
  generalize hDdef : y ^ 2 - 2 * A * x = D at hD0' hlam hνvge
  have hν0 : -2 * y / D ≠ 0 := div_ne_zero (mul_ne_zero (neg_ne_zero.mpr h2) hy) hD0'
  refine ⟨(3 * x ^ 2 + A) / D, -2 * y / D, hlam, hνvge, hν0, ?_, ?_⟩
  · field_simp
  · field_simp
    linear_combination 3 * e - hDdef

/-- The chord through two points of the kernel of reduction with distinct abscissas is
`λ x + ν y = 1` with `v(λ) ≥ 2m`, `v(ν) ≥ 3m`. -/
theorem kernel_chord_line {m : ℤ} (hm : 1 ≤ m) {x₁ y₁ x₂ y₂ : K0} (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0)
    (e₁ : y₁ ^ 2 = x₁ ^ 3 + A * x₁) (e₂ : y₂ ^ 2 = x₂ ^ 3 + A * x₂)
    (ht₁ : VGe π m (x₁ / y₁)) (ht₂ : VGe π m (x₂ / y₂))
    (hw₁ : VGe π (3 * m) (1 / y₁)) (hw₂ : VGe π (3 * m) (1 / y₂)) (hx : x₁ ≠ x₂) :
    ∃ lam ν : K0, VGe π (2 * m) lam ∧ VGe π (3 * m) ν ∧ ν ≠ 0 ∧
      (y₁ - y₂) / (x₁ - x₂) = -lam / ν ∧ y₁ = (y₁ - y₂) / (x₁ - x₂) * x₁ + 1 / ν ∧
      y₂ = (y₁ - y₂) / (x₁ - x₂) * x₂ + 1 / ν := by
  have ht : x₁ / y₁ ≠ x₂ / y₂ := t_ne_of_x_ne hπ hA hm hy₁ hy₂ e₁ e₂ ht₁ hw₁ hw₂ hx
  have hlam := vge_chord_slope hπ hA hm (tw_equation hy₁ e₁) (tw_equation hy₂ e₂) ht ht₁ ht₂
    hw₁ hw₂
  have hdet : x₁ * y₂ - x₂ * y₁ ≠ 0 := by
    intro h0; apply ht
    rw [div_eq_div_iff hy₁ hy₂]; linear_combination h0
  have hdet' : x₂ * y₁ - y₂ * x₁ ≠ 0 := by
    intro h0; apply hdet; linear_combination -h0
  have hlam' : (1 / y₂ - 1 / y₁) / (x₂ / y₂ - x₁ / y₁) = (y₂ - y₁) / (x₁ * y₂ - x₂ * y₁) := by
    rw [div_sub_div _ _ hy₂ hy₁, div_sub_div _ _ hy₂ hy₁, div_div_div_cancel_right₀
      (mul_ne_zero hy₂ hy₁), div_eq_div_iff hdet' hdet]
    ring
  rw [hlam'] at hlam
  have hν : 1 / y₁ - (y₂ - y₁) / (x₁ * y₂ - x₂ * y₁) * (x₁ / y₁) =
      (x₁ - x₂) / (x₁ * y₂ - x₂ * y₁) := by
    rw [div_mul_div_comm, div_sub_div _ _ hy₁ (mul_ne_zero hdet hy₁), div_eq_div_iff
      (mul_ne_zero hy₁ (mul_ne_zero hdet hy₁)) hdet]
    ring
  have hνvge : VGe π (3 * m) ((x₁ - x₂) / (x₁ * y₂ - x₂ * y₁)) := by
    rw [← hν]; exact hw₁.sub hπ ((hlam.mul hπ ht₁).mono (by omega))
  have hx0 : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  generalize hDdef : x₁ * y₂ - x₂ * y₁ = D at hdet hlam hνvge
  have hν0 : (x₁ - x₂) / D ≠ 0 := div_ne_zero hx0 hdet
  refine ⟨(y₂ - y₁) / D, (x₁ - x₂) / D, hlam, hνvge, hν0, ?_, ?_, ?_⟩
  · field_simp
    ring
  · field_simp
    linear_combination hDdef
  · field_simp
    linear_combination hDdef

variable [(shortCurve A).IsElliptic]

/-- The third point of the line `λ x + ν y = 1` through two points of the kernel. -/
theorem kernel_third_point {m : ℤ} (hm : 1 ≤ m) {x₁ y₁ x₂ y₂ ℓ lam ν : K0}
    (h₁ : (shortCurve A).toAffine.Equation x₁ y₁) (h₂ : (shortCurve A).toAffine.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (shortCurve A).toAffine.negY x₂ y₂))
    (hℓ : (shortCurve A).toAffine.slope x₁ x₂ y₁ y₂ = ℓ) (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0)
    (ht₁ : VGe π m (x₁ / y₁)) (ht₂ : VGe π m (x₂ / y₂))
    (hlam : VGe π (2 * m) lam) (hν : VGe π (3 * m) ν) (hν0 : ν ≠ 0) (hℓν : ℓ = -lam / ν)
    (hc₁ : y₁ = ℓ * x₁ + 1 / ν) (hc₂ : y₂ = ℓ * x₂ + 1 / ν)
    (e₃ : (-(ℓ * (ℓ ^ 2 - x₁ - x₂) + 1 / ν)) ^ 2 =
      (ℓ ^ 2 - x₁ - x₂) ^ 3 + A * (ℓ ^ 2 - x₁ - x₂)) :
    -(ℓ * (ℓ ^ 2 - x₁ - x₂) + 1 / ν) ≠ 0 ∧
      VGe π m ((ℓ ^ 2 - x₁ - x₂) / -(ℓ * (ℓ ^ 2 - x₁ - x₂) + 1 / ν)) ∧
      VGe π (3 * m) (1 / -(ℓ * (ℓ ^ 2 - x₁ - x₂) + 1 / ν)) ∧
      VGe π (m + 1) ((ℓ ^ 2 - x₁ - x₂) / -(ℓ * (ℓ ^ 2 - x₁ - x₂) + 1 / ν) - x₁ / y₁ - x₂ / y₂) := by
  have hV := vieta_shortCurve h₁ h₂ hxy hℓ
  have hc : y₁ - ℓ * x₁ = 1 / ν := by rw [hc₁]; ring
  rw [hc] at hV
  obtain ⟨V2, V3⟩ := hV
  generalize hx₃ : ℓ ^ 2 - x₁ - x₂ = x₃ at V2 V3 e₃ ⊢
  generalize hy₃ : -(ℓ * x₃ + 1 / ν) = y₃ at e₃ ⊢
  have hline : lam * x₃ - ν * y₃ = 1 := by
    rw [← hy₃, hℓν]; field_simp; ring
  -- `y₃ ≠ 0`
  have hy₃0 : y₃ ≠ 0 := by
    intro h0
    rw [h0, mul_zero, sub_zero] at hline
    have hl0 : lam ≠ 0 := by rintro rfl; rw [zero_mul] at hline; exact zero_ne_one hline
    have hx₃0 : x₃ ≠ 0 := by rintro h; rw [h, mul_zero] at hline; exact zero_ne_one hline
    rw [h0] at e₃
    have hsq : x₃ ^ 2 = -A := by
      have : x₃ * (x₃ ^ 2 + A) = 0 := by linear_combination -e₃
      linear_combination (mul_eq_zero.mp this).resolve_left hx₃0
    have hv : vp π x₃ = -vp π lam := by
      have : x₃ = 1 / lam := by rw [eq_div_iff hl0]; linear_combination hline
      rw [this, one_div, vp_inv hπ]
    have hvl : 2 * m ≤ vp π lam := (vge_iff hl0).mp hlam
    have hA' : VGe π 0 (x₃ ^ 2) := by rw [hsq]; exact hA.neg hπ
    rw [vge_iff (pow_ne_zero 2 hx₃0), vp_pow hπ, hv] at hA'
    push_cast at hA'
    omega
  -- the `t`-identity
  have hAl : VGe π 1 (A * lam ^ 2) := (hA.mul hπ (hlam.pow hπ 2)).mono (by push_cast; omega)
  have hD0 : 1 + A * lam ^ 2 ≠ 0 := one_add_ne_zero hπ hAl
  have hDv : vp π (1 + A * lam ^ 2) = 0 := vp_one_add hπ hAl
  have hD' : A * ℓ ^ 2 + (1 / ν) ^ 2 ≠ 0 := by
    rw [hℓν]
    intro h0
    apply hD0
    have : A * (-lam / ν) ^ 2 + (1 / ν) ^ 2 = (1 + A * lam ^ 2) / ν ^ 2 := by
      field_simp; ring
    rw [this] at h0
    exact (div_eq_zero_iff.mp h0).resolve_right (pow_ne_zero 2 hν0)
  have hid := sum_t_identity (A := A) (x₁ := x₁) (x₂ := x₂) (x₃ := x₃) (y₃ := y₃)
    (by rw [← hx₃]; ring) V2 V3 hc₁ hc₂ (by rw [← hy₃, neg_neg]) hy₁ hy₂ hy₃0 hD'
  have hdiff : x₃ / y₃ - x₁ / y₁ - x₂ / y₂ = 2 * A * lam * ν / (1 + A * lam ^ 2) := by
    have : x₃ / y₃ - x₁ / y₁ - x₂ / y₂ = -(2 * A * ℓ / (A * ℓ ^ 2 + (1 / ν) ^ 2)) := by
      rw [← hid]; ring
    have key : A * (-lam / ν) ^ 2 + (1 / ν) ^ 2 = (1 + A * lam ^ 2) / ν ^ 2 := by
      field_simp; ring
    rw [this, hℓν, key, div_div_eq_mul_div, neg_div', div_left_inj' hD0]
    field_simp
  have hE : VGe π (m + 1) (x₃ / y₃ - x₁ / y₁ - x₂ / y₂) := by
    rw [hdiff]
    have hN : VGe π (5 * m) (2 * A * lam * ν) :=
      ((((vge_ofNat hπ 2).mul hπ hA).mul hπ hlam).mul hπ hν).mono (by omega)
    have := hN.div hπ hD0
    rw [hDv, sub_zero] at this
    exact this.mono (by omega)
  have ht₃ : VGe π m (x₃ / y₃) := by
    have : x₃ / y₃ = (x₃ / y₃ - x₁ / y₁ - x₂ / y₂) + x₁ / y₁ + x₂ / y₂ := by ring
    rw [this]
    exact ((hE.mono (by omega)).add hπ ht₁).add hπ ht₂
  refine ⟨hy₃0, ht₃, ?_, hE⟩
  have : 1 / y₃ = lam * (x₃ / y₃) - ν := by
    field_simp; linear_combination -hline
  rw [this]
  exact ((hlam.mul hπ ht₃).mono (by omega)).sub hπ hν

end Valuation

end ZInQ
