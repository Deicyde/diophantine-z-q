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

/-- **The addition estimate** in the kernel of reduction. If `v(x/y) ≥ m ≥ 1` and
`v(1/y) ≥ 3m` for two points whose sum is not `O`, then the sum has the same bounds and
`v(t(P₁ + P₂) - t(P₁) - t(P₂)) ≥ m + 1`. -/
theorem kernel_add {m : ℤ} (hm : 1 ≤ m) {x₁ y₁ x₂ y₂ : K0}
    (h₁ : (shortCurve A).toAffine.Nonsingular x₁ y₁)
    (h₂ : (shortCurve A).toAffine.Nonsingular x₂ y₂) (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0)
    (ht₁ : VGe π m (x₁ / y₁)) (ht₂ : VGe π m (x₂ / y₂))
    (hw₁ : VGe π (3 * m) (1 / y₁)) (hw₂ : VGe π (3 * m) (1 / y₂))
    (hne : Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ ≠ 0) :
    ∃ x₃ y₃ h₃, Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ = Point.some x₃ y₃ h₃ ∧ y₃ ≠ 0 ∧
      VGe π m (x₃ / y₃) ∧ VGe π (3 * m) (1 / y₃) ∧
      VGe π (m + 1) (x₃ / y₃ - x₁ / y₁ - x₂ / y₂) := by
  have e₁ := (shortCurve_equation_iff A x₁ y₁).mp h₁.1
  have e₂ := (shortCurve_equation_iff A x₂ y₂).mp h₂.1
  have hxy : ¬(x₁ = x₂ ∧ y₁ = (shortCurve A).toAffine.negY x₂ y₂) :=
    fun h => hne (Point.add_of_Y_eq h.1 h.2)
  rw [Point.add_some hxy]
  obtain ⟨lam, ν, hlam, hν, hν0, hℓν, hc₁, hc₂⟩ : ∃ lam ν : K0, VGe π (2 * m) lam ∧
      VGe π (3 * m) ν ∧ ν ≠ 0 ∧ (shortCurve A).toAffine.slope x₁ x₂ y₁ y₂ = -lam / ν ∧
      y₁ = (shortCurve A).toAffine.slope x₁ x₂ y₁ y₂ * x₁ + 1 / ν ∧
      y₂ = (shortCurve A).toAffine.slope x₁ x₂ y₁ y₂ * x₂ + 1 / ν := by
    by_cases hx : x₁ = x₂
    · have hyy : y₁ = y₂ := by
        rcases Y_eq_of_X_eq h₁.1 h₂.1 hx with h | h
        · exact h
        · exact absurd ⟨hx, h⟩ hxy
      subst hx hyy
      have hy' : y₁ ≠ (shortCurve A).toAffine.negY x₁ y₁ := fun h => hxy ⟨rfl, h⟩
      have hslope : (shortCurve A).toAffine.slope x₁ x₁ y₁ y₁ = (3 * x₁ ^ 2 + A) / (y₁ - -y₁) := by
        rw [Affine.slope_of_Y_ne rfl hy']; simp [shortCurve_negY]
      obtain ⟨lam, ν, h1, h2, h3, h4, h5⟩ := kernel_tangent_line hπ hA hm hy₁ e₁ ht₁ hw₁
      exact ⟨lam, ν, h1, h2, h3, by rw [hslope, h4], by rw [hslope]; exact h5,
        by rw [hslope]; exact h5⟩
    · have hslope : (shortCurve A).toAffine.slope x₁ x₂ y₁ y₂ = (y₁ - y₂) / (x₁ - x₂) :=
        Affine.slope_of_X_ne hx
      obtain ⟨lam, ν, h1, h2, h3, h4, h5, h6⟩ :=
        kernel_chord_line hπ hA hm hy₁ hy₂ e₁ e₂ ht₁ ht₂ hw₁ hw₂ hx
      exact ⟨lam, ν, h1, h2, h3, by rw [hslope, h4], by rw [hslope]; exact h5,
        by rw [hslope]; exact h6⟩
  have h₃ := nonsingular_add h₁ h₂ hxy
  refine ⟨_, _, h₃, rfl, ?_⟩
  have eX : (shortCurve A).toAffine.addX x₁ x₂ ((shortCurve A).toAffine.slope x₁ x₂ y₁ y₂) =
      (shortCurve A).toAffine.slope x₁ x₂ y₁ y₂ ^ 2 - x₁ - x₂ := by
    rw [Affine.addX, shortCurve_a₁, shortCurve_a₂]; ring
  have eY : (shortCurve A).toAffine.addY x₁ x₂ y₁ ((shortCurve A).toAffine.slope x₁ x₂ y₁ y₂) =
      -((shortCurve A).toAffine.slope x₁ x₂ y₁ y₂ *
        ((shortCurve A).toAffine.slope x₁ x₂ y₁ y₂ ^ 2 - x₁ - x₂) + 1 / ν) := by
    rw [Affine.addY, Affine.negAddY, eX, shortCurve_negY]
    linear_combination -hc₁
  have e₃ := (shortCurve_equation_iff A _ _).mp h₃.1
  rw [eX, eY] at e₃ ⊢
  generalize hℓ : (shortCurve A).toAffine.slope x₁ x₂ y₁ y₂ = ℓ at hℓν hc₁ hc₂ e₃ ⊢
  exact kernel_third_point hπ hA hm h₁.1 h₂.1 hxy hℓ hy₁ hy₂ ht₁ ht₂ hlam hν hν0 hℓν hc₁ hc₂ e₃

omit [(shortCurve A).IsElliptic] in
/-- A point with `v(x) < 0` has `v(x) = -2n`, `v(y) = -3n` for some `n ≥ 1`. -/
theorem level_of_not_vge {x y : K0} (e : y ^ 2 = x ^ 3 + A * x) (hx : ¬VGe π 0 x) :
    ∃ n : ℤ, 1 ≤ n ∧ x ≠ 0 ∧ y ≠ 0 ∧ vp π x = -2 * n ∧ vp π y = -3 * n := by
  have hx0 : x ≠ 0 := fun h => hx (Or.inl h)
  have hvx : vp π x < 0 := by rw [vge_iff hx0] at hx; omega
  have hAx : VGe π (vp π x) (A * x) := by
    have := hA.mul hπ (VGe.of_vp_eq (π := π) hx0 rfl); simpa using this
  have hx3 : vp π (x ^ 3) = 3 * vp π x := by rw [vp_pow hπ]; norm_num
  have hsum : vp π (x ^ 3 + A * x) = 3 * vp π x := by
    rw [← hx3]; exact vp_add_eq_of_vge hπ (pow_ne_zero 3 hx0) (hAx.mono (by omega))
  have hsum0 : x ^ 3 + A * x ≠ 0 :=
    add_ne_zero_of_vge hπ (pow_ne_zero 3 hx0) (hAx.mono (by omega))
  have hy0 : y ≠ 0 := by rintro rfl; apply hsum0; rw [← e]; ring
  have hy2 : 2 * vp π y = 3 * vp π x := by
    rw [← hsum, ← e, vp_pow hπ]; norm_num
  refine ⟨-vp π x / 2, ?_, hx0, hy0, ?_, ?_⟩ <;> omega

omit hπ hA [(shortCurve A).IsElliptic] in
/-- The parameter `t = x / y` of a point (`0` for `O`). -/
noncomputable def tCoord (A : K0) : (shortCurve A).toAffine.Point → K0
  | 0 => 0
  | .some x y _ => x / y

/-- **The kernel of reduction has no torsion prime to `p`**: if `v(x) < 0` and `π ∤ q`, then
`q (x, y) ≠ O`. -/
theorem nsmul_ne_zero_of_not_vge {x y : K0} (h : (shortCurve A).toAffine.Nonsingular x y)
    (hx : ¬VGe π 0 x) {q : ℕ} (hq : ¬π ∣ (q : Zs)) : q • Point.some x y h ≠ 0 := by
  have e := (shortCurve_equation_iff A x y).mp h.1
  obtain ⟨n, hn, hx0, hy0, hvx, hvy⟩ := level_of_not_vge hπ hA e hx
  have hq0 : q ≠ 0 := by rintro rfl; exact hq (by simp)
  have hqv : vp π (q : K0) = 0 := by
    rw [← toK0_natCast]
    exact (vp_eq_zero_iff hπ (by exact_mod_cast hq0)).mpr hq
  set P := Point.some x y h with hP
  set t := x / y with htdef
  have ht : vp π t = n := by rw [htdef, vp_div hπ hx0 hy0, hvx, hvy]; ring
  have hw : vp π (1 / y) = 3 * n := by rw [one_div, vp_inv hπ, hvy]; ring
  have ht0 : t ≠ 0 := div_ne_zero hx0 hy0
  have htn : VGe π n t := VGe.of_vp_eq ht0 ht
  have hwn : VGe π (3 * n) (1 / y) := VGe.of_vp_eq (one_div_ne_zero hy0) hw
  have key : ∀ k : ℕ, 1 ≤ k → (k • P = 0 ∨ ∃ x' y' h', k • P = Point.some x' y' h' ∧ y' ≠ 0 ∧
      VGe π n (x' / y') ∧ VGe π (3 * n) (1 / y')) ∧
      VGe π (n + 1) (tCoord A (k • P) - k * t) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      rw [one_nsmul]
      refine ⟨Or.inr ⟨x, y, h, rfl, hy0, htn, hwn⟩, ?_⟩
      rw [hP, tCoord, Nat.cast_one, one_mul, sub_self]
      exact VGe.zero _ _
    | succ k hk ih =>
      obtain ⟨hcase, hcong⟩ := ih
      rw [succ_nsmul]
      rcases hcase with h0 | ⟨x', y', h', hk', hy', ht', hw'⟩
      · rw [h0, zero_add]
        refine ⟨Or.inr ⟨x, y, h, rfl, hy0, htn, hwn⟩, ?_⟩
        rw [h0] at hcong
        have : tCoord A P - ((k + 1 : ℕ) : K0) * t = tCoord A 0 - k * t := by
          rw [hP]; simp only [tCoord]; rw [htdef]; push_cast; ring
        rw [this]; exact hcong
      · rw [hk']
        by_cases hs : Point.some x' y' h' + P = 0
        · rw [hs]
          refine ⟨Or.inl rfl, ?_⟩
          have hxy : x' = x ∧ y' = (shortCurve A).toAffine.negY x y := by
            by_contra hxy
            rw [hP, Point.add_some hxy] at hs
            exact Point.some_ne_zero _ hs
          rw [hk'] at hcong
          obtain ⟨rfl, hyy⟩ := hxy
          rw [shortCurve_negY] at hyy
          subst hyy
          have : tCoord A 0 - ((k + 1 : ℕ) : K0) * t = tCoord A (Point.some x' (-y) h') - k * t := by
            simp only [tCoord]; rw [htdef, div_neg]; push_cast; ring
          rw [this]; exact hcong
        · obtain ⟨x₃, y₃, h₃, hsum, hy₃, ht₃, hw₃, hE⟩ :=
            kernel_add hπ hA hn h' h hy' hy0 ht' htn hw' hwn hs
          rw [hsum]
          refine ⟨Or.inr ⟨x₃, y₃, h₃, rfl, hy₃, ht₃, hw₃⟩, ?_⟩
          rw [hk'] at hcong
          have : tCoord A (Point.some x₃ y₃ h₃) - ((k + 1 : ℕ) : K0) * t =
              (x₃ / y₃ - x' / y' - x / y) + (tCoord A (Point.some x' y' h') - k * t) := by
            simp only [tCoord]; rw [htdef]; push_cast; ring
          rw [this]; exact hE.add hπ hcong
  intro hqP
  have := (key q (Nat.one_le_iff_ne_zero.mpr hq0)).2
  rw [hqP] at this
  simp only [tCoord, zero_sub] at this
  have hqt : (q : K0) * t ≠ 0 := mul_ne_zero (by exact_mod_cast hq0) ht0
  rw [vge_iff (neg_ne_zero.mpr hqt), vp_neg hπ, vp_mul hπ (by exact_mod_cast hq0) ht0, hqv,
    ht] at this
  omega

end Valuation

end ZInQ
