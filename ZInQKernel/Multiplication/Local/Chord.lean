import ZInQKernel.Multiplication.Local.ValHelpers
import ZInQKernel.Model.Descent.KernelReduction

/-!
# The chord estimate on `y² = x³ + A x` over a valued field

Let `v : AddValuation K (WithTop ℤ)` and `A ∈ K` with `v(A) ≥ 0`. For an affine point `(x, y)`
with `y ≠ 0` put `t = x / y` and `w = 1 / y` (so `z = -t`, `ω = -w` in the notation of the
blueprint), which satisfy `w = t³ + A t w²` (`tw_equation`).

*Addition estimate* (`chord_add`): if `v(tᵢ) ≥ m ≥ 1` and `v(wᵢ) ≥ 3m` for two points whose
sum is not `O`, then the sum is affine with the same bounds and
`v(t(P₁ + P₂) - t₁ - t₂) ≥ m + 1`; `chord_add_five` is the sharp form: the chord identity
`z(P₁ + P₂) = z(P₁) + z(P₂) + 2Aλν/(1 + Aλ²)` and `v(t(P₁ + P₂) - t₁ - t₂) ≥ 5m`.

This is the generic form (any field, any `ℤ ∪ {∞}`-valued valuation) of the estimate proved for
`K₀` in `ZInQKernel/Model/Descent/KernelReduction.lean`, whose chord algebra (`vieta_shortCurve`,
`sum_t_identity`, `tw_equation`) is reused.
-/

namespace ZInQ.Mult

open WeierstrassCurve WeierstrassCurve.Affine

variable {K : Type*} [Field K] {v : AddValuation K (WithTop ℤ)} {A : K}

section Estimates

variable [DecidableEq K] (hA : Vge v 0 A)
include hA

omit [DecidableEq K] in
/-- The slope `λ` of the chord in the `(t, w)`-plane has `v(λ) ≥ 2m`. -/
theorem vge_chord_slope' {m : ℤ} (hm : 1 ≤ m) {t₁ t₂ w₁ w₂ : K}
    (e₁ : w₁ = t₁ ^ 3 + A * t₁ * w₁ ^ 2) (e₂ : w₂ = t₂ ^ 3 + A * t₂ * w₂ ^ 2) (ht : t₁ ≠ t₂)
    (ht₁ : Vge v m t₁) (ht₂ : Vge v m t₂) (hw₁ : Vge v (3 * m) w₁) (hw₂ : Vge v (3 * m) w₂) :
    Vge v (2 * m) ((w₂ - w₁) / (t₂ - t₁)) := by
  have hD1 : Vge v 1 (-(A * t₁ * (w₁ + w₂))) :=
    (((hA.mul ht₁).mul (hw₁.add hw₂)).mono (by omega)).neg
  have hD0 := one_add_ne_zero hD1
  have key : (w₂ - w₁) / (t₂ - t₁) =
      (t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2 + A * w₂ ^ 2) / (1 + -(A * t₁ * (w₁ + w₂))) := by
    rw [div_eq_div_iff (sub_ne_zero.mpr ht.symm) hD0]
    linear_combination e₂ - e₁
  rw [key]
  refine Vge.div_unit ?_ (val_one_add hD1)
  refine (((ht₁.pow 2).mono (by push_cast; omega)).add
    ((ht₁.mul ht₂).mono (by omega))).add ((ht₂.pow 2).mono (by push_cast; omega)) |>.add ?_
  exact (hA.mul (hw₂.pow 2)).mono (by push_cast; omega)

omit [DecidableEq K] in
/-- In the formal neighbourhood, two points with the same `t` have the same `w`. -/
theorem w_eq_of_t_eq {m : ℤ} (hm : 1 ≤ m) {t w₁ w₂ : K}
    (e₁ : w₁ = t ^ 3 + A * t * w₁ ^ 2) (e₂ : w₂ = t ^ 3 + A * t * w₂ ^ 2)
    (ht : Vge v m t) (hw₁ : Vge v (3 * m) w₁) (hw₂ : Vge v (3 * m) w₂) : w₁ = w₂ := by
  have hD1 : Vge v 1 (-(A * t * (w₁ + w₂))) :=
    (((hA.mul ht).mul (hw₁.add hw₂)).mono (by omega)).neg
  have hD0 := one_add_ne_zero hD1
  have hprod : (w₁ - w₂) * (1 + -(A * t * (w₁ + w₂))) = 0 := by
    linear_combination e₁ - e₂
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hD0)

/-- In the formal neighbourhood, distinct abscissas have distinct `t = x / y`. -/
theorem t_ne_of_x_ne' {m : ℤ} (hm : 1 ≤ m) {x₁ y₁ x₂ y₂ : K} (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0)
    (e₁ : y₁ ^ 2 = x₁ ^ 3 + A * x₁) (e₂ : y₂ ^ 2 = x₂ ^ 3 + A * x₂)
    (ht₁ : Vge v m (x₁ / y₁)) (hw₁ : Vge v (3 * m) (1 / y₁)) (hw₂ : Vge v (3 * m) (1 / y₂))
    (hx : x₁ ≠ x₂) : x₁ / y₁ ≠ x₂ / y₂ := by
  intro ht
  have f₁ := tw_equation hy₁ e₁
  have f₂ := tw_equation hy₂ e₂
  rw [← ht] at f₂
  have hw : 1 / y₁ = 1 / y₂ := w_eq_of_t_eq hA hm f₁ f₂ ht₁ hw₁ hw₂
  have hy : y₁ = y₂ := by
    have := congrArg (fun z => 1 / z) hw; simpa using this
  apply hx
  rw [← hy] at ht
  have := congrArg (· * y₁) ht
  simpa [div_mul_cancel₀ _ hy₁] using this

omit [DecidableEq K] in
/-- The tangent at a point of the formal neighbourhood is `λ x + ν y = 1` with `v(λ) ≥ 2m`,
`v(ν) ≥ 3m`. -/
theorem formal_tangent_line {m : ℤ} (hm : 1 ≤ m) (h2 : (2 : K) ≠ 0) {x y : K} (hy : y ≠ 0)
    (e : y ^ 2 = x ^ 3 + A * x) (ht : Vge v m (x / y)) (hw : Vge v (3 * m) (1 / y)) :
    ∃ lam ν : K, Vge v (2 * m) lam ∧ Vge v (3 * m) ν ∧ ν ≠ 0 ∧
      (3 * x ^ 2 + A) / (y - -y) = -lam / ν ∧ y = (3 * x ^ 2 + A) / (y - -y) * x + 1 / ν := by
  have hD1 : Vge v 1 (-(2 * A * (x / y) * (1 / y))) :=
    ((((vge_ofNat 2).mul hA).mul ht).mul hw |>.mono (by omega)).neg
  have hDv := val_one_add hD1
  have hD0 := one_add_ne_zero hD1
  have hlam : Vge v (2 * m)
      ((3 * (x / y) ^ 2 + A * (1 / y) ^ 2) / (1 + -(2 * A * (x / y) * (1 / y)))) := by
    refine Vge.div_unit ?_ hDv
    exact (((vge_ofNat 3).mul (ht.pow 2)).mono (by push_cast; omega)).add
      ((hA.mul (hw.pow 2)).mono (by push_cast; omega))
  have hD : (1 : K) + -(2 * A * (x / y) * (1 / y)) = (y ^ 2 - 2 * A * x) / y ^ 2 := by
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
  have hνvge : Vge v (3 * m) (-2 * y / (y ^ 2 - 2 * A * x)) := by
    rw [← hν]; exact hw.sub ((hlam.mul ht).mono (by omega))
  have hyy : y - -y = 2 * y := by ring
  rw [hyy]
  generalize hDdef : y ^ 2 - 2 * A * x = D at hD0' hlam hνvge
  have hν0 : -2 * y / D ≠ 0 := div_ne_zero (mul_ne_zero (neg_ne_zero.mpr h2) hy) hD0'
  refine ⟨(3 * x ^ 2 + A) / D, -2 * y / D, hlam, hνvge, hν0, ?_, ?_⟩
  · field_simp
  · field_simp
    linear_combination 3 * e - hDdef

/-- The chord through two points of the formal neighbourhood with distinct abscissas is
`λ x + ν y = 1` with `v(λ) ≥ 2m`, `v(ν) ≥ 3m`. -/
theorem formal_chord_line {m : ℤ} (hm : 1 ≤ m) {x₁ y₁ x₂ y₂ : K} (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0)
    (e₁ : y₁ ^ 2 = x₁ ^ 3 + A * x₁) (e₂ : y₂ ^ 2 = x₂ ^ 3 + A * x₂)
    (ht₁ : Vge v m (x₁ / y₁)) (ht₂ : Vge v m (x₂ / y₂))
    (hw₁ : Vge v (3 * m) (1 / y₁)) (hw₂ : Vge v (3 * m) (1 / y₂)) (hx : x₁ ≠ x₂) :
    ∃ lam ν : K, Vge v (2 * m) lam ∧ Vge v (3 * m) ν ∧ ν ≠ 0 ∧
      (y₁ - y₂) / (x₁ - x₂) = -lam / ν ∧ y₁ = (y₁ - y₂) / (x₁ - x₂) * x₁ + 1 / ν ∧
      y₂ = (y₁ - y₂) / (x₁ - x₂) * x₂ + 1 / ν := by
  have ht : x₁ / y₁ ≠ x₂ / y₂ := t_ne_of_x_ne' hA hm hy₁ hy₂ e₁ e₂ ht₁ hw₁ hw₂ hx
  have hlam := vge_chord_slope' hA hm (tw_equation hy₁ e₁) (tw_equation hy₂ e₂) ht ht₁ ht₂
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
  have hνvge : Vge v (3 * m) ((x₁ - x₂) / (x₁ * y₂ - x₂ * y₁)) := by
    rw [← hν]; exact hw₁.sub ((hlam.mul ht₁).mono (by omega))
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

/-- The third point of the line `λ x + ν y = 1` through two points of the formal
neighbourhood, with the exact chord identity `t₃ - t₁ - t₂ = 2Aλν/(1 + Aλ²)` and the sharp
bound `v(t₃ - t₁ - t₂) ≥ 5m`. -/
theorem formal_third_point_five {m : ℤ} (hm : 1 ≤ m) {x₁ y₁ x₂ y₂ ℓ lam ν : K}
    (h₁ : (shortCurve A).toAffine.Equation x₁ y₁) (h₂ : (shortCurve A).toAffine.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (shortCurve A).toAffine.negY x₂ y₂))
    (hℓ : (shortCurve A).toAffine.slope x₁ x₂ y₁ y₂ = ℓ) (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0)
    (ht₁ : Vge v m (x₁ / y₁)) (ht₂ : Vge v m (x₂ / y₂))
    (hlam : Vge v (2 * m) lam) (hν : Vge v (3 * m) ν) (hν0 : ν ≠ 0) (hℓν : ℓ = -lam / ν)
    (hc₁ : y₁ = ℓ * x₁ + 1 / ν) (hc₂ : y₂ = ℓ * x₂ + 1 / ν)
    (e₃ : (-(ℓ * (ℓ ^ 2 - x₁ - x₂) + 1 / ν)) ^ 2 =
      (ℓ ^ 2 - x₁ - x₂) ^ 3 + A * (ℓ ^ 2 - x₁ - x₂)) :
    -(ℓ * (ℓ ^ 2 - x₁ - x₂) + 1 / ν) ≠ 0 ∧
      Vge v m ((ℓ ^ 2 - x₁ - x₂) / -(ℓ * (ℓ ^ 2 - x₁ - x₂) + 1 / ν)) ∧
      Vge v (3 * m) (1 / -(ℓ * (ℓ ^ 2 - x₁ - x₂) + 1 / ν)) ∧
      (ℓ ^ 2 - x₁ - x₂) / -(ℓ * (ℓ ^ 2 - x₁ - x₂) + 1 / ν) - x₁ / y₁ - x₂ / y₂ =
        2 * A * lam * ν / (1 + A * lam ^ 2) ∧
      Vge v (5 * m) ((ℓ ^ 2 - x₁ - x₂) / -(ℓ * (ℓ ^ 2 - x₁ - x₂) + 1 / ν) - x₁ / y₁ - x₂ / y₂) := by
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
    obtain ⟨n, hn⟩ := val_eq_coe (v := v) hl0
    have hv : v x₃ = (-n : ℤ) := by
      have : x₃ = lam⁻¹ := eq_inv_of_mul_eq_one_right hline
      rw [this]; exact val_inv_coe hn
    have hvl : 2 * m ≤ n := (vge_iff_of_eq hn).mp hlam
    have hA' : Vge v 0 (x₃ ^ 2) := by rw [hsq]; exact hA.neg
    rw [vge_iff_of_eq (val_pow_coe hv 2)] at hA'
    push_cast at hA'
    omega
  -- the `t`-identity
  have hAl : Vge v 1 (A * lam ^ 2) := (hA.mul (hlam.pow 2)).mono (by push_cast; omega)
  have hD0 : 1 + A * lam ^ 2 ≠ 0 := one_add_ne_zero hAl
  have hDv : v (1 + A * lam ^ 2) = 0 := val_one_add hAl
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
  have hE : Vge v (5 * m) (x₃ / y₃ - x₁ / y₁ - x₂ / y₂) := by
    rw [hdiff]
    have hN : Vge v (5 * m) (2 * A * lam * ν) :=
      ((((vge_ofNat 2).mul hA).mul hlam).mul hν).mono (by omega)
    exact hN.div_unit hDv
  have ht₃ : Vge v m (x₃ / y₃) := by
    have : x₃ / y₃ = (x₃ / y₃ - x₁ / y₁ - x₂ / y₂) + x₁ / y₁ + x₂ / y₂ := by ring
    rw [this]
    exact ((hE.mono (by omega)).add ht₁).add ht₂
  refine ⟨hy₃0, ht₃, ?_, hdiff, hE⟩
  have : 1 / y₃ = lam * (x₃ / y₃) - ν := by
    field_simp; linear_combination -hline
  rw [this]
  exact ((hlam.mul ht₃).mono (by omega)).sub hν

/-- The third point of the line `λ x + ν y = 1` through two points of the formal
neighbourhood. -/
theorem formal_third_point {m : ℤ} (hm : 1 ≤ m) {x₁ y₁ x₂ y₂ ℓ lam ν : K}
    (h₁ : (shortCurve A).toAffine.Equation x₁ y₁) (h₂ : (shortCurve A).toAffine.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (shortCurve A).toAffine.negY x₂ y₂))
    (hℓ : (shortCurve A).toAffine.slope x₁ x₂ y₁ y₂ = ℓ) (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0)
    (ht₁ : Vge v m (x₁ / y₁)) (ht₂ : Vge v m (x₂ / y₂))
    (hlam : Vge v (2 * m) lam) (hν : Vge v (3 * m) ν) (hν0 : ν ≠ 0) (hℓν : ℓ = -lam / ν)
    (hc₁ : y₁ = ℓ * x₁ + 1 / ν) (hc₂ : y₂ = ℓ * x₂ + 1 / ν)
    (e₃ : (-(ℓ * (ℓ ^ 2 - x₁ - x₂) + 1 / ν)) ^ 2 =
      (ℓ ^ 2 - x₁ - x₂) ^ 3 + A * (ℓ ^ 2 - x₁ - x₂)) :
    -(ℓ * (ℓ ^ 2 - x₁ - x₂) + 1 / ν) ≠ 0 ∧
      Vge v m ((ℓ ^ 2 - x₁ - x₂) / -(ℓ * (ℓ ^ 2 - x₁ - x₂) + 1 / ν)) ∧
      Vge v (3 * m) (1 / -(ℓ * (ℓ ^ 2 - x₁ - x₂) + 1 / ν)) ∧
      Vge v (m + 1) ((ℓ ^ 2 - x₁ - x₂) / -(ℓ * (ℓ ^ 2 - x₁ - x₂) + 1 / ν) - x₁ / y₁ - x₂ / y₂) := by
  obtain ⟨h1, h2, h3, -, h5⟩ := formal_third_point_five hA hm h₁ h₂ hxy hℓ hy₁ hy₂ ht₁ ht₂ hlam hν
    hν0 hℓν hc₁ hc₂ e₃
  exact ⟨h1, h2, h3, h5.mono (by omega)⟩

/-- **The chord estimate**, sharp form. If `v(x/y) ≥ m ≥ 1` and `v(1/y) ≥ 3m` for two points
whose sum is not `O`, then the sum is affine with the same bounds; in the coordinates `z = -x/y`,
`ω = -1/y` the line through the two points (the tangent if they are equal) is `ω = λ z + ν` with
`v(λ) ≥ 2m`, `v(ν) ≥ 3m`, and `z(P₁ + P₂) = z(P₁) + z(P₂) + 2Aλν/(1 + Aλ²)`; in particular
`v(t(P₁ + P₂) - t(P₁) - t(P₂)) ≥ 5m`. -/
theorem chord_add_five {m : ℤ} (hm : 1 ≤ m) {x₁ y₁ x₂ y₂ : K}
    (h₁ : (shortCurve A).toAffine.Nonsingular x₁ y₁)
    (h₂ : (shortCurve A).toAffine.Nonsingular x₂ y₂) (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0)
    (ht₁ : Vge v m (x₁ / y₁)) (ht₂ : Vge v m (x₂ / y₂))
    (hw₁ : Vge v (3 * m) (1 / y₁)) (hw₂ : Vge v (3 * m) (1 / y₂))
    (hne : Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ ≠ 0) :
    ∃ x₃ y₃ h₃, Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ = Point.some x₃ y₃ h₃ ∧ y₃ ≠ 0 ∧
      Vge v m (x₃ / y₃) ∧ Vge v (3 * m) (1 / y₃) ∧
      ∃ lam ν : K, Vge v (2 * m) lam ∧ Vge v (3 * m) ν ∧
        -1 / y₁ = lam * (-x₁ / y₁) + ν ∧ -1 / y₂ = lam * (-x₂ / y₂) + ν ∧
        -x₃ / y₃ = -x₁ / y₁ + -x₂ / y₂ + 2 * A * lam * ν / (1 + A * lam ^ 2) ∧
        Vge v (5 * m) (x₃ / y₃ - x₁ / y₁ - x₂ / y₂) := by
  have e₁ := (shortCurve_equation_iff A x₁ y₁).mp h₁.1
  have e₂ := (shortCurve_equation_iff A x₂ y₂).mp h₂.1
  have hxy : ¬(x₁ = x₂ ∧ y₁ = (shortCurve A).toAffine.negY x₂ y₂) :=
    fun h => hne (Point.add_of_Y_eq h.1 h.2)
  rw [Point.add_some hxy]
  obtain ⟨lam, ν, hlam, hν, hν0, hℓν, hc₁, hc₂⟩ : ∃ lam ν : K, Vge v (2 * m) lam ∧
      Vge v (3 * m) ν ∧ ν ≠ 0 ∧ (shortCurve A).toAffine.slope x₁ x₂ y₁ y₂ = -lam / ν ∧
      y₁ = (shortCurve A).toAffine.slope x₁ x₂ y₁ y₂ * x₁ + 1 / ν ∧
      y₂ = (shortCurve A).toAffine.slope x₁ x₂ y₁ y₂ * x₂ + 1 / ν := by
    by_cases hx : x₁ = x₂
    · have hyy : y₁ = y₂ := by
        rcases Y_eq_of_X_eq h₁.1 h₂.1 hx with h | h
        · exact h
        · exact absurd ⟨hx, h⟩ hxy
      subst hx hyy
      have hy' : y₁ ≠ (shortCurve A).toAffine.negY x₁ y₁ := fun h => hxy ⟨rfl, h⟩
      have h2 : (2 : K) ≠ 0 := by
        intro h2
        apply hy'
        rw [shortCurve_negY]
        linear_combination y₁ * h2
      have hslope : (shortCurve A).toAffine.slope x₁ x₁ y₁ y₁ =
          (3 * x₁ ^ 2 + A) / (y₁ - -y₁) := by
        rw [Affine.slope_of_Y_ne rfl hy']; simp
      obtain ⟨lam, ν, h1, h2, h3, h4, h5⟩ := formal_tangent_line hA hm h2 hy₁ e₁ ht₁ hw₁
      exact ⟨lam, ν, h1, h2, h3, by rw [hslope, h4], by rw [hslope]; exact h5,
        by rw [hslope]; exact h5⟩
    · have hslope : (shortCurve A).toAffine.slope x₁ x₂ y₁ y₂ = (y₁ - y₂) / (x₁ - x₂) :=
        Affine.slope_of_X_ne hx
      obtain ⟨lam, ν, h1, h2, h3, h4, h5, h6⟩ :=
        formal_chord_line hA hm hy₁ hy₂ e₁ e₂ ht₁ ht₂ hw₁ hw₂ hx
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
  obtain ⟨hy₃, ht₃, hw₃, hid, h5⟩ :=
    formal_third_point_five hA hm h₁.1 h₂.1 hxy hℓ hy₁ hy₂ ht₁ ht₂ hlam hν hν0 hℓν hc₁ hc₂ e₃
  refine ⟨hy₃, ht₃, hw₃, lam, -ν, hlam, hν.neg, ?_, ?_, ?_, h5⟩
  · have hl : lam * x₁ + ν * y₁ = 1 := by rw [hc₁, hℓν]; field_simp; ring
    field_simp; linear_combination hl
  · have hl : lam * x₂ + ν * y₂ = 1 := by rw [hc₂, hℓν]; field_simp; ring
    field_simp; linear_combination hl
  · rw [neg_div, neg_div, neg_div]; linear_combination -hid

/-- **The addition estimate.** If `v(x/y) ≥ m ≥ 1` and `v(1/y) ≥ 3m` for two points whose sum
is not `O`, then the sum is affine with the same bounds and
`v(t(P₁ + P₂) - t(P₁) - t(P₂)) ≥ m + 1`. -/
theorem chord_add {m : ℤ} (hm : 1 ≤ m) {x₁ y₁ x₂ y₂ : K}
    (h₁ : (shortCurve A).toAffine.Nonsingular x₁ y₁)
    (h₂ : (shortCurve A).toAffine.Nonsingular x₂ y₂) (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0)
    (ht₁ : Vge v m (x₁ / y₁)) (ht₂ : Vge v m (x₂ / y₂))
    (hw₁ : Vge v (3 * m) (1 / y₁)) (hw₂ : Vge v (3 * m) (1 / y₂))
    (hne : Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ ≠ 0) :
    ∃ x₃ y₃ h₃, Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ = Point.some x₃ y₃ h₃ ∧ y₃ ≠ 0 ∧
      Vge v m (x₃ / y₃) ∧ Vge v (3 * m) (1 / y₃) ∧
      Vge v (m + 1) (x₃ / y₃ - x₁ / y₁ - x₂ / y₂) := by
  obtain ⟨x₃, y₃, h₃, heq, hy₃, ht₃, hw₃, -, -, -, -, -, -, -, h5⟩ :=
    chord_add_five hA hm h₁ h₂ hy₁ hy₂ ht₁ ht₂ hw₁ hw₂ hne
  exact ⟨x₃, y₃, h₃, heq, hy₃, ht₃, hw₃, h5.mono (by omega)⟩

end Estimates

end ZInQ.Mult
