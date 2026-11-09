import ZInQKernel.Model.Field.Euclidean

/-!
# Valuations at the primes of `ℤ[√2]`

Blueprint: `model/field/integers-pid.md` (the valuation part).

For a prime element `π` of the principal ideal domain `ℤ[s]`, `vp π : K₀ → ℤ` is the
`π`-adic valuation (`vp π 0 = 0` by convention). It is built from Mathlib's adic valuation
`IsDedekindDomain.HeightOneSpectrum.valuation` of the height-one prime `(π)`. The basic facts:
`vp π (x y) = vp π x + vp π y`, `vp π (x + y) ≥ min (vp π x) (vp π y)` with equality when the
two valuations differ, and for `a ∈ ℤ[s] \ {0}`, `n ≤ vp π a ↔ πⁿ ∣ a`.
-/

namespace ZInQ

open IsDedekindDomain WithZero

/-- The height-one prime `(π)` of `ℤ[s]`. -/
def primeSpec (π : Zs) (hπ : Prime π) : HeightOneSpectrum Zs :=
  ⟨Ideal.span {π}, (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ, by simpa using hπ.ne_zero⟩

theorem primeSpec_asIdeal (π : Zs) (hπ : Prime π) :
    (primeSpec π hπ).asIdeal = Ideal.span {π} := rfl

open Classical in
/-- The `π`-adic valuation `v_π : K₀ → ℤ` (with `v_π 0 = 0`, and `v_π = 0` if `π` is not prime). -/
noncomputable def vp (π : Zs) (z : K0) : ℤ :=
  if hπ : Prime π then -log ((primeSpec π hπ).valuation K0 z) else 0

variable {π : Zs} (hπ : Prime π)
include hπ

theorem vp_def (z : K0) : vp π z = -log ((primeSpec π hπ).valuation K0 z) := by
  simp only [vp, hπ, ↓reduceDIte]

omit hπ in
@[simp] theorem vp_zero : vp π 0 = 0 := by
  unfold vp; split_ifs <;> simp

theorem vp_mul {x y : K0} (hx : x ≠ 0) (hy : y ≠ 0) : vp π (x * y) = vp π x + vp π y := by
  simp only [vp_def hπ, map_mul]
  rw [log_mul (by simp [hx]) (by simp [hy])]; ring

@[simp] theorem vp_one : vp π 1 = 0 := by simp [vp_def hπ]

theorem vp_inv (x : K0) : vp π x⁻¹ = -vp π x := by
  simp [vp_def hπ, map_inv₀, log_inv]

theorem vp_div {x y : K0} (hx : x ≠ 0) (hy : y ≠ 0) : vp π (x / y) = vp π x - vp π y := by
  rw [div_eq_mul_inv, vp_mul hπ hx (inv_ne_zero hy), vp_inv hπ]; ring

theorem vp_pow (x : K0) (n : ℕ) : vp π (x ^ n) = n * vp π x := by
  simp [vp_def hπ, log_pow]

theorem vp_zpow (x : K0) (n : ℤ) : vp π (x ^ n) = n * vp π x := by
  simp [vp_def hπ, map_zpow₀, log_zpow]

theorem vp_neg (x : K0) : vp π (-x) = vp π x := by
  simp [vp_def hπ]

/-- `v_π(x + y) ≥ min (v_π x) (v_π y)`. -/
theorem min_le_vp_add {x y : K0} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min (vp π x) (vp π y) ≤ vp π (x + y) := by
  simp only [vp_def hπ]
  set v := (primeSpec π hπ).valuation K0
  have hvx : v x ≠ 0 := by simp [v, hx]
  have hvy : v y ≠ 0 := by simp [v, hy]
  have hvxy : v (x + y) ≠ 0 := by simp [v, hxy]
  rw [min_neg_neg, neg_le_neg_iff]
  rcases le_total (v x) (v y) with h | h
  · rw [max_eq_right ((log_le_log hvx hvy).mpr h)]
    exact (log_le_log hvxy hvy).mpr ((v.map_add x y).trans (max_eq_right h).le)
  · rw [max_eq_left ((log_le_log hvy hvx).mpr h)]
    exact (log_le_log hvxy hvx).mpr ((v.map_add x y).trans (max_eq_left h).le)

/-- `v_π(x + y) = min (v_π x) (v_π y)` when `v_π x ≠ v_π y`. -/
theorem vp_add_eq_min_of_ne {x y : K0} (hx : x ≠ 0) (hy : y ≠ 0) (hne : vp π x ≠ vp π y) :
    vp π (x + y) = min (vp π x) (vp π y) := by
  simp only [vp_def hπ] at hne ⊢
  set v := (primeSpec π hπ).valuation K0
  have hvx : v x ≠ 0 := by simp [v, hx]
  have hvy : v y ≠ 0 := by simp [v, hy]
  rw [min_neg_neg]
  have hne' : v x ≠ v y := fun h => hne (by rw [h])
  rcases lt_or_gt_of_ne hne' with h | h
  · rw [Valuation.map_add_eq_of_lt_right v h, max_eq_right ((log_le_log hvx hvy).mpr h.le)]
  · rw [Valuation.map_add_eq_of_lt_left v h, max_eq_left ((log_le_log hvy hvx).mpr h.le)]

/-! ### Values on `ℤ[s]` -/

theorem vp_toK0_eq (a : Zs) :
    vp π (Zs.toK0 a) = -log ((primeSpec π hπ).intValuation a) := by
  rw [vp_def hπ, HeightOneSpectrum.valuation_of_algebraMap]

/-- For `a ∈ ℤ[s]`, `a ≠ 0`: `n ≤ v_π(a) ↔ πⁿ ∣ a`. -/
theorem le_vp_iff_pow_dvd {a : Zs} (ha : a ≠ 0) (n : ℕ) :
    (n : ℤ) ≤ vp π (Zs.toK0 a) ↔ π ^ n ∣ a := by
  rw [vp_toK0_eq hπ, le_neg, ← log_exp (-(n : ℤ)),
    log_le_log ((primeSpec π hπ).intValuation_ne_zero a ha) exp_ne_zero,
    HeightOneSpectrum.intValuation_le_pow_iff_dvd, primeSpec_asIdeal, Ideal.span_singleton_pow,
    Ideal.span_singleton_dvd_span_singleton_iff_dvd]

theorem vp_nonneg (a : Zs) : 0 ≤ vp π (Zs.toK0 a) := by
  by_cases ha : a = 0
  · simp [ha]
  · exact_mod_cast (le_vp_iff_pow_dvd hπ ha 0).mpr (by simp)

theorem vp_pos_iff {a : Zs} (ha : a ≠ 0) : 0 < vp π (Zs.toK0 a) ↔ π ∣ a := by
  have := le_vp_iff_pow_dvd hπ ha 1
  rw [pow_one] at this
  rw [← this]; push_cast; omega

theorem vp_eq_zero_iff {a : Zs} (ha : a ≠ 0) : vp π (Zs.toK0 a) = 0 ↔ ¬ π ∣ a := by
  rw [← vp_pos_iff hπ ha]
  have := vp_nonneg hπ a
  omega

theorem vp_eq_iff {a : Zs} (ha : a ≠ 0) (n : ℕ) :
    vp π (Zs.toK0 a) = n ↔ π ^ n ∣ a ∧ ¬ π ^ (n + 1) ∣ a := by
  rw [← le_vp_iff_pow_dvd hπ ha, ← le_vp_iff_pow_dvd hπ ha]
  push_cast; omega

@[simp] theorem vp_self : vp π (Zs.toK0 π) = 1 := by
  have := (vp_eq_iff hπ hπ.ne_zero 1).mpr ⟨by simp, fun h => ?_⟩
  · exact_mod_cast this
  · rw [pow_succ, pow_one] at h
    obtain ⟨c, hc⟩ := h
    have : π * 1 = π * (π * c) := by rw [mul_one, ← mul_assoc]; exact hc
    have h1 := mul_left_cancel₀ hπ.ne_zero this
    exact hπ.not_isUnit (IsUnit.of_mul_eq_one c h1.symm)

theorem vp_unit (u : Zsˣ) : vp π (Zs.toK0 u) = 0 :=
  (vp_eq_zero_iff hπ u.ne_zero).mpr fun h => hπ.not_isUnit (isUnit_of_dvd_unit h u.isUnit)

theorem vp_isUnit {a : Zs} (ha : IsUnit a) : vp π (Zs.toK0 a) = 0 := by
  obtain ⟨u, rfl⟩ := ha; exact vp_unit hπ u

omit hπ in
/-- Associated primes give the same valuation. -/
theorem vp_eq_of_associated {π' : Zs} (h : Associated π π') : vp π = vp π' := by
  by_cases hπ : Prime π
  · have hπ' : Prime π' := h.prime hπ
    have hspec : primeSpec π hπ = primeSpec π' hπ' := by
      ext1; simp only [primeSpec_asIdeal]
      exact Ideal.span_singleton_eq_span_singleton.mpr h
    funext z; rw [vp_def hπ, vp_def hπ', hspec]
  · have hπ' : ¬ Prime π' := fun hp => hπ (h.symm.prime hp)
    funext z; simp [vp, hπ, hπ']

end ZInQ
