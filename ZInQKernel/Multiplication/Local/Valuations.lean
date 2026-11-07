import ZInQKernel.Multiplication.Local.ValHelpers
import ZInQKernel.Model.Field
import ZInQKernel.Multiplication.Local.PrimesAbove

/-!
# Additive valuations from `ℤᵐ⁰`-valued valuations

Mathlib's discrete valuations (the adic valuation of a height-one prime, the valuation of an
adic completion) take values in `ℤᵐ⁰`, with `v(π) = exp(-1)`. `ordOf w` is the corresponding
additive valuation `x ↦ -log w(x) ∈ ℤ ∪ {∞}`, in which the local statements of the
multiplication chapter are phrased. `vP π hπ = ordOf ((primeSpec π hπ).valuation K0)` is the
additive valuation of `K₀` at a prime `π` of `ℤ[s]`; it agrees with the model chapter's
`vp π` on `K₀ˣ` and is `⊤` at `0`.
-/

namespace ZInQ.Mult

open WithZero

variable {K : Type*} [Field K]

open Classical in
/-- The additive valuation `-log w(x)` (`⊤` at `0`) attached to `w : Valuation K ℤᵐ⁰`. -/
noncomputable def ordOf (w : Valuation K ℤᵐ⁰) : AddValuation K (WithTop ℤ) :=
  AddValuation.of (fun x => if x = 0 then ⊤ else ((-log (w x) : ℤ) : WithTop ℤ))
    (by simp)
    (by simp)
    (by
      intro x y
      by_cases hx : x = 0
      · subst hx; simp
      by_cases hy : y = 0
      · subst hy; simp
      by_cases hxy : x + y = 0
      · simp [hxy]
      have hwx : w x ≠ 0 := (Valuation.ne_zero_iff w).mpr hx
      have hwy : w y ≠ 0 := (Valuation.ne_zero_iff w).mpr hy
      have hwxy : w (x + y) ≠ 0 := (Valuation.ne_zero_iff w).mpr hxy
      simp only [hx, hy, hxy, ite_false]
      rw [← WithTop.coe_min, WithTop.coe_le_coe]
      rcases le_total (w x) (w y) with h | h
      · have h1 : w (x + y) ≤ w y := le_trans (w.map_add x y) (max_le h le_rfl)
        have := (log_le_log hwxy hwy).mpr h1
        exact le_trans (min_le_right _ _) (by omega)
      · have h1 : w (x + y) ≤ w x := le_trans (w.map_add x y) (max_le le_rfl h)
        have := (log_le_log hwxy hwx).mpr h1
        exact le_trans (min_le_left _ _) (by omega))
    (by
      intro x y
      by_cases hx : x = 0
      · subst hx; simp
      by_cases hy : y = 0
      · subst hy; simp
      have hwx : w x ≠ 0 := (Valuation.ne_zero_iff w).mpr hx
      have hwy : w y ≠ 0 := (Valuation.ne_zero_iff w).mpr hy
      simp only [hx, hy, mul_eq_zero, or_self, ite_false, w.map_mul, log_mul hwx hwy]
      rw [← WithTop.coe_add]; congr 1; ring)

theorem ordOf_apply (w : Valuation K ℤᵐ⁰) {x : K} (hx : x ≠ 0) :
    ordOf w x = ((-log (w x) : ℤ) : WithTop ℤ) := by
  simp [ordOf, AddValuation.of_apply, hx]

/-- `ordOf w x ≥ m` iff `w x ≤ exp (-m)`. -/
theorem le_ordOf_iff (w : Valuation K ℤᵐ⁰) (x : K) (m : ℤ) :
    (m : WithTop ℤ) ≤ ordOf w x ↔ w x ≤ exp (-m) := by
  by_cases hx : x = 0
  · subst hx; simp [ordOf]
  rw [ordOf_apply w hx, WithTop.coe_le_coe, ← log_le_iff_le_exp ((Valuation.ne_zero_iff w).mpr hx)]
  omega

/-- The additive valuation of `K₀` at the prime `π` of `ℤ[s]`. -/
noncomputable def vP (π : Zs) (hπ : Prime π) : AddValuation K0 (WithTop ℤ) :=
  ordOf ((primeSpec π hπ).valuation K0)

theorem vP_apply {π : Zs} (hπ : Prime π) {x : K0} (hx : x ≠ 0) :
    vP π hπ x = (vp π x : WithTop ℤ) := by
  rw [vP, ordOf_apply _ hx, vp_def hπ]

/-- `vP π x ≥ m` in terms of the model chapter's `vp π` (with `vp π 0 = 0`). -/
theorem le_vP_iff {π : Zs} (hπ : Prime π) (x : K0) (m : ℤ) :
    (m : WithTop ℤ) ≤ vP π hπ x ↔ x = 0 ∨ m ≤ vp π x := by
  by_cases hx : x = 0
  · subst hx; simp
  rw [vP_apply hπ hx, WithTop.coe_le_coe]; simp [hx]

/-- Elements of `ℤ[s]` are integral at every prime. -/
theorem vP_toK0_nonneg {π : Zs} (hπ : Prime π) (a : Zs) : 0 ≤ vP π hπ (Zs.toK0 a) :=
  (le_vP_iff hπ _ 0).mpr (Or.inr (vp_nonneg hπ a))

/-- `v_{σπ}(y) = v_π(σ y)` for the additive valuations. -/
theorem vP_star {π : Zs} (hπ : Prime π) (y : K0) :
    vP (star π) (prime_star hπ) y = vP π hπ (star y) := by
  by_cases hy : y = 0
  · subst hy; simp
  have hsy : star y ≠ 0 := by rwa [ne_eq, star_eq_zero]
  rw [vP_apply _ hy, vP_apply _ hsy, vp_star hπ]

end ZInQ.Mult
