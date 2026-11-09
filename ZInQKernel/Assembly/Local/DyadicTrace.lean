import ZInQKernel.Multiplication.Local

/-!
# Valuation and trace at the prime `(s)`

Blueprint: `assembly/local-tests/dyadic-trace.md`.

Let `v_s = vp sqrt2Z` be the valuation of `K₀` at `(s)` (`v_s(2) = 2`), `σ = star` the
conjugation and `Tr x = x + σ x = QuadraticAlgebra.trace x ∈ ℚ`. Then

1. `v_s(σ x) = v_s(x)` (`vS_star`);
2. if `v_s(x) ≥ 2k` then `v₂(Tr x) ≥ k + 1` (`vS_trace_ge`).

With the model chapter's convention `vp π 0 = 0` and `padicValRat 2 0 = 0`, item 2 is stated as
`Tr x = 0 ∨ k + 1 ≤ v₂(Tr x)`, as for odd primes (`ZInQ.Mult.vp_trace_ge`).
-/

namespace ZInQ.Assembly

open ZInQ.Mult

theorem star_sqrt2Z : star sqrt2Z = -sqrt2Z := by
  ext <;> simp [sqrt2Z]

/-- **Item 1.** `v_s(σ x) = v_s(x)`. -/
theorem vS_star (x : K0) : vp sqrt2Z (star x) = vp sqrt2Z x := by
  rw [← vp_star prime_sqrt2Z, star_sqrt2Z,
    ← vp_eq_of_associated (Associated.refl sqrt2Z).neg_right]

/-- Item 1 for the additive valuation `vS`. -/
theorem vS_star' (x : K0) : vS (star x) = vS x := by
  by_cases hx : x = 0
  · rw [hx, star_zero]
  rw [vP_apply _ hx, vP_apply _ (by rwa [ne_eq, star_eq_zero]), vS_star]

/-- **Item 2.** If `v_s(x) ≥ 2k` then `v₂(Tr x) ≥ k + 1` (or `Tr x = 0`). -/
theorem vS_trace_ge {x : K0} {k : ℤ} (hx : 2 * k ≤ vp sqrt2Z x) :
    QuadraticAlgebra.trace x = 0 ∨ k + 1 ≤ padicValRat 2 (QuadraticAlgebra.trace x) := by
  rw [K0.trace_eq]
  by_cases ha : x.re = 0
  · left; rw [ha, mul_zero]
  right
  have hf := vS_formula_withTop (c₀ := x.re) (c₁ := x.im) (Or.inl ha)
  rw [show (⟨x.re, x.im⟩ : K0) = x from rfl] at hf
  have h1 : ((2 * k : ℤ) : WithTop ℤ) ≤ ((2 * padicValRat 2 x.re : ℤ) : WithTop ℤ) :=
    calc ((2 * k : ℤ) : WithTop ℤ) ≤ ((vp sqrt2Z x : ℤ) : WithTop ℤ) := by exact_mod_cast hx
      _ = min (2 * v2Top x.re) (2 * v2Top x.im + 1) := hf
      _ ≤ 2 * v2Top x.re := min_le_left _ _
      _ = _ := by simp only [v2Top, ha, ite_false]; norm_cast
  have h2 := WithTop.coe_le_coe.mp h1
  have h22 : padicValRat 2 (2 : ℚ) = 1 := by
    have := padicValRat.self (p := 2) one_lt_two; simpa using this
  rw [padicValRat.mul (by norm_num) ha, h22]
  omega

end ZInQ.Assembly
