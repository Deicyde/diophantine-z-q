import ZInQKernel.Model.Descent.Torsion

/-!
# `P₀` has infinite order

Part of `model/generator.md` (Proposition 3.1): by the torsion theorem every point of finite
order of `E(K₀)` is killed by `2`, hence lies in `{O, (0,0), (d,0), (-d,0)}`; `P₀` is affine with
nonzero ordinate. This does not use the Mordell–Weil theorem.
-/

namespace ZInQ

open WeierstrassCurve WeierstrassCurve.Affine

/-- `[2] P₀ ≠ O`: `P₀` is not a two-torsion point, its ordinate being nonzero. -/
theorem two_nsmul_genP0_ne_zero : 2 • genP0 ≠ 0 := by
  rw [Ne, genCurve_two_torsion]
  rintro (h | h | h | h)
  · exact genP0_ne_zero h
  all_goals
    simp only [genP0, genT0, genTd, genTnegd, Point.mk, Point.some.injEq] at h
    exact genY0_ne_zero h.2

/-- **`P₀` has infinite order** (from the torsion theorem, without Mordell–Weil). -/
theorem genP0_not_isOfFinAddOrder : ¬ IsOfFinAddOrder genP0 := fun h =>
  two_nsmul_genP0_ne_zero (two_nsmul_eq_zero_of_isOfFinAddOrder h)

theorem addOrderOf_genP0 : addOrderOf genP0 = 0 :=
  addOrderOf_eq_zero genP0_not_isOfFinAddOrder

/-- `n ↦ ι(n)` is injective. -/
theorem iota_injective : Function.Injective iota :=
  iota_injective_of_addOrderOf_eq_zero addOrderOf_genP0

end ZInQ
