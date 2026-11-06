import Mathlib

/-!
# Mordell–Weil for the generator curve

Proposition 3.1 (`prop:generator`) combines a two-isogeny descent, a torsion bound by
reduction and a finite height search with the Mordell–Weil theorem. This file defines the
field `K₀`, the curve `E` and the statement `MordellWeilE` that `E(K₀)` is finitely
generated. It was a hypothesis of the main theorem until the descent proved it:
`ZInQ.mordellWeilE` in `ZInQKernel/Model/Descent/MordellWeil.lean`.
-/

namespace ZInQ

theorem not_isSquare_two_rat : ¬ IsSquare (2 : ℚ) := by
  rintro ⟨r, hr⟩
  apply irrational_sqrt_two
  refine ⟨|r|, ?_⟩
  have h2 : (r : ℝ) * r = 2 := by exact_mod_cast hr.symm
  rw [Rat.cast_abs, ← h2, Real.sqrt_mul_self_eq_abs]

instance : Fact (¬ IsSquare (2 : ℚ)) := ⟨not_isSquare_two_rat⟩

/-- `K₀ = ℚ(s)` with `s² = 2`. -/
abbrev K0 : Type := QuadraticAlgebra ℚ 2 0

/-- The element `s = √2` of `K₀`. -/
def sqrt2 : K0 := ⟨0, 1⟩

/-- `d = 75 - 53 s`. -/
def genD : K0 := ⟨75, -53⟩

/-- The generator curve `E : y² = x³ - d² x` over `K₀`. -/
def genCurve : WeierstrassCurve K0 where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := -genD ^ 2
  a₆ := 0

/-- **Hypothesis MW** (the Mordell–Weil theorem for `E/K₀`): `E(K₀)` is finitely generated. -/
def MordellWeilE : Prop := AddGroup.FG genCurve.toAffine.Point

end ZInQ
