import ANormalizationCandidate
/- STRUCTURAL APPLICATION FIXTURE (not a mathematical counterexample; the genuine
   counterexample is the PROVED `quartic_fails_at_zero` in the checks file).
   Shows: positivity of the degrees is load-bearing in the application. -/
open ClimbANormalizationExpected ClimbANormalization
example : ∀ (G : Type) [Group G] (ρ : GlueC10.Qbar →ₐ[ℚ] ℂ) (d : G → ℚ) (c : G → G → ℚ),
    (∀ g h, c g h ≠ 0) →
    (∀ g h, d g * d h = (c g h) ^ (4 : ℕ) * d (g * h)) →
    ∃ aQ : G → GlueC10.Qbar, ∀ g, ρ (aQ g) = aComplex (d g) :=
  bundledFixedPlaceNormalization
