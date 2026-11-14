import ANormalizationCandidate
/- STRUCTURAL APPLICATION FIXTURE (not a mathematical counterexample).
   Shows: the ℚ-level quartic multiplicativity is load-bearing — with it dropped the proved
   bundle does not inhabit the statement.
   Does NOT show: that the conclusion is false without it. -/
open ClimbANormalizationExpected ClimbANormalization
example : ∀ (G : Type) [Group G] (ρ : GlueC10.Qbar →ₐ[ℚ] ℂ) (d : G → ℚ) (c : G → G → ℚ),
    (∀ g, 0 < d g) → (∀ g h, c g h ≠ 0) →
    ∃ aQ : G → GlueC10.Qbar,
      (∀ g, ρ (aQ g) = aComplex (d g)) ∧
      (∀ g h, aQ g * aQ h * qbarOfRat (c g h) = qbarSign (c g h) * aQ (g * h)) :=
  bundledFixedPlaceNormalization
