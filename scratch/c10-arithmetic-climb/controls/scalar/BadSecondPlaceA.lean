import ANormalizationCandidate
/- STRUCTURAL PLACE-MISMATCH FIXTURE (not a mathematical counterexample).
   Shows: the bundle is stated for the ONE caller-fixed place; a second place ρ' is a
   different statement the term does not inhabit.
   Does NOT show: that no aQ can satisfy two places. -/
open ClimbANormalizationExpected ClimbANormalization
example : ∀ (G : Type) [Group G] (ρ ρ' : GlueC10.Qbar →ₐ[ℚ] ℂ) (d : G → ℚ) (c : G → G → ℚ),
    (∀ g, 0 < d g) → (∀ g h, c g h ≠ 0) →
    (∀ g h, d g * d h = (c g h) ^ (4 : ℕ) * d (g * h)) →
    ∃ aQ : G → GlueC10.Qbar, ∀ g, ρ' (aQ g) = aComplex (d g) :=
  bundledFixedPlaceNormalization
