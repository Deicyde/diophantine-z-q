import ANormalizationCandidate
/- STRUCTURAL INAPPLICABILITY FIXTURE (not a mathematical counterexample).
   Shows: algebraic closedness of the source field is load-bearing in the preimage lemma.
   Does NOT show: an explicit value with no ℚ-preimage (none is constructed here). -/
open ClimbANormalizationExpected ClimbANormalization
example (z : ℂ) (hz : IsAlgebraic ℚ z) : ∃ w : ℚ, (algebraMap ℚ ℂ) w = z :=
  algebraicValueHasPreimage ℚ (algebraMap ℚ ℂ) z hz
