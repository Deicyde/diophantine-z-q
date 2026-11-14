import BetaFixedPlace
/- STRUCTURAL NORMALIZATION FIXTURE (not a mathematical counterexample).
   Shows: β₀ 1 = 1 is NOT obtainable from the cochain equation alone; the proved statement
   needs the explicit ε₀ 1 1 = 1 condition, which GlueDescent.B2.IsSignCocycle does not give.
   Does NOT show: that β₀ 1 ≠ 1 for the actual B2 datum. -/
open GlueDescent.B2Q ClimbBetaExpected ClimbBetaFixedPlace
example : ∀ (ε₀ : GQ → GQ → GlueC10.Qbarˣ) (β₀ : GQ → GlueC10.Qbarˣ),
    (∀ g h, β₀ g * β₀ h = ε₀ g h * β₀ (g * h)) → β₀ 1 = 1 :=
  normalizationFromUnitEquation
