import FieldAdapterCandidate
/- STRUCTURAL NORMALIZATION FIXTURE (not a mathematical counterexample).
   Shows: βF 1 = 1 is not obtainable from the cochain equation alone; the explicit
   ε₀ 1 1 = 1 is required, as the contract demands.
   Does NOT show: that βF 1 ≠ 1 for the actual datum. -/
open ClimbFieldAdapterExpected ClimbFieldAdapter GlueDescent.B2Q
example : ∀ (β₀ : GQ → GlueC10.Qbarˣ) (ε₀ : GQ → GQ → GlueC10.Qbarˣ),
    (∀ g h, β₀ g * β₀ h = ε₀ g h * β₀ (g * h)) → betaField β₀ 1 = 1 :=
  fieldNormalizedAtOne
