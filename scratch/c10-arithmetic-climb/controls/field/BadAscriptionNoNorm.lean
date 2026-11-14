import C10AscriptionCandidate
/- STRUCTURAL FIXTURE (not a mathematical counterexample).
   Shows: the ε₀ 1 1 = 1 premise is load-bearing in the ascription — with it dropped the
   proved term does not inhabit the statement, so hβ1 cannot be slipped in.
   Does NOT show: that the conclusion is false without it. -/
open GlueDescent GlueC10 PkgI3 GlueC10Link ClimbFieldAdapterExpected ClimbC10Ascription
example : ∀ (β₀ : GQ → GlueC10.Qbarˣ) (ε₀ : GQ → GQ → GlueC10.Qbarˣ),
    (∀ g h, β₀ g * β₀ h = ε₀ g h * β₀ (g * h)) →
    (∀ g h, betaField β₀ g * betaField β₀ h = epsField ε₀ g h * betaField β₀ (g * h)) ∧
    (∀ g, betaField β₀ g ≠ 0) ∧ betaField β₀ 1 = 1 := slotsAreAdapterTheorems
