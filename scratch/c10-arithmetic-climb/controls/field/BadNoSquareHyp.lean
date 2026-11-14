import FieldAdapterCandidate
/- STRUCTURAL APPLICATION FIXTURE (not a mathematical counterexample).
   Shows: F4 carries the GIVEN units-level square equation; with the hypothesis dropped the
   term does not inhabit the statement, so the square cannot be quietly manufactured. -/
open ClimbBetaExpected ClimbFieldAdapterExpected ClimbFieldAdapter GlueDescent.B2Q
example : ∀ (N : ℕ) [NeZero N] (χ₀ : DirichletCharacter GlueC10.Qbar N)
    (β₀ : GQ → GlueC10.Qbarˣ),
    ∀ g, (betaField β₀ g) ^ 2 = Units.val (galCharacter χ₀ g) := fieldSquare
