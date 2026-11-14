import BetaFixedPlace
/- STRUCTURAL SOURCE-CONDITION FIXTURE (not a mathematical counterexample).
   Shows: the ε-side lift is derived from the SOURCE IsSignCocycle condition (its values are
   square roots of 1); dropping that condition makes the term ill-typed, so no ε is invented.
   Does NOT show: that an arbitrary complex 2-cochain cannot be lifted by some other route. -/
open GlueDescent.B2Q ClimbBetaExpected ClimbBetaFixedPlace
example : ∀ (ρ : GlueC10.Qbar →ₐ[ℚ] ℂ) (ε : GQ → GQ → ℂˣ),
    ∃ ε₀ : GQ → GQ → GlueC10.Qbarˣ, ∀ g h, unitPlace ρ (ε₀ g h) = ε g h :=
  exists_signCocycle_lift
