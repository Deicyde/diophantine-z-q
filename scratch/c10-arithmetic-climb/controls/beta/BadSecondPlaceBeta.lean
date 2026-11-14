import BetaFixedPlace
/- STRUCTURAL PLACE-MISMATCH FIXTURE (not a mathematical counterexample).
   Shows: the proved transport is stated for the ONE caller-fixed place; a term proved for ρ
   does not inhabit a statement whose conclusion is read through a second place ρ'.
   Does NOT show: that no lift can be compatible with two places. -/
open GlueDescent.B2Q ClimbBetaExpected ClimbBetaFixedPlace
example : ∀ (N : ℕ) [NeZero N] (ρ ρ' : GlueC10.Qbar →ₐ[ℚ] ℂ)
    (χ₀ : DirichletCharacter GlueC10.Qbar N) (χ : DirichletCharacter ℂ N),
    (∀ a : ZMod N, ρ (χ₀ a) = χ a) →
    ∀ (β : GQ → ℂˣ), IsLocallyConstant β → (∀ g, β g ^ 2 = GlueDescent.B2Q.galChar χ g) →
      ∀ (ε₀ : GQ → GQ → GlueC10.Qbarˣ),
        (∀ g h, β g * β h = unitPlace ρ (ε₀ g h) * β (g * h)) →
        ∃ β₀ : GQ → GlueC10.Qbarˣ, ∀ g, unitPlace ρ' (β₀ g) = β g :=
  givenB2CoefficientTransport
