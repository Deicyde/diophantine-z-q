import BetaFixedPlace
/- STRUCTURAL GUARD-REJECTION FIXTURE (not a mathematical counterexample).
   Shows: the level guard is load-bearing in this application — at N = 0 the transport cannot
   be applied and NeZero 0 is not silently derivable.
   Does NOT show: that a level-0 transport is false. -/
open GlueDescent.B2Q ClimbBetaExpected ClimbBetaFixedPlace
example (ρ : GlueC10.Qbar →ₐ[ℚ] ℂ) (χ₀ : DirichletCharacter GlueC10.Qbar 0)
    (χ : DirichletCharacter ℂ 0) (hχ : ∀ a : ZMod 0, ρ (χ₀ a) = χ a)
    (β : GQ → ℂˣ) (hlc : IsLocallyConstant β) (hsq : ∀ g, β g ^ 2 = galChar χ g)
    (ε₀ : GQ → GQ → GlueC10.Qbarˣ)
    (hco : ∀ g h, β g * β h = unitPlace ρ (ε₀ g h) * β (g * h)) :
    ∃ β₀ : GQ → GlueC10.Qbarˣ, ∀ g, unitPlace ρ (β₀ g) = β g := by
  obtain ⟨β₀, h, -⟩ := givenB2CoefficientTransport 0 ρ χ₀ χ hχ β hlc hsq ε₀ hco
  exact ⟨β₀, h⟩
