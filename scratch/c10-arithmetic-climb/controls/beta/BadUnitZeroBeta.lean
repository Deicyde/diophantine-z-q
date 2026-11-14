import BetaFixedPlace
/- STRUCTURAL UNIT/ZERO FIXTURE (not a mathematical counterexample).
   Shows: the transported datum is unit-valued on both sides — a β supplied as a plain
   ℂ-valued function (which may vanish) does not typecheck against the proved statement, so
   the Units.val bridge is not bypassable.
   Does NOT show: that a zero-admitting transport statement is false. -/
open GlueDescent.B2Q ClimbBetaExpected ClimbBetaFixedPlace
example (N : ℕ) [NeZero N] (ρ : GlueC10.Qbar →ₐ[ℚ] ℂ)
    (χ₀ : DirichletCharacter GlueC10.Qbar N) (χ : DirichletCharacter ℂ N)
    (hχ : ∀ a : ZMod N, ρ (χ₀ a) = χ a)
    (β : GQ → ℂ) (hlc : IsLocallyConstant β) (hsq : ∀ g, β g ^ 2 = galChar χ g)
    (ε₀ : GQ → GQ → GlueC10.Qbarˣ)
    (hco : ∀ g h, β g * β h = unitPlace ρ (ε₀ g h) * β (g * h)) :
    ∃ β₀ : GQ → GlueC10.Qbarˣ, ∀ g, unitPlace ρ (β₀ g) = β g := by
  obtain ⟨β₀, h, -⟩ := givenB2CoefficientTransport N ρ χ₀ χ hχ β hlc hsq ε₀ hco
  exact ⟨β₀, h⟩
