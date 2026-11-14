import CharacterDescent
/- NEGATIVE CONTROL C: the actual consumer's primality hypotheses are load-bearing; the
   order bound must not be obtainable without `∀ p ∈ T, p.Prime`. -/
example : ∀ (T Tm : Finset ℕ), Tm ⊆ T → ∀ (ρ : GlueC10.Qbar →ₐ[ℚ] ℂ),
    ∃ χ₀ : DirichletCharacter GlueC10.Qbar (GlueDescent.chiLevel Tm),
      (∀ a : ZMod (GlueDescent.chiLevel Tm), ρ (χ₀ a) = GlueDescent.chi Tm a) ∧
      orderOf χ₀ ≤ 2 * ∏ p ∈ T.filter (· ≠ 2), (p - 1) :=
  ClimbCharacterDescent.actualGlueCharacter
