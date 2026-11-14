import CharacterDescent
/- NEGATIVE CONTROL B: the place is fixed. One descended character cannot be claimed to
   reproduce the same complex character through two arbitrary places at once. -/
example : ∀ (n : ℕ) [NeZero n] (ρ ρ' : GlueC10.Qbar →ₐ[ℚ] ℂ) (χ : DirichletCharacter ℂ n),
    ∃ χ₀ : DirichletCharacter GlueC10.Qbar n,
      (∀ a : ZMod n, ρ (χ₀ a) = χ a) ∧ (∀ a : ZMod n, ρ' (χ₀ a) = χ a) :=
  ClimbCharacterDescent.fixedPlaceDescent
