import CharacterDescent
/- NEGATIVE CONTROL A: the positivity guard is real. Applying the fixed-place descent at
   level 0 must fail for want of `NeZero 0`; it must NOT be silently derivable. -/
example (ρ : GlueC10.Qbar →ₐ[ℚ] ℂ) (χ : DirichletCharacter ℂ 0) :
    ∃ χ₀ : DirichletCharacter GlueC10.Qbar 0,
      (∀ a : ZMod 0, ρ (χ₀ a) = χ a) ∧ orderOf χ₀ = orderOf χ :=
  ClimbCharacterDescent.fixedPlaceDescent 0 ρ χ
