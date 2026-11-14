import CharacterDescent
/- NEGATIVE CONTROL D: algebraic closedness of the coefficient field is load-bearing.
   The same values have no preimage in ℚ, and the value lemma must not apply there. -/
example (n : ℕ) [NeZero n] (χ : DirichletCharacter ℂ n) (a : ZMod n) :
    ∃ w : ℚ, (algebraMap ℚ ℂ) w = χ a :=
  ClimbCharacterDescent.exists_preimage_value (algebraMap ℚ ℂ) n χ a
