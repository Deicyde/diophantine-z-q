import CharacterDescent

/-!
EVIDENCE SUPPLEMENT (added after review of CharacterDescent.lean b21abc3…; that file's bytes
are unchanged). Two jobs only:

* a cheap POSITIVE boundary application of the actual `GlueDescent.chi` at the smallest
  levels its existing guard admits (`Tm = ∅`, level 1; `Tm = T = {2}`, level 4);
* a complete axiom/type report over EVERY declaration of `ClimbCharacterDescent`
  (12 declarations), not only the 8 roots reported in the candidate file.

No new mathematics, no functional/Tate/β construction, no C10 claim.
-/

open ClimbCharacterDescent

/-! ## Positive boundary: the actual character at the smallest admissible levels -/

example : GlueDescent.chiLevel (∅ : Finset ℕ) = 1 := by
  simp [GlueDescent.chiLevel]

/-- `Tm = ∅`: level 1, the guard `0 < chiLevel ∅` holds, and the descent applies. -/
example (ρ : GlueC10.Qbar →ₐ[ℚ] ℂ) :
    ∃ χ₀ : DirichletCharacter GlueC10.Qbar (GlueDescent.chiLevel ∅),
      (∀ a : ZMod (GlueDescent.chiLevel ∅), ρ (χ₀ a) = GlueDescent.chi ∅ a) ∧
      orderOf χ₀ = orderOf (GlueDescent.chi ∅) ∧
      orderOf χ₀ ≤ 2 * ∏ p ∈ (∅ : Finset ℕ).filter (· ≠ 2), (p - 1) :=
  actualGlueCharacter ∅ ∅ (by simp) (by simp) ρ

example : GlueDescent.chiLevel ({2} : Finset ℕ) = 4 := by
  simp [GlueDescent.chiLevel, GlueDescent.lev]

/-- `Tm = T = {2}`: level `lev 2 = 4`, the prime hypothesis is the actual one. -/
example (ρ : GlueC10.Qbar →ₐ[ℚ] ℂ) :
    ∃ χ₀ : DirichletCharacter GlueC10.Qbar (GlueDescent.chiLevel {2}),
      (∀ a : ZMod (GlueDescent.chiLevel {2}), ρ (χ₀ a) = GlueDescent.chi {2} a) ∧
      orderOf χ₀ = orderOf (GlueDescent.chi {2}) ∧
      orderOf χ₀ ≤ 2 * ∏ p ∈ ({2} : Finset ℕ).filter (· ≠ 2), (p - 1) :=
  actualGlueCharacter {2} {2} (by norm_num) (by simp) ρ

/-- The guard at those levels is satisfied, not bypassed. -/
example : 0 < GlueDescent.chiLevel (∅ : Finset ℕ) := chiLevel_pos (T := ∅) (by simp) (by simp)
example : 0 < GlueDescent.chiLevel ({2} : Finset ℕ) :=
  chiLevel_pos (T := {2}) (by norm_num) (by simp)

/-! ## Complete type report: all 12 declarations of the namespace -/

#check @ClimbCharacterDescent.exists_preimage_of_pow_eq_one
#check @ClimbCharacterDescent.exists_preimage_value
#check @ClimbCharacterDescent.descend
#check @ClimbCharacterDescent.descend_apply
#check @ClimbCharacterDescent.ringHomComp_descend
#check @ClimbCharacterDescent.descend_nonunit
#check @ClimbCharacterDescent.ringHomCompHom_injective
#check @ClimbCharacterDescent.orderOf_descend
#check @ClimbCharacterDescent.fixedPlaceDescent
#check @ClimbCharacterDescent.fixedPlaceOddness
#check @ClimbCharacterDescent.chiLevel_pos
#check @ClimbCharacterDescent.actualGlueCharacter

/-! ## Complete axiom report: all 12 declarations (the candidate file printed 8) -/

#print axioms ClimbCharacterDescent.exists_preimage_of_pow_eq_one
#print axioms ClimbCharacterDescent.exists_preimage_value
#print axioms ClimbCharacterDescent.descend
#print axioms ClimbCharacterDescent.descend_apply
#print axioms ClimbCharacterDescent.ringHomComp_descend
#print axioms ClimbCharacterDescent.descend_nonunit
#print axioms ClimbCharacterDescent.ringHomCompHom_injective
#print axioms ClimbCharacterDescent.orderOf_descend
#print axioms ClimbCharacterDescent.fixedPlaceDescent
#print axioms ClimbCharacterDescent.fixedPlaceOddness
#print axioms ClimbCharacterDescent.chiLevel_pos
#print axioms ClimbCharacterDescent.actualGlueCharacter
