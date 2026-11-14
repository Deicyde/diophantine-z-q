import CharacterDescent

/-!
Independent type/spec guard for the candidate. Each `example` restates the intended
statement in full, WITHOUT naming the `ClimbCharacterExpected` definitions, and closes it
with the candidate theorem: this checks the actual proved types, not just the def names.
-/

open ClimbCharacterDescent

-- (1) fixed-place descent, written out
example : ∀ (n : ℕ) [NeZero n] (ρ : GlueC10.Qbar →ₐ[ℚ] ℂ) (χ : DirichletCharacter ℂ n),
    ∃ χ₀ : DirichletCharacter GlueC10.Qbar n,
      (∀ a : ZMod n, ρ (χ₀ a) = χ a) ∧ orderOf χ₀ = orderOf χ :=
  fixedPlaceDescent

-- (2) oddness, written out
example : ∀ (n : ℕ) [NeZero n] (ρ : GlueC10.Qbar →ₐ[ℚ] ℂ) (χ : DirichletCharacter ℂ n),
    χ (-1) = -1 →
      ∃ χ₀ : DirichletCharacter GlueC10.Qbar n,
        (∀ a : ZMod n, ρ (χ₀ a) = χ a) ∧ χ₀ (-1) = -1 ∧ orderOf χ₀ = orderOf χ :=
  fixedPlaceOddness

-- (3) the actual GlueDescent character, its own level and its own order bound, written out
example : ∀ (T Tm : Finset ℕ), (∀ p ∈ T, p.Prime) → Tm ⊆ T →
    ∀ (ρ : GlueC10.Qbar →ₐ[ℚ] ℂ),
      ∃ χ₀ : DirichletCharacter GlueC10.Qbar (GlueDescent.chiLevel Tm),
        (∀ a : ZMod (GlueDescent.chiLevel Tm), ρ (χ₀ a) = GlueDescent.chi Tm a) ∧
        orderOf χ₀ = orderOf (GlueDescent.chi Tm) ∧
        orderOf χ₀ ≤ 2 * ∏ p ∈ T.filter (· ≠ 2), (p - 1) :=
  actualGlueCharacter

-- (4) the spec module's own definitions are the ones proved
example : ClimbCharacterExpected.FixedPlaceDescent := fixedPlaceDescent
example : ClimbCharacterExpected.FixedPlaceOddness := fixedPlaceOddness
example : ClimbCharacterExpected.ActualGlueCharacter := actualGlueCharacter

-- (5) zero/non-unit values are preserved by the descent (definitional for any MulChar)
example {R : Type*} [CommMonoid R] {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) (hf : Function.Injective f) (χ : MulChar R L)
    (h : ∀ a : R, ∃ w : K, f w = χ a) {a : R} (ha : ¬ IsUnit a) :
    descend f hf χ h a = 0 := descend_nonunit f hf χ h ha

-- (6) the descent really is a section of `ringHomComp` along the SAME f
example {R : Type*} [CommMonoid R] {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) (hf : Function.Injective f) (χ : MulChar R L)
    (h : ∀ a : R, ∃ w : K, f w = χ a) :
    (descend f hf χ h).ringHomComp f = χ := ringHomComp_descend f hf χ h

-- (7) level is literally unchanged: the descended character has the same ZMod domain
example (Tm : Finset ℕ) (χ₀ : DirichletCharacter GlueC10.Qbar (GlueDescent.chiLevel Tm)) :
    MulChar (ZMod (GlueDescent.chiLevel Tm)) GlueC10.Qbar := χ₀
