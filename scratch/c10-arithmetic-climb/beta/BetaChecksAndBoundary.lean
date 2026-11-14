import BetaFixedPlace

/-!
Independent type/spec guard and positive boundary applications for the β transport.
Every `example` restates the statement in full (not by spec-definition name) and closes it
with the candidate theorem. The β-side is never constructed here: at level 4 the given β is a
binder, exactly as the B2 source supplies it.
-/

open GlueDescent GlueDescent.B2 GlueDescent.B2Q ClimbBetaExpected ClimbBetaFixedPlace

-- (1) the transport target, written out
example : ∀ (N : ℕ) [NeZero N] (ρ : GlueC10.Qbar →ₐ[ℚ] ℂ)
    (χ₀ : DirichletCharacter GlueC10.Qbar N) (χ : DirichletCharacter ℂ N),
    (∀ a : ZMod N, ρ (χ₀ a) = χ a) →
    ∀ (β : GQ → ℂˣ), IsLocallyConstant β → (∀ g, β g ^ 2 = galChar χ g) →
      ∀ (ε₀ : GQ → GQ → GlueC10.Qbarˣ),
        (∀ g h, β g * β h = unitPlace ρ (ε₀ g h) * β (g * h)) →
        ∃ β₀ : GQ → GlueC10.Qbarˣ,
          (∀ g, unitPlace ρ (β₀ g) = β g) ∧ IsLocallyConstant β₀ ∧
          (∀ g, β₀ g ^ 2 = galCharacter χ₀ g) ∧
          (∀ g h, β₀ g * β₀ h = ε₀ g h * β₀ (g * h)) ∧
          (∀ g, (β₀ g : GlueC10.Qbar) ≠ 0) :=
  givenB2CoefficientTransport

-- (2) the separate normalization condition, written out
example : ∀ (ε₀ : GQ → GQ → GlueC10.Qbarˣ) (β₀ : GQ → GlueC10.Qbarˣ),
    (∀ g h, β₀ g * β₀ h = ε₀ g h * β₀ (g * h)) → ε₀ 1 1 = 1 → β₀ 1 = 1 :=
  normalizationFromUnitEquation

-- (3) the spec module's own definitions are the ones proved
example : ClimbBetaExpected.GivenB2CoefficientTransport := givenB2CoefficientTransport
example : ClimbBetaExpected.NormalizationFromUnitEquation := normalizationFromUnitEquation

/-- The level guards at the two boundary levels, DERIVED (not assumed) from the existing
primality hypotheses through the character lane's `chiLevel_pos`. -/
local instance neZero_chiLevel_empty : NeZero (GlueDescent.chiLevel (∅ : Finset ℕ)) :=
  NeZero.of_pos (ClimbCharacterDescent.chiLevel_pos (T := ∅) (by simp) (by simp))

local instance neZero_chiLevel_two : NeZero (GlueDescent.chiLevel ({2} : Finset ℕ)) :=
  NeZero.of_pos (ClimbCharacterDescent.chiLevel_pos (T := {2}) (by norm_num) (by simp))

-- (4) POSITIVE boundary, actual level 1 (`Tm = ∅`): the actual character, its actual descent,
-- and a given β with its given equations.
example (ρ : GlueC10.Qbar →ₐ[ℚ] ℂ)
    (β : GQ → ℂˣ) (hlc : IsLocallyConstant β)
    (hsq : ∀ g, β g ^ 2 = galChar (GlueDescent.chi ∅) g)
    (ε₀ : GQ → GQ → GlueC10.Qbarˣ)
    (hco : ∀ g h, β g * β h = unitPlace ρ (ε₀ g h) * β (g * h)) :
    ∃ (χ₀ : DirichletCharacter GlueC10.Qbar (GlueDescent.chiLevel ∅))
      (β₀ : GQ → GlueC10.Qbarˣ),
      (∀ g, unitPlace ρ (β₀ g) = β g) ∧ IsLocallyConstant β₀ ∧
      (∀ g, β₀ g ^ 2 = galCharacter χ₀ g) ∧
      (∀ g h, β₀ g * β₀ h = ε₀ g h * β₀ (g * h)) := by
  obtain ⟨χ₀, hχ, -, -⟩ := ClimbCharacterDescent.actualGlueCharacter ∅ ∅ (by simp) (by simp) ρ
  obtain ⟨β₀, h1, h2, h3, h4, -⟩ :=
    givenB2CoefficientTransport _ ρ χ₀ (GlueDescent.chi ∅) hχ β hlc hsq ε₀ hco
  exact ⟨χ₀, β₀, h1, h2, h3, h4⟩

-- (5) POSITIVE boundary, actual level 4 (`Tm = T = {2}`, `lev 2 = 4`), same shape.
example (ρ : GlueC10.Qbar →ₐ[ℚ] ℂ)
    (β : GQ → ℂˣ) (hlc : IsLocallyConstant β)
    (hsq : ∀ g, β g ^ 2 = galChar (GlueDescent.chi {2}) g)
    (ε₀ : GQ → GQ → GlueC10.Qbarˣ)
    (hco : ∀ g h, β g * β h = unitPlace ρ (ε₀ g h) * β (g * h)) :
    ∃ (χ₀ : DirichletCharacter GlueC10.Qbar (GlueDescent.chiLevel {2}))
      (β₀ : GQ → GlueC10.Qbarˣ),
      (∀ g, unitPlace ρ (β₀ g) = β g) ∧ IsLocallyConstant β₀ ∧
      (∀ g, β₀ g ^ 2 = galCharacter χ₀ g) ∧
      (∀ g h, β₀ g * β₀ h = ε₀ g h * β₀ (g * h)) ∧
      orderOf χ₀ ≤ 2 * ∏ p ∈ ({2} : Finset ℕ).filter (· ≠ 2), (p - 1) := by
  obtain ⟨χ₀, hχ, -, hord⟩ :=
    ClimbCharacterDescent.actualGlueCharacter {2} {2} (by norm_num) (by simp) ρ
  obtain ⟨β₀, h1, h2, h3, h4, -⟩ :=
    givenB2CoefficientTransport _ ρ χ₀ (GlueDescent.chi {2}) hχ β hlc hsq ε₀ hco
  exact ⟨χ₀, β₀, h1, h2, h3, h4, hord⟩

-- (6) the ε-side lift is from the SOURCE sign condition only
example (ρ : GlueC10.Qbar →ₐ[ℚ] ℂ) (ε : GQ → GQ → ℂˣ) (hε : IsSignCocycle ε) :
    ∃ ε₀ : GQ → GQ → GlueC10.Qbarˣ,
      (∀ g h, unitPlace ρ (ε₀ g h) = ε g h) ∧ IsSignCocycle ε₀ :=
  exists_signCocycle_lift ρ ε hε
