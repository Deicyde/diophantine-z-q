import FieldAdapterCandidate

/-!
Independent type guard for the field adapter, plus one PROVED counterexample.
Each example restates a predicate in full, without naming the Expected definition, and closes
it with the candidate theorem; then each is ascribed by name.
-/

open ClimbBetaExpected ClimbFieldAdapterExpected ClimbFieldAdapter GlueDescent.B2Q

-- F1
example : ∀ (β₀ : GQ → GlueC10.Qbarˣ) (ε₀ : GQ → GQ → GlueC10.Qbarˣ),
    (∀ g, betaField β₀ g = Units.val (β₀ g)) ∧
    (∀ g h, epsField ε₀ g h = Units.val (ε₀ g h)) := fieldValuedBeta

-- F2
example : ∀ (β₀ : GQ → GlueC10.Qbarˣ) (ε₀ : GQ → GQ → GlueC10.Qbarˣ),
    (∀ g h, β₀ g * β₀ h = ε₀ g h * β₀ (g * h)) →
    ∀ g h, betaField β₀ g * betaField β₀ h = epsField ε₀ g h * betaField β₀ (g * h) :=
  fieldCochain

-- F3
example : ∀ (β₀ : GQ → GlueC10.Qbarˣ) (g : GQ), betaField β₀ g ≠ 0 := fieldNonzero

-- F4
example : ∀ (N : ℕ) [NeZero N] (χ₀ : DirichletCharacter GlueC10.Qbar N)
    (β₀ : GQ → GlueC10.Qbarˣ), (∀ g, β₀ g ^ 2 = galCharacter χ₀ g) →
    ∀ g, (betaField β₀ g) ^ 2 = Units.val (galCharacter χ₀ g) := fieldSquare

-- F5 (conditional)
example : ∀ (β₀ : GQ → GlueC10.Qbarˣ) (ε₀ : GQ → GQ → GlueC10.Qbarˣ),
    (∀ g h, β₀ g * β₀ h = ε₀ g h * β₀ (g * h)) → ε₀ 1 1 = 1 → betaField β₀ 1 = 1 :=
  fieldNormalizedAtOne

-- F6 (outside the frozen five)
example : ∀ (ρ : GlueC10.Qbar →ₐ[ℚ] ℂ) (β₀ : GQ → GlueC10.Qbarˣ)
    (ε₀ : GQ → GQ → GlueC10.Qbarˣ) (β : GQ → ℂˣ) (ε : GQ → GQ → ℂˣ),
    (∀ g, unitPlace ρ (β₀ g) = β g) → (∀ g h, unitPlace ρ (ε₀ g h) = ε g h) →
    (∀ g, ρ (betaField β₀ g) = Units.val (β g)) ∧
    (∀ g h, ρ (epsField ε₀ g h) = Units.val (ε g h)) := fieldPlaceImages

-- carrier identity
example : GlueC10.GQ = GlueDescent.B2Q.GQ := gqIdentity

-- by-name ascriptions
example : ClimbFieldAdapterExpected.FieldValuedBeta := fieldValuedBeta
example : ClimbFieldAdapterExpected.FieldCochain := fieldCochain
example : ClimbFieldAdapterExpected.FieldNonzero := fieldNonzero
example : ClimbFieldAdapterExpected.FieldSquare := fieldSquare
example : ClimbFieldAdapterExpected.FieldNormalizedAtOne := fieldNormalizedAtOne
example : ClimbFieldAdapterExpected.FieldPlaceImages := fieldPlaceImages
example : ClimbFieldAdapterExpected.GQIdentity := gqIdentity

/-- **PROVED counterexample (mathematics, not a structural fixture).** F3 is free only because
of the `Units.val` provenance: the same statement for an ARBITRARY field-valued function is
false, witnessed by the constant `0`. This is the contract's audit item 1. -/
theorem nonzero_false_for_arbitrary_field_function :
    ¬ (∀ (b : GQ → GlueC10.Qbar) (g : GQ), b g ≠ 0) := by
  intro h
  exact h (fun _ => 0) 1 rfl

#print axioms nonzero_false_for_arbitrary_field_function
