import FieldAdapterCandidate
/- STRUCTURAL PLACE-MISMATCH FIXTURE (not a mathematical counterexample).
   Shows: the retained images are for the ONE caller-fixed place; a second place ρ' is a
   different statement the term does not inhabit. -/
open ClimbBetaExpected ClimbFieldAdapterExpected ClimbFieldAdapter GlueDescent.B2Q
example : ∀ (ρ ρ' : GlueC10.Qbar →ₐ[ℚ] ℂ) (β₀ : GQ → GlueC10.Qbarˣ)
    (ε₀ : GQ → GQ → GlueC10.Qbarˣ) (β : GQ → ℂˣ) (ε : GQ → GQ → ℂˣ),
    (∀ g, unitPlace ρ (β₀ g) = β g) → (∀ g h, unitPlace ρ (ε₀ g h) = ε g h) →
    (∀ g, ρ' (betaField β₀ g) = Units.val (β g)) ∧
    (∀ g h, ρ' (epsField ε₀ g h) = Units.val (ε g h)) := fieldPlaceImages
