import FieldAdapterExpected
import BetaFixedPlace

/-!
# Candidate: C10 field adapter (B-G1)

PRIVATE CANDIDATE. Proves the six predicates of `ClimbFieldAdapterExpected`
(`FieldAdapterExpected.lean`, sha256
7210310608ec45965a27f3237d0b11029517ca1f1ae1f3b4685dea01fbc7ac6a, definitions only) plus the
carrier identity, and nothing else. The Expected file is imported as compiled and is NOT
edited.

The whole mathematical content is `Units.val`: `β₀` and `ε₀` are GIVEN units-valued data (the
frozen β lane's output shape, itself conditional on the four B2 leaves and the given
`L`/`ε`/`T`), and this module only carries their equations into the field. Nothing is
constructed: no B2, no `ε`, no `c`, no `a`, no `χ`, no `T`, no `af`, no global tuple.

`C := GlueC10.Qbar` is an ASCRIPTION. It is not a selection of the consumer's `C`, and these
predicates do not let `GlueC10Link.c10_of_squares` be applied: its `C`, `β`, `ε`, `c`, `a`
binders remain OPEN. `hβ1` is delivered only under the explicit `ε₀ 1 1 = 1`. No local
constancy or continuity appears here (120c 176394), and no preimage/algebraicity machinery is
re-derived (character, β and a-σ lanes own it).
-/

noncomputable section

open ClimbBetaExpected ClimbFieldAdapterExpected GlueDescent.B2Q

namespace ClimbFieldAdapter

/-! ## Carrier identity, discharged before any call -/

theorem gqIdentity : ClimbFieldAdapterExpected.GQIdentity := rfl

/-! ## F1 — the specializations are literally the unit coercions -/

theorem fieldValuedBeta : ClimbFieldAdapterExpected.FieldValuedBeta :=
  fun _ _ => ⟨fun _ => rfl, fun _ _ => rfl⟩

/-! ## F2 — the cochain equation in the field -/

theorem fieldCochain : ClimbFieldAdapterExpected.FieldCochain := by
  intro β₀ ε₀ hco g h
  have := congrArg (Units.val : GlueC10.Qbarˣ → GlueC10.Qbar) (hco g h)
  simpa [betaField, epsField] using this

/-! ## F3 — nonvanishing, free from the unit provenance -/

theorem fieldNonzero : ClimbFieldAdapterExpected.FieldNonzero :=
  fun β₀ g => (β₀ g).ne_zero

/-! ## F4 — the square equation in the field -/

theorem fieldSquare : ClimbFieldAdapterExpected.FieldSquare := by
  intro N _ χ₀ β₀ hsq g
  have := congrArg (Units.val : GlueC10.Qbarˣ → GlueC10.Qbar) (hsq g)
  simpa [betaField] using this

/-! ## F5 — normalization, only under the explicit units-level datum -/

theorem fieldNormalizedAtOne : ClimbFieldAdapterExpected.FieldNormalizedAtOne := by
  intro β₀ ε₀ hco hε
  have h1 : β₀ 1 = 1 := ClimbBetaFixedPlace.normalizationFromUnitEquation ε₀ β₀ hco hε
  rw [betaField, h1, Units.val_one]

/-! ## F6 — the literal fixed-`ρ` images are retained (outside the frozen five) -/

theorem fieldPlaceImages : ClimbFieldAdapterExpected.FieldPlaceImages := by
  intro ρ β₀ ε₀ β ε hβ hε
  constructor
  · intro g
    have := congrArg (Units.val : ℂˣ → ℂ) (hβ g)
    simpa [betaField, unitPlace] using this
  · intro g h
    have := congrArg (Units.val : ℂˣ → ℂ) (hε g h)
    simpa [epsField, unitPlace] using this

end ClimbFieldAdapter

/-! ## Reports -/

#print axioms ClimbFieldAdapter.gqIdentity
#print axioms ClimbFieldAdapter.fieldValuedBeta
#print axioms ClimbFieldAdapter.fieldCochain
#print axioms ClimbFieldAdapter.fieldNonzero
#print axioms ClimbFieldAdapter.fieldSquare
#print axioms ClimbFieldAdapter.fieldNormalizedAtOne
#print axioms ClimbFieldAdapter.fieldPlaceImages

#check @ClimbFieldAdapter.gqIdentity
#check @ClimbFieldAdapter.fieldValuedBeta
#check @ClimbFieldAdapter.fieldCochain
#check @ClimbFieldAdapter.fieldNonzero
#check @ClimbFieldAdapter.fieldSquare
#check @ClimbFieldAdapter.fieldNormalizedAtOne
#check @ClimbFieldAdapter.fieldPlaceImages
