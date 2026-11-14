import FieldAdapterCandidate
/- STRUCTURAL PROVENANCE FIXTURE (the matching MATHEMATICAL counterexample is the proved
   `nonzero_false_for_arbitrary_field_function` in the checks file).
   Shows: F3 is stated for the Units.val specialization only; an arbitrary field-valued β is a
   different statement the term does not inhabit. -/
open ClimbFieldAdapterExpected ClimbFieldAdapter GlueDescent.B2Q
example : ∀ (b : GQ → GlueC10.Qbar) (g : GQ), b g ≠ 0 := fieldNonzero
