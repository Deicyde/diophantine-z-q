/-
STRUCTURAL MUST-FAIL: missing supplied set-finiteness certificate.
Expected: type mismatch; the theorem still requires s.Finite.
Not a mathematical counterexample or a proof of necessity for every subset.
Run only after FCF_Proof imports successfully; retain exact source and diagnostics.
-/
import FCF_Proof
open ClimbFiniteCoefficientField

example (s : Set Qbar) : FiniteDimensional ℚ (fieldOf s) := by
  exact finiteDimensional_fieldOf s
