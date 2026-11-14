/-
STRUCTURAL MUST-FAIL: finite value image is not a supplied locally constant proof.
Expected type mismatch; this is not a mathematical LC counterexample witness.
The provider transfers GIVEN LC by injection, never derives it from finite range.
-/
import B2PackingProof
open ClimbB2CoefficientPacking

example (β₀ : GQ → Qbarˣ) (hf : (Set.range β₀).Finite) : IsLocallyConstant β₀ := by
  exact hf
