/-
STRUCTURAL MUST-FAIL: a finite set of arbitrary complex values is not the Qbar input.
Expected: type mismatch Set ℂ versus Set Qbar at the producer application.
This tests the literal Qbar/preimage boundary only. No transcendental witness is
constructed; algebraicity and fixed-place preimages remain explicit prior inputs.
-/
import FCF_Proof
open ClimbFiniteCoefficientField

example (s : Set ℂ) (hs : s.Finite) :
    FiniteDimensional ℚ (IntermediateField.adjoin ℚ s) := by
  exact finiteDimensional_fieldOf s hs
