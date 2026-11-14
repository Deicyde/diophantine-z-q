/-
STRUCTURAL MUST-FAIL: omit the original sign-cocycle certificate.
Expected type mismatch; epsilonValues_finite still awaits IsSignCocycle.
The range proof uses its supplied square projection, not finite GQ/pairs.
-/
import B2PackingProof
open ClimbB2CoefficientPacking

example (ε₀ : GQ → GQ → Qbarˣ) : (epsilonValues ε₀).Finite := by
  exact epsilonValues_finite ε₀
