/-
STRUCTURAL MUST-FAIL: nonzero-polynomial guard is not supplied at p=0.
Expected type mismatch; finite_setOfPred_isRoot still awaits 0≠0.
The control does not use the empty formal rootSet of the zero polynomial.
-/
import B2PackingProof
open ClimbB2CoefficientPacking

example : Set.Finite {z : Qbar | Polynomial.IsRoot (0 : Polynomial Qbar) z} := by
  exact Polynomial.finite_setOfPred_isRoot (p := (0 : Polynomial Qbar))
