/-
STRUCTURAL MUST-FAIL: a finite pair sample is not the full GQ×GQ epsilon range.
Expected finite-set type mismatch; no infinite-image counterexample is claimed.
-/
import B2PackingProof
open ClimbB2CoefficientPacking

example (ε₀ : GQ → GQ → Qbarˣ) : (epsilonValues ε₀).Finite := by
  exact Set.finite_range (fun _ : Fin 1 => (ε₀ 1 1 : Qbar))
