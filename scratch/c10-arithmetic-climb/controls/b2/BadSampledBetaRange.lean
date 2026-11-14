/-
STRUCTURAL MUST-FAIL: a finite one-element sample is not a full GQ value range.
Expected finite-set type mismatch, not a proof of infinite actual beta image.
-/
import B2PackingProof
open ClimbB2CoefficientPacking

example (β₀ : GQ → Qbarˣ) : (betaValues β₀).Finite := by
  exact Set.finite_range (fun _ : Fin 1 => (β₀ 1 : Qbar))
