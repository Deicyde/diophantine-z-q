/-
STRUCTURAL MUST-FAIL: finite unit-only character values are not the full
ZMod N value range, which retains nonunit zeros. Expected finite-set mismatch.
No assertion that either actual range is infinite or that zero appears at N=1.
-/
import B2PackingProof
open ClimbB2CoefficientPacking

example (N : ℕ) [NeZero N] (χ₀ : DirichletCharacter Qbar N) :
    (characterValues χ₀).Finite := by
  exact Set.finite_range (fun u : (ZMod N)ˣ => (χ₀.toUnitHom u : Qbar))
