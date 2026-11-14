/-
STRUCTURAL MUST-FAIL: literal beta lift cannot recover unrelated replacement a.
Expected equality type mismatch; no explicit unequal-value witness is claimed.
-/
import B2PackingProof
open ClimbB2CoefficientPacking

example (N : ℕ) (χ₀ : DirichletCharacter Qbar N) (ε₀ : GQ → GQ → Qbarˣ)
    (β₀ : GQ → Qbarˣ) (g : GQ) (a : Qbar) :
    fieldInclusion χ₀ ε₀ β₀ (betaLift χ₀ ε₀ β₀ g) = a := by
  exact (show fieldInclusion χ₀ ε₀ β₀ (betaLift χ₀ ε₀ β₀ g) = (β₀ g : Qbar) from rfl)
