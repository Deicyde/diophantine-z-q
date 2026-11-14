/-
STRUCTURAL MUST-FAIL: a given finite-degree adjoin certificate is not for a
substituted bottom field. Expected FD type mismatch; no claim bottom is not FD.
-/
import B2PackingProof
open ClimbB2CoefficientPacking

example (N : ℕ) (χ₀ : DirichletCharacter Qbar N) (ε₀ : GQ → GQ → Qbarˣ)
    (β₀ : GQ → Qbarˣ) (hS : (coefficients χ₀ ε₀ β₀).Finite) :
    FiniteDimensional ℚ (⊥ : IntermediateField ℚ Qbar) := by
  exact ClimbFiniteCoefficientField.finiteDimensional_fieldOf (coefficients χ₀ ε₀ β₀) hS
