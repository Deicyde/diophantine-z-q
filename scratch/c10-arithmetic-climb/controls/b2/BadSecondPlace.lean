/-
STRUCTURAL MUST-FAIL: restriction uses the given rho, not an unrelated rho'.
Expected equality type mismatch; not a constructed inequivalent-place witness.
-/
import B2PackingProof
open ClimbB2CoefficientPacking

example (N : ℕ) (χ₀ : DirichletCharacter Qbar N) (ε₀ : GQ → GQ → Qbarˣ)
    (β₀ : GQ → Qbarˣ) (g : GQ) (ρ ρ' : Qbar →ₐ[ℚ] ℂ) :
    restrictedComplexPlace χ₀ ε₀ β₀ ρ (betaLift χ₀ ε₀ β₀ g) = ρ' (β₀ g : Qbar) := by
  exact (show restrictedComplexPlace χ₀ ε₀ β₀ ρ (betaLift χ₀ ε₀ β₀ g) = ρ (β₀ g : Qbar) from rfl)
