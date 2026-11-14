/-
STRUCTURAL MUST-FAIL: no epsilon(1,1)=1 condition is supplied for beta(1)=1.
Expected type mismatch: the old conditional supplier still awaits epsilon11=1.
Real unnormalized minus-one data are separate positive fixtures.
-/
import B2PackingProof
open ClimbB2CoefficientPacking

example (ε₀ : GQ → GQ → Qbarˣ) (β₀ : GQ → Qbarˣ)
    (hco : ∀ g h, β₀ g * β₀ h = ε₀ g h * β₀ (g*h)) : β₀ 1 = 1 := by
  exact ClimbBetaFixedPlace.normalizationFromUnitEquation ε₀ β₀ hco
