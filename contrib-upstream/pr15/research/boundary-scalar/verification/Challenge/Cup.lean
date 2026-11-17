import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Tactic.Ring

/- Frozen specification: concrete definitions, intentional theorem proof holes.
Imports match the paired solution module; no solution import. -/

namespace Research.BoundaryCupAdapter

variable {K F S H : Type*}
variable [CommRing K]
variable [AddCommGroup F] [Module K F]
variable [AddCommGroup S] [Module K S]
variable [AddCommGroup H] [Module K H]

def transportedPairing (omega : LinearMap.BilinForm K F)
    (epsilon : K) (J : F ≃ₗ[K] S) (f : F) (s : S) : K :=
  epsilon * omega f (J.symm s)

theorem cross_evaluations_eq
    (omega : LinearMap.BilinForm K F) (halt : omega.IsAlt)
    (epsilon c : K) (J : F ≃ₗ[K] S)
    (dF : F →ₗ[K] H) (dS : S →ₗ[K] H)
    (lambdaF lambdaS : H →ₗ[K] K) (v x : F)
    (hadjF : ∀ s : S,
      lambdaF (dS s) = c * transportedPairing omega epsilon J v s)
    (hadjS : ∀ f : F,
      lambdaS (dF f) = -c * transportedPairing omega epsilon J f (J v)) :
    lambdaF (dS (J x)) = lambdaS (dF x) := by sorry

theorem cross_evaluations_with_factors
    (omega : LinearMap.BilinForm K F) (halt : omega.IsAlt)
    (epsilon cF cS : K) (J : F ≃ₗ[K] S)
    (dF : F →ₗ[K] H) (dS : S →ₗ[K] H)
    (lambdaF lambdaS : H →ₗ[K] K) (v x : F)
    (hadjF : ∀ s : S,
      lambdaF (dS s) = cF * transportedPairing omega epsilon J v s)
    (hadjS : ∀ f : F,
      lambdaS (dF f) = -cS * transportedPairing omega epsilon J f (J v)) :
    lambdaF (dS (J x)) = cF * (epsilon * omega v x) ∧
      lambdaS (dF x) = cS * (epsilon * omega v x) := by sorry

end Research.BoundaryCupAdapter
