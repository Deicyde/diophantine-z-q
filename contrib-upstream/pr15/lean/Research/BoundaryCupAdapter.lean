import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Tactic.Ring

/-!
# Typed boundary--cup adapter

The two boundary--cup adjunctions below are hypotheses. This module proves
their algebraic consequence for the actual supplied maps and functionals;
it does not construct arithmetic Selmer complexes or prove those adjunctions.

Finite and singular spaces can differ. The pairing uses `J.symm` to transport
the singular argument back to the finite space, so no ill-typed `J^2` is used.
The common normalization `c` can be nonunit. No primitive replacement of a
class or functional occurs.
-/

namespace Research.BoundaryCupAdapter

variable {K F S H : Type*}
variable [CommRing K]
variable [AddCommGroup F] [Module K F]
variable [AddCommGroup S] [Module K S]
variable [AddCommGroup H] [Module K H]

/-- The local pairing transported along the finite-to-singular equivalence. -/
def transportedPairing (omega : LinearMap.BilinForm K F)
    (epsilon : K) (J : F ≃ₗ[K] S) (f : F) (s : S) : K :=
  epsilon * omega f (J.symm s)

/-- Two lower-level boundary--cup identities with the same normalization
give equal cross-boundary evaluations. All maps and functionals are retained. -/
theorem cross_evaluations_eq
    (omega : LinearMap.BilinForm K F) (halt : omega.IsAlt)
    (epsilon c : K) (J : F ≃ₗ[K] S)
    (dF : F →ₗ[K] H) (dS : S →ₗ[K] H)
    (lambdaF lambdaS : H →ₗ[K] K) (v x : F)
    (hadjF : ∀ s : S,
      lambdaF (dS s) = c * transportedPairing omega epsilon J v s)
    (hadjS : ∀ f : F,
      lambdaS (dF f) = -c * transportedPairing omega epsilon J f (J v)) :
    lambdaF (dS (J x)) = lambdaS (dF x) := by
  rw [hadjF, hadjS]
  simp only [transportedPairing, J.symm_apply_apply]
  rw [← halt.neg_eq v x]
  ring

/-- Independent finite and singular normalizations expose exactly their
respective factors; equality is not supplied when those factors differ. -/
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
      lambdaS (dF x) = cS * (epsilon * omega v x) := by
  constructor
  · simpa only [transportedPairing, J.symm_apply_apply] using hadjF (J x)
  · rw [hadjS]
    simp only [transportedPairing, J.symm_apply_apply]
    rw [← halt.neg_eq v x]
    ring

end Research.BoundaryCupAdapter
