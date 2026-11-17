import Challenge.UnitCriterion

/-!
# A separately stated arithmetic-facing adapter

Frozen concrete specification: selected theorem proof holes are intentional.
No solution module is imported. Reviewed against the intended mathematical contract.

The functionals are the same `lamF` and `lamS` stored in CommonStrictData.
They are not replaced by primitive generators or adjusted after comparison.
The following identities are explicit INPUTS. This file does not assert
that the manuscript's Galois cochains or Poitou--Tate maps satisfy them.
No custom axiom is introduced, and no determinant equality is a premise.
-/

namespace Research.DerivativeSwitch.ScalarRatio

open Matrix
open scoped Matrix

variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

def beta (d : CommonStrictData K I) (epsilon : K) (f s : Local K) : K :=
  epsilon * area f ((d.J : Matrix (Fin 2) (Fin 2) K) *ᵥ s)

/-- Full boundary--cup identities on the local spaces, with potentially
DIFFERENT normalization factors. All evaluations use the actual recorded rows. -/
structure BoundaryCupIdentity (d : CommonStrictData K I)
    (epsilon cF cS : K) : Prop where
  involution : (d.J : Matrix (Fin 2) (Fin 2) K) *
    (d.J : Matrix (Fin 2) (Fin 2) K) = 1
  finite : ∀ s : Local K,
    d.lamF ⬝ᵥ (d.AS *ᵥ s) = cF * beta d epsilon d.v s
  singular : ∀ f : Local K,
    d.lamS ⬝ᵥ (d.AF *ᵥ f) =
      -cS * beta d epsilon f ((d.J : Matrix (Fin 2) (Fin 2) K) *ᵥ d.v)

/-- The two scalars are derived by evaluating the adjunctions on the actual
fractional complements. This is not a hypothesis `qF=qS`. -/
theorem boundary_cup_cross_evaluations
    (d : CommonStrictData K I) (epsilon cF cS : K)
    (h : BoundaryCupIdentity d epsilon cF cS) :
    d.qF = cF * epsilon * d.eta ∧ d.qS = cS * epsilon * d.eta := by sorry

theorem normalization_defect
    (d : CommonStrictData K I) (epsilon cF cS uF uS : K)
    (h : BoundaryCupIdentity d epsilon cF cS)
    (heps : epsilon ≠ 0) (hcS : cS ≠ 0)
    (huF : HasCoordinate (join d.D0 d.AF) (cycle d.hF d.v) d.lamF uF)
    (huS : HasCoordinate (join d.D0 d.AS)
      (cycle d.hS ((d.J : Matrix (Fin 2) (Fin 2) K) *ᵥ d.v)) d.lamS uS) :
    d.delta * uF / uS = -cF / cS := by sorry

theorem common_normalization_adapter
    (d : CommonStrictData K I) (epsilon c uF uS : K)
    (h : BoundaryCupIdentity d epsilon c c)
    (huF : HasCoordinate (join d.D0 d.AF) (cycle d.hF d.v) d.lamF uF)
    (huS : HasCoordinate (join d.D0 d.AS)
      (cycle d.hS ((d.J : Matrix (Fin 2) (Fin 2) K) *ᵥ d.v)) d.lamS uS) :
    d.delta * uF = -uS := by sorry

theorem det_neg_one_common_normalization
    (d : CommonStrictData K I) (epsilon c uF uS : K)
    (hdet : d.delta = -1)
    (h : BoundaryCupIdentity d epsilon c c)
    (huF : HasCoordinate (join d.D0 d.AF) (cycle d.hF d.v) d.lamF uF)
    (huS : HasCoordinate (join d.D0 d.AS)
      (cycle d.hS ((d.J : Matrix (Fin 2) (Fin 2) K) *ᵥ d.v)) d.lamS uS) : uF = uS := by sorry

theorem integral_boundary_cup_adapter
    (d : CommonStrictData K I) (R : Subring K) (detJ scale : Rˣ)
    (hdet : d.delta = unitValue R detJ)
    (epsilon cF cS uF uS : K)
    (h : BoundaryCupIdentity d epsilon cF cS)
    (hscale : cF = unitValue R scale * cS)
    (huF : HasCoordinate (join d.D0 d.AF) (cycle d.hF d.v) d.lamF uF)
    (huS : HasCoordinate (join d.D0 d.AS)
      (cycle d.hS ((d.J : Matrix (Fin 2) (Fin 2) K) *ᵥ d.v)) d.lamS uS) :
    UnitRelated R uF uS := by sorry

end Research.DerivativeSwitch.ScalarRatio
