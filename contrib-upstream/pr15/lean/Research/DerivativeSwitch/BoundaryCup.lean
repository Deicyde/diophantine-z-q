import Research.DerivativeSwitch.UnitCriterion

/-!
# A separately stated arithmetic-facing adapter

Received as an uncompiled candidate. Current verification is recorded in
`research/scalar-ratio/VERIFICATION.md`.

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

lemma area_swap (v x : Local K) : area x v = -area v x := by
  unfold area
  ring

/-- Local pairing after the manuscript's conjugate transport, in fixed bases. -/
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
    d.qF = cF * epsilon * d.eta ∧ d.qS = cS * epsilon * d.eta := by
  have hx : (d.J : Matrix (Fin 2) (Fin 2) K) *ᵥ ((d.J : Matrix (Fin 2) (Fin 2) K) *ᵥ d.x) = d.x := by
    rw [Matrix.mulVec_mulVec, h.involution, Matrix.one_mulVec]
  have hv : (d.J : Matrix (Fin 2) (Fin 2) K) *ᵥ ((d.J : Matrix (Fin 2) (Fin 2) K) *ᵥ d.v) = d.v := by
    rw [Matrix.mulVec_mulVec, h.involution, Matrix.one_mulVec]
  constructor
  · calc
      d.qF = cF * beta d epsilon d.v ((d.J : Matrix (Fin 2) (Fin 2) K) *ᵥ d.x) :=
        h.finite _
      _ = cF * epsilon * d.eta := by
        unfold beta
        rw [hx]
        dsimp [CommonStrictData.eta]
        ring
  · calc
      d.qS = -cS * beta d epsilon d.x ((d.J : Matrix (Fin 2) (Fin 2) K) *ᵥ d.v) :=
        h.singular _
      _ = cS * epsilon * d.eta := by
        unfold beta
        rw [hv, area_swap]
        dsimp [CommonStrictData.eta]
        ring

/-- With unequal normalizations, the defect is exactly their ratio. -/
theorem normalization_defect
    (d : CommonStrictData K I) (epsilon cF cS uF uS : K)
    (h : BoundaryCupIdentity d epsilon cF cS)
    (heps : epsilon ≠ 0) (hcS : cS ≠ 0)
    (huF : HasCoordinate (join d.D0 d.AF) (cycle d.hF d.v) d.lamF uF)
    (huS : HasCoordinate (join d.D0 d.AS)
      (cycle d.hS ((d.J : Matrix (Fin 2) (Fin 2) K) *ᵥ d.v)) d.lamS uS) :
    d.delta * uF / uS = -cF / cS := by
  obtain ⟨hqF, hqS⟩ := boundary_cup_cross_evaluations d epsilon cF cS h
  have hs : d.qS ≠ 0 := by
    rw [hqS]
    exact mul_ne_zero (mul_ne_zero hcS heps) d.area_ne
  rw [d.actual_coordinate_ratio uF uS huF huS hs, hqF, hqS]
  have heta : d.eta ≠ 0 := d.area_ne
  field_simp [hcS, heps, heta]

/-- Common normalization gives the exact transported equality. The common
factor may be nonunit or even zero; division by it is not needed. -/
theorem common_normalization_adapter
    (d : CommonStrictData K I) (epsilon c uF uS : K)
    (h : BoundaryCupIdentity d epsilon c c)
    (huF : HasCoordinate (join d.D0 d.AF) (cycle d.hF d.v) d.lamF uF)
    (huS : HasCoordinate (join d.D0 d.AS)
      (cycle d.hS ((d.J : Matrix (Fin 2) (Fin 2) K) *ᵥ d.v)) d.lamS uS) :
    d.delta * uF = -uS := by
  obtain ⟨hqF, hqS⟩ := boundary_cup_cross_evaluations d epsilon c c h
  obtain ⟨hf, hs⟩ := d.coordinate_values uF uS huF huS
  rw [hf, hs, hqF, hqS]
  ring

/-- In the fixed det(J)=-1 cofactor convention, the numerical coordinates
are exactly equal, not merely equal in valuation. -/
theorem det_neg_one_common_normalization
    (d : CommonStrictData K I) (epsilon c uF uS : K)
    (hdet : d.delta = -1)
    (h : BoundaryCupIdentity d epsilon c c)
    (huF : HasCoordinate (join d.D0 d.AF) (cycle d.hF d.v) d.lamF uF)
    (huS : HasCoordinate (join d.D0 d.AS)
      (cycle d.hS ((d.J : Matrix (Fin 2) (Fin 2) K) *ᵥ d.v)) d.lamS uS) : uF = uS := by
  have heq := common_normalization_adapter d epsilon c uF uS h huF huS
  rw [hdet, neg_one_mul] at heq
  exact neg_injective heq

/-- A unit discrepancy of the boundary--cup normalizations is sufficient.
This adapter consumes lower-level adjunction data, not the desired tensor
comparison. It permits a common nonunit clearing factor and zero cases. -/
theorem integral_boundary_cup_adapter
    (d : CommonStrictData K I) (R : Subring K) (detJ scale : Rˣ)
    (hdet : d.delta = unitValue R detJ)
    (epsilon cF cS uF uS : K)
    (h : BoundaryCupIdentity d epsilon cF cS)
    (hscale : cF = unitValue R scale * cS)
    (huF : HasCoordinate (join d.D0 d.AF) (cycle d.hF d.v) d.lamF uF)
    (huS : HasCoordinate (join d.D0 d.AS)
      (cycle d.hS ((d.J : Matrix (Fin 2) (Fin 2) K) *ᵥ d.v)) d.lamS uS) :
    UnitRelated R uF uS := by
  apply (d.actual_integral_unit_criterion R detJ hdet uF uS huF huS).mpr
  obtain ⟨hqF, hqS⟩ := boundary_cup_cross_evaluations d epsilon cF cS h
  refine ⟨scale, ?_⟩
  rw [hqF, hqS, hscale]
  ring

end Research.DerivativeSwitch.ScalarRatio
