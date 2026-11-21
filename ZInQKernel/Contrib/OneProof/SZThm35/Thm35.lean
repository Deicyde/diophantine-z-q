import ZInQKernel.Contrib.OneProof.SZThm33.SemistableCriterion
import ZInQKernel.Contrib.OneProof.SZThm35.SemistabilityCriterion
import ZInQKernel.Contrib.OneProof.SZThm35.NeronModelSemistability
import ZInQKernel.Contrib.OneProof.SZThm35.PotentialSemistability.FiniteSeparableDVR
import ZInQKernel.HDecomp.A6.Extend

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace SZRaynaud

/-- Grothendieck's semistable reduction theorem, as stated in Silverberg–Zarhin,
*Semistable reduction and torsion subgroups of abelian varieties*, Thm. 3.4,
pp. 405–406 (SGA 7 I, Exp. IX, Th. 3.6, p. 351). One finite Galois extension works
at every prolongation of the original discrete valuation. Because
`HasSemistableReductionSZ` is existential, the statement also asserts that a Néron
model exists over each prolongation (Bosch–Lütkebohmert–Raynaud, *Néron Models*,
§1.4, Thm. 3; locator unverified); Silverberg–Zarhin's notion of semistable
reduction (Def. 3.1, p. 405) presupposes that model. -/
def SilverbergZarhinThm34 : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (A : PkgI3.AbVar K),
    ∃ E : IntermediateField K (AlgebraicClosure K), FiniteDimensional K E ∧ IsGalois K E ∧
      ∀ V : ValuationSubring E, V.comap (algebraMap K E) = O →
        HasSemistableReductionSZ (A.baseChange E) V

set_option maxHeartbeats 1200000 in
/-- Theorem 3.5 follows from the Galois criterion in Theorem 3.3 and the
potential semistability supplied to that criterion. -/
theorem silverbergZarhinThm35_of_sz33_of_potential_semistability
    (hSZ : SilverbergZarhinThm33)
    (hPotential : ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
      (w : ValuationSubring (AlgebraicClosure K)),
      w.comap (algebraMap K (AlgebraicClosure K)) = O → ∀ A : PkgI3.AbVar K,
      HasSemistableReductionSZ A O ∨
        ∃ E : IntermediateField K (AlgebraicClosure K), FiniteDimensional K E ∧ Algebra.IsSeparable K E ∧
          IsDiscreteValuationRing (w.comap (algebraMap E (AlgebraicClosure K))) ∧
          HasSemistableReductionSZ (A.baseChange E) (w.comap (algebraMap E (AlgebraicClosure K)))) :
    SilverbergZarhinThm35 := by
  intro K _ O _ A m hm hu hr N hN
  obtain ⟨w, hw⟩ := GlueA6Alg.exists_valuationSubring_comap_eq (L := AlgebraicClosure K) O
  have hs := hasSemistableReductionSZ_of_sz33_of_rational_torsion O w A hw hSZ
    (hPotential K O w hw A) m hm hu hr
  exact isSemistableResT_of_hasSemistableReductionSZ N hN hs

/-- Raynaud's criterion for rational full torsion of level at least three,
the project's specialization of Silverberg–Zarhin Thm. 3.5, follows from
the semistable reduction theorem (Thm. 3.4). -/
theorem silverbergZarhinThm35_of_sz34 (h : SilverbergZarhinThm34) : SilverbergZarhinThm35 := by
  apply silverbergZarhinThm35_of_sz33_of_potential_semistability silverbergZarhinThm33_proof
  intro K _ O _ w hw A
  obtain ⟨E, hfin, hgal, hs⟩ := h K O A
  refine Or.inr ⟨E, hfin, inferInstance,
    isDiscreteValuationRing_intermediate_of_finite_separable O w hw E, hs _ ?_⟩
  rw [ValuationSubring.comap_comap, ← IsScalarTower.algebraMap_eq, hw]

end SZRaynaud
