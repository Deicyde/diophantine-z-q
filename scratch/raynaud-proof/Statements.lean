import ZInQKernel.Contrib.OneProof.RaynaudSemistableCP

/-! raynaud-proof: verbatim copies of the field and of the restricted leaf, checked against the originals. -/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReductSplit ReductGlue

namespace RaynaudProofCopy

/-- Copy of `ReductGlue.RaynaudSemistableSH` (TailZ14 L1105), verbatim. -/
def RaynaudSemistableSH : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O],
    IsStrictlyHenselianDVR O → ∀ (A : PkgI3.AbVar K) (m : ℕ), 3 ≤ m → IsUnit (m : O) →
    (∀ x : A.Pt (AlgebraicClosure K), x ^ m = 1 →
      ∃ y : A.Pt K, ZInQ.Contrib.AbVarBC.extPt A (Algebra.ofId K (AlgebraicClosure K)) y = x) →
    SemistableNeronModels A O

/-- Copy of `ReductB.RaynaudSemistableSHcp` (TailZ23 L305), verbatim. -/
def RaynaudSemistableSHcp : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [PerfectField (IsLocalRing.ResidueField O)],
    IsStrictlyHenselianDVR O → ∀ (A : PkgI3.AbVar K) (m : ℕ), 3 ≤ m → IsUnit (m : O) →
    (∀ x : A.Pt (AlgebraicClosure K), x ^ m = 1 →
      ∃ y : A.Pt K, ZInQ.Contrib.AbVarBC.extPt A (Algebra.ofId K (AlgebraicClosure K)) y = x) →
    SemistableNeronModels A O

example : RaynaudSemistableSH = ReductGlue.RaynaudSemistableSH := rfl
example : RaynaudSemistableSHcp = ReductB.RaynaudSemistableSHcp := rfl
example : HDec.HSyn.OpenResearchLeaves26 → ReductGlue.RaynaudSemistableSH := fun r => r.raynaudSemistableSH

end RaynaudProofCopy

#print axioms RaynaudCP.consumers_of_cp
#print axioms RaynaudCP.raynaudSemistableSHcp_of_SH
