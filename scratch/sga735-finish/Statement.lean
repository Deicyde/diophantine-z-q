import ZInQKernel.Contrib.OneProof.SGA7IX35Unip

/-! sga735-finish: verbatim copy of the field statement `UnipotentForward.SGA7_IX_3_5_ForwardGeom`
(ZInQKernel/Contrib/OneProof/UnipotentForward.lean L420) with a `rfl` check, and the relation of the new leaf
`SGA735Nil.SGA7_IX_3_5_ForwardUnipAC` to it (a specialization: restriction to algebraically closed `k(s)`,
conclusion weakened from `(σ-1)² = 0` to `σ - 1` nilpotent). -/

noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
open ReductSplit ReductGlue ZInQ.HeightSplit
namespace SGA735FinishCopy
def SGA7_IX_3_5_ForwardGeom : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O],
    IsStrictlyHenselianDVR O →
    ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (w : ValuationSubring Ω),
    w.comap (algebraMap K Ω) = O → ∀ A : PkgI3.AbVar K,
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : O) → HasSemistableReduction A O →
      ∀ σ : Ω ≃ₐ[K] Ω, IsInertia w σ → (galTΩ A ℓ σ - 1) * (galTΩ A ℓ σ - 1) = 0

example : SGA7_IX_3_5_ForwardGeom = UnipotentForward.SGA7_IX_3_5_ForwardGeom := rfl

/-- The new leaf follows from the field (never stronger). -/
example (h : SGA7_IX_3_5_ForwardGeom) : SGA735Nil.SGA7_IX_3_5_ForwardUnipAC :=
  SGA735Nil.forwardUnipAC_of_forwardGeom h

/-- ... from sga735-narrow's restricted leaf, and from the `k(s)` reading. -/
example (h : SGA735AC.SGA7_IX_3_5_ForwardGeomAC) : SGA735Nil.SGA7_IX_3_5_ForwardUnipAC :=
  SGA735Nil.forwardUnipAC_of_forwardGeomAC h
example (h : SGA735AC.SGA7_IX_3_5_ForwardRes) : SGA735Nil.SGA7_IX_3_5_ForwardUnipAC :=
  SGA735Nil.forwardUnipAC_of_forwardRes h
end SGA735FinishCopy
end

#print axioms SGA735Nil.forwardUnipAC_of_forwardGeom
#print axioms SGA735Nil.raynaudCriterionNFNil_of_forwardUnipAC
#print axioms SGA735Nil.raynaudCriterionNFNil_of_sq
