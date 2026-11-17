import ZInQKernel.Contrib.OneProof.SGA7IX35ForwardAC

/-! Verbatim copy of the field statement `UnipotentForward.SGA7_IX_3_5_ForwardGeom`
(ZInQKernel/Contrib/OneProof/UnipotentForward.lean L420), with a `rfl` check, and the relation of the new leaf to it. -/

noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
open ReductSplit ReductGlue ZInQ.HeightSplit
namespace SGA735Copy
def SGA7_IX_3_5_ForwardGeom : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O],
    IsStrictlyHenselianDVR O →
    ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (w : ValuationSubring Ω),
    w.comap (algebraMap K Ω) = O → ∀ A : PkgI3.AbVar K,
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : O) → HasSemistableReduction A O →
      ∀ σ : Ω ≃ₐ[K] Ω, IsInertia w σ → (galTΩ A ℓ σ - 1) * (galTΩ A ℓ σ - 1) = 0

example : SGA7_IX_3_5_ForwardGeom = UnipotentForward.SGA7_IX_3_5_ForwardGeom := rfl

/-- The new leaf is the copy with `[IsAlgClosed (IsLocalRing.ResidueField O)]` added; it follows from the copy. -/
example (h : SGA7_IX_3_5_ForwardGeom) : SGA735AC.SGA7_IX_3_5_ForwardGeomAC := SGA735AC.forwardGeomAC_of_forwardGeom h

/-- ... and from the `k(s)` reading of semistability. -/
example (h : SGA735AC.SGA7_IX_3_5_ForwardRes) : SGA735AC.SGA7_IX_3_5_ForwardGeomAC :=
  SGA735AC.forwardGeomAC_of_forwardRes h
end SGA735Copy
end
