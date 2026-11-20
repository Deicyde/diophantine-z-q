import ZInQKernel.Contrib.OneProof.RC.CMField2.PrimeComparison
import ZInQKernel.Contrib.OneProof.RC.CMField2.CoordinateDescent

/-! Field of definition on the normalized model, tex 2915–2917 (c). -/

open AlgebraicGeometry NumberField TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
open ZInQ.Contrib.CloudB3RC53.CST
open ZInQ.Manuscript.RC.PreparedParam

namespace ZInQ.Manuscript.RC.CMField2

/-- Only the normalized branch comparison is needed at general level. -/
theorem cmFieldOfDefinition (N : ℕ) [NeZero N] (hb : BranchDescends N) :
    CMFieldOfDefinition (X0Branch.model N) :=
  cmFieldOfDefinition_of N singularModulusMemRingClass hb

/-- At level one the regular chart values descend unconditionally. -/
theorem cmFieldOfDefinition_modelOne : CMFieldOfDefinition X0Model2.modelOne :=
  cmFieldOfDefinition_modelOne_of singularModulusMemRingClass

/-- The same level-one result for the normalized branch model. -/
theorem cmFieldOfDefinition_one : CMFieldOfDefinition (X0Branch.model 1) :=
  cmFieldOfDefinition 1 branchDescends_one

/-- Both coordinates of the modular-polynomial plane point descend in one
embedding of the ring class field, at every level. -/
theorem heegner_coordinates_mem_ringClass
    {K : Type} [Field K] [NumberField K] (O : NumberFieldOrder K)
    (hk : Module.finrank ℚ K = 2) (hc : IsTotallyComplex K)
    {N : ℕ} [NeZero N] {d A B C : ℤ} (hD : O.discr = d) (hd : d < 0)
    (hcop : IsCoprime d (N : ℤ)) (hf : IsHeegnerForm N d A B C) :
    ∃ ι : ringClassField O →ₐ[ℚ] ℂ,
      X0Model.analyticJ (cmPoint A B d) ∈ Set.range ι ∧
      X0Model.analyticJN N (cmPoint A B d) ∈ Set.range ι :=
  heegner_coordinates_mem_ringClass_of singularModulusMemRingClass O hk hc hD hd hcop hf


end ZInQ.Manuscript.RC.CMField2
