import ZInQKernel.Contrib.OneProof.RC.CMField2.LevelOne
import ZInQKernel.Contrib.OneProof.RC.CMField2.OrientedIdeals

/-! Combining the arithmetic and the chart proofs, tex 2915–2917 (c). -/

noncomputable section

open AlgebraicGeometry NumberField TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
open ZInQ.Contrib.CloudB3RC53.CST
open ZInQ.Manuscript.RC.PreparedParam

namespace ZInQ.Manuscript.RC.CMField2

/-- At level one every regular chart value descends as soon as the proper
ideal singular moduli do, in the chosen embedding. -/
theorem branchDescends_one : BranchDescends 1 := by
  intro K _ _ O hk hc κ ι _ hj d A B C hD hd hcop hf
  obtain ⟨I, _, hI, _⟩ := exists_heegner_singularModuli_in_embedding O hk hc κ hD hd hcop hf
  apply finitePointEval_one_mem_range _ ι.toRatAlgHom
  change X0Model.analyticJ (cmPoint A B d) ∈ Set.range ι
  rw [hI]
  exact hj I

/-- At level one simultaneous membership of the singular moduli alone
suffices for the field-of-definition statement. -/
theorem cmFieldOfDefinition_modelOne_of (hm : SingularModulusMemRingClass) :
    CMFieldOfDefinition X0Model2.modelOne := by
  intro K _ _ hk hc O d A B C hD hd hcop hf
  obtain ⟨κ, I, J, hI, _⟩ := exists_heegner_singularModuli O hk hc hD hd hcop hf
  obtain ⟨ι, _, h⟩ := hm K O hk hc κ
  refine ⟨ι.toRatAlgHom, modelOne_fieldPoint_of_analyticJ _ ι.toRatAlgHom ?_⟩
  change X0Model.analyticJ (cmPoint A B d) ∈ Set.range ι
  rw [hI]
  exact h I

/-- Both plane coordinates descend in the same embedding furnished by the
ring class field comparison. -/
theorem heegner_coordinates_mem_ringClass_of (hm : SingularModulusMemRingClass)
    {K : Type} [Field K] [NumberField K] (O : NumberFieldOrder K)
    (hk : Module.finrank ℚ K = 2) (hc : IsTotallyComplex K)
    {N : ℕ} [NeZero N] {d A B C : ℤ} (hD : O.discr = d) (hd : d < 0)
    (hcop : IsCoprime d (N : ℤ)) (hf : IsHeegnerForm N d A B C) :
    ∃ ι : ringClassField O →ₐ[ℚ] ℂ,
      X0Model.analyticJ (cmPoint A B d) ∈ Set.range ι ∧
      X0Model.analyticJN N (cmPoint A B d) ∈ Set.range ι := by
  obtain ⟨κ, I, J, hI, hJ⟩ := exists_heegner_singularModuli O hk hc hD hd hcop hf
  obtain ⟨ι, _, h⟩ := hm K O hk hc κ
  refine ⟨ι.toRatAlgHom, ?_, ?_⟩
  · rw [hI]
    exact h I
  · rw [hJ]
    exact h J


end ZInQ.Manuscript.RC.CMField2
