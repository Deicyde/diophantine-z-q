import ZInQKernel.Contrib.OneProof.RC.BranchDescends.Prints
import ZInQKernel.Contrib.OneProof.RC.BranchDescends.Residue

/-! The field of definition of the normalized CM branch, tex 2915–2916. -/

noncomputable section

open AlgebraicGeometry CategoryTheory
open ZInQ.Manuscript.RC.CMScope ZInQ.Contrib.CloudB3RC53.CST

namespace ZInQ.Manuscript.RC.BranchDescends

set_option backward.isDefEq.respectTransparency.types false in
/-- Evaluating a section at a complex point is the same as evaluating its
germ in the local ring at the image of that point. -/
theorem sectionMap_eq_germ_evaluation
    {X : Scheme.{0}} (x : Spec (.of ℂ) ⟶ X) (U : X.Opens)
    (h : x (IsLocalRing.closedPoint ℂ) ∈ U) :
    X0Model.sectionMap x U (Scheme.preimage_eq_top_of_closedPoint_mem x h).ge =
      X.presheaf.germ U _ h ≫ Scheme.stalkClosedPointTo x := by
  symm
  rw [Scheme.germ_stalkClosedPointTo]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom,
    X0Model.sectionMap, Scheme.Hom.appLE, Category.assoc]
  rfl

/-- Every value of the normal model's local ring is the finite analytic
value of the corresponding modular function (on the spot, c). -/
theorem stalkValue_is_modularValue (N : ℕ) [NeZero N] (τ : UpperHalfPlane)
    (r : (X0Model.curve N).presheaf.stalk
      (X0Model.complexPoint N τ (IsLocalRing.closedPoint ℂ))) :
    ∃ s : X0Model.meromorphicValuation (τ : ℂ),
      s.val = X0Model.fieldGerm N τ
        (X0Model.functionField N (algebraMap _ (X0Model.curve N).functionField r)) ∧
      X0Model.valueOfGerm (τ : ℂ) s = Scheme.stalkClosedPointTo (X0Model.complexPoint N τ) r := by
  let X := X0Model.curve N
  let x := X0Model.complexPoint N τ
  obtain ⟨U, hU, a, rfl⟩ := X.presheaf.exists_germ_eq r
  have h : x (default : Spec (.of ℂ)) ∈ U :=
    Subsingleton.elim (IsLocalRing.closedPoint ℂ) (default : Spec (.of ℂ)) ▸ hU
  let : Nonempty U := ⟨⟨_, hU⟩⟩
  obtain ⟨s, hg, hs⟩ := X0Model.sectionGerm N τ U a h
  refine ⟨s, ?_, ?_⟩
  · rwa [X.algebraMap_germ_eq_germToFunctionField hU a]
  · change X0Model.valueOfGerm (τ : ℂ) s =
      (X.presheaf.germ U _ hU ≫ Scheme.stalkClosedPointTo x) a
    rw [← sectionMap_eq_germ_evaluation x U hU]
    exact hs

/-- The single value-form CM input gives scoped CM descent at every
nonzero level. The lift uses the residue field of the normalized curve (c). -/
theorem cmFieldOfDefinitionScoped_of_values {N : ℕ} [NeZero N]
    (h : HeegnerValuesInRingClassField N) : CMFieldOfDefinitionScoped (X0Branch.model N) := by
  intro K _ _ hK hc hs h4 h3 β hβ c _ hcop d A B C hO hd hn hf hB
  obtain ⟨ι, hv⟩ := h K hK hc hs h4 h3 β hβ c hcop d A B C hO hd hn hf hB
  refine ⟨ι, fieldPoint_of_stalk_values ((X0Branch.model N).complexPoint _) ι ?_⟩
  intro r
  change Scheme.stalkClosedPointTo (X0Model.complexPoint N (cmPoint A B d)) r ∈ Set.range ι
  obtain ⟨s, hg, hs'⟩ := stalkValue_is_modularValue N (cmPoint A B d) r
  rw [← hs']
  exact hv _ s hg

/-- At level one the same value-form argument gives the normalized
model conclusion of the independent singular modulus proof. -/
theorem cmFieldOfDefinitionScoped_one_of_values
    (h : HeegnerValuesInRingClassField 1) : CMFieldOfDefinitionScoped (X0Branch.model 1) :=
  cmFieldOfDefinitionScoped_of_values h

end ZInQ.Manuscript.RC.BranchDescends
