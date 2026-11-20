import ZInQKernel.Contrib.OneProof.RC.CMScope.Selector
import ZInQKernel.Contrib.OneProof.RC.CMScope.Anchor

open ZInQ.Manuscript.RC.CMScope ZInQ.Manuscript.RC.Wiring
  ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST

#print axioms genus_values
#print axioms ring_values
#print axioms prepared_values
#print axioms missing_values
#print axioms genusValues
#print axioms ringValues
#print axioms withParamIndices
#print axioms genusInstance
#print axioms selG_isSome_of_admissible
#print axioms exists_selected_of_admissible
#print axioms selectedDatum
#print axioms pointInputs
#print axioms oddStagedOfParamValues
#print axioms factor_embedding
#print axioms fieldPoint_map_map
#print axioms anchorValue
#print axioms discr_ne_of_split_two
#print axioms scale_form
#print axioms cmPointsAtScale
#print axioms genuineHeegnerAnchor

-- The selector field fills the anchor's CM binder at its ambient instance.
example {ℓ : ℕ} {W : WData ℓ} [NeZero (newformLevel (Ecurve ℓ))]
    (a : ParamInputs W) :
    CMFieldOfDefinitionScoped (ZInQ.Manuscript.RC.X0Branch.model (newformLevel (Ecurve ℓ))) :=
  a.hCMField
