import ZInQKernel.Contrib.OneProof.CMjBridges
import ZInQKernel.OneProof.H.TailZ
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_PeriodPair_jLattice_surjective

namespace HDec.CMBranch.CMjBridges

/-- The other uniformization interface is also available from the point form. -/
theorem group_model_uniformization_check : ZInQ.DefFaltings.AnalyticUniformizationExists :=
  ZInQ.HeightGlue.analyticUniformizationExists_of_t35 uniformization_exists

/-- The upper half-plane version of the vendored proof of surjectivity. -/
theorem modularJ_surjective_check : Function.Surjective modularJ := by
  intro x
  obtain ⟨τ, hτ⟩ :=
    P2MW.S_PeriodPair_jLattice_surjective.ModularCurve.kwQepw115c_jH_surjective x
  exact ⟨τ, (modularJ_eq τ).trans hτ⟩

#print axioms modularJ_eq
#print axioms weierstrass_j_map
#print axioms degree_le_of_mem_range
#print axioms toOrder_discr_eq_orderDisc
#print axioms FowlerBridges.card_pic_eq_properClassNumber
#print axioms card_pic_le_of_singular_modulus
#print axioms mem_latticeMultipliers_iff
#print axioms periodDiscriminant_unique
#print axioms periodDiscriminant_iff_orderDisc
#print axioms uniformization_exists
#print axioms exists_complex_baseChange_cm
#print axioms cmPeriodLattice_proof
#print axioms exists_cm_period
#print axioms cmjDegree_of_print_of_periodJDescends
#print axioms group_model_uniformization_check
#print axioms modularJ_surjective_check

end HDec.CMBranch.CMjBridges
