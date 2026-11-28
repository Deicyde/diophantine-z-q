import ZInQKernel.Contrib.OneProof.CMHeight62Full.TreeH1
import ZInQKernel.Contrib.OneProof.CMHeight62Full.TreeH2
import ZInQKernel.Contrib.OneProof.CMHeight62Full.TreeStep7

/-!
# Axiom check of the tree wiring, part A

Imports the three tree-wiring files (H1, H2, H5) and prints the axioms of every theorem and
definition they add. Each should report at most `propext`, `Classical.choice` and `Quot.sound`.
-/

namespace ZInQ.Contrib.CMHeight62Full

-- H1
#print axioms ringEquivIntegersOfRangeEq
#print axioms coe_ringEquivIntegersOfRangeEq
#print axioms isDiscreteValuationRing_of_range_eq
#print axioms exists_isDomain_isDVR_of_ringEquiv
#print axioms dim_baseChange_eq_one
#print axioms identityPlace
#print axioms identityPlace_spec
#print axioms originEquiv
#print axioms genStalk_isDiscreteValuationRing
#print axioms exists_hodgeLine_of_dim_one

-- H2, abstract cores
#print axioms fracEquiv
#print axioms fracEquiv_algebraMap
#print axioms fracAlgEquiv
#print axioms fracAlgEquiv_apply
#print axioms valuation_fracEquiv_le_one_iff
#print axioms ord_fracEquiv_eq_one_of_span_eq
#print axioms valuation_fracEquiv_eq_of_span_eq
#print axioms mem_range_algebraMap_iff_of_isLocalization
#print axioms structGermHom_stalkMap
#print axioms structGermHom_stalkSpecializes
#print axioms structGermHom_comp_specMap
#print axioms originStalkEquivAt
#print axioms structGermHom_originIso₁
#print axioms structGermHom_originIso₂
#print axioms originStalkEquivAt_structMap

-- H2, the tree instance
#print axioms originEquiv_eq_originStalkEquivAt
#print axioms omegaEquiv
#print axioms omegaAlgEquiv
#print axioms omegaAlgEquiv_apply
#print axioms omegaEquiv_algebraMap
#print axioms valuation_omegaEquiv_le_one_iff
#print axioms valuation_omegaEquiv_le_one_iff_of_isLocalization
#print axioms valuation_omegaEquiv_eq_of_span_eq
#print axioms ord_omegaEquiv_eq_one_of_span_eq
#print axioms finiteDimensional_poleSpace_identityPlace
#print axioms omegaEquiv_structMap
#print axioms algebraMap_structMap_omega
#print axioms omegaEquiv_tG
#print axioms treeH2

-- H5
#print axioms localComparison
#print axioms step7
#print axioms cmHeight62_full

end ZInQ.Contrib.CMHeight62Full
