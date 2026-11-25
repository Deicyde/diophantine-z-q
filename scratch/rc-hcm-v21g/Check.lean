import ZInQKernel.Contrib.OneProof.RC.HCMV21.DeuringRankFour
import ZInQKernel.Contrib.OneProof.RC.PMAdelic.Geometry
import ZInQKernel.Contrib.OneProof.RC.PMWire.Fibre
import ZInQKernel.Contrib.OneProof.RC.HCMV21.LevelDeuringInjective

open ZInQ.Manuscript.RC

-- part (0)
#print axioms HCMV21.deuringSupersingularEndOrder_of_rankFour
#print axioms HCMV21.exists_referenceEndOrder_of_rankFour
-- part (1)
#check @PMAdelic.JetchevKane
#check @PMAdelic.OperatorComparison
#print axioms PMAdelic.JetchevKane.idealClasses
#print axioms PMAdelic.OperatorComparison.hecke_compare
#print axioms PMAdelic.OperatorComparison.atkin_compare
#print axioms PMAdelic.OperatorComparison.frobenius_compare
#print axioms PMAdelic.OperatorComparison.frobenius_ss
#print axioms PMAdelic.geometricInput
#print axioms PMAdelic.geometry
#print axioms PMWire.adaptComparison
#print axioms PMWire.adaptOperators
-- part (2)
#print axioms HCMV21.enhancedSetoid
#print axioms HCMV21.SupersingularEnhanced.exists_generator
#print axioms HCMV21.exists_referenceFrame
#print axioms HCMV21.leftClassSetEquiv
#print axioms HCMV21.order_star_mem
#print axioms HCMV21.LeftIdeal.exists_integral_primeTo
#print axioms HCMV21.classSetEquivOfReference
#print axioms HCMV21.classSetEquivOfReference_self
#print axioms HCMV21.leftRing_classSetEquivOfReference
#print axioms HCMV21.exists_levelReferenceCoordinates
#print axioms HCMV21.HomPlacement.exists_unit
#print axioms HCMV21.levelIdeal_locallyPrincipal_tate
#print axioms HCMV21.placedLevelIdeal_locallyPrincipal
#print axioms HCMV21.levelDeuringClass
#print axioms HCMV21.levelDeuringClass_reference
#print axioms HCMV21.endRight_injective
#print axioms HCMV21.mem_levelHom_of_comp
#print axioms HCMV21.exists_endRight_eq_level
#print axioms HCMV21.levelEndEquivRight
#print axioms HCMV21.levelDeuringClass_order
#print axioms HCMV21.levelDeuringClass_reference_order
#print axioms HCMV21.orderSpan_levelLattice
#print axioms HCMV21.levelDeuringClass_injective
