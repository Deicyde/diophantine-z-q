import ZInQKernel.Contrib.OneProof.RC.HCMV21.DeuringRankFour
import ZInQKernel.Contrib.OneProof.RC.PMAdelic.Geometry
import ZInQKernel.Contrib.OneProof.RC.PMWire.Fibre
import ZInQKernel.Contrib.OneProof.RC.HCMV21.LevelDeuringInjective
import ZInQKernel.Contrib.OneProof.RC.HCMV21.PrimeModelReach
import ZInQKernel.Contrib.OneProof.RC.GoodRowWire.Assembly

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
-- fixup: item 1
#print axioms GoodRowWire.oddStagedOfSamePlace
-- fixup: item 2
#print axioms HCMV21.exists_ne_of_dim_eq_one
#print axioms HCMV21.isNonconstant_id
#print axioms HCMV21.isSeparableMor_id
#print axioms HCMV21.isSeparableIsogeny_id
#print axioms HCMV21.separableReach_of_separableIsogenyExists
#print axioms HCMV21.LeftIdeal.mem_rightRing_iff_mem_mirror_leftRing
#print axioms HCMV21.exists_algEquiv_extend
#print axioms HCMV21.exists_endRight_eq_of_mem_rightRing
#print axioms HCMV21.levelEndEquivRight_apply
#print axioms HCMV21.levelEndEquivMirror
#print axioms HCMV21.nonempty_enhancedIso_of_translate
-- fixup: item 3
#print axioms HCMV21.frO_naturality
#print axioms HCMV21.frO_tensor
#print axioms HCMV21.primeFrob
#print axioms HCMV21.primeFrobBC
#print axioms HCMV21.primeFrobBC_left_fst
#print axioms HCMV21.primeFrobBC_pt
#print axioms HCMV21.surjective_primeFrobBC
#print axioms HCMV21.surjective_pow_hom
#print axioms HCMV21.surjective_tensorHom
#print axioms HCMV21.isNonconstant_of_ne_zero
#print axioms HCMV21.base_genericPoint_of_isNonconstant
#print axioms HCMV21.isMonHom_of_frob_comp
#print axioms HCMV21.isNonconstant_of_comp
#print axioms HCMV21.separableReach_of_primeModel
#print axioms HCMV21.levelDeuringClass_injective_primeModel
