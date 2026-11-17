import ZInQKernel.Contrib.HeckeAll.Provider
import ZInQKernel.Contrib.PSide.TYZInputsIff
import ZInQKernel.Contrib.T14.Main
import ZInQKernel.Contrib.T28.Assemble
import ZInQKernel.Contrib.RLeaf.T36Torsion
import ZInQKernel.Contrib.RLeaf.T37GoodReduction
import ZInQKernel.Contrib.AbVarBC.Main
import ZInQKernel.Contrib.FrobPieces.SmoothGeomConnIntegral
import ZInQKernel.Contrib.TYZGenus.RingClassBridge
import ZInQKernel.Contrib.Mobius.Main
import ZInQKernel.Contrib.Dim.IntegralHom
import ZInQKernel.Contrib.Dim.LeafPush2
import ZInQKernel.Contrib.Dim.HodgeLattice
import ZInQKernel.Contrib.HeightBC.Main
import ZInQKernel.Contrib.AbsFrob.AlgFrobRed
import ZInQKernel.Contrib.AbsFrob.Sanity
import ZInQKernel.Contrib.UnramRoots.Main
import ZInQKernel.Contrib.UnramRoots.Sanity
import ZInQKernel.Contrib.FrobChain.Main
import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.ClassFields.KroneckerWeber
import ZInQKernel.Contrib.AVB1.Poincare
import ZInQKernel.Contrib.AVB1.AlgClosed
import ZInQKernel.Contrib.KroneckerWeber.Basic
import ZInQKernel.Contrib.CloudW06PoincareRigidity.T11bExists
import ZInQKernel.Contrib.CloudW08EigenformTwists.EigenformTwist
import ZInQKernel.Contrib.CloudW02Connectedness.Basic
import ZInQKernel.Contrib.CloudW01Spread.Smooth
import ZInQKernel.Contrib.CloudW01Spread.FinitePresentation
import ZInQKernel.Contrib.CloudW03NeronSurj.Main
import ZInQKernel.Contrib.CloudW07JacobiansCurves.JacobianExists
import ZInQKernel.Contrib.CloudW07JacobiansCurves.NormalModel

/-! The two closed providers (lane74: the literature headline they fed was removed with Route K). -/

#print axioms ZInQ.Contrib.functionalEquation5
#print axioms ZInQ.Contrib.heckeContinuation
#print axioms ZInQ.Contrib.PSide.tyzInputs_iff_readingA
#print axioms ZInQ.Contrib.T14.brauerHasse2C
#print axioms ZInQ.Contrib.T14.brauerReciprocity2C
#print axioms T28.igusaClebschSeparation_proved
#print axioms ZInQ.RLeaf.t36_torsionStructure
#print axioms ZInQ.RLeaf.T37.t37_goodReductionUnramified
#print axioms ZInQ.Contrib.AbVarBC.abVarBaseChange
#print axioms FrobPieces.smoothGeomConnIntegral
#print axioms ZInQ.Contrib.TYZGenus.RingClassBridge.hprimeNormal
#print axioms ZInQ.Contrib.TYZGenus.RingClassBridge.iInH4
#print axioms ZInQ.Contrib.TYZGenus.RingClassBridge.tyzThm35ReadingA_of_cmLeaves_ringClassD
#print axioms LeafQM.AV.CurveGlue.mobiusGlue_of_T5
#print axioms LeafQM.AV.CurveGlue.mobiusGlue_of_t5
#print axioms ZInQ.Contrib.Dim.topologicalKrullDim_eq_of_isIntegralHom_of_surjective
#print axioms ZInQ.Contrib.Dim.height_eq_natCard_of_isMaximal_mvPolynomial
#print axioms ZInQ.Contrib.Dim.ringKrullDim_and_spanFinrank_localization
#print axioms ZInQ.Contrib.Dim.ringKrullDim_stalk_of_smoothOfRelativeDimension
#print axioms ZInQ.Contrib.Dim.isRegularLocalRing_stalk_of_smooth
#print axioms ZInQ.Contrib.Dim.finrank_cotangentSpace_of_smoothOfRelativeDimension
#print axioms ZInQ.Contrib.Dim.ringKrullDim_stalk_of_section
#print axioms ZInQ.Contrib.Dim.topologicalKrullDim_eq_ringKrullDim_stalk_of_smooth
#print axioms ZInQ.Contrib.Dim.topologicalKrullDim_eq_of_smoothOfRelativeDimension
#print axioms ZInQ.Contrib.Dim.ringKrullDim_eq_trdeg_fractionRing
#print axioms ZInQ.Contrib.Dim.exists_aeval_eq_zero_of_trdeg_le_one
#print axioms ZInQ.Contrib.Dim.topologicalKrullDim_eq_trdeg_functionField
#print axioms ZInQ.Contrib.Dim.trdeg_functionField_eq_of_smoothOfRelativeDimension
#print axioms ZInQ.Contrib.Dim.dimEqTrdeg
#print axioms ZInQ.Contrib.Dim.dimEqTrdegAlg
#print axioms ZInQ.Contrib.Dim.algDepOfTrdegOne
#print axioms ZInQ.Contrib.Dim.smoothTrdeg
#print axioms ZInQ.Contrib.Dim.curveFnFieldAlgDep
#print axioms ZInQ.Contrib.Dim.dimEqTrdegOver
#print axioms ZInQ.Contrib.Dim.smoothTrdegOver
#print axioms ZInQ.Contrib.Dim.curveAlgOverTranscendental
#print axioms ZInQ.Contrib.Dim.regularAtOrigin
#print axioms ZInQ.Contrib.Dim.dimAtOrigin
#print axioms ZInQ.Contrib.Dim.dimBaseChange
#print axioms ZInQ.Contrib.Dim.tangentDimAtOrigin
#print axioms ZInQ.Contrib.Dim.hodgeLatticeTheorem
#print axioms ZInQ.HeightBC.hodgeBCInjective
#print axioms ZInQ.HeightBC.omegaBaseChange
#print axioms ZInQ.HeightBC.omegaLocalization
#print axioms ZInQ.HeightBC.cotangentSpanBC
#print axioms ZInQ.HeightBC.uniformizationLiftAnalytic
#print axioms ZInQ.HeightBC.modelHeightBaseChange
#print axioms ZInQ.HeightBC.hodgeLineBaseChange
#print axioms ZInQ.HeightBC.stableHeightBaseChange
#print axioms ZInQ.HeightBC.stableFaltingsHeight_eq_neron_of_N1N2
#print axioms ZInQ.H5Glue.neronModelMinimal
#print axioms ZInQ.H5Glue.openSubgroupHeight
#print axioms ZInQ.Contrib.HeightBC.modelHeightBaseChange
#print axioms ZInQ.Contrib.HeightBC.openSubgroupHeight
#print axioms ZInQ.Contrib.HeightBC.neronModelMinimal
#print axioms ZInQ.Contrib.HeightBC.stableFaltingsHeight_eq_neron_of_N1N2
#print axioms AbsFrobDef.fr
#print axioms AbsFrobDef.fr_naturality
#print axioms AbsFrobDef.fr_Spec
#print axioms AbsFrobDef.fr_naturality'
#print axioms AbsFrobDef.fr_Spec_zmod
#print axioms AbsFrobDef.fr_Spec_polynomial_ne_id
#print axioms AlgFrobRedRed.absFrob
#print axioms UnramRootsTask.unramRoots
#print axioms UnramRootsTask.unramRoots_all
#print axioms UnramRootsTask.unramRoots_two
#print axioms UnramRootsTask.unramProcyclic_of_frobData
#print axioms UnramRootsTask.frobData_exists
#print axioms UnramRootsTask.Sanity.unramRoots_two_nonvacuous
#print axioms ZInQ.Contrib.FrobChain.algFrobRed_of_neron_nmp
#print axioms ZInQ.Contrib.FrobChain.tateBridge35_of_neron_nmp
#print axioms ZInQ.Contrib.FrobChain.linkedFrob_of_neron_nmp
#print axioms ZInQ.Contrib.FrobChain.frobTraceLink_copy_iff
#print axioms ZInQ.Contrib.FrobChain.smoothGeomConnIntegral_copy_iff
#print axioms ZInQ.Contrib.FrobChain.kernel_leaves_iff
#print axioms FrobPiecesGood.algFrobRed_of_neron_nmp
#print axioms FrobPiecesGood.tateBridge35_of_neron_nmp
#print axioms LinkedFrobRed.linkedFrob_of_neron_nmp
#print axioms LinkedFrobRed.linkedFrob_of_algFrobLink
#print axioms LinkedFrobRed.linkedFrob_of_algFrobRed
#print axioms LinkedFrobRed.linkedFrob_of_gen
#print axioms LinkedFrobRed.linkedFrob_of_goodRed_nmp
#print axioms FrobTrace.tateBridge35_of_algFrobRed
#print axioms FrobTrace.algFrobOne_of_red
#print axioms FrobTrace.algFrobLink_of_one
#print axioms FrobTrace.tateBridge35_of_algFrobLink
#print axioms AlgFrobRedRed.algFrobRed_of_gen
#print axioms AlgFrobRedRed.fExtendGen_of_nmp
#print axioms AlgFrobRedRed.algFrobRed_of_nmp
#print axioms FrobPiecesGood.smoothGeomConnIntegral
#print axioms FrobPiecesNeron.goodRedCofinite_of_neron
#print axioms FrobPiecesGood.algFrobRed_of_spread_nmp
#print axioms FrobPiecesGood.tateBridge35_of_spread_nmp
#print axioms G0FibreSimple.rigidityHom
#print axioms UnramTate.tateBridge_of_tateModuleFree
#print axioms G14Bridge.tateBridge_five_three_of_35
#print axioms ZInQ.Contrib.KroneckerWeber.isAbelianGalois_of_comm
#print axioms ZInQ.Contrib.KroneckerWeber.exists_pos_algHom_cyclotomicField
#print axioms ZInQ.Contrib.KroneckerWeber.hSynKroneckerWeber
#print axioms ZInQ.Contrib.KroneckerWeber.glueKroneckerWeber
#print axioms ZInQ.Contrib.KroneckerWeber.kroneckerWeberCyclic_of_kroneckerWeber
#print axioms ZInQ.Contrib.KroneckerWeber.kroneckerWeber_cyclic
#print axioms ZInQ.Contrib.AVB1.homFreeFinite_of_algClosed
#print axioms ZInQ.Contrib.AVB1.charPolyIndepOfEll_of_algClosed
#print axioms ZInQ.Contrib.AVB1.bcHom_injective
#print axioms ZInQ.Contrib.AVB1.tateBC_bijective_closure
#print axioms ZInQ.Contrib.AVB1.poincareReducibility_of_pieces
#print axioms ZInQ.Contrib.AVB1.poincareReducibility_of_simpleImage
#print axioms ZInQ.Contrib.AVB1.simpleImageIsogeny_of_pieces
-- cloud workers (w57)
#print axioms ZInQ.Contrib.CloudW06PoincareRigidity.T11bExists_proof
#print axioms ZInQ.Contrib.CloudW08EigenformTwists.EigenformTwist_proof
#print axioms ZariskiConn.ZariskiConnectedness_proof
#print axioms ZInQ.Contrib.SpreadOut.EGAIV_17_7_8_ii_proof
#print axioms ZInQ.Contrib.SpreadOut.EGAIV_8_8_2_ii_proof
#print axioms ZInQ.Contrib.NeronC.NeronMappingAbelianSchemeSurj_proof
-- cloud worker W07 (w59)
#print axioms ZInQ.Contrib.CloudW07JacobiansCurves.JacobianExists_proof
#print axioms ZInQ.Contrib.CloudW07JacobiansCurves.NormalModelOfFunctionFieldQ_proof
