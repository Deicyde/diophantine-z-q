import ZInQKernel.MainLiterature
import ZInQKernel.Contrib.HeckeAll.Provider
import ZInQKernel.Contrib.GaussFE.Headline
import ZInQKernel.Contrib.PSide.APZero
import ZInQKernel.Contrib.PSide.BadPrimes
import ZInQKernel.Contrib.PSide.Coeff
import ZInQKernel.Contrib.PSide.Convergence
import ZInQKernel.Contrib.PSide.Hasse
import ZInQKernel.Contrib.PSide.Supersingular
import ZInQKernel.Contrib.PSide.TYZInputsIff
import ZInQKernel.Contrib.GZDecomp.Decomp
import ZInQKernel.Contrib.T14.Main
import ZInQKernel.Contrib.T28.Assemble
import ZInQKernel.Contrib.RLeaf.T36Torsion
import ZInQKernel.Contrib.RLeaf.T37GoodReduction
import ZInQKernel.Contrib.AbVarBC.Main
import ZInQKernel.Contrib.GZTheta.NewCMFinal
import ZInQKernel.Contrib.GZTheta.ALFinal
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
import ZInQKernel.Contrib.GZStatements.Weak
import ZInQKernel.Contrib.GZStatements.Level
import ZInQKernel.Contrib.GZStatements.Compat
import ZInQKernel.Contrib.GZStatements.Hensel
import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.ClassFields.KroneckerWeber
import ZInQKernel.Contrib.AVB1.Poincare
import ZInQKernel.Contrib.AVB1.AlgClosed
import ZInQKernel.Contrib.KroneckerWeber.Basic
import ZInQKernel.Contrib.TYZChain.Main
import ZInQKernel.Contrib.TYZChain.Headline
import ZInQKernel.Contrib.TYZChain.ModFn
import ZInQKernel.Contrib.TYZChain.SSExponent

/-! The two closed providers fed into the unchanged headline theorem: Theorem 1.1 from
`SixContactMin`, `TYZThm35ReadingA` and `GrossZagier` alone. -/

theorem contribCheck_headline (hH : ZInQ.SixContactMin) (hA : ZInQ.Literature.TYZThm35ReadingA)
    (hG : ZInQ.Literature.GrossZagier) : ZInQ.FrozenTarget :=
  ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_tyzThm35ReadingA_heckeContinuation_functionalEquation5_grossZagier
    hH hA ZInQ.Contrib.heckeContinuation ZInQ.Contrib.functionalEquation5 hG

#print axioms ZInQ.Contrib.functionalEquation5
#print axioms ZInQ.Contrib.heckeContinuation
#print axioms contribCheck_headline
#print axioms ZInQ.Contrib.GaussFE.frozenTarget_of_sixContactMin_tyzThm35ReadingA_grossZagier
#print axioms ZInQ.Contrib.PSide.tyzInputs_iff_readingA
#print axioms ZInQ.Contrib.PSide.LSeriesSummable_cd
#print axioms ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves
#print axioms ZInQ.Contrib.T14.brauerHasse2C
#print axioms ZInQ.Contrib.T14.brauerReciprocity2C
#print axioms T28.igusaClebschSeparation_proved
#print axioms ZInQ.RLeaf.t36_torsionStructure
#print axioms ZInQ.RLeaf.T37.t37_goodReductionUnramified
#print axioms ZInQ.Contrib.AbVarBC.abVarBaseChange
#print axioms ZInQ.GZTheta.heckeThetaNewform
#print axioms ZInQ.GZTheta.atkinLiTwistNew
#print axioms ZInQ.GZTheta.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishing_grossZagierHeegner
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
#print axioms ZInQ.GZStatements.fhNonvanishingCd_of_fhNonvanishing
#print axioms ZInQ.GZStatements.grossZagierHeegnerCd_of_grossZagierHeegner
#print axioms ZInQ.GZStatements.grossZagierRankCd_of_grossZagierHeegnerCd
#print axioms ZInQ.GZStatements.grossZagierCd_of_fhNonvanishingCd_grossZagierRankCd
#print axioms ZInQ.GZStatements.grossZagierCd_of_fhNonvanishingCd_grossZagierHeegnerCd
#print axioms ZInQ.GZStatements.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd
#print axioms ZInQ.GZStatements.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierRankCd
#print axioms ZInQ.GZStatements.grossZagierRankCd_of_grossZagierCd
#print axioms ZInQ.GZStatements.grossZagierHeegnerCd_of_grossZagierCd
#print axioms ZInQ.GZStatements.grossZagierHeegnerCd_of_grossZagier
#print axioms ZInQ.GZStatements.level_eq_of_coeff_cd
#print axioms ZInQ.GZStatements.heegnerHyp_iff_of_coeff_cd
#print axioms ZInQ.GZStatements.heegnerHyp_32_iff
#print axioms ZInQ.GZStatements.jacobiSym_neg_level
#print axioms ZInQ.GZStatements.coprime_of_heegnerHyp
#print axioms ZInQ.GZStatements.jacobiSym_two_eq_one_iff
#print axioms ZInQ.GZStatements.jacobiSym_prime_eq_legendreSym
#print axioms ZInQ.GZStatements.heegnerHyp_iff_split
#print axioms ZInQ.GZStatements.chiD_mul
#print axioms ZInQ.GZStatements.chiD_prime
#print axioms ZInQ.GZStatements.chiD_two
#print axioms ZInQ.GZStatements.exists_sq_mod_four_mul_of_heegnerHyp
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
#print axioms ZInQ.Contrib.TYZChain.tyzThm35ReadingA_of_leaves
#print axioms ZInQ.Contrib.TYZChain.tyzThm35ReadingA_of_tyzChainLeaves
#print axioms ZInQ.Contrib.TYZChain.frozenTarget_of_sixContactMin_grossZagier_tyzChainLeaves
#print axioms ZInQ.Contrib.TYZGenus.CMBridge.tyzDelta_spec
#print axioms ZInQ.Contrib.TYZGenus.CMBridge.exists_actsAsArtinO
#print axioms ZInQ.Contrib.TYZGenus.CMBridge.lemma321_of
#print axioms ZInQ.Contrib.TYZGenus.CMBridge.genusPointLeafCM_of_pinned
#print axioms ZInQ.Contrib.TYZGenus.CMBridge.genusPointLeaf_of_pinned
#print axioms ZInQ.Contrib.TYZGenus.CMBridge.tyzThm35ReadingA_of_pinned
#print axioms ZInQ.Contrib.TYZGenus.CMBridge.tyzThm35ReadingA_of_pinned'
#print axioms ZInQ.Contrib.TYZGenus.CMBridge.tyzSigmaFixesZn_of
#print axioms ZInQ.Contrib.TYZGenus.CMBridge.galPt_Z7
#print axioms ZInQ.Contrib.TYZGenus.CMBridge.class7GenusPtDefined_of
#print axioms ZInQ.Contrib.TYZGenus.CMBridge.tyzThm35ReadingA_of_pinnedLeaves
#print axioms ZInQ.Contrib.TYZGenus.CMBridge.Copy.genusPointLeafCM_eq
#print axioms ZInQ.Contrib.TYZGenus.CMBridge.phi0_spec
#print axioms ZInQ.Contrib.TYZGenus.CMBridge.iInHprime
#print axioms ZInQ.Contrib.TYZGenus.CMBridge.cmFieldOfDefinition7_of
#print axioms ZInQ.Contrib.TYZGenus.CMBridge.tyzThm35ReadingA_of_rewired
#print axioms ZInQ.Contrib.TYZGenus.CMBridge.genusFieldLeLni
#print axioms ZInQ.Contrib.TYZGenus.CMBridge.tyzThm35ReadingA_of_cmLeaves7
#print axioms ZInQ.Contrib.TYZGenus.CMBridge.exists_complexConj
#print axioms ZInQ.Contrib.TYZGenus.CMBridge.lemma321Seven_of
#print axioms ZInQ.Contrib.TYZGenus.CMBridge.tyzThm35ReadingA_of_cmLeaves7'
#print axioms ZInQ.Contrib.TYZGenus.CMBridge.sqrtPstarInHilbert
#print axioms ZInQ.Contrib.TYZGenus.CMBridge.betaOnGenus7_of
#print axioms ZInQ.Contrib.TYZGenus.CMBridge.artinPstarChi
#print axioms ZInQ.Contrib.TYZGenus.CMBridge.normP2
#print axioms ZInQ.Contrib.TYZGenus.CMBridge.lemma321Seven_of'
#print axioms ZInQ.Contrib.TYZGenus.CMBridge.tyzThm35ReadingA_of_ringClassD_sigmaShiftsF0_lemma318_thm35First_lemma321Five_thm36Seven
#print axioms ZInQ.Contrib.TYZGenus.CMBridge.tyzThm36Seven_of
#print axioms ZInQ.Contrib.TYZGenus.CMBridge.tyzThm35ReadingA_of_ringClassD_sigmaFixesZn_lemma318_thm35First_lemma321Five_shimura
#print axioms ZInQ.Contrib.TYZGenus.CMBridge.cmAlgebraic_of_cmValue
#print axioms ZInQ.Contrib.TYZGenus.CMBridge.tyzThm36Seven_of_shimuraModFn
#print axioms ZInQ.Contrib.TYZGenus.CMBridge.tyzThm35ReadingA_of_lcal_shimuraModFn_lemma318_thm35First_lemma321Five
#print axioms ZInQ.Contrib.TYZGenus.T321.lemma321Five_of
#print axioms ZInQ.Contrib.TYZGenus.T321.tyzThm36ConjFive_of
#print axioms ZInQ.Contrib.TYZGenus.T321.tyzThm36OneFive_of
#print axioms ZInQ.Contrib.TYZGenus.T321.wNegatesI
#print axioms ZInQ.Contrib.TYZGenus.T321.betaOnGenus5
#print axioms ZInQ.Contrib.TYZGenus.T321.kerFixesZnMod
#print axioms ZInQ.Contrib.TYZGenus.T321.lemma321Five_of_shimuraModFn_betaOneLift
#print axioms ZInQ.Contrib.TYZGenus.T321.tyzThm35ReadingA_of_lcal_shimuraModFn_lemma318_thm35First_betaOneLift
#print axioms ZInQ.Contrib.TYZGenus.T321B.betaOneLiftExists
#print axioms ZInQ.Contrib.TYZGenus.T321.lemma321Five_of_shimuraModFn'
#print axioms ZInQ.Contrib.TYZGenus.T321.tyzThm35ReadingA_of_lcal_shimuraModFn_lemma318_thm35First
#print axioms ZInQ.Contrib.TYZGenus.TYZ35.thm35First_of_lcal_thm33
#print axioms ZInQ.Contrib.TYZGenus.TYZ35.tyzThm35ReadingA_of_lcal_shimuraModFn_lemma318_thm33_lemma321Five
#print axioms ZInQ.Contrib.TYZGenus.T318.lemma318Literal_HHprime_of'
#print axioms ZInQ.Contrib.TYZGenus.T318.hhprimeFrobSq
#print axioms ZInQ.Contrib.TYZGenus.T318.lemma318Literal_HHprime_of_ss_sqrtTwo
#print axioms ZInQ.Contrib.TYZGenus.T318.sqrtTwo_not_mem_HHprime_of_single
#print axioms ZInQ.Contrib.TYZGenus.T318.lemma318_at_single
#print axioms ZInQ.Contrib.TYZGenus.T318.sqrtTwoNotInHHprime_of_sigmaLift
#print axioms ZInQ.Contrib.TYZGenus.T318.tyzThm35ReadingA_of_cmLeaves_ringClassD_ss_sqrtTwo
#print axioms ZInQ.Contrib.TYZGenus.T318.lemma318Literal_HHprime_of_sqrtTwoNotIn
#print axioms ZInQ.Contrib.TYZGenus.T318.lemma318_at_single_unconditional
#print axioms ZInQ.Contrib.TYZGenus.T318.tyzThm35ReadingA_of_cmLeaves_ringClassD_sqrtTwo
#print axioms ZInQ.Contrib.TYZGenus.T318.supersingularExponentWeak
#print axioms ZInQ.Contrib.TYZLcal.gCl_three
#print axioms ZInQ.Contrib.TYZLcal.ell_one_odd
#print axioms ZInQ.Contrib.TYZLcal.lcalOne_of_leaves
#print axioms ZInQ.Contrib.TYZLcal.isLContinuation_Fone
#print axioms ZInQ.Contrib.TYZLcal.norm_lValOne_one_le
#print axioms ZInQ.Contrib.TYZLcal.omegaInt_ge_two
#print axioms ZInQ.Contrib.TYZLcal.lValOneBound
#print axioms ZInQ.Contrib.TYZLcal.tyzLcalOne_of_leaves
#print axioms ZInQ.Contrib.TYZLcal.tyzThm35ReadingA_of_three_leaves
#print axioms ZInQ.Contrib.TYZLcal.genusPackage_iff_readingA_of_two
#print axioms ZInQ.Contrib.TYZLcal.lemma29Mod2_iff
#print axioms ZInQ.Contrib.TYZLcal.tyzLcalOne_of_leaves'
#print axioms ZInQ.Contrib.TYZGenus.ShimuraModFnTask.shimuraReciprocityModFn_of_split
#print axioms ZInQ.Contrib.TYZGenus.ShimuraModFnTask.shimuraReciprocityModFn_isolated
#print axioms ZInQ.Contrib.TYZGenus.ShimuraModFnTask.reciprocity_of_rep
#print axioms ZInQ.Contrib.TYZGenus.ShimuraModFnTask.jPair_reciprocity
#print axioms ZInQ.Contrib.TYZGenus.ShimuraModFnTask.isIsolated_one
#print axioms ZInQ.Contrib.TYZGenus.ShimuraModFnTask.shimuraReciprocityModFn_eq
#print axioms ZInQ.Contrib.TYZGenus.ShimuraModFnTask.isRatModFn_jInv
#print axioms ZInQ.Contrib.TYZGenus.ShimuraModFnTask.isRatModFn_jN
#print axioms ZInQ.Contrib.TYZGenus.ShimuraModFnTask.jPair_of_modFn
#print axioms ZInQ.Contrib.SSExponent.supersingularExponentA
#print axioms ZInQ.Contrib.SSExponent.t318_supersingularExponentA
#print axioms ZInQ.Contrib.SSExponent.lemma318Literal_HHprime_of_sqrtTwoNotIn_ss
