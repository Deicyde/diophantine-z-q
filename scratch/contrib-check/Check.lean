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
import of `ZInQKernel.Contrib.HeightBC.Main` and the lines below): the closed height base-change

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
