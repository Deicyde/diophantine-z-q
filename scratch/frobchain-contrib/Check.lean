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
import ZInQKernel.Contrib.FrobChain.Main

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

/-! ## frobchain-contrib: the frob chain in the Contrib build -/

-- the chain's statements are Props with no auto-bound arguments
#check (FrobTrace.AlgFrobRed : Prop)
#check (G14Bridge.TateBridge35 : Prop)
#check (UnramTate.LinkedFrob : Prop)
#check @G14Trace.FrobTraceLink
#check (FrobPiecesNeron.AbVarSpreadsOut : Prop)
#check (FrobPiecesNeron.ProperSmoothGenConnected : Prop)

-- the closed reductions
#print axioms ZInQ.Contrib.FrobChain.algFrobRed_of_neron_nmp
#print axioms ZInQ.Contrib.FrobChain.tateBridge35_of_neron_nmp
#print axioms ZInQ.Contrib.FrobChain.linkedFrob_of_neron_nmp
#print axioms ZInQ.Contrib.FrobChain.frobTraceLink_copy_iff
#print axioms ZInQ.Contrib.FrobChain.smoothGeomConnIntegral_copy_iff
#print axioms ZInQ.Contrib.FrobChain.kernel_leaves_iff
-- the same, under the owners' names
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
#print axioms AlgFrobRedRed.absFrob
#print axioms FrobPiecesGood.smoothGeomConnIntegral
#print axioms FrobPiecesNeron.goodRedCofinite_of_neron
#print axioms FrobPiecesGood.algFrobRed_of_spread_nmp
#print axioms FrobPiecesGood.tateBridge35_of_spread_nmp
#print axioms G0FibreSimple.rigidityHom
#print axioms UnramTate.tateBridge_of_tateModuleFree
#print axioms G14Bridge.tateBridge_five_three_of_35
