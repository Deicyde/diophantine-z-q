import ZInQKernel.Contrib.TYZChain.Main
import ZInQKernel.Contrib.TYZChain.Headline
import ZInQKernel.Contrib.TYZChain.ModFn
import ZInQKernel.Contrib.TYZChain.SSExponent

/-! # tyz-chain axiom audit

Run with `lake env lean scratch/tyz-chain/Check.lean` after `lake build ZInQKernel.Contrib.TYZChain.Main
ZInQKernel.Contrib.TYZChain.Headline ZInQKernel.Contrib.TYZChain.ModFn ZInQKernel.Contrib.TYZChain.SSExponent`. Output: `Check.out`.
The `#print axioms` lines of the source scratch files, with full names, then the main theorem. -/

-- main theorem
#print axioms ZInQ.Contrib.TYZChain.tyzThm35ReadingA_of_leaves

-- the statement of the main theorem (hypotheses as listed in its docstring)
#check @ZInQ.Contrib.TYZChain.tyzThm35ReadingA_of_leaves

-- headline variant (TYZChain/Headline.lean)
#print axioms ZInQ.Contrib.TYZChain.tyzThm35ReadingA_of_tyzChainLeaves
#print axioms ZInQ.Contrib.TYZChain.frozenTarget_of_sixContactMin_grossZagier_tyzChainLeaves
#check @ZInQ.Contrib.TYZChain.frozenTarget_of_sixContactMin_grossZagier_tyzChainLeaves

-- cm-bridge (TYZChain/Bridge.lean)
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

-- tyz-321 (TYZChain/L321.lean)
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

-- tyz-35 (TYZChain/Thm35.lean)
#print axioms ZInQ.Contrib.TYZGenus.TYZ35.thm35First_of_lcal_thm33
#print axioms ZInQ.Contrib.TYZGenus.TYZ35.tyzThm35ReadingA_of_lcal_shimuraModFn_lemma318_thm33_lemma321Five

-- tyz-318 (TYZChain/Lemma318.lean)
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

-- tyz-lcal (TYZChain/Lcal.lean)
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

-- shimura-modfn (TYZChain/ModFn.lean)
#print axioms ZInQ.Contrib.TYZGenus.ShimuraModFnTask.shimuraReciprocityModFn_of_split
#print axioms ZInQ.Contrib.TYZGenus.ShimuraModFnTask.shimuraReciprocityModFn_isolated
#print axioms ZInQ.Contrib.TYZGenus.ShimuraModFnTask.reciprocity_of_rep
#print axioms ZInQ.Contrib.TYZGenus.ShimuraModFnTask.jPair_reciprocity
#print axioms ZInQ.Contrib.TYZGenus.ShimuraModFnTask.isIsolated_one
#print axioms ZInQ.Contrib.TYZGenus.ShimuraModFnTask.shimuraReciprocityModFn_eq
#print axioms ZInQ.Contrib.TYZGenus.ShimuraModFnTask.isRatModFn_jInv
#print axioms ZInQ.Contrib.TYZGenus.ShimuraModFnTask.isRatModFn_jN
#print axioms ZInQ.Contrib.TYZGenus.ShimuraModFnTask.jPair_of_modFn

-- ss-exponent (TYZChain/SSExponent.lean)
#print axioms ZInQ.Contrib.SSExponent.supersingularExponentA
#print axioms ZInQ.Contrib.SSExponent.t318_supersingularExponentA
#print axioms ZInQ.Contrib.SSExponent.lemma318Literal_HHprime_of_sqrtTwoNotIn_ss
