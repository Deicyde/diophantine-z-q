import ZInQKernel.MainGreenTao
import ZInQKernel.Contrib.OneProof.DeRhamRange
import ZInQKernel.Contrib.OneProof.PoleCompletenessFromRCGenuineFinal
import ZInQKernel.Contrib.OneProof.CasselsTatePairing
import ZInQKernel.Contrib.RC53Assist.BCDTPrint.Descent
import ZInQKernel.Contrib.OneProof.SilvermanRankOne
import ZInQKernel.Contrib.OneProof.VpDualMerge.Chain

/-! # Headline check for vpdual-merge

* `addedLeaves29VP_ofLive`: the live added bundle `OpenAddedLeaves29` (`scholzeH1AbVar`,
  `t10TateDuality`) gives the new bundle `OpenAddedLeaves29VP` (`vpDual`) through
  `DeRhamScholze.HTMerge.vpDual_of_pair`, so the new bundle is weaker than the live one; it has one
  field fewer.
* `frozenTarget_with_vpDual`: `ZInQ.OneProof.frozenTarget`'s body (`OneProof/Main.lean`) verbatim,
  with `HDec.HSyn.sixContactMin_of_open98` replaced by `HDec.HSyn.sixContactMin_of_open98_vp`, over
  `OpenAddedLeaves29VP`.
-/

namespace VpDualMerge

/-- The live added bundle gives the new one: `vpDual` from the pair (`vpDual_of_pair`). -/
theorem addedLeaves29VP_ofLive (l : HDec.HSyn.OpenAddedLeaves29) :
    HDec.HSyn.OpenAddedLeaves29VP where
  vpDual := DeRhamScholze.HTMerge.vpDual_of_pair l.scholzeH1AbVar l.t10TateDuality

example : HDec.HSyn.OpenResearchLeaves78 → HDec.HSyn.OpenTextbookLeaves18 →
    HDec.HSyn.OpenAddedLeaves29VP → _root_.ZInQ.SixContactMin :=
  HDec.HSyn.sixContactMin_of_open98_vp

/-- **Theorem 1.1 with one field `vpDual`**: `frozenTarget` with the added bundle
`OpenAddedLeaves29VP` (`VpDualDeRhamAbVar` in place of `ScholzeH1AbVar` and `T10_TateDuality`). -/
theorem frozenTarget_with_vpDual
    (r : HDec.HSyn.OpenResearchLeaves78) (t : HDec.HSyn.OpenTextbookLeaves18)
    (l : HDec.HSyn.OpenAddedLeaves29VP)
    (hRC : ZInQ.Manuscript.SelmerTwoPower.RestrictedConverseGenuine)
    (hCT : ZInQ.Manuscript.PoleS12.CasselsTatePairingCurves)
    (hRank : ZInQ.Manuscript.PoleS12.SilvermanRank.SilvermanAEC_C_16_5_5_RankOne) :
    _root_.ZInQ.FrozenTarget :=
  ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_poleCompleteness
    (HDec.HSyn.sixContactMin_of_open98_vp r t l)
    (ZInQ.Manuscript.PoleS12.SilvermanRank.poleCompleteness_of_rankOne hRC hCT
      (ZInQ.Manuscript.PoleS12.SilvermanRank.rankOne_of_aec hRank))

end VpDualMerge

#print axioms VpDualMerge.frozenTarget_with_vpDual
#print axioms VpDualMerge.addedLeaves29VP_ofLive
#print axioms DeRhamScholze.HTMerge.vpDualDeRhamAbVar_iff
#print axioms DeRhamScholze.HTMerge.vpDual_of_pair
#print axioms DeRhamScholze.HTMerge.htDecomp_of_vpDual
#print axioms DeRhamScholze.HTMerge.deRhamVpAbVarDirect_of_vpDual
#print axioms DeRhamScholze.HTMerge.hodgeTateDecompHom_of_vpDual
#print axioms DeRhamScholze.HTMerge.hodgeTateDecompOr_of_vpDual
#print axioms DeRhamScholze.HTMerge.hodgeTateDecompAbVar_of_vpDual
#print axioms HDec.HSyn.c8Leaves_of_OpenAddedLeaves28_vp
#print axioms HDec.HSyn.openResearchLeaves60_y3x6_of_OpenResearchLeaves63_nos_ds_vp
#print axioms HDec.HSyn.sixContactMin_of_open82_nos_ds_vp
#print axioms HDec.HSyn.sixContactMin_of_open83_nos_ds_vp
#print axioms HDec.HSyn.sixContactMin_of_open84_ds_vp
#print axioms HDec.HSyn.openResearchLeaves65_of_OpenResearchLeaves66_ds_vp
#print axioms HDec.HSyn.sixContactMin_of_open85_ds_vp
#print axioms HDec.HSyn.sixContactMin_of_open86_ds_vp
#print axioms HDec.HSyn.sixContactMin_of_open87_ds_vp
#print axioms HDec.HSyn.sixContactMin_of_open88_ds_vp
#print axioms HDec.HSyn.sixContactMin_of_open89_ds_vp
#print axioms HDec.HSyn.sixContactMin_of_open90_ds_vp
#print axioms HDec.HSyn.sixContactMin_of_open91_ds_vp
#print axioms HDec.HSyn.sixContactMin_of_open92_ds_vp
#print axioms HDec.HSyn.sixContactMin_of_open93_ds_vp
#print axioms HDec.HSyn.sixContactMin_of_open94_ds_vp
#print axioms HDec.HSyn.sixContactMin_of_open95_ds_vp
#print axioms HDec.HSyn.sixContactMin_of_open96_ds_vp
#print axioms HDec.HSyn.openAddedLeaves28_of_OpenAddedLeaves29_vp
#print axioms HDec.HSyn.sixContactMin_of_open98_vp
