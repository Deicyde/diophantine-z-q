import ZInQKernel.OneProof.Main
import ZInQKernel.Contrib.OneProof.HeegnerPointRationalCd
import ZInQKernel.Contrib.OneProof.GrossConjugationCd
import ZInQKernel.Contrib.OneProof.CdOptimal

/-! cd-optimal: the `Main.lean` edit of gz-optimal's route A (`scratch/gz-optimal/MainEdit.lean`,
`frozenTarget_gzoptimal`) with `GZOptimal.CdOptimal` replaced by its proof `CdOpt.cdOptimal_of` from
`CdOpt.EtaW32Character` (printed: the Newman / Gordon–Hughes eta-quotient transformation law, one instance)
and `CdOpt.CdTwistedPeriodOdd` (glue). `hL3` is replaced by the `C_d` chain: heegner-32's
`grossZagierHeegnerCd_of_printed` (Heegner point from `hCM`, already an argument), gz-conj's proved
`grossConjugationCd`, and `GrossZagierFormulaCd` from `GrossZagierModuliOptCd` + the two statements above. -/

namespace ZInQ.Contrib.TYZChain
open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

theorem frozenTarget_cdoptimal
    (r : HDec.HSyn.OpenResearchLeaves23) (t : HDec.HSyn.OpenTextbookLeaves11) (l : HDec.HSyn.OpenAddedLeaves17)
    (g : HDec.HSyn.OpenGlue7)
    (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2)
    (hCM : _root_.T5Glue.ShimuraMainCM)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hFH : ZInQ.GZFH.FriedbergHoffsteinB_FE)
    (hGZ : ZInQ.GZOptimal.GrossZagierModuliOptCd) (hW : ZInQ.CdOpt.EtaW32Character)
    (hT : ZInQ.CdOpt.CdTwistedPeriodOdd) :
    ZInQ.FrozenTarget :=
  ZInQ.GZStatements.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd
    (HDec.HSyn.sixContactMin_of_open30 r t l g)
    (ThetaWP8.tyzThm35ReadingA_noHX h11 h29 hCM h33)
    (ZInQ.GZStatements.fhNonvanishingCd_of_fhNonvanishing
      (ZInQ.GZFH.fhNonvanishing_of_friedbergHoffsteinB_FE hFH))
    (ZInQ.Heegner32.grossZagierHeegnerCd_of_printed hCM
      (ZInQ.CdOpt.grossZagierFormulaCd_of_cdLeaves hGZ hW hT) ZInQ.GZConj.grossConjugationCd)

end ZInQ.Contrib.TYZChain

#print axioms ZInQ.Contrib.TYZChain.frozenTarget_cdoptimal
