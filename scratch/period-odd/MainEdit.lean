import ZInQKernel.OneProof.Main
import ZInQKernel.Contrib.OneProof.HeegnerPointRationalCd
import ZInQKernel.Contrib.OneProof.GrossConjugationCd
import ZInQKernel.Contrib.OneProof.PeriodOdd

/-! period-odd: cd-optimal's `Main.lean` edit (`scratch/cd-optimal/MainEdit.lean`, `frozenTarget_cdoptimal`)
with `CdOpt.CdTwistedPeriodOdd` removed: `GrossZagierFormulaCd` from `GrossZagierModuliOptCd` and
`EtaW32Character` alone (`PeriodOdd.grossZagierFormulaCd_of_etaW32`). So `hL3` is replaced by these two
printed leaves (with heegner-32's `hCM`, already an argument, and gz-conj's proved conjugation relation). -/

namespace ZInQ.Contrib.TYZChain
open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

theorem frozenTarget_periododd
    (r : HDec.HSyn.OpenResearchLeaves23) (t : HDec.HSyn.OpenTextbookLeaves11) (l : HDec.HSyn.OpenAddedLeaves17)
    (g : HDec.HSyn.OpenGlue7)
    (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2)
    (hCM : _root_.T5Glue.ShimuraMainCM)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hFH : ZInQ.GZFH.FriedbergHoffsteinB_FE)
    (hGZ : ZInQ.GZOptimal.GrossZagierModuliOptCd) (hW : ZInQ.CdOpt.EtaW32Character) :
    ZInQ.FrozenTarget :=
  ZInQ.GZStatements.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd
    (HDec.HSyn.sixContactMin_of_open30 r t l g)
    (ThetaWP8.tyzThm35ReadingA_noHX h11 h29 hCM h33)
    (ZInQ.GZStatements.fhNonvanishingCd_of_fhNonvanishing
      (ZInQ.GZFH.fhNonvanishing_of_friedbergHoffsteinB_FE hFH))
    (ZInQ.Heegner32.grossZagierHeegnerCd_of_printed hCM
      (ZInQ.PeriodOdd.grossZagierFormulaCd_of_etaW32 hGZ hW) ZInQ.GZConj.grossConjugationCd)

end ZInQ.Contrib.TYZChain

#print axioms ZInQ.Contrib.TYZChain.frozenTarget_periododd
