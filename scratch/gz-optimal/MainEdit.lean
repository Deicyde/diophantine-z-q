import ZInQKernel.OneProof.Main
import ZInQKernel.Contrib.OneProof.HeegnerPointRationalCd
import ZInQKernel.Contrib.OneProof.GrossConjugationCd
import ZInQKernel.Contrib.OneProof.GrossZagierOptimal

/-! gz-optimal: the `Main.lean` edit (the hL3 fold heegner-32 + gz-conj + gz-moduli, with gz-moduli's leaf
replaced), checked out of tree against `frozenTarget` at 85111fc7 (+ merges of wip/heegner-32 718d8d4c and
wip/gz-conj 2c7ce521). `hL3 : GZDecomp.GrossZagierHeegner` (composite) is replaced by the `C_d` chain:
heegner-32's `grossZagierHeegnerCd_of_printed` (Heegner point from `hCM`, already an argument), gz-conj's proved
`grossConjugationCd`, and `GrossZagierFormulaCd` from

* route A (`frozenTarget_gzoptimal`): `GZOptimal.GrossZagierModuliOptCd` (leaf, optimal parametrization only) and
  `GZOptimal.CdOptimal` (GLUE: `C_d` is its own strong Weil curve);
* route B (`frozenTarget_gzoptimal_transfer`): `GrossZagierModuliOptCd`, `StrongWeilOptimalCd` and
  `AnalyticIsogenyRational` (textbook, composite). -/

namespace ZInQ.Contrib.TYZChain
open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

theorem frozenTarget_gzoptimal
    (r : HDec.HSyn.OpenResearchLeaves23) (t : HDec.HSyn.OpenTextbookLeaves11) (l : HDec.HSyn.OpenAddedLeaves17)
    (g : HDec.HSyn.OpenGlue7)
    (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2)
    (hCM : _root_.T5Glue.ShimuraMainCM)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hFH : ZInQ.GZFH.FriedbergHoffsteinB_FE)
    (hGZ : ZInQ.GZOptimal.GrossZagierModuliOptCd) (hOpt : ZInQ.GZOptimal.CdOptimal) :
    ZInQ.FrozenTarget :=
  ZInQ.GZStatements.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd
    (HDec.HSyn.sixContactMin_of_open30 r t l g)
    (ThetaWP8.tyzThm35ReadingA_noHX h11 h29 hCM h33)
    (ZInQ.GZStatements.fhNonvanishingCd_of_fhNonvanishing
      (ZInQ.GZFH.fhNonvanishing_of_friedbergHoffsteinB_FE hFH))
    (ZInQ.Heegner32.grossZagierHeegnerCd_of_printed hCM
      (ZInQ.GZOptimal.grossZagierFormulaCd_of_selfOptimal hGZ hOpt) ZInQ.GZConj.grossConjugationCd)

theorem frozenTarget_gzoptimal_transfer
    (r : HDec.HSyn.OpenResearchLeaves23) (t : HDec.HSyn.OpenTextbookLeaves11) (l : HDec.HSyn.OpenAddedLeaves17)
    (g : HDec.HSyn.OpenGlue7)
    (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2)
    (hCM : _root_.T5Glue.ShimuraMainCM)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hFH : ZInQ.GZFH.FriedbergHoffsteinB_FE)
    (hGZ : ZInQ.GZOptimal.GrossZagierModuliOptCd) (hSW : ZInQ.GZOptimal.StrongWeilOptimalCd)
    (hI : ZInQ.GZOptimal.AnalyticIsogenyRational) :
    ZInQ.FrozenTarget :=
  ZInQ.GZStatements.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd
    (HDec.HSyn.sixContactMin_of_open30 r t l g)
    (ThetaWP8.tyzThm35ReadingA_noHX h11 h29 hCM h33)
    (ZInQ.GZStatements.fhNonvanishingCd_of_fhNonvanishing
      (ZInQ.GZFH.fhNonvanishing_of_friedbergHoffsteinB_FE hFH))
    (ZInQ.Heegner32.grossZagierHeegnerCd_of_printed hCM
      (ZInQ.GZOptimal.grossZagierFormulaCd_of_transfer hGZ hSW hI) ZInQ.GZConj.grossConjugationCd)

end ZInQ.Contrib.TYZChain

#print axioms ZInQ.Contrib.TYZChain.frozenTarget_gzoptimal
#print axioms ZInQ.Contrib.TYZChain.frozenTarget_gzoptimal_transfer
