import ZInQKernel.OneProof.Main
import ZInQKernel.Contrib.OneProof.HeegnerPointRationalCd
import ZInQKernel.Contrib.OneProof.GrossConjugationCd
import ZInQKernel.Contrib.OneProof.GrossZagierAlgebraic

/-! gzopt-dict: the current `Main.lean` (`ZInQ.OneProof.frozenTarget`, origin/main e41a7169) with `hL3`
(`GZDecomp.GrossZagierHeegner`, every `E`) replaced by its `C_d` chain (heegner-32's
`grossZagierHeegnerCd_of_printed` with `hCM`, gz-conj's proved conjugation relation, period-odd's
`grossZagierFormulaCd_of_etaW32`), as in period-odd's `MainEdit.lean`, and gz-optimal's analytic leaf
`GrossZagierModuliOptCd` replaced by the algebraic leaf `GrossZagierAlgOptCd` and the `q`-expansion
principle `Gamma0QExpansion` (`GZAlg.grossZagierFormulaCd_of_alg`). -/

namespace ZInQ.Contrib.TYZChain
open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

theorem frozenTarget_gzoptdict
    (r : HDec.HSyn.OpenResearchLeaves26) (t : HDec.HSyn.OpenTextbookLeaves12) (l : HDec.HSyn.OpenAddedLeaves17)
    (g : HDec.HSyn.OpenGlue8)
    (h11 : TYZThm11Integral)
    (hL3s : H29Split.LegendreThreeSquares) (hJP : H29Split.JonesPallX2Y2Z16)
    (hfx : H29Split.TYZTestVectorExists) (hL29 : H29Split.TYZLemma29PrintedNe3)
    (hT21 : H29Split.TYZThm21At31) (hP23 : H29Split.TYZProp23Printed)
    (hCM : _root_.T5Glue.ShimuraMainCM)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hFH : ZInQ.GZFH.FriedbergHoffsteinB_FE)
    (hGZ : ZInQ.GZAlg.GrossZagierAlgOptCd) (hQ : ZInQ.GZAlg.Gamma0QExpansion)
    (hW : ZInQ.CdOpt.EtaW32Character) :
    ZInQ.FrozenTarget :=
  ZInQ.GZStatements.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd
    (HDec.HSyn.sixContactMin_of_open35 r t l g)
    (ThetaWP8.tyzThm35ReadingA_noHX h11
      (H29Split.tyzLemma29Mod2_of_sixLeaves hL3s hJP hfx hL29 hT21 hP23) hCM h33)
    (ZInQ.GZStatements.fhNonvanishingCd_of_fhNonvanishing
      (ZInQ.GZFH.fhNonvanishing_of_friedbergHoffsteinB_FE hFH))
    (ZInQ.Heegner32.grossZagierHeegnerCd_of_printed hCM
      (ZInQ.GZAlg.grossZagierFormulaCd_of_alg hGZ hQ hW) ZInQ.GZConj.grossConjugationCd)

end ZInQ.Contrib.TYZChain

#print axioms ZInQ.Contrib.TYZChain.frozenTarget_gzoptdict
