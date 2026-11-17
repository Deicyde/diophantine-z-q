import ZInQKernel.OneProof.Main
import ZInQKernel.Contrib.OneProof.HeegnerPointRationalCd

/-! The `Main.lean` edit for heegner-32, checked out of tree: `frozenTarget` with `hL3` replaced by the `C_d`
chain (gz-statements' `GrossZagierHeegnerCd`), whose Heegner point now needs no canonical model of `X₀(32 d²)`:

* `frozenTarget_heegner32`: `hL3` replaced by `GrossZagierFormulaCd` and `GrossConjugationCd` (printed) alone;
* `frozenTarget_heegner32_used`: `hL3` replaced by the used instance `X0ModuliGaloisParamCd` of the canonical model
  (consequence), `GrossZagierFormulaCd`, `GrossConjugationCd`. -/

namespace ZInQ.Contrib.TYZChain
open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

theorem frozenTarget_heegner32
    (r : HDec.HSyn.OpenResearchLeaves23) (t : HDec.HSyn.OpenTextbookLeaves11) (l : HDec.HSyn.OpenAddedLeaves17)
    (g : HDec.HSyn.OpenGlue7)
    (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2)
    (hCM : _root_.T5Glue.ShimuraMainCM)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hFH : ZInQ.GZFH.FriedbergHoffsteinB_FE)
    (hGZ : ZInQ.GZHL3.GrossZagierFormulaCd)
    (hGC : ZInQ.GZHL3.GrossConjugationCd) :
    ZInQ.FrozenTarget :=
  ZInQ.GZStatements.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd
    (HDec.HSyn.sixContactMin_of_open30 r t l g)
    (ThetaWP8.tyzThm35ReadingA_noHX h11 h29 hCM h33)
    (ZInQ.GZStatements.fhNonvanishingCd_of_fhNonvanishing
      (ZInQ.GZFH.fhNonvanishing_of_friedbergHoffsteinB_FE hFH))
    (ZInQ.Heegner32.grossZagierHeegnerCd_of_printed hCM hGZ hGC)

theorem frozenTarget_heegner32_used
    (r : HDec.HSyn.OpenResearchLeaves23) (t : HDec.HSyn.OpenTextbookLeaves11) (l : HDec.HSyn.OpenAddedLeaves17)
    (g : HDec.HSyn.OpenGlue7)
    (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2)
    (hCM : _root_.T5Glue.ShimuraMainCM)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hFH : ZInQ.GZFH.FriedbergHoffsteinB_FE)
    (hXd : ZInQ.Heegner32.X0ModuliGaloisParamCd) (hGZ : ZInQ.GZHL3.GrossZagierFormulaCd)
    (hGC : ZInQ.GZHL3.GrossConjugationCd) :
    ZInQ.FrozenTarget :=
  ZInQ.GZStatements.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd
    (HDec.HSyn.sixContactMin_of_open30 r t l g)
    (ThetaWP8.tyzThm35ReadingA_noHX h11 h29 hCM h33)
    (ZInQ.GZStatements.fhNonvanishingCd_of_fhNonvanishing
      (ZInQ.GZFH.fhNonvanishing_of_friedbergHoffsteinB_FE hFH))
    (ZInQ.GZWeil.grossZagierHeegnerCd_of_threeLeaves
      (ZInQ.Heegner32.heegnerPointRationalCd_of_used hCM hXd) hGZ hGC)

end ZInQ.Contrib.TYZChain

#print axioms ZInQ.Contrib.TYZChain.frozenTarget_heegner32
#print axioms ZInQ.Contrib.TYZChain.frozenTarget_heegner32_used
