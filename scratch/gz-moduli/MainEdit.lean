import ZInQKernel.OneProof.Main
import ZInQKernel.Contrib.OneProof.GrossZagierHeegner.WeilLattice
import ZInQKernel.Contrib.OneProof.GrossZagierHeegner.HeegnerCd
import ZInQKernel.Contrib.OneProof.GrossZagierModuli

/-! gz-moduli: the `Main.lean` edit, checked out of tree, against `frozenTarget` at 60a3fac7.
`hL3 : GZDecomp.GrossZagierHeegner` (composite) is replaced by the `C_d` chain (gz-statements'
`GrossZagierHeegnerCd`, gz-weil's `grossZagierHeegnerCd_of_threeLeaves`) with
* `HeegnerPointRationalCd` from gz-heegner's printed form (`ShimuraMainCM`, already `hCM`, and
  `X0ModuliGaloisMero`),
* `GrossZagierFormulaCd` from its moduli form `GZModuli.GrossZagierModuliCd` (this task),
* `GrossConjugationCd` (gz-hl3's printed leaf; gz-conj works on its moduli form). -/

namespace ZInQ.Contrib.TYZChain
open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

theorem frozenTarget_gzmoduli
    (r : HDec.HSyn.OpenResearchLeaves23) (t : HDec.HSyn.OpenTextbookLeaves11) (l : HDec.HSyn.OpenAddedLeaves17)
    (g : HDec.HSyn.OpenGlue7)
    (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2)
    (hCM : _root_.T5Glue.ShimuraMainCM)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hFH : ZInQ.GZFH.FriedbergHoffsteinB_FE)
    (hXm : ZInQ.GZHeegner.X0ModuliGaloisMero) (hGZM : ZInQ.GZModuli.GrossZagierModuliCd)
    (hGC : ZInQ.GZHL3.GrossConjugationCd) :
    ZInQ.FrozenTarget :=
  ZInQ.GZStatements.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd
    (HDec.HSyn.sixContactMin_of_open30 r t l g)
    (ThetaWP8.tyzThm35ReadingA_noHX h11 h29 hCM h33)
    (ZInQ.GZStatements.fhNonvanishingCd_of_fhNonvanishing
      (ZInQ.GZFH.fhNonvanishing_of_friedbergHoffsteinB_FE hFH))
    (ZInQ.GZWeil.grossZagierHeegnerCd_of_threeLeaves
      (ZInQ.GZHeegner.heegnerPointRationalCd_of_printed hCM hXm)
      (ZInQ.GZModuli.grossZagierFormulaCd_of_moduli hGZM) hGC)

end ZInQ.Contrib.TYZChain

#print axioms ZInQ.Contrib.TYZChain.frozenTarget_gzmoduli
