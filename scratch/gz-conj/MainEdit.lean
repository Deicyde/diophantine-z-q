import ZInQKernel.OneProof.Main
import ZInQKernel.Contrib.OneProof.GrossConjugationCd

/-! The `Main.lean` edit for gz-conj, checked out of tree: `frozenTarget` (main 60a3fac7) with `hL3`
replaced by gz-weil's `C_d` chain (gz-statements' `GrossZagierHeegnerCd`) in which
`GrossConjugationCd` is proved: two Heegner-point leaves remain (`frozenTarget_gzconj`), or one
leaf plus gz-heegner's printed canonical model `X0ModuliGaloisMero` (`frozenTarget_gzconj_printed`). -/

namespace ZInQ.Contrib.TYZChain

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

theorem frozenTarget_gzconj
    (r : HDec.HSyn.OpenResearchLeaves23) (t : HDec.HSyn.OpenTextbookLeaves11) (l : HDec.HSyn.OpenAddedLeaves17)
    (g : HDec.HSyn.OpenGlue7)
    (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2)
    (hCM : _root_.T5Glue.ShimuraMainCM)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hFH : ZInQ.GZFH.FriedbergHoffsteinB_FE)
    (hHP : ZInQ.GZHL3.HeegnerPointRationalCd) (hGZ : ZInQ.GZHL3.GrossZagierFormulaCd) :
    ZInQ.FrozenTarget :=
  ZInQ.GZStatements.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd
    (HDec.HSyn.sixContactMin_of_open30 r t l g)
    (ThetaWP8.tyzThm35ReadingA_noHX h11 h29 hCM h33)
    (ZInQ.GZStatements.fhNonvanishingCd_of_fhNonvanishing
      (ZInQ.GZFH.fhNonvanishing_of_friedbergHoffsteinB_FE hFH))
    (ZInQ.GZConj.grossZagierHeegnerCd_of_twoLeaves hHP hGZ)

theorem frozenTarget_gzconj_printed
    (r : HDec.HSyn.OpenResearchLeaves23) (t : HDec.HSyn.OpenTextbookLeaves11) (l : HDec.HSyn.OpenAddedLeaves17)
    (g : HDec.HSyn.OpenGlue7)
    (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2)
    (hCM : _root_.T5Glue.ShimuraMainCM)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hFH : ZInQ.GZFH.FriedbergHoffsteinB_FE)
    (hX : ZInQ.GZHeegner.X0ModuliGaloisMero) (hGZ : ZInQ.GZHL3.GrossZagierFormulaCd) :
    ZInQ.FrozenTarget :=
  frozenTarget_gzconj r t l g h11 h29 hCM h33 hFH
    (ZInQ.GZHeegner.heegnerPointRationalCd_of_printed hCM hX) hGZ

end ZInQ.Contrib.TYZChain

example : ZInQ.GZHL3.GrossConjugationCd := ZInQ.GZConj.grossConjugationCd

#print axioms ZInQ.GZConj.grossConjugationCd
#print axioms ZInQ.GZConj.conj_clause
#print axioms ZInQ.GZConj.rootNumber_cd
#print axioms ZInQ.GZConj.lattice_eq_of_g
#print axioms ZInQ.GZConj.grossZagierHeegnerCd_of_printed
#print axioms ZInQ.Contrib.TYZChain.frozenTarget_gzconj
#print axioms ZInQ.Contrib.TYZChain.frozenTarget_gzconj_printed
