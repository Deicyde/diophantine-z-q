import ZInQKernel.OneProof.Main
import ZInQKernel.Contrib.OneProof.MainCMPolar

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus in
/-- `frozenTarget` with `hCM` replaced by mtcm-polar's two leaves, hcm-printed's three Weierstrass leaves and the
bundle's textbook fields (`shimuraMainCM_of_polar`). -/
theorem frozenTarget_mtcmPolar
    (r : HDec.HSyn.OpenResearchLeaves22) (t : HDec.HSyn.OpenTextbookLeaves11) (l : HDec.HSyn.OpenAddedLeaves17)
    (g : HDec.HSyn.OpenGlue7)
    (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2)
    (hP : MainCMPolar.MainTheoremCMPolMax) (hE : MainCMPolar.CMAbVarExists)
    (hWU : HcmPrinted.WeierstrassUniformization)
    (hWP : HcmPrinted.WeierstrassParam) (hWA : HcmPrinted.WeierstrassAbVar)
    (hX : _root_.T5Glue.X0ModuliGalois)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hFH : ZInQ.GZFH.FriedbergHoffsteinB_FE) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget :=
  ZInQ.OneProof.frozenTarget r t l g h11 h29
    (MainCMPolar.shimuraMainCM_of_polar hP hE hWU hWP hWA t.uniformizationLeafAll t.gagaMorphism)
    hX h33 hFH hL3

#print axioms frozenTarget_mtcmPolar
