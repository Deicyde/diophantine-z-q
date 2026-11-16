import ZInQKernel.OneProof.Main
import ZInQKernel.Contrib.OneProof.CMPrimitive

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus in
/-- `frozenTarget` with `hCM` replaced by cm-primitive's primitive-type leaf `MainTheoremCMPolMaxPrim`, mtcm-polar's
`CMAbVarExists`, hcm-printed's three Weierstrass leaves and the bundle's textbook fields
(`CMPrimitive.shimuraMainCM_of_polMaxPrim`). -/
theorem frozenTarget_cmPrimitive
    (r : HDec.HSyn.OpenResearchLeaves23) (t : HDec.HSyn.OpenTextbookLeaves11) (l : HDec.HSyn.OpenAddedLeaves17)
    (g : HDec.HSyn.OpenGlue7)
    (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2)
    (hP : CMPrimitive.MainTheoremCMPolMaxPrim) (hE : MainCMPolar.CMAbVarExists)
    (hWU : HcmPrinted.WeierstrassUniformization)
    (hWP : HcmPrinted.WeierstrassParam) (hWA : HcmPrinted.WeierstrassAbVar)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hFH : ZInQ.GZFH.FriedbergHoffsteinB_FE) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget :=
  ZInQ.OneProof.frozenTarget r t l g h11 h29
    (CMPrimitive.shimuraMainCM_of_polMaxPrim hP hE hWU hWP hWA t.uniformizationLeafAll t.gagaMorphism)
    h33 hFH hL3

#print axioms frozenTarget_cmPrimitive
