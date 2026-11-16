import ZInQKernel.OneProof.Main
import ZInQKernel.Contrib.OneProof.ShimuraMainCMG1

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus in
/-- `frozenTarget` with `hCM` replaced by the three hcm-g1 leaves. -/
theorem frozenTarget_hcmG1
    (r : HDec.HSyn.OpenResearchLeaves22) (t : HDec.HSyn.OpenTextbookLeaves11) (l : HDec.HSyn.OpenAddedLeaves17)
    (g : HDec.HSyn.OpenGlue7)
    (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2)
    (hS : HcmG1.ShimuraThm54) (hWU : HcmG1.WeierstrassUniformization) (hWP : HcmG1.WeierstrassParam)
    (hX : _root_.T5Glue.X0ModuliGalois)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hFH : ZInQ.GZFH.FriedbergHoffsteinB_FE) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget :=
  ZInQ.OneProof.frozenTarget r t l g h11 h29 (HcmG1.shimuraMainCM_of_g1 hS hWU hWP) hX h33 hFH hL3

#print axioms frozenTarget_hcmG1
