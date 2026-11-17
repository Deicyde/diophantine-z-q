import ZInQKernel.OneProof.Main
import ZInQKernel.Contrib.OneProof.TYZTestVectorExists
import ZInQKernel.Contrib.OneProof.TYZThm21At31

/-! hfx-proof: the manual fold of `hfx` (autofold folds bundle fields only; `hfx` is a top-level argument of
`frozenTarget`): `frozenTarget` without `hfx`, and without both `hfx` and `hT21` (t21-proof). -/

namespace ZInQ.Contrib.TYZChain

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

theorem frozenTarget_noHfx
    (r : HDec.HSyn.OpenResearchLeaves26) (t : HDec.HSyn.OpenTextbookLeaves12) (l : HDec.HSyn.OpenAddedLeaves17)
    (g : HDec.HSyn.OpenGlue8)
    (h11 : TYZThm11Integral)
    (hL3s : H29Split.LegendreThreeSquares) (hJP : H29Split.JonesPallX2Y2Z16)
    (hL29 : H29Split.TYZLemma29PrintedNe3)
    (hT21 : H29Split.TYZThm21At31) (hP23 : H29Split.TYZProp23Printed)
    (hCM : _root_.T5Glue.ShimuraMainCM)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hFH : ZInQ.GZFH.FriedbergHoffsteinB_FE) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget :=
  ZInQ.OneProof.frozenTarget r t l g h11 hL3s hJP ZInQ.Contrib.HfxProof.tyzTestVectorExists hL29 hT21 hP23
    hCM h33 hFH hL3

theorem frozenTarget_noHfxT21
    (r : HDec.HSyn.OpenResearchLeaves26) (t : HDec.HSyn.OpenTextbookLeaves12) (l : HDec.HSyn.OpenAddedLeaves17)
    (g : HDec.HSyn.OpenGlue8)
    (h11 : TYZThm11Integral)
    (hL3s : H29Split.LegendreThreeSquares) (hJP : H29Split.JonesPallX2Y2Z16)
    (hL29 : H29Split.TYZLemma29PrintedNe3) (hP23 : H29Split.TYZProp23Printed)
    (hCM : _root_.T5Glue.ShimuraMainCM)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hFH : ZInQ.GZFH.FriedbergHoffsteinB_FE) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget :=
  ZInQ.OneProof.frozenTarget r t l g h11 hL3s hJP ZInQ.Contrib.HfxProof.tyzTestVectorExists hL29
    ZInQ.Contrib.T21Proof.tyzThm21At31 hP23 hCM h33 hFH hL3

end ZInQ.Contrib.TYZChain

#print axioms ZInQ.Contrib.TYZChain.frozenTarget_noHfx
#print axioms ZInQ.Contrib.TYZChain.frozenTarget_noHfxT21
