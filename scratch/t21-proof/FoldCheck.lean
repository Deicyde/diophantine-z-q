import ZInQKernel.OneProof.Main
import ZInQKernel.Contrib.OneProof.TYZThm21At31

/-! t21-proof: the manual fold of `hT21` (autofold folds bundle fields only): `frozenTarget` without `hT21`. -/

namespace ZInQ.Contrib.TYZChain

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

theorem frozenTarget_noT21
    (r : HDec.HSyn.OpenResearchLeaves26) (t : HDec.HSyn.OpenTextbookLeaves12) (l : HDec.HSyn.OpenAddedLeaves17)
    (g : HDec.HSyn.OpenGlue8)
    (h11 : TYZThm11Integral)
    (hL3s : H29Split.LegendreThreeSquares) (hJP : H29Split.JonesPallX2Y2Z16)
    (hfx : H29Split.TYZTestVectorExists) (hL29 : H29Split.TYZLemma29PrintedNe3)
    (hP23 : H29Split.TYZProp23Printed)
    (hCM : _root_.T5Glue.ShimuraMainCM)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hFH : ZInQ.GZFH.FriedbergHoffsteinB_FE) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget :=
  ZInQ.OneProof.frozenTarget r t l g h11 hL3s hJP hfx hL29 ZInQ.Contrib.T21Proof.tyzThm21At31 hP23 hCM h33
    hFH hL3

end ZInQ.Contrib.TYZChain

#print axioms ZInQ.Contrib.TYZChain.frozenTarget_noT21
