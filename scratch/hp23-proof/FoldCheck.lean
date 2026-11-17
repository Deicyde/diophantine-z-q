import ZInQKernel.OneProof.Main
import ZInQKernel.Contrib.OneProof.TYZTestVectorExists
import ZInQKernel.Contrib.OneProof.TYZProp23Printed

/-! hp23-proof: the manual fold of `hP23` (autofold folds bundle fields only; `hP23` is a top-level argument of
`frozenTarget`): `frozenTarget` without `hP23`, and without both `hfx` (hfx-proof's theorem) and `hP23`. -/

namespace ZInQ.Contrib.TYZChain

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

theorem frozenTarget_noP23
    (r : HDec.HSyn.OpenResearchLeaves28) (t : HDec.HSyn.OpenTextbookLeaves13) (l : HDec.HSyn.OpenAddedLeaves19)
    (h11 : TYZThm11Integral)
    (hfx : H29Split.TYZTestVectorExists) (hL29 : H29Split.TYZLemma29PrintedNe3)
    (hCM : _root_.T5Glue.ShimuraMainCM)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hBFH : ZInQ.BFHPrinted.BFHClauseIIGamma0) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget :=
  ZInQ.OneProof.frozenTarget r t l h11 hfx hL29 ZInQ.Contrib.HP23Proof.tyzProp23Printed hCM h33 hBFH hL3

theorem frozenTarget_noHfxP23
    (r : HDec.HSyn.OpenResearchLeaves28) (t : HDec.HSyn.OpenTextbookLeaves13) (l : HDec.HSyn.OpenAddedLeaves19)
    (h11 : TYZThm11Integral)
    (hL29 : H29Split.TYZLemma29PrintedNe3)
    (hCM : _root_.T5Glue.ShimuraMainCM)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hBFH : ZInQ.BFHPrinted.BFHClauseIIGamma0) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget :=
  ZInQ.OneProof.frozenTarget r t l h11 ZInQ.Contrib.HfxProof.tyzTestVectorExists hL29
    ZInQ.Contrib.HP23Proof.tyzProp23Printed hCM h33 hBFH hL3

end ZInQ.Contrib.TYZChain

#print axioms ZInQ.Contrib.TYZChain.frozenTarget_noP23
#print axioms ZInQ.Contrib.TYZChain.frozenTarget_noHfxP23
