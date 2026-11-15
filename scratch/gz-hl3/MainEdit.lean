import ZInQKernel.OneProof.Main
import ZInQKernel.Contrib.OneProof.GrossZagierHeegner

/-! The `Main.lean` edit for `hL3`, checked out of tree: `frozenTarget` with `hL3` replaced by the six leaves. -/

namespace ZInQ.Contrib.TYZChain
open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

theorem frozenTarget_gzhl3
    (r : HDec.HSyn.OpenResearchLeaves20) (t : HDec.HSyn.OpenTextbookLeaves11) (l : HDec.HSyn.OpenAddedLeaves16)
    (g : HDec.HSyn.OpenGlue7)
    (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2)
    (hCM : _root_.T5Glue.ShimuraMainCM) (hX : _root_.T5Glue.X0ModuliGalois)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hL2 : ZInQ.GZDecomp.FHNonvanishing)
    (hU : ZInQ.GZHL3.WeierstrassUniformization) (hSW : ZInQ.GZHL3.StrongWeilCurve)
    (hI : ZInQ.GZHL3.IsogenyLattice) (hHP : ZInQ.GZHL3.HeegnerPointRational)
    (hGZ : ZInQ.GZHL3.GrossZagierFormula) (hGC : ZInQ.GZHL3.GrossConjugation) :
    ZInQ.FrozenTarget :=
  ZInQ.OneProof.frozenTarget r t l g h11 h29 hCM hX h33 hL2
    (ZInQ.GZHL3.grossZagierHeegner_of_leaves hU hSW hI hHP hGZ hGC)

end ZInQ.Contrib.TYZChain

#print axioms ZInQ.Contrib.TYZChain.frozenTarget_gzhl3
