import ZInQKernel.OneProof.Main
import ZInQKernel.Contrib.OneProof.BFHNonvanishing

/-! The fold of task bfh-leaf, checked without editing `Main`: the body of `ZInQ.OneProof.frozenTarget`
(`ZInQKernel/OneProof/Main.lean`, base 862bd440) with the top hypothesis
`hFH : ZInQ.GZFH.FriedbergHoffsteinB_FE` replaced by the printed leaf
`hBFH : ZInQ.BFHPrinted.BFHClauseII` (Bump–Friedberg–Hoffstein 1990, clause (ii)), and
`ZInQ.GZFH.fhNonvanishing_of_friedbergHoffsteinB_FE hFH` replaced by
`ZInQ.BFHPrinted.fhNonvanishing_of_bfhClauseII hBFH`. Every other argument and the term are copied
verbatim from `Main.lean`. -/

namespace ZInQ.Contrib.TYZChain

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

/-- **Theorem 1.1, from every statement still open, with `hFH` replaced by BFH clause (ii).** -/
theorem frozenTarget_bfh
    (r : HDec.HSyn.OpenResearchLeaves22) (t : HDec.HSyn.OpenTextbookLeaves11) (l : HDec.HSyn.OpenAddedLeaves17)
    (g : HDec.HSyn.OpenGlue7)
    (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2)
    (hCM : _root_.T5Glue.ShimuraMainCM)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hBFH : ZInQ.BFHPrinted.BFHClauseII) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget :=
  ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves
    (HDec.HSyn.sixContactMin_of_open29 r t l g)
    (ThetaWP8.tyzThm35ReadingA_noHX h11 h29 hCM h33)
    ZInQ.GZTheta.Frontier.heckeThetaNewform (ZInQ.BFHPrinted.fhNonvanishing_of_bfhClauseII hBFH) hL3

end ZInQ.Contrib.TYZChain

#print axioms ZInQ.Contrib.TYZChain.frozenTarget_bfh
