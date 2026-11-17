import ZInQKernel.OneProof.Main
import ZInQKernel.Contrib.OneProof.BFHKronecker

/-! The fold of task bfh-kronecker, checked without editing `Main`: the body of
`ZInQ.OneProof.frozenTarget` (`ZInQKernel/OneProof/Main.lean`, base 516c2abe) with the top hypothesis
`hFH : ZInQ.GZFH.FriedbergHoffsteinB_FE` replaced by the printed leaf
`hBFH : ZInQ.BFHPrinted.BFHClauseIIKronecker` (Bump–Friedberg–Hoffstein 1990, clause (ii), with
`χ_D(n) = (D / n)` the Kronecker symbol).

* `frozenTarget_bfhKronecker` (the fold, `B = 4` only): the call
  `ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves … heckeThetaNewform
  (ZInQ.GZFH.fhNonvanishing_of_friedbergHoffsteinB_FE hFH) hL3` is replaced by
  `ZInQ.BFHPrinted.frozenTarget_of_sixContactMin_tyzThm35ReadingA_bfhKronecker … heckeThetaNewform hBFH hL3`
  (same first three arguments, verbatim).
* `frozenTarget_bfhKronecker_allB` (drop-in alternative): only the argument
  `ZInQ.GZFH.fhNonvanishing_of_friedbergHoffsteinB_FE hFH` is replaced by
  `ZInQ.BFHPrinted.fhNonvanishing_of_bfhClauseIIKronecker hBFH`. -/

namespace ZInQ.Contrib.TYZChain

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

/-- **Theorem 1.1, from every statement still open, with `hFH` replaced by BFH clause (ii) over the
Kronecker symbol** (the leaf applied once, at `B = 4`, `S` = the primes dividing `2N`). -/
theorem frozenTarget_bfhKronecker
    (r : HDec.HSyn.OpenResearchLeaves22) (t : HDec.HSyn.OpenTextbookLeaves11) (l : HDec.HSyn.OpenAddedLeaves17)
    (g : HDec.HSyn.OpenGlue7)
    (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2)
    (hCM : _root_.T5Glue.ShimuraMainCM)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hBFH : ZInQ.BFHPrinted.BFHClauseIIKronecker) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget :=
  ZInQ.BFHPrinted.frozenTarget_of_sixContactMin_tyzThm35ReadingA_bfhKronecker
    (HDec.HSyn.sixContactMin_of_open29 r t l g)
    (ThetaWP8.tyzThm35ReadingA_noHX h11 h29 hCM h33)
    ZInQ.GZTheta.Frontier.heckeThetaNewform hBFH hL3

/-- The drop-in alternative (every bound `B`, through `FHNonvanishing`). -/
theorem frozenTarget_bfhKronecker_allB
    (r : HDec.HSyn.OpenResearchLeaves22) (t : HDec.HSyn.OpenTextbookLeaves11) (l : HDec.HSyn.OpenAddedLeaves17)
    (g : HDec.HSyn.OpenGlue7)
    (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2)
    (hCM : _root_.T5Glue.ShimuraMainCM)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hBFH : ZInQ.BFHPrinted.BFHClauseIIKronecker) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget :=
  ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves
    (HDec.HSyn.sixContactMin_of_open29 r t l g)
    (ThetaWP8.tyzThm35ReadingA_noHX h11 h29 hCM h33)
    ZInQ.GZTheta.Frontier.heckeThetaNewform (ZInQ.BFHPrinted.fhNonvanishing_of_bfhClauseIIKronecker hBFH) hL3

end ZInQ.Contrib.TYZChain

#print axioms ZInQ.Contrib.TYZChain.frozenTarget_bfhKronecker
#print axioms ZInQ.Contrib.TYZChain.frozenTarget_bfhKronecker_allB
