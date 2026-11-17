import ZInQKernel.OneProof.Main
import ZInQKernel.Contrib.OneProof.BFHGamma0

/-! The fold of task bfh-gamma0, checked without editing `Main`: the body of
`ZInQ.OneProof.frozenTarget` (`ZInQKernel/OneProof/Main.lean` on main, 2880fef1e) with the top
hypothesis `hFH : ZInQ.GZFH.FriedbergHoffsteinB_FE` replaced by the printed leaf
`hBFH : ZInQ.BFHPrinted.BFHClauseIIGamma0` (Bump–Friedberg–Hoffstein 1990, clause (ii), for the
classical newform on `Γ₀(N)`, `χ_D(n) = (D / n)`).

* `frozenTarget_bfhGamma0` (the fold, `B = 4` only): the call
  `ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves A B H
  (ZInQ.GZFH.fhNonvanishing_of_friedbergHoffsteinB_FE hFH) hL3` is replaced by
  `ZInQ.BFHPrinted.frozenTarget_of_sixContactMin_tyzThm35ReadingA_bfhGamma0 A B H hBFH hL3`
  (`A`, `B`, `H` verbatim from main's body).
* `frozenTarget_bfhGamma0_allB` (drop-in alternative): only the argument
  `ZInQ.GZFH.fhNonvanishing_of_friedbergHoffsteinB_FE hFH` is replaced by
  `ZInQ.BFHPrinted.fhNonvanishing_of_bfhClauseIIGamma0 hBFH`. -/

namespace ZInQ.Contrib.TYZChain

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

/-- **Theorem 1.1, from every statement still open, with `hFH` replaced by BFH clause (ii) over the
classical `Γ₀(N)`-newform** (the leaf applied once, at `B = 4`, `S` = the primes dividing `2N`). -/
theorem frozenTarget_bfhGamma0
    (r : HDec.HSyn.OpenResearchLeaves26) (t : HDec.HSyn.OpenTextbookLeaves12) (l : HDec.HSyn.OpenAddedLeaves17)
    (g : HDec.HSyn.OpenGlue8)
    (h11 : TYZThm11Integral)
    (hL3s : H29Split.LegendreThreeSquares) (hJP : H29Split.JonesPallX2Y2Z16)
    (hfx : H29Split.TYZTestVectorExists) (hL29 : H29Split.TYZLemma29PrintedNe3)
    (hT21 : H29Split.TYZThm21At31) (hP23 : H29Split.TYZProp23Printed)
    (hCM : _root_.T5Glue.ShimuraMainCM)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hBFH : ZInQ.BFHPrinted.BFHClauseIIGamma0) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget :=
  ZInQ.BFHPrinted.frozenTarget_of_sixContactMin_tyzThm35ReadingA_bfhGamma0
    (HDec.HSyn.sixContactMin_of_open35 r t l g)
    (ThetaWP8.tyzThm35ReadingA_noHX h11 (H29Split.tyzLemma29Mod2_of_sixLeaves hL3s hJP hfx hL29 hT21 hP23) hCM h33)
    ZInQ.GZTheta.Frontier.heckeThetaNewform hBFH hL3

/-- The drop-in alternative (every bound `B`, through `FHNonvanishing`). -/
theorem frozenTarget_bfhGamma0_allB
    (r : HDec.HSyn.OpenResearchLeaves26) (t : HDec.HSyn.OpenTextbookLeaves12) (l : HDec.HSyn.OpenAddedLeaves17)
    (g : HDec.HSyn.OpenGlue8)
    (h11 : TYZThm11Integral)
    (hL3s : H29Split.LegendreThreeSquares) (hJP : H29Split.JonesPallX2Y2Z16)
    (hfx : H29Split.TYZTestVectorExists) (hL29 : H29Split.TYZLemma29PrintedNe3)
    (hT21 : H29Split.TYZThm21At31) (hP23 : H29Split.TYZProp23Printed)
    (hCM : _root_.T5Glue.ShimuraMainCM)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hBFH : ZInQ.BFHPrinted.BFHClauseIIGamma0) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget :=
  ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves
    (HDec.HSyn.sixContactMin_of_open35 r t l g)
    (ThetaWP8.tyzThm35ReadingA_noHX h11 (H29Split.tyzLemma29Mod2_of_sixLeaves hL3s hJP hfx hL29 hT21 hP23) hCM h33)
    ZInQ.GZTheta.Frontier.heckeThetaNewform (ZInQ.BFHPrinted.fhNonvanishing_of_bfhClauseIIGamma0 hBFH) hL3

end ZInQ.Contrib.TYZChain

#print axioms ZInQ.Contrib.TYZChain.frozenTarget_bfhGamma0
#print axioms ZInQ.Contrib.TYZChain.frozenTarget_bfhGamma0_allB
