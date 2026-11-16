import ZInQKernel.OneProof.H.TailZ42
import ZInQKernel.OneProof.TYZSplit
import ZInQKernel.OneProof.TopChain
import ZInQKernel.Contrib.TYZChain.Main
import ZInQKernel.Contrib.OneProof.RingClassLattice
import ZInQKernel.Contrib.OneProof.TYZLemma29Mod2
import ZInQKernel.Contrib.OneProof.FHNonvanishing
import ZInQKernel.Contrib.OneProof.ThetaWeierstrass8
import ZInQKernel.Contrib.OneProof.JonesPall

/-!
# jp-compile: manual fold check for `hJP`

`ZInQKernel/OneProof/Main.lean` (fork main 2880fef1 / 0caafe66, unchanged) with the binder
`hJP : H29Split.JonesPallX2Y2Z16` dropped and PR #38's proof
`ZInQ.Contrib.OneProof.JonesPall.jonesPall_proof` passed in its place. autofold.py folds only bundle fields,
so the fold of this `frozenTarget` argument is manual; this file is the fold's new `Main` body.
-/

namespace ZInQ.Contrib.TYZChain

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

/-- **Theorem 1.1, from every statement still open.** -/
theorem _root_.ZInQ.OneProof.frozenTarget
    (r : HDec.HSyn.OpenResearchLeaves26) (t : HDec.HSyn.OpenTextbookLeaves12) (l : HDec.HSyn.OpenAddedLeaves17)
    (g : HDec.HSyn.OpenGlue8)
    (h11 : TYZThm11Integral)
    (hL3s : H29Split.LegendreThreeSquares)
    (hfx : H29Split.TYZTestVectorExists) (hL29 : H29Split.TYZLemma29PrintedNe3)
    (hT21 : H29Split.TYZThm21At31) (hP23 : H29Split.TYZProp23Printed)
    (hCM : _root_.T5Glue.ShimuraMainCM)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hFH : ZInQ.GZFH.FriedbergHoffsteinB_FE) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget :=
  ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves
    (HDec.HSyn.sixContactMin_of_open35 r t l g)
    (ThetaWP8.tyzThm35ReadingA_noHX h11 (H29Split.tyzLemma29Mod2_of_sixLeaves hL3s
      ZInQ.Contrib.OneProof.JonesPall.jonesPall_proof hfx hL29 hT21 hP23) hCM h33)
    ZInQ.GZTheta.Frontier.heckeThetaNewform (ZInQ.GZFH.fhNonvanishing_of_friedbergHoffsteinB_FE hFH) hL3

end ZInQ.Contrib.TYZChain

#print axioms ZInQ.OneProof.frozenTarget

#check @ZInQ.OneProof.frozenTarget
