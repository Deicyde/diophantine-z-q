import ZInQKernel.OneProof.Main
import ZInQKernel.Contrib.OneProof.TYZThm11Integral

/-!
# h11-reduce: Theorem 1.1 with `h11`, `hL29`, `hT21` replaced by `hL29R`, `hTun` (the manual fold)

`frozenTarget` (base 0caafe66) with its arguments `h11 : TYZThm11Integral`,
`hL29 : H29Split.TYZLemma29PrintedNe3` and `hT21 : H29Split.TYZThm21At31` removed and two leaves added:
`hL29R : H11Reduce.TYZLemma29PrintedNe3R` (Lemma 2.9 for real sign choices of 𝓛; implies `hL29`) and
`hTun : H11Reduce.TunnellOddL1` (Tunnell's formula). The body is `Main.lean`'s with
`h11 := tyzThm11Integral_of_leaves hL3s hJP hfx hL29R hTun` and
`tyzLemma29Mod2_of_sixLeaves hL3s hJP hfx hL29 hT21 hP23` replaced by
`tyzLemma29Mod2_of_tunnellR hL3s hJP hfx hL29R hP23 hTun`.
-/

namespace ZInQ.Contrib.TYZChain

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

theorem h11reduce_frozenTarget
    (r : HDec.HSyn.OpenResearchLeaves26) (t : HDec.HSyn.OpenTextbookLeaves12) (l : HDec.HSyn.OpenAddedLeaves17)
    (g : HDec.HSyn.OpenGlue8)
    (hL3s : H29Split.LegendreThreeSquares) (hJP : H29Split.JonesPallX2Y2Z16)
    (hfx : H29Split.TYZTestVectorExists) (hL29R : H11Reduce.TYZLemma29PrintedNe3R)
    (hP23 : H29Split.TYZProp23Printed) (hTun : H11Reduce.TunnellOddL1)
    (hCM : _root_.T5Glue.ShimuraMainCM)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hFH : ZInQ.GZFH.FriedbergHoffsteinB_FE) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget :=
  ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves
    (HDec.HSyn.sixContactMin_of_open35 r t l g)
    (ThetaWP8.tyzThm35ReadingA_noHX (H11Reduce.tyzThm11Integral_of_leaves hL3s hJP hfx hL29R hTun)
      (H11Reduce.tyzLemma29Mod2_of_tunnellR hL3s hJP hfx hL29R hP23 hTun) hCM h33)
    ZInQ.GZTheta.Frontier.heckeThetaNewform (ZInQ.GZFH.fhNonvanishing_of_friedbergHoffsteinB_FE hFH) hL3

/-- The new hypotheses give the old ones it drops: `h11` and `hL29` (so the new theorem is at least as strong
as `frozenTarget` with those two arguments discharged). -/
theorem h11reduce_old_args (hL3s : H29Split.LegendreThreeSquares) (hJP : H29Split.JonesPallX2Y2Z16)
    (hfx : H29Split.TYZTestVectorExists) (hL29R : H11Reduce.TYZLemma29PrintedNe3R)
    (hTun : H11Reduce.TunnellOddL1) :
    TYZThm11Integral ∧ H29Split.TYZLemma29PrintedNe3 :=
  ⟨H11Reduce.tyzThm11Integral_of_leaves hL3s hJP hfx hL29R hTun, H11Reduce.tyzLemma29PrintedNe3_of_R hL29R⟩

end ZInQ.Contrib.TYZChain

#print axioms ZInQ.Contrib.TYZChain.h11reduce_frozenTarget
