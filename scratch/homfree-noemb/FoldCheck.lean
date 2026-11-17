import ZInQKernel.OneProof.Main
import ZInQKernel.Contrib.OneProof.HomFreeFiniteAlgClosedReroute

/-! homfree-noemb fold check: `ZInQ.FrozenTarget` from every open statement of `ZInQ.OneProof.frozenTarget`
except `OpenTextbookLeaves13.homFreeFiniteAlgClosed` (the textbook bundle is `OpenTextbookLeaves13HF`, the same
structure without that field). The body is `frozenTarget`'s, with `sixContactMin_of_open38` replaced by the
rerouted `sixContactMin_of_open38_hf`. -/

namespace ZInQ.Contrib.TYZChain

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

theorem _root_.ZInQ.OneProof.frozenTarget_hf
    (r : HDec.HSyn.OpenResearchLeaves28) (t : HDec.HSyn.OpenTextbookLeaves13HF) (l : HDec.HSyn.OpenAddedLeaves19)
    (h11 : TYZThm11Integral)
    (hfx : H29Split.TYZTestVectorExists) (hL29 : H29Split.TYZLemma29PrintedNe3)
    (hP23 : H29Split.TYZProp23Printed)
    (hCM : _root_.T5Glue.ShimuraMainCM)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hBFH : ZInQ.BFHPrinted.BFHClauseIIGamma0) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget :=
  ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves
    (HDec.HSyn.sixContactMin_of_open38_hf r t l)
    (ThetaWP8.tyzThm35ReadingA_noHX h11 (H29Split.tyzLemma29Mod2_of_sixLeaves ZInQ.Contrib.OneProof.LegendreThreeSquares.legendreThreeSquares_proof
      ZInQ.Contrib.OneProof.JonesPall.jonesPall_proof hfx hL29 ZInQ.Contrib.T21Proof.tyzThm21At31 hP23) hCM h33)
    ZInQ.GZTheta.Frontier.heckeThetaNewform (ZInQ.BFHPrinted.fhNonvanishing_of_bfhClauseIIGamma0 hBFH) hL3

end ZInQ.Contrib.TYZChain

/-- The structures differ exactly by the field: every field of `OpenTextbookLeaves13HF` is a field of
`OpenTextbookLeaves13` with the same type (checked by this map, field by field). -/
theorem HDec.HSyn.openTextbookLeaves13HF_of_13 (t : HDec.HSyn.OpenTextbookLeaves13) :
    HDec.HSyn.OpenTextbookLeaves13HF where
  mumfordTorsionAlgClosed := t.mumfordTorsionAlgClosed
  charPolyIndepOfEllAlgClosed := t.charPolyIndepOfEllAlgClosed
  poincareComplement := t.poincareComplement
  gagaMorphism := t.gagaMorphism
  neronSchemeExtensionExists := t.neronSchemeExtensionExists

#print axioms ZInQ.OneProof.frozenTarget_hf
#print axioms HDec.HSyn.sixContactMin_of_open38_hf
