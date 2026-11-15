import ZInQKernel.OneProof.Main
import ZInQKernel.OneProof.Discharges
import ZInQKernel.Contrib.OneProof.TYZLemma29Mod2

/-! Check file (h29-ne3), as in `docs/one-proof/CONTRIBUTING.md`: imports `Main`, `Discharges` and the
revised contribution (`scratch/h29-ne3/TYZLemma29Mod2.lean`, built as the module
`ZInQKernel.Contrib.OneProof.TYZLemma29Mod2` by copying it over that file in the task worktree). -/

open ZInQ.Contrib.TYZDecomp in
/-- Theorem 1.1 with `h29` replaced by the six published statements (same as `scratch/h29-ne3/MainEdit.lean`). -/
theorem h29ne3_frozenTarget
    (r : HDec.HSyn.OpenResearchLeaves19) (t : HDec.HSyn.OpenTextbookLeaves10) (l : HDec.HSyn.OpenAddedLeaves16)
    (g : HDec.HSyn.OpenGlue7) (h11 : TYZThm11Integral)
    (hL3s : H29Split.LegendreThreeSquares) (hJP : H29Split.JonesPallX2Y2Z16)
    (hfx : H29Split.TYZTestVectorExists) (hL29 : H29Split.TYZLemma29PrintedNe3)
    (hT21 : H29Split.TYZThm21At31) (hP23 : H29Split.TYZProp23Printed)
    (hCM : _root_.T5Glue.ShimuraMainCM) (hX : _root_.T5Glue.X0ModuliGalois)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hL2 : ZInQ.GZDecomp.FHNonvanishing) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget :=
  ZInQ.OneProof.frozenTarget r t l g h11
    (H29Split.tyzLemma29Mod2_of_sixLeaves hL3s hJP hfx hL29 hT21 hP23) hCM hX h33 hL2 hL3

#print axioms ZInQ.Contrib.TYZDecomp.H29Split.tyzLemma29Mod2_of_sixLeaves
#print axioms ZInQ.Contrib.TYZDecomp.H29Split.tyzLemma29Printed_of_ne3_thm21
#print axioms ZInQ.Contrib.TYZDecomp.H29Split.lemma29At_three
#print axioms ZInQ.Contrib.TYZDecomp.H29Split.torsionOrder_qNeg_three
#print axioms ZInQ.Contrib.TYZDecomp.H29Split.sqClasses_three
#print axioms ZInQ.Contrib.TYZDecomp.H29Split.pairIdx_three_eq
#print axioms h29ne3_frozenTarget

#discharges
