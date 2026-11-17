import ZInQKernel.OneProof.Main
import ZInQKernel.OneProof.Discharges
import ZInQKernel.Contrib.OneProof.FriedbergHoffsteinBFE

#discharges

/-! The fold, checked without editing Main: `frozenTarget` with `hFH` replaced by the printed leaf. -/
theorem fhprinted_frozenTarget
    (r : HDec.HSyn.OpenResearchLeaves22) (t : HDec.HSyn.OpenTextbookLeaves11)
    (l : HDec.HSyn.OpenAddedLeaves17) (g : HDec.HSyn.OpenGlue7)
    (h11 : ZInQ.Contrib.TYZDecomp.TYZThm11Integral) (h29 : ZInQ.Contrib.TYZDecomp.TYZLemma29Mod2)
    (hCM : _root_.T5Glue.ShimuraMainCM) (hX : _root_.T5Glue.X0ModuliGalois)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hFHP : ZInQ.FHPrinted.FriedbergHoffsteinB_Printed)
    (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget :=
  ZInQ.OneProof.frozenTarget r t l g h11 h29 hCM hX h33
    (ZInQ.FHPrinted.friedbergHoffsteinB_FE_of_printed hFHP) hL3

#print axioms fhprinted_frozenTarget
#print axioms ZInQ.FHPrinted.friedbergHoffsteinB_FE_of_printed
#print axioms ZInQ.FHPrinted.friedbergHoffsteinB_printed_of_FE
#print axioms ZInQ.FHPrinted.friedbergHoffsteinB_printed_iff_FE
#print axioms ZInQ.FHPrinted.rootNumberTwistEqOne_iff
#print axioms ZInQ.FHPrinted.idelicChar_eq_jacobiSym
