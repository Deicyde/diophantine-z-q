
open ZInQ.Contrib.TYZDecomp in
/-- Theorem 1.1 with `h29` replaced by the five published statements. -/
theorem h29fix_frozenTarget
    (r : HDec.HSyn.OpenResearchLeaves19) (t : HDec.HSyn.OpenTextbookLeaves10) (l : HDec.HSyn.OpenAddedLeaves16)
    (g : HDec.HSyn.OpenGlue7) (h11 : TYZThm11Integral)
    (hL : H29Split.LegendreThreeSquares) (hJ : H29Split.JonesPallX2Y2Z16)
    (hfx : H29Split.TYZTestVectorExists) (hL29 : H29Split.TYZLemma29Printed)
    (hP23 : H29Split.TYZProp23Printed)
    (hCM : _root_.T5Glue.ShimuraMainCM) (hX : _root_.T5Glue.X0ModuliGalois)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hL2 : ZInQ.GZDecomp.FHNonvanishing) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget :=
  ZInQ.OneProof.frozenTarget r t l g h11
    (H29Split.tyzLemma29Mod2_of_printedLeaves_legendre hL hJ hfx hL29 hP23) hCM hX h33 hL2 hL3

#print axioms ZInQ.Contrib.TYZDecomp.H29Split.tyzLemma29Mod2_of_printedLeaves_legendre
#print axioms ZInQ.Contrib.TYZDecomp.H29Split.legendreJonesPall_of
#print axioms ZInQ.Contrib.TYZDecomp.H29Split.tv_eq_of_toClassGroup_eq
#print axioms ZInQ.Contrib.TYZDecomp.H29Split.genusPeriodTV_eq_of_section
#print axioms ZInQ.Contrib.TYZDecomp.H29Split.exists_isPlaceTwo
#print axioms h29fix_frozenTarget

#discharges
