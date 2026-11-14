/-! ## av-b1: leaf-fold3's fields t6, t7, t8 (`HDec.HSyn.OpenTextbookLeaves3`) from smaller Props -/

namespace HDec

namespace AVB1Check

open ZInQ.Contrib.AVB1

/-- leaf-fold3's field `t6 : PkgI3.HomFreeFinite` from Mumford §19 Thm 3 over algebraically closed
fields. -/
theorem t6_of_algClosed (h : HomFreeFiniteAlgClosed) : PkgI3.HomFreeFinite :=
  homFreeFinite_of_algClosed h

/-- leaf-fold3's field `t7 : PkgI3.CharPolyIndepOfEll` from Mumford §19 Thm 4 over algebraically
closed fields. -/
theorem t7_of_algClosed (h : CharPolyIndepOfEllAlgClosed) : PkgI3.CharPolyIndepOfEll :=
  charPolyIndepOfEll_of_algClosed h

/-- leaf-fold3's field `t8 : PkgI3.PoincareReducibility` from Poincaré's theorem (complement form)
and two textbook facts. -/
theorem t8_of_pieces (hP : PoincareComplement) (hI : ImageFactorization) (hS : SimpleSurjIsogeny) :
    PkgI3.PoincareReducibility :=
  poincareReducibility_of_pieces hP hI hS

/-- The three fields at once. -/
theorem t6_t7_t8_of_avb1 (h6 : HomFreeFiniteAlgClosed) (h7 : CharPolyIndepOfEllAlgClosed)
    (hP : PoincareComplement) (hI : ImageFactorization) (hS : SimpleSurjIsogeny) :
    PkgI3.HomFreeFinite ∧ PkgI3.CharPolyIndepOfEll ∧ PkgI3.PoincareReducibility :=
  ⟨t6_of_algClosed h6, t7_of_algClosed h7, t8_of_pieces hP hI hS⟩

/-- The field types of leaf-fold3's bundle are exactly these Props. -/
example (t : HSyn.OpenTextbookLeaves3) :
    PkgI3.HomFreeFinite ∧ PkgI3.CharPolyIndepOfEll ∧ PkgI3.PoincareReducibility :=
  ⟨t.t6, t.t7, t.t8⟩

end AVB1Check

end HDec

#print axioms HDec.ZInQ.Contrib.AVB1.bcHom_injective
#print axioms HDec.ZInQ.Contrib.AVB1.tateBC_bijective_closure
#print axioms HDec.ZInQ.Contrib.AVB1.homFreeFinite_of_algClosed
#print axioms HDec.ZInQ.Contrib.AVB1.charPolyIndepOfEll_of_algClosed
#print axioms HDec.ZInQ.Contrib.AVB1.poincareReducibility_of_pieces
#print axioms HDec.AVB1Check.t6_of_algClosed
#print axioms HDec.AVB1Check.t7_of_algClosed
#print axioms HDec.AVB1Check.t8_of_pieces
#print axioms HDec.AVB1Check.t6_t7_t8_of_avb1
