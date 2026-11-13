
/-! ## g12-det: `G12Weight` from `HTExtend` and the two new leaves -/

namespace G0Galois

/-- **`G12Weight` from `HTExtend` (glue) and the leaves `SenTwist`, `FiniteImageHT`.** -/
theorem g12Weight_of_htExtend (hX : HTExtend) (hSen : SenTwist) (hFI : FiniteImageHT) :
    G12Weight :=
  g12Weight_of_HT (htConj_of hX) hSen hFI

end G0Galois

#print axioms G0Galois.g12Weight_of_htExtend
