
/-! ## g12-det: g0-mod-galois's `GaloisPieces` with `weight`, `detTate`, `finIndex` discharged -/

namespace G0Galois

open PkgI4 (GaloisRep GaloisChar)

/-- **`GaloisPieces` from Burnside, R14Det, `G9Glue`, `G10Glue`, the two new leaves `SenTwist`,
`FiniteImageHT`, weil-pairing's three leaves and T26.** -/
theorem galoisPieces_of (hB : BurnsideAbsIrred) (hR : R14Det) (h9 : G9Glue) (h10 : G10Glue)
    (hSen : SenTwist) (hFI : FiniteImageHT) (hW : WeilPairing.T09_SymmIsogenyExists)
    (hQ : WeilPairing.IsogenyQuasiInverse) (hD : WeilPairing.DivisiblePoints)
    (hT : PkgI3.TateModuleFree) : GaloisPieces :=
  ⟨hB, hR, h9, h10, g12Weight_of_senTwist hSen hFI, detTate_of_leaves hW hQ hD hT,
    resQFiniteIndex⟩

/-- **G8-G12 from the leaf bundles with the remaining glue `G9Glue`, `G10Glue` only** (plus the
leaves Burnside, R14Det, `SenTwist`, `FiniteImageHT`, weil-pairing's three; T26 is the bundle's
`t26`). -/
theorem g8_g12_of_leaves' (r : HSyn.ResearchLeaves) (t : HSyn.TextbookLeaves)
    (hB : BurnsideAbsIrred) (hR : R14Det) (h9 : G9Glue) (h10 : G10Glue)
    (hSen : SenTwist) (hFI : FiniteImageHT) (hW : WeilPairing.T09_SymmIsogenyExists)
    (hQ : WeilPairing.IsogenyQuasiInverse) (hD : WeilPairing.DivisiblePoints)
    {K : Type} [Field K] [NumberField K] [IsGalois ℚ K] (A : PkgI3.AbVar K) (T : Finset ℕ)
    (h2 : G2Out K T) (h6 : G6Out A) (h3 : G3Out A 5 T)
    (Tm : PkgI4.GQ → Module.End (PadicAlgCl 5) (Vb A 5))
    (c ε : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 5) (a β : PkgI4.GQ → PadicAlgCl 5)
    (u : GlueDescent.MatrixUnits2 (PadicAlgCl 5) (Vb A 5))
    (h7 : G7Out A 5 Tm c ε a β u) :
    ∃ r₅ : GaloisRep 5 2, G8Out A 5 (GlueDescent.rho Tm a β) r₅ ∧ G9Out r₅ ∧ G10Out r₅ ∧
      G11Out T r₅ ∧ G12Out r₅ :=
  g8_g12_of_leaves r t (galoisPieces_of hB hR h9 h10 hSen hFI hW hQ hD t.t26) A T h2 h6 h3 Tm
    c ε a β u h7

end G0Galois

#print axioms G0Galois.galoisPieces_of
#print axioms G0Galois.g8_g12_of_leaves'
