
/-- **The glue pieces, one-triple form** (task pin-apply, after qm-pin): `GluePieces` with the
three QM pieces 4, 9, 10 stated for some triple satisfying the repaired clause lists
(`G0Split.FibreSimpleW`, `ThetaPointOfFibreW`, `ModularConstituentW`) and qm-pin's curve glue
`MobiusGlue` as an eleventh named piece. Given the leaves, it is equivalent to `GluePieces` plus
`MobiusGlue` (`gluePieces_of_pin`, `gluePiecesPin_of`). -/
structure GluePiecesPin : Prop where
  dimFinite : G0Split.DimFinite
  dimBaseChange : G0Split.DimBaseChange
  /-- 4. G5-G6 on the fibre surface, for one triple. -/
  fibreSimple : G0Split.FibreSimpleW
  productModelHeight : ZInQ.H5Neron.ProductModelHeight
  stableHeightBaseChange : G0Split.StableHeightBaseChange
  productExists : G0Split.ProductExists
  reverseIsogeny : G0Split.ReverseIsogeny
  /-- 9. G19 on the fibre surface, for one triple. -/
  thetaPoint : G0Split.ThetaPointOfFibreW
  /-- 10. G2, G4, G7-G16, for one triple. -/
  modularConstituent : G0Split.ModularConstituentW
  heightCopies : HeightCopiesAgree
  /-- 12. qm-pin's curve glue: two triples compared on `Φ` by `g` are compared on `π` by `g`. -/
  mobius : LeafQM.AV.Pin.MobiusGlue

theorem gluePieces_of_pin (r : ResearchLeaves) (gp : GluePiecesPin) : GluePieces := by
  obtain ⟨a, b, c, d, e, f, g, h, i, j, hM⟩ := gp
  obtain ⟨h4, h9, h10⟩ := G0Split.qmPieces_iff_w hM (LeafAdopt.R1R2fp_of_rep r.r1r2)
  exact ⟨a, b, h4.2 c, d, e, f, g, h9.2 h, h10.2 i, j⟩

theorem gluePiecesPin_of (r : ResearchLeaves) (gp : GluePieces) (hM : LeafQM.AV.Pin.MobiusGlue) :
    GluePiecesPin := by
  obtain ⟨a, b, c, d, e, f, g, h, i, j⟩ := gp
  obtain ⟨h4, h9, h10⟩ := G0Split.qmPieces_iff_w hM (LeafAdopt.R1R2fp_of_rep r.r1r2)
  exact ⟨a, b, h4.1 c, d, e, f, g, h9.1 h, h10.1 i, j, hM⟩

/-- **G0, one-triple form** (no `sorry`): the leaves and `GluePiecesPin` imply `SixContactMin`. -/
theorem sixContactMin_of_leaves_pin (r : ResearchLeaves) (t : TextbookLeaves)
    (gp : GluePiecesPin) : ZInQ.SixContactMin :=
  sixContactMin_of_leaves r t (gluePieces_of_pin r gp)
