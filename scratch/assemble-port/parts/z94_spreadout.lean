/-! ## assemble-port: spread-out (N1-g1 `AbVarSpreadsOut` from three EGA IV leaves)

spread-out proves, in the kernel module `ZInQKernel/Contrib/SpreadOut/NumberField.lean` (merged from origin/wip/spread-out,
imported here through imports_tailD.txt), `ZInQ.Contrib.SpreadOut.NF.abVarSpreadsOut_of_ega`: the body of neron-lg's
`AbVarSpreadsOut` for the kernel's `PkgI3.AbVar` (`ZInQKernel/HDecomp/Objects.lean`), from the leaves `EGAIV_8_8_2_ii`,
`EGAIV_8_10_5_xii`, `EGAIV_17_7_8_ii` (`ZInQKernel/Contrib/SpreadOut/Spread.lean`, Mathlib-only statements). The theorem
below applies it to frob-pieces' copy `FrobPiecesNeron.AbVarSpreadsOut` (over this file's `PkgI3.AbVar`, a structure with
the same five fields): an abelian variety `B` of this file is sent to the kernel's `⟨B.X⟩`, and the conclusion, which
mentions only `B.X` and its group structure, is accepted by unfolding. -/

namespace HSyn

/-- **N1-g1 from EGA IV₃ 8.8.2 (ii), EGA IV₃ 8.10.5 (xii), EGA IV₄ 17.7.8 (ii)** (spread-out). -/
theorem abVarSpreadsOut_of_ega (h882 : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_8_2_ii)
    (hpr : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii)
    (hsm : _root_.ZInQ.Contrib.SpreadOut.EGAIV_17_7_8_ii) : FrobPiecesNeron.AbVarSpreadsOut :=
  fun L _ _ B => _root_.ZInQ.Contrib.SpreadOut.NF.abVarSpreadsOut_of_ega h882 hpr hsm L ⟨B.X⟩

end HSyn

#print axioms HSyn.abVarSpreadsOut_of_ega
