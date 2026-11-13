
/-! # spread-out: `FrobTrace.AlgFrobRed` and `G14Bridge.TateBridge35` without N1-g1

Appended by `build_full.sh` after frob-pieces' assembled `FrobPiecesFull.lean` (used unchanged,
with this task's import `ZInQKernel.Contrib.SpreadOut.NumberField` added to its import block).
frob-pieces' `FrobPiecesNeron.AbVarSpreadsOut` is a verbatim copy of neron-lg's N1-g1; it is
discharged here by `ZInQ.Contrib.SpreadOut.NF.abVarSpreadsOut_of_ega` from the three EGA IV
leaves. -/

namespace ZInQ.SpreadOutFull

open ZInQ.Contrib.SpreadOut

/-- frob-pieces' copy of N1-g1 from the EGA IV leaves 8.8.2 (ii), 8.10.5 (xii), 17.7.8 (ii). -/
theorem frobPiecesNeron_abVarSpreadsOut (h882 : EGAIV_8_8_2_ii) (hpr : EGAIV_8_10_5_xii)
    (hsm : EGAIV_17_7_8_ii) : FrobPiecesNeron.AbVarSpreadsOut :=
  fun L _ _ B => NF.abVarSpreadsOut_of_ega h882 hpr hsm L B

/-- **`FrobTrace.AlgFrobRed` from the EGA IV leaves 8.8.2 (ii), 8.10.5 (xii), 17.7.8 (ii), the
leaf candidate `ProperSmoothGenConnected` (Zariski connectedness) and the kernel leaves I2-Red,
I2-NMP (proved).** -/
theorem algFrobRed_of_ega_nmp (h882 : EGAIV_8_8_2_ii) (hpr : EGAIV_8_10_5_xii)
    (hsm : EGAIV_17_7_8_ii) (hc : FrobPiecesNeron.ProperSmoothGenConnected)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hN : PkgI2.NeronMappingAbelianScheme.{0}) :
    FrobTrace.AlgFrobRed :=
  FrobPiecesGood.algFrobRed_of_neron_nmp (frobPiecesNeron_abVarSpreadsOut h882 hpr hsm) hc hRed hN

/-- **`G14Bridge.TateBridge35` from I3.M0, the EGA IV leaves, `ProperSmoothGenConnected`, I2-Red,
I2-NMP (proved).** -/
theorem tateBridge35_of_ega_nmp (hT : PkgI3.TateModuleFree) (h882 : EGAIV_8_8_2_ii)
    (hpr : EGAIV_8_10_5_xii) (hsm : EGAIV_17_7_8_ii)
    (hc : FrobPiecesNeron.ProperSmoothGenConnected)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hN : PkgI2.NeronMappingAbelianScheme.{0}) :
    G14Bridge.TateBridge35 :=
  FrobPiecesGood.tateBridge35_of_neron_nmp hT (frobPiecesNeron_abVarSpreadsOut h882 hpr hsm) hc
    hRed hN

end ZInQ.SpreadOutFull

#print axioms ZInQ.SpreadOutFull.frobPiecesNeron_abVarSpreadsOut
#print axioms ZInQ.SpreadOutFull.algFrobRed_of_ega_nmp
#print axioms ZInQ.SpreadOutFull.tateBridge35_of_ega_nmp
