
/-! # zariski-conn: `ProperSmoothGenConnected` from Zariski's connectedness theorem

Appended by `scratch/zariski-conn/build.sh` after a verbatim copy of frob-pieces' assembled
`FrobPiecesFull.lean`. The proofs are in `ZInQKernel/Contrib/ZariskiConn/Basic.lean` (imported
above). -/

noncomputable section

namespace ZariskiConnGlue

open CategoryTheory AlgebraicGeometry
open ZInQ LeafQM.AV GlueDescent G0ModField UnramTate AlgFrobRedRed

/-- **frob-pieces' `ProperSmoothGenConnected` from Zariski's connectedness theorem (proved).**
The Contrib copy `ZariskiConn.ProperSmoothGenConnected` has the same text, so the two `def`s are
definitionally equal. -/
theorem properSmoothGenConnected (hZ : ZariskiConn.ZariskiConnectedness.{0}) :
    FrobPiecesNeron.ProperSmoothGenConnected :=
  ZariskiConn.properSmoothGenConnected_of_zariskiConnectedness hZ

/-- **`GoodRedCofinite` from N1-g1 and Zariski's connectedness theorem (proved).** -/
theorem goodRedCofinite_of_neron_zariski (hsp : FrobPiecesNeron.AbVarSpreadsOut)
    (hZ : ZariskiConn.ZariskiConnectedness.{0}) : AlgFrobRedRed.GoodRedCofinite :=
  FrobPiecesNeron.goodRedCofinite_of_neron hsp (properSmoothGenConnected hZ)

/-- **`FrobTrace.AlgFrobRed` from N1-g1, Zariski's connectedness theorem, I2-Red and I2-NMP
(proved).** -/
theorem algFrobRed_of_neron_zariski_nmp (hsp : FrobPiecesNeron.AbVarSpreadsOut)
    (hZ : ZariskiConn.ZariskiConnectedness.{0})
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hN : PkgI2.NeronMappingAbelianScheme.{0}) :
    FrobTrace.AlgFrobRed :=
  FrobPiecesGood.algFrobRed_of_neron_nmp hsp (properSmoothGenConnected hZ) hRed hN

/-- **`G14Bridge.TateBridge35` from I3.M0, N1-g1, Zariski's connectedness theorem, I2-Red and
I2-NMP (proved).** -/
theorem tateBridge35_of_neron_zariski_nmp (hT : PkgI3.TateModuleFree)
    (hsp : FrobPiecesNeron.AbVarSpreadsOut) (hZ : ZariskiConn.ZariskiConnectedness.{0})
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hN : PkgI2.NeronMappingAbelianScheme.{0}) :
    G14Bridge.TateBridge35 :=
  FrobPiecesGood.tateBridge35_of_neron_nmp hT hsp (properSmoothGenConnected hZ) hRed hN

end ZariskiConnGlue

end

#print axioms ZariskiConn.properSmoothGenConnected_of_zariskiConnectedness
#print axioms ZariskiConn.appTop_bijective_of_generic
#print axioms ZariskiConn.app_bijective_of_appTop_bijective
#print axioms ZariskiConn.dedekind_fractionRing_of_away
#print axioms ZariskiConnGlue.properSmoothGenConnected
#print axioms ZariskiConnGlue.goodRedCofinite_of_neron_zariski
#print axioms ZariskiConnGlue.algFrobRed_of_neron_zariski_nmp
#print axioms ZariskiConnGlue.tateBridge35_of_neron_zariski_nmp
