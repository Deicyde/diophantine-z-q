
/-! # frob-pieces: the combined form with afr-absfrob's `AbsFrob` and `FExtendGen`

Appended by `build_full.sh` after afr-absfrob's assembled `AfrAbsFrob.lean` (verbatim copy, which
begins with alg-frob-red's `AlgFrobRed.lean`) and this task's parts. -/

noncomputable section

namespace FrobPiecesGood

open CategoryTheory AlgebraicGeometry
open ZInQ LeafQM.AV GlueDescent G0ModField UnramTate AlgFrobRedRed

/-- **`FrobTrace.AlgFrobRed` from neron-lg's glue N1-g1 `AbVarSpreadsOut`, the leaf candidate
`ProperSmoothGenConnected` and the kernel leaves I2-Red, I2-NMP (proved).** -/
theorem algFrobRed_of_neron_nmp (hsp : FrobPiecesNeron.AbVarSpreadsOut)
    (hc : FrobPiecesNeron.ProperSmoothGenConnected)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hN : PkgI2.NeronMappingAbelianScheme.{0}) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_nmp (FrobPiecesNeron.goodRedCofinite_of_neron hsp hc) smoothGeomConnIntegral
    hRed hN

/-- **`FrobTrace.AlgFrobRed` from `AbSchemeSpreadsOut` and the kernel leaves I2-Red, I2-NMP
(proved).** -/
theorem algFrobRed_of_spread_nmp (hG : AbSchemeSpreadsOut)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hN : PkgI2.NeronMappingAbelianScheme.{0}) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_nmp (goodRedCofinite_of hG) smoothGeomConnIntegral hRed hN

/-- **`FrobTrace.AlgFrobRed` from `GoodRedCofinite` and the kernel leaves I2-Red, I2-NMP
(proved).** -/
theorem algFrobRed_of_goodRed_nmp (hG : GoodRedCofinite)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hN : PkgI2.NeronMappingAbelianScheme.{0}) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_nmp hG smoothGeomConnIntegral hRed hN

/-- **`G14Bridge.TateBridge35` from I3.M0, N1-g1, `ProperSmoothGenConnected`, I2-Red, I2-NMP
(proved).** -/
theorem tateBridge35_of_neron_nmp (hT : PkgI3.TateModuleFree)
    (hsp : FrobPiecesNeron.AbVarSpreadsOut) (hc : FrobPiecesNeron.ProperSmoothGenConnected)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hN : PkgI2.NeronMappingAbelianScheme.{0}) :
    G14Bridge.TateBridge35 :=
  FrobTrace.tateBridge35_of_algFrobRed hT (algFrobRed_of_neron_nmp hsp hc hRed hN)

/-- **`G14Bridge.TateBridge35` from I3.M0, `AbSchemeSpreadsOut`, I2-Red, I2-NMP (proved).** -/
theorem tateBridge35_of_spread_nmp (hT : PkgI3.TateModuleFree) (hG : AbSchemeSpreadsOut)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hN : PkgI2.NeronMappingAbelianScheme.{0}) :
    G14Bridge.TateBridge35 :=
  FrobTrace.tateBridge35_of_algFrobRed hT (algFrobRed_of_spread_nmp hG hRed hN)

end FrobPiecesGood

end

#print axioms AlgFrobRedRed.absFrob
#print axioms AlgFrobRedRed.fExtendGen_of_nmp
#print axioms FrobPiecesGood.algFrobRed_of_neron_nmp
#print axioms FrobPiecesGood.algFrobRed_of_spread_nmp
#print axioms FrobPiecesGood.algFrobRed_of_goodRed_nmp
#print axioms FrobPiecesGood.tateBridge35_of_neron_nmp
#print axioms FrobPiecesGood.tateBridge35_of_spread_nmp
