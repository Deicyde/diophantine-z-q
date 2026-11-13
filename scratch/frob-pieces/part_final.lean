
/-! # frob-pieces: `AlgFrobRed` with `SmoothGeomConnIntegral` discharged and `GoodRedCofinite`
replaced by `AbSchemeSpreadsOut` -/

noncomputable section

namespace FrobPiecesGood

open CategoryTheory AlgebraicGeometry
open ZInQ LeafQM.AV GlueDescent G0ModField UnramTate AlgFrobRedRed

/-- **alg-frob-red's `SmoothGeomConnIntegral`, proved** (it is definitionally the verbatim copy
`FrobPieces.SmoothGeomConnIntegral` of `ZInQKernel/Contrib/FrobPieces/SmoothGeomConnIntegral.lean`,
proved there from the vendored Tau Ceti theorem `TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral`). -/
theorem smoothGeomConnIntegral : AlgFrobRedRed.SmoothGeomConnIntegral :=
  FrobPieces.smoothGeomConnIntegral

/-- **`AlgFrobRed` from `AbSchemeSpreadsOut`, I2-Red, `FExtendGen`, `AbsFrob` (proved).** -/
theorem algFrobRed_of_spread (hG : AbSchemeSpreadsOut)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hE : FExtendGen) (hA : AbsFrob) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_gen (goodRedCofinite_of hG) smoothGeomConnIntegral hRed hE hA

/-- **`AlgFrobRed` from `GoodRedCofinite`, I2-Red, `FExtendGen`, `AbsFrob` (proved).** -/
theorem algFrobRed_of_four (hG : GoodRedCofinite)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hE : FExtendGen) (hA : AbsFrob) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_gen hG smoothGeomConnIntegral hRed hE hA

/-- **`TateBridge35` from I3.M0, `AbSchemeSpreadsOut`, I2-Red, `FExtendGen`, `AbsFrob`
(proved).** -/
theorem tateBridge35_of_spread (hT : PkgI3.TateModuleFree) (hG : AbSchemeSpreadsOut)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hE : FExtendGen) (hA : AbsFrob) :
    G14Bridge.TateBridge35 :=
  FrobTrace.tateBridge35_of_algFrobRed hT (algFrobRed_of_spread hG hRed hE hA)

end FrobPiecesGood

end

#print axioms FrobPiecesGood.isUnit_intCast_of_coprime
#print axioms FrobPiecesGood.pullbackGrp_congr
#print axioms FrobPiecesGood.goodRedCofinite_of
#print axioms FrobPiecesGood.smoothGeomConnIntegral
#print axioms FrobPiecesGood.algFrobRed_of_spread
#print axioms FrobPiecesGood.algFrobRed_of_four
#print axioms FrobPiecesGood.tateBridge35_of_spread
