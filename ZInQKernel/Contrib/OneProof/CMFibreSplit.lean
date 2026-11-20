import ZInQKernel.Contrib.OneProof.CMFibreSplit.Reduction
import ZInQKernel.Contrib.OneProof.CMFibreSplit.Curve
import ZInQKernel.Contrib.OneProof.CMFibreSplit.CurveOrder

/-! # cm-fibre-split: `CMBranch.CMFibreSplit` (diophantine_zq.tex, thm:height, proof, L581-586)

`CMFibreSplit` is proved from the chain's leaves at the open4 generation alone (G2 `FibreCoverExists`, T6
`HomFreeFiniteC`, Néron–Ogg–Shafarevich, Raynaud, torsion structure, Yu's dichotomy `YuB6Alg`): no new leaf, no new
glue. Steps (`Reduction.lean`, `Curve.lean`, `CurveOrder.lean`): A8's Hom field at every fibre without NoCM
(`cmHomFieldModel_of`), the CM case of Yu's dichotomy (`end0Matrix_of_noncentral`), scaled matrix units
(`exists_scaledMatrixUnits`), the curve `E` and the isogeny `E² → A` (`matrixUnit_isogeny`), and the geometric
endomorphism ring of `E` an order of `ℚ(√d)` (`cmCurveOrder_of`). Report: docs/research/cm-fibre-split.md. -/

namespace HDec
namespace CMBranch
namespace FibreSplit

/-- **`CMFibreSplit` from the chain's leaves and the glue `CMCurveOrder`.** -/
theorem cmFibreSplit_of_curveOrder (hYu : QMLattice.YuB6Alg)
    (hHFF : _root_.ZInQ.Contrib.OneProof.HomFreeC.HomFreeFiniteC) (hCover : G0ModField.FibreCoverExists)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterionNF.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (hCO : CMCurveOrder) : CMFibreSplit :=
  cmFibreSplit_of hYu hHFF (cmHomFieldModel_of hCover hHFF hNOS hRay hTors) (cmMatrixUnitSplit_of hCO)

/-- **`CMFibreSplit` proved from the chain's leaves** (statement verbatim; no new hypothesis beyond leaves the chain
already carries at the open4 generation). -/
theorem cmFibreSplit_of_leaves (hYu : QMLattice.YuB6Alg)
    (hHFF : _root_.ZInQ.Contrib.OneProof.HomFreeC.HomFreeFiniteC) (hCover : G0ModField.FibreCoverExists)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterionNF.{0})
    (hTors : PkgI2.TorsionStructure.{0}) : CMFibreSplit :=
  cmFibreSplit_of_curveOrder hYu hHFF hCover hNOS hRay hTors (cmCurveOrder_of hHFF)

end FibreSplit
end CMBranch
end HDec
