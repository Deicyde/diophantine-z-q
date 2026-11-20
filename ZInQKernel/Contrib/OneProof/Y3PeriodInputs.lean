import ZInQKernel.Contrib.OneProof.H.TailZ98
import ZInQKernel.Contrib.OneProof.Y3QuotientProjectiveLine

/-! The period and modular-function inputs to the level-three quotient
comparison follow from the analytic theorems already established in the project. -/

namespace Y3P1j

open HDec.HSyn
open HDec.HSyn.G0Split.FibreQM

/-- The period lattices, CM fixed points, CM analytic representation and
normalized Hauptmodul used in the quotient comparison hold simultaneously. -/
theorem period_inputs :
    PeriodMapH.QMTwistLattice ∧ PeriodMapH.CMFixedHasCM ∧
    RayClassCFT.CMAnalytic ∧ HDec.PkgI1.QMHauptmodul := by
  have hCorr := AvSplit.Final.h69 uniformizationLeafAll_proof
    ZInQ.Contrib.OneProof.GAGAMorphism.gagaMorphism_proof
  have hHom := t11aRiemannHom_of_corr4 (homLatticeCorr_ofK5 hCorr)
  have hΘ := HDec.QMSplit.Theta.thetaModularity_of GapTheta.igusaPsi4_proof GapTheta.igusaChi10_proof
  have hV := HDec.LeafQCheck.VB.valenceBound_of_formula
    (HDec.LeafQCheck.HM.QMSplit.valenceFormulaGammaStar_of_leaves
      ValenceCocompact.valenceFormulaCocompactEq_proof HDec.GammaStarArea.shimizuCovolumeO1_proof)
  exact ⟨PeriodGlue.qmTwistLattice_of' hHom leafSkolemNoether_proved4,
    PeriodMapH.cmFixedHasCM_of (PeriodGlue.t11aRiemannEnd_of_hom hHom),
    RayClassCFT.cmAnalytic_of (ZInQ.HomUnify.homLinearLift_of_corr hCorr),
    HDec.LeafQCheck.HM.qmHauptmodul_of_base2
      (HDec.LeafQCheck.HM.base2_of_base3 hΘ HDec.LeafQCheck.gammaStarGen_proof hV
        (HDec.LeafQCheck.HM.QMSplit.qmHauptmodulBase3_of_leaves hΘ
          ValenceCocompact.valenceFormulaCocompactEq_proof HDec.GammaStarArea.shimizuCovolumeO1_proof
          CM24.igusaCMValue24_field))⟩

/-- The normalized projective-line identification follows from the two moduli
inputs and descent of the distinguished CM points. -/
theorem y3ToP1j_of_moduli_and_descent
    (hI : Y3RouteA.Y3FullThreeRepZ30) (hD : Y3Hodge.DeligneCanonicalModelY3EveryPrint)
    (hC : PeriodMapH.CMDescends) : Y3ToP1j := by
  obtain ⟨hL, hF, hA, hj⟩ := period_inputs
  exact y3ToP1j_of_canonical_model_and_cm hI hD hL hF hC hA hj

end Y3P1j
