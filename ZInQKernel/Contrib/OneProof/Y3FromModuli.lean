import ZInQKernel.Contrib.OneProof.Y3CMDescent
import ZInQKernel.Contrib.OneProof.Y3PeriodInputs

/-! The normalized coordinate on the level-three quotient from the moduli
representation and canonical-model comparison. -/

namespace Y3P1j

/-- The level-three quotient is the normalized rational projective line.
The moduli and canonical-model hypotheses are the ones used elsewhere in the proof. -/
theorem y3ToP1j_of_printed_moduli
    (hI : Y3RouteA.Y3FullThreeRepZ30) (hD : Y3Hodge.DeligneCanonicalModelY3EveryPrint) :
    Y3ToP1j := by
  obtain ⟨_, _, hA, hj⟩ := period_inputs
  have hG := ZInQ.Contrib.OneProof.GAGAMorphism.gagaMorphism_proof
  have hT := ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof
  have hCorr := HDec.HSyn.homLatticeCorr_ofK5 (AvSplit.Final.h69 uniformizationLeafAll_proof hG)
  apply y3ToP1j_of_moduli_and_descent hI hD
  exact cmDescends_of_z30 hI hD
    (HDec.QMLattice.qmCentralizerCMC_of uniformizationLeafAll_proof hG hT) hA hj
    (HDec.HSyn.torsionStructure_ofK5 (AvSplit.Final.h25 hT))
    (HDec.HSyn.uniformizationExists_ofK5 (AvSplit.Final.h38 uniformizationLeafAll_proof hT))
    hCorr (HDec.HSyn.t11b_of_exists5 HDec.HSyn.t11bExists_lf8)

end Y3P1j
