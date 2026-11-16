import ZInQKernel.OneProof.Main
import ZInQKernel.OneProof.Discharges
import ZInQKernel.Contrib.OneProof.NeronDVR

#discharges

#print axioms GapNeron.neronSchemeModelExistsNF
#print axioms GapNeron.neronSchemeModelExistsNF'
#print axioms GapNeron.neronSchemeModelExistsDVRNF_of_field
#print axioms GapNeron.ss1_ss3_of_cpNF
#print axioms GapNeron.ss1_ss3_of_cp_fullNF
#print axioms GapNeron.semistablePersists_final_nfNF
#print axioms GapNeron.semistableReductionThm_final_nfNF
#print axioms GapNeron.raynaudCriterion_leavesNF
#print axioms GapNeron.grothendieckMonodromy_final'NF
#print axioms GapNeron.raynaudCriterionNF_of_general
#print axioms GapNeron.grothendieckMonodromyNF_of_general
#print axioms GapNeron.r6_r8_NF_of_N1

/-! Replacement check: `ss1_ss3_of14` (TailZ23 L763) with the restated consumer, over the open-14 bundle. -/
open HDec.HSyn in
example (r : OpenResearchLeaves14) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves12) :
    _root_.ZInQ.HeightSplit.SemistableReductionThm ∧ _root_.ZInQ.HeightSplit.SemistablePersists :=
  GapNeron.ss1_ss3_of_cpNF r.semistablePersistsSHcp r.strictHenselizationPair (semistableReductionDVR_of14 r t)
    (GapNeron.neronSchemeModelExistsNF t.neronSchemeExtensionExists)
    (_root_.ReductGlue.semistableLocalGlobal_leaf (_root_.CToPrinted.neronLocalizesDVR_of_printed r.blr_1_2_4))
    (semistableAlmostAll_of10 (addedLeaves9_of_open14 r t l))
