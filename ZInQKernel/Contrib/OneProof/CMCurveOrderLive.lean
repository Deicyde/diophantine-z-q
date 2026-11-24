import ZInQKernel.Contrib.OneProof.CMBranch
import ZInQKernel.Contrib.OneProof.CMCurveOrder.R6U
import ZInQKernel.Contrib.OneProof.HeckeSqrt
import ZInQKernel.Contrib.OneProof.H.Y3Copy1

/-! # Live suppliers for the CM fibre split

Reuse the suppliers of the live kernel-field call, but take their inputs
directly. This lets the next bundle fill `cmFibreSplit` without already having it.
-/

set_option maxHeartbeats 1000000

namespace HDec.CMBranch.FibreSplit

open HSyn

/-- The full-level-three model and its canonical-model identification, the
manuscript's map to the `j`-line, and the live Néron, NOS, and wild inertia
inputs suffice for the unchanged CM split (`thm:height`, L520–561, L582–586,
L814–818). All are already fields of the open83 research bundle. -/
theorem cmFibreSplit_of_liveInputs
    (hNeron : _root_.ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind)
    (hNOS : _root_.NOSSepDict.NeronOggShafarevichSep)
    (hSZ : _root_.SZRaynaud.SilverbergZarhinThm35)
    (hWild : _root_.SZRaynaud.ElliotWildInertiaTrivial)
    (hModel : _root_.Y3RouteA.Y3FullThreeRepZ30)
    (hDeligne : _root_.Y3Hodge.DeligneCanonicalModelY3EveryPrint)
    (hY3j : _root_.Y3P1j.Y3ToP1j) : CMFibreSplit := by
  have hU := _root_.uniformizationLeafAll_proof
  have hG := _root_.ZInQ.Contrib.OneProof.GAGAMorphism.gagaMorphism_proof
  have hM := _root_.ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof
  have hT := _root_.AvSplit.Final.h25 hM
  have hGroup := _root_.LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_dvr
    (_root_.ZInQ.Contrib.GoodModelIso.mumfordGroupLawDVR_of_dedekind hNeron)
  have hShimura := _root_.Y3Fix.shimuraMainThmIDeligneY3AbU_of_print
    hM (_root_.Y3RouteA.y3FineModuliAbP_of_z30 hModel) (_root_.Y3Hodge.deligneH_of_print hDeligne)
  have hRayClass := (_root_.LeafQM.AV.R1UnivRigid.rayClassCM_iff_ab_gl hGroup).mpr
    (_root_.RayClassCFT.rayClassCMAb_of_leaves hShimura hU hG)
  have hR := _root_.Y3X6.r1r2fpY3_of hY3j hRayClass
  have hConn := _root_.DCY3Used.y3Connected_of_ab_gl hGroup
    (_root_.DCY3Used.y3ConnectedAb_of_U hShimura)
  obtain ⟨hAut, hFixed, -⟩ := QMSplit.Aut.rows_of_C
    (QMLattice.qmCentralizerCMC_of hU hG hM) (t11b_of_exists5 t11bExists_lf8)
  have hSerre := serreRigidity3_of_T35_5 (_root_.AvSplit.Final.h38 hU hM) (_root_.AvSplit.Final.h69 hU hG)
  have hVert := _root_.SGRDirect.heckeVertWitness_of_nvSqrtAny_y3c
    (LeafAdopt.R1R2fp_of_rep_y3c hR) (torsionStructure_ofK5 hT) hAut hSerre hFixed
    _root_.Abhyankar.nvLocalInertia (_root_.SGRDirect.heckeSqrtBranchAny_proof hY3j)
  have hCover := G0ModField.fibreCoverExists_of_propTSAll' hT
    (propTSAll_of_pieces3_y3c hR hT hConn hAut hSerre hFixed chartProper_proved4 chartQuasiFinite_proved4 hVert)
    unramifiedConjugates_proved
  have hR6U : D2A6.R6U :=
    ⟨_root_.SZRaynaud.raynaudWildNF_of_leaves hSZ hWild
      (_root_.GapNeron.neronSchemeModelExistsNF
        (_root_.ZInQ.Contrib.GroupLawNeron.neronSchemeExtensionExists_of_dedekind hNeron)), hModel⟩
  exact cmFibreSplit_of_curveOrder324_R6U (QMLattice.yuB6Alg_of' hU hG hM)
    (_root_.ZInQ.Contrib.OneProof.HomFreeC.homFreeFiniteC hU hM)
    hCover (_root_.NOSSepDict.neronOggShafarevich_of_sep hNOS) hR6U hT

end HDec.CMBranch.FibreSplit
