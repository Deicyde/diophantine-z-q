import ZInQKernel.Contrib.OneProof.CMjReroute.SplitBL
import ZInQKernel.Contrib.OneProof.CMCurveOrderLiveNOS

/-!
# The live supplier of the CM fibre split with the sub-order bound

`FibreSplit.cmFibreSplit_of_liveInputs_nos` fills the bundle field `cmFibreSplit` from six research
inputs: the Néron models over Dedekind bases, Raynaud's criterion, the wild-inertia statement, the
full-level-three model of `Y₃` over `ℤ[1/30]`, Deligne's canonical model of `Y₃` and the map
`Y₃ → P¹_j` (manuscript L520-561, L582-586, L814-818). `cmFibreSplitBL_of_liveInputs_nos` takes the
same six inputs and gives `CMFibreSplitBL`: the same Hom-field and matrix-unit proofs
(`FibreSplit.cmHomFieldModel_of_R6U_nos`, `cmMatrixUnitSplitBL_of`), and the class-number bound
`card Pic(R₀) ≤ 324` from three of the six inputs (`Y3FullThreeRepZ30`,
`DeligneCanonicalModelY3EveryPrint`, `Y3ToP1j`). No input is added.
-/

set_option maxHeartbeats 1000000

namespace HDec.CMBranch.FibreSplit

open HSyn

/-- The six inputs of `cmFibreSplit_of_liveInputs_nos` give `CMFibreSplitBL`; its body is that of
`cmFibreSplit_of_liveInputs_nos` with `CMjReroute.cmFibreSplitBL_of` in place of
`cmFibreSplit_of_curveOrder324_R6U_nos` at the end. -/
theorem _root_.HDec.CMBranch.CMjReroute.cmFibreSplitBL_of_liveInputs_nos
    (hNeron : _root_.ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind)
    (hSZ : _root_.SZRaynaud.SilverbergZarhinThm35)
    (hWild : _root_.SZRaynaud.ElliotWildInertiaTrivial)
    (hModel : _root_.Y3RouteA.Y3FullThreeRepZ30)
    (hDeligne : _root_.Y3Hodge.DeligneCanonicalModelY3EveryPrint)
    (hY3j : _root_.Y3P1j.Y3ToP1j) : CMjReroute.CMFibreSplitBL := by
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
  have hSerre := serreRigidity3_of_T35_5 (_root_.AvSplit.Final.h38 hU hM)
    (_root_.AvSplit.Final.h69 hU hG)
  have hVert := _root_.SGRDirect.heckeVertWitness_of_nvSqrtAny_y3c
    (LeafAdopt.R1R2fp_of_rep_y3c hR) (torsionStructure_ofK5 hT) hAut hSerre hFixed
    _root_.Abhyankar.nvLocalInertia (_root_.SGRDirect.heckeSqrtBranchAny_proof hY3j)
  have hCover := G0ModField.fibreCoverExists_of_propTSAll' hT
    (propTSAll_of_pieces3_y3c hR hT hConn hAut hSerre hFixed chartProper_proved4
      chartQuasiFinite_proved4 hVert)
    unramifiedConjugates_proved
  have hR6U : D2A6.R6U :=
    ⟨_root_.SZRaynaud.raynaudWildNF_of_leaves hSZ hWild
      (_root_.GapNeron.neronSchemeModelExistsNF
        (_root_.ZInQ.Contrib.GroupLawNeron.neronSchemeExtensionExists_of_dedekind hNeron)), hModel⟩
  have hHF := _root_.ZInQ.Contrib.OneProof.HomFreeC.homFreeFiniteC hU hM
  exact CMjReroute.cmFibreSplitBL_of (QMLattice.yuB6Alg_of' hU hG hM) hHF
    (cmHomFieldModel_of_R6U_nos hCover hHF _root_.NOSNarrow.nosForward_proof hR6U hT)
    (CMjReroute.cmMatrixUnitSplitBL_of (cmCurveOrder_of_324 (cmCurveOrder324_of hHF)))
    hModel hDeligne hY3j

end HDec.CMBranch.FibreSplit
