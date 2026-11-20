import ZInQKernel.Contrib.OneProof.CMCurveOrderLive
import ZInQKernel.Contrib.OneProof.NOSNarrow

/-! # cm-port2's CM fibre split without the NOS field

cm-port2 (`CMCurveOrderLive.lean`, `CMCurveOrder/R6U.lean`) fills `cmFibreSplit` from seven research fields, one of them
`neronOggShafarevichSep`, which nos-narrow has since removed. The split reads it only through
`kernelField_of_model_hf` and `good_of_QML3U` (the Hom field of A8, L540-561), i.e. only the forward implication
good reduction ⇒ inertia fixes prime-to-p torsion, which is proved (`NOSNarrow.nosForward_proof`). The copies below are
cm-port2's proofs verbatim with nos-narrow's `_nos` readers in place of those two calls; the provider takes the other
six fields. Each has an example recovering cm-port2's signature.
-/

noncomputable section
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

namespace HDec.CMBranch.FibreSplit

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ ZInQ.JHeight HDec.LeafQM.AV HDec.ZInQ.DefFaltings
open HSyn HSyn.G0Split
open _root_.CMBranch
open TwistDescentXC TwistDescentHFD G0ModField G0ModField.KernelField
open scoped Quaternion TensorProduct

/-- `cmHomFieldModel_of_R6U` with the forward implication in place of the NOS field. -/
theorem cmHomFieldModel_of_R6U_nos (hCover : G0ModField.FibreCoverExists)
    (hHFF : _root_.ZInQ.Contrib.OneProof.HomFreeC.HomFreeFiniteC)
    (hF : _root_.NOSNarrow.NOSForward) (hRay : D2A6.R6U)
    (hTors : PkgI2.TorsionStructure.{0}) : CMHomFieldModel := by
  intro Y Φ π u P hctx
  obtain ⟨K, hfK, hgK, hKF, hramK, PK, hPK⟩ := g2Out_of_cover Y Φ u P (hCover Y Φ π u P hctx)
  have hK : GlueB3Unram.GalUnramifiedOutside K (T u) :=
    (G4WeilRes.galUnramifiedOutside_iff K (T u)).mpr hramK
  obtain ⟨r, hr, G, hG, E, hfE, hgE, hEG, hramE, hfix⟩ :=
    kernelField_of_model_hf_nos hHFF hF K hKF PK.A (conj_dim K PK.A PK.surface) (T u) hK
      (good_of_QML3U_nos hRay hTors K PK (T u) (_root_.HDec.D2A6.T324_subset_T u))
  haveI : IsGalois ℚ ↥(E ⊔ K) := IsGalois.mk
  have hE : Module.finrank ℚ E ≤ 3 ^ (r ^ 2) := hEG ▸ GlueRepo.TorsionFree.card_le_three_pow G
  have hdeg : Module.finrank ℚ ↥(E ⊔ K) ≤ heightD :=
    GlueRepo.Numerics.a8_field E K Compiler.Precision.heightD_eq hKF hE hr
  obtain ⟨⟨yK, hyK, hyKP⟩, -⟩ := hPK
  obtain ⟨hR1, -, -, -⟩ := hctx
  obtain ⟨Q, hQ, hbc⟩ := hR1.2.2.2.1 K LeafQM.AV.Qbar K.val yK PK hyK
  have hQP : M3.mk Q = M3.mk P := hQ.symm.trans hyKP
  obtain ⟨e⟩ := Quotient.exact hQP
  obtain ⟨θ₁, θ₁', h11, h12, -⟩ := bc_transport G0FibreSimple.rigidityHom PK K.val Q hbc
  obtain ⟨-, θ₀, θ₀', h01, h02, -⟩ := paste_iso PK.A (le_sup_right : K ≤ E ⊔ K)
  refine ⟨E ⊔ K, inferInstance, hdeg, @PkgI3.AbVar.baseChange K _ PK.A ↥(E ⊔ K) _ (incAlg le_sup_right),
    PkgI3.AbVar.Hom.mk' (θ₀.hom ≫ θ₁.hom ≫ e.φ.hom), PkgI3.AbVar.Hom.mk' (e.ψ.hom ≫ θ₁'.hom ≫ θ₀'.hom),
    ?_, ?_, endBC_surjective_of_homField PK.A le_sup_right hfix⟩
  · simp only [PkgI3.AbVar.Hom.hom_mk', Category.assoc]
    rw [reassoc_of% e.left, reassoc_of% h11, h01]
  · simp only [PkgI3.AbVar.Hom.hom_mk', Category.assoc]
    rw [reassoc_of% h02, reassoc_of% h12, e.right]

/-- `cmFibreSplit_of_curveOrder324_R6U` with the forward implication in place of the NOS field. -/
theorem cmFibreSplit_of_curveOrder324_R6U_nos (hYu : QMLattice.YuB6Alg)
    (hHF : _root_.ZInQ.Contrib.OneProof.HomFreeC.HomFreeFiniteC)
    (hCover : G0ModField.FibreCoverExists) (hF : _root_.NOSNarrow.NOSForward)
    (hRay : D2A6.R6U) (hTors : PkgI2.TorsionStructure.{0}) : CMFibreSplit :=
  cmFibreSplit_of hYu hHF (cmHomFieldModel_of_R6U_nos hCover hHF hF hRay hTors)
    (cmMatrixUnitSplit_of (cmCurveOrder_of_324 (cmCurveOrder324_of hHF)))

/-- cm-port2's provider without the NOS field: the full-level-three model and its canonical-model identification, the
manuscript's map to the `j`-line, and the live Néron and wild inertia inputs give the unchanged CM split
(`thm:height`, L520–561, L582–586, L814–818); good reduction ⇒ inertia triviality is `NOSNarrow.nosForward_proof`. -/
theorem cmFibreSplit_of_liveInputs_nos
    (hNeron : _root_.ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind)
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
  exact cmFibreSplit_of_curveOrder324_R6U_nos (QMLattice.yuB6Alg_of' hU hG hM)
    (_root_.ZInQ.Contrib.OneProof.HomFreeC.homFreeFiniteC hU hM)
    hCover _root_.NOSNarrow.nosForward_proof hR6U hT

example (hYu : QMLattice.YuB6Alg) (hHF : _root_.ZInQ.Contrib.OneProof.HomFreeC.HomFreeFiniteC)
    (hCover : G0ModField.FibreCoverExists) (hNOS : PkgI2.NeronOggShafarevich.{0})
    (hRay : D2A6.R6U) (hTors : PkgI2.TorsionStructure.{0}) : CMFibreSplit :=
  cmFibreSplit_of_curveOrder324_R6U_nos hYu hHF hCover (_root_.NOSNarrow.nosForward_of_r7a hNOS) hRay hTors

end HDec.CMBranch.FibreSplit

#print axioms HDec.CMBranch.FibreSplit.cmFibreSplit_of_liveInputs_nos
