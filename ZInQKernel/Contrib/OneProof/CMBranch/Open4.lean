import ZInQKernel.Contrib.OneProof.CMBranch.Localize

/-! # cm-branch: `SixContactMin` at the generation of `sixContactMin_of_open4_hf_pz_eb`, with the manuscript's CM branch

The chain's `HSyn.sixContactMin_of_open4_hf_pz_eb` builds `GluePieces` (`gluePieces_of_open4_hf_pz_eb`) with
`fibreSimple` and `modularConstituent` proved from FS5 (NoCM), which reads `r.r5count` (González–Rotger
Prop. 5.6), `l.cmOptimalEmbedding`, `l.x6ConicModel` (the `X₆` Kummer fibre) and the conjunct `R5ptProps`
of `r.r1r2` (González–Rotger Thm 5.12). `sixContactMin_of_open4_cm` takes the same bundles and proves
`SixContactMin` without FS5: the other glue pieces verbatim, `FibreSimpleNC` and `ModularConstituentNC`
from the localized chain, and the CM branch from the manuscript's leaves. This is the hand-fold entry
point (docs/research/cm-branch.md §7).
-/

namespace HDec
set_option maxHeartbeats 1000000
noncomputable section
namespace HSyn
open CategoryTheory AlgebraicGeometry G0Split

/-- **`SixContactMin` from leaf-fold4's open statements with the manuscript's CM branch** (no FS5). -/
theorem sixContactMin_of_open4_cm (r : OpenResearchLeaves2EB) (t : OpenTextbookLeaves4HFPZ)
    (l : OpenAddedLeaves4PZ) (g : OpenGlue4) (h20 : G0Split.R20Lower) (hYu : QMLattice.YuB6Alg)
    (hθ : PkgI1.QMHauptmodul → G0Split.ThetaPt.ThetaSplit.ThetaRatiosAtQM)
    (hSplit : CMBranch.CMFibreSplit) (hF : CMBranch.FowlerProp27) (hJ : CMBranch.CMjDegree)
    (hPG : CMBranch.CMPotentialGood) (h62 : CMBranch.CMHeight62) (hRP : CMBranch.ReducedCMPeriod)
    (hAddU : CMBranch.HeightAdditivityUpper) : ZInQ.SixContactMin :=
  let t2 := textbookLeaves2_of_open3_hf_pz (textbookLeaves3_of_open4_hf_pz t)
  let r3 := researchLeaves3_of_open2_eb r
  let t3 := textbookLeaves_of_open2_hf_pz t2
  have hMob : LeafQM.AV.Pin.MobiusGlue := mobiusGlue_of_t5' t.t5
  have hFSNC : CMBranch.FibreSimpleNC :=
    CMBranch.fibreSimpleNC_of_pieces_hf hYu
      (G0FibreSimple.endDivisionDescent_of G0FibreSimple.baseChangeFaithful_proof
        (G0FibreSimple.isogenyDescends_of G0FibreSimple.finiteDescends_proof))
      (G0FibreSimple.endDivisionOfSchemeIso_of_rigidity G0FibreSimple.rigidityHom)
      (G0FibreSimple.end0Division_of_homFree_hf t3.t6 mulIsogeny_proved)
      (G0FibreSimple.centralizerOfMatrixEnd0_of_homFree_hf t3.t6)
  have hModNC : CMBranch.ModularConstituentNC :=
    HSyn.modularConstituentNC_of_field_hf_pz t3
      (G0ModField.fibreCoverExists_of_propTSAll' t.t5
        (propTSAll_of_pieces3 r.r1r2 t.t5 l.y3Connected l.qmAutCard l.serreRigidity3 l.alFixedPoints
          chartProper_proved4 chartQuasiFinite_proved4 g.heckeVertWitness) unramifiedConjugates_proved)
      (G0ModField.KernelField.kernelFieldExistsNC_of_split_hf t.t6 r.r7a r.r6 t.t5 hYu
        G0ModField.KernelField.oMaximal endTransport_proved conjIsogMaps_proved3)
      UnramTate.unramifiedSup_mf
      (G0AssembleMod.afterG7NC_of3_hf_pz_eb r3 t3
        ⟨burnsideAbsIrred_proved3, r.r14,
          g9Glue_of_deRhamComparisonHT r.r10,
          G0Galois.g10Glue_of_conjTwist
            (G0Galois.conjTwistNontrivial_of_leaves t.t5 (tateModuleFree_of_t5' t.t5) t.t35
              (HomUnify.homLinearLift_of_corr t.homLatticeCorr)),
          G0Galois.g12Weight_of_senTwist l.senTwist l.finiteImageHT,
          detTate_of_leaves4_pz l.t09SymmIsogenyExists l.isogenyQuasiInverse t.t5
            (tateModuleFree_of_t5' t.t5),
          G0AssembleMod.resQFiniteIndex⟩
        (g9GlueNoT23_of_deRhamComparisonHT r.r10)
        (G0ModNewform.dirichletOfFinite_of_t17 t17_proved) r.r17
        Swan.swanIndependent_proved Swan.swanIntegral_proved
        Swan.adaptedExists_proved
        (HSyn.modelG3G6NC_of_leaves3 hFSNC r.r7a r.r6 t.t5)
        (G0AssembleMod.linkedTateDataNC_of_local t.t7
          (HSyn.linkedTateLocalNC_of_leaves3_hf r.r6 t.t5 (tateModuleFree_of_t5' t.t5)
            (abVarSpreadsOut_of_ega4 l.egaIV_8_8_2_ii l.egaIV_8_10_5_xii l.egaIV_17_7_8_ii)
            (properSmoothGenConnected_of_zariski4 l.zariskiConnectedness)
            t.t4 t.t3 hFSNC t.t6 hYu)))
  have hDimF : DimFinite := G0Split.dimFinite
  have hDim : DimBaseChange := G0Split.dimBaseChange
  have hPMH : ZInQ.H5Neron.ProductModelHeight := ZInQ.ProductHeight.productModelHeight_of_splits productUnifSplits_proved
      (ZInQ.UnifDims.productMetrizationOfProductUnif_of_tangentDim t.t35 tangentDimAtOrigin_proved3)
  have hBC : StableHeightBaseChange := G0StableBC.stableHeightBaseChange_of_hodgeLine
      (ZInQ.HeightBC.g0_hodgeLine_iff.mpr (ZInQ.HeightBC.hodgeLineBaseChange_of_glue4
        hodgeBCInjective_proved3 cotangentSpanBC_proved omegaBaseChange_proved3
        uniformizationLiftAnalytic_proved))
  have hProdE : ProductExists := G0Product.productExists
  have hRev : ReverseIsogeny := G0RevIsog.reverseIsogeny_of_leaves3_eb r3 G0Split.dimFinite
  have hThetaPt : ThetaPointOfFibre := G0Split.ThetaPt.ThetaSplit.thetaPointOfFibre_of_qm_atQM
      (G0Split.FibreQM.fibreQMPeriod_main_rep r.r1r2 hMob l.qmHauptmodul
        t.t35 t2.t11a l.qmClassNumberOne (r.r1b r.r1r2) (periodMapGlue_of_leaves4 r.r1r2 t.t5 t.homLatticeCorr l.cmDescends)
        hauptmodulUnique_proved4
        (qmDenZeroCM3_of_leaves4 r.r4 l.gammaStarGen l.valenceBoundGammaStar) cPtsTransport_proved3)
      (hθ l.qmHauptmodul)
  have hCopies : HeightCopiesAgree := G0HeightCopies.heightCopiesAgree
  CMBranch.sixContactMin_of_branches (LeafQM.AV.exists_fibre_object (LeafAdopt.R1R2fp_of_rep r3.r1r2))
    (CMBranch.nonCMBranch_of r3 t3 hDimF hDim hPMH hBC hProdE hRev hThetaPt hCopies hFSNC hModNC h20)
    (CMBranch.cmBranchOut_of r3.h5.1 hDim (thetaPazuki (r22Concrete_of r3.r22 hCopies) hThetaPt)
      hSplit hF hJ hPG h62 hRP hAddU r3.r19 h20)

end HSyn
end
end HDec
