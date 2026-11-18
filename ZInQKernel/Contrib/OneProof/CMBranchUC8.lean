import ZInQKernel.Contrib.OneProof.CMBranch.Open4
import ZInQKernel.OneProof.H.C8Chain

/-! # fold-cm: the manuscript's CM branch at the generation of the live chain's base (`_u_c8` bundles)

The live chain of `sixContactMin_of_open80` (fold-c8) bottoms out at `HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8`
(`OneProof/H/C8Chain.lean`), which proves `FibreSimple` from FS5 (NoCM). cm-branch's
`HSyn.sixContactMin_of_open4_cm` (`CMBranch/Open4.lean`) is the manuscript's CM branch (diophantine_zq.tex L581-631) at
the same generation, but over the bundles before d2a6b (R6 = `RaynaudCriterionNF`) and fold-c8 (the Weil-pairing
fields). This file states the CM branch over the live bundles `OpenResearchLeaves2EBU` (R6 replaced by
`D2A6.R6U`, L529-530) and `OpenAddedLeaves4PZC8` (`c8 : C8Conrad.C8Inputs`, step C8 by local algebraicity, L758-766):
cm-branch's localized theorems (fibre context `FibreCtxNC`, i.e. at fibres without CM) copied with d2a6b's and
fold-c8's replacements (`good_of_QML3` -> `good_of_QML3U`, `localGlue_at` -> `localGlue_at_u`, `qmModelG3_of` ->
`D2A6.qmModelG3U_of_z30`, `{3} ⊆ T u` -> `T324 ⊆ T u`, `GaloisPieces` -> `GaloisPiecesC8`). No mathematics changes:
each theorem is the composite of a localized theorem of cm-branch and a reroute of d2a6b / fold-c8.
-/

namespace HDec
set_option maxHeartbeats 1000000
noncomputable section

/-! ## 1. The kernel field (G4) at fibres without CM, on `R6U` -/

section KF
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q
namespace G0ModField.KernelField
open G0ModField

/-- cm-branch's `kernelFieldExistsNC_of_pieces_hf` on `R6U` (d2a6b's `kernelFieldExists_of_pieces_hf_u`, localized). -/
theorem kernelFieldExistsNC_of_pieces_hf_u (hHFF : _root_.ZInQ.Contrib.OneProof.HomFreeC.HomFreeFiniteC)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : _root_.HDec.D2A6.R6U)
    (hTors : PkgI2.TorsionStructure.{0}) (hCount : TorsionCountPts)
    (hMaps : ConjMapsOnHomFieldNC) : KernelFieldExistsNC := by
  intro Y Φ π u P hctx K _ _ hKF hramK PK hPK
  have hK : GlueB3Unram.GalUnramifiedOutside K (T u) :=
    (G4WeilRes.galUnramifiedOutside_iff K (T u)).mpr hramK
  obtain ⟨r, hr, G, hG, E, hfE, hgE, hEG, hramE, hfix⟩ :=
    kernelField_of_model_hf hHFF hNOS K hKF PK.A (conj_dim K PK.A PK.surface) (T u) hK
      (good_of_QML3U hNOS hRay hTors K PK (T u) (_root_.HDec.D2A6.T324_subset_T u))
  haveI : IsGalois ℚ ↥(E ⊔ K) := IsGalois.mk
  obtain ⟨m, hm⟩ := hMaps Y Φ π u P hctx K hKF hramK PK hPK (E ⊔ K) le_sup_right hfix
  obtain ⟨c, hc⟩ := conjugacyData_of_conjMaps _ _ m
    (hCount _ _ (bc_dim le_sup_right PK.A PK.surface)) hm
  exact ⟨r, hr, G, hG, E, hfE, hgE, hEG, hramE, m, c, hc⟩

/-- cm-branch's `kernelFieldExistsNC_of_split_hf` on `R6U`. -/
theorem kernelFieldExistsNC_of_split_hf_u (hHFF : _root_.ZInQ.Contrib.OneProof.HomFreeC.HomFreeFiniteC)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : _root_.HDec.D2A6.R6U)
    (hTors : PkgI2.TorsionStructure.{0}) (hYu : QMLattice.YuB6Alg)
    (hmax : OMaximal) (hb : EndTransport) (hG : ConjIsogMaps) : KernelFieldExistsNC :=
  kernelFieldExistsNC_of_pieces_hf_u hHFF hNOS hRay hTors (torsionCountPts_of_leaf hTors)
    (conjMapsOnHomFieldNC_of (conjMapsNoCM_of hTors hG
      (endEqOOnHomField_of (endEqOFibre_of_hf hYu hHFF hmax) hb)))

end G0ModField.KernelField
end KF

/-! ## 2. G3 and G5-G6 on G7's model at fibres without CM, from the model of `Y₃` over `ℤ[1/30]` -/

section MG
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open G0ModField

namespace HSyn.LinkedTate
/-- cm-branch's `modelG3G6NC_of` with d2a6b's `QMModelG3U` (`T324 ⊆ T u` in place of `{3} ⊆ T u`;
`D2A6.modelG3G6_of_U`, localized). -/
theorem modelG3G6NC_of_U (hFS : CMBranch.FibreSimpleNC) (hG3 : _root_.HDec.D2A6.QMModelG3U) :
    HSyn.G0AssembleMod.ModelG3G6NC := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hdata
  letI : NumberField L' := numberField_of_fd L'
  have hmod := hdata.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨K, hKL, PK, -, rfl⟩ := hdata.1
  have hT := _root_.HDec.D2A6.T324_subset_T u
  refine ⟨⟨endDivisionNC_of hFS hctx L' _ hmod, ?_⟩, ?_, ?_⟩
  · exact @noncomm_baseChange2 K _ PK L _ (incAlg hKL) L' _ (incAlg hLL')
  · exact g3Out_mono hT (hG3 K L L' hKL hLL' PK 5)
  · exact g3Out_mono hT (hG3 K L L' hKL hLL' PK 3)
end HSyn.LinkedTate

namespace HSyn
/-- cm-branch's `modelG3G6NC_of_leaves3` on `R6U` (d2a6b's `modelG3G6_of_leaves3U`, localized). -/
theorem modelG3G6NC_of_leaves3U (hFS : CMBranch.FibreSimpleNC) (hNOS : PkgI2.NeronOggShafarevich.{0})
    (hRay : D2A6.R6U) (hTors : PkgI2.TorsionStructure.{0}) :
    G0AssembleMod.ModelG3G6NC :=
  HSyn.LinkedTate.modelG3G6NC_of_U hFS (_root_.HDec.D2A6.qmModelG3U_of_z30 hNOS hRay.2)
end HSyn
end MG

/-! ## 3. The linked Tate data at fibres without CM, on `R6U` -/

section LT
open CategoryTheory.MonObj
open GlueDescent GlueC10 PkgI3
open scoped TensorProduct
attribute [-instance] TauCeti.FinitePadicExtension.toAlgebra
  TauCeti.FinitePadicExtension.ofInstances TauCeti.FinitePadicExtension.toModuleFinite
  TauCeti.FinitePadicExtension.toValuativeExtension
namespace LTLocal
open CategoryTheory AlgebraicGeometry
open G0ModField

/-- cm-branch's `linkedTateLocalDNC_of_tateBridge35` on `R6U` (`localGlue_at` -> d2a6b's `localGlue_at_u`). -/
theorem linkedTateLocalDNC_of_tateBridge35_u (hR6 : _root_.HDec.D2A6.R6U)
    (hTors : ObjBridge.TorsionStructure) (hU5 : G15Ram.UnramRoots 2 5)
    (hU3 : G15Ram.UnramRoots 2 3) (hB : G14Bridge.TateBridge35) (hRk : ModelEndRank4NC) :
    LinkedTateLocalDNC := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hD hLD
  letI : NumberField L' := numberField_of_fd L'
  have hdim := dim_bc_of_g7Data hD
  have hrk := hRk Y Φ π u P hctx L A ε N χ β L' hLL' hD
  obtain ⟨aQ, βQ, j5, j3, Tm5, c5, ε5, u5, Tm3, c3, ε3, u3, h5, h3, hF, ιC, hC⟩ :=
    hB u P L A ε N χ β L' hLL' hD hdim hrk
  have hCl5 := g7Clauses_of_transport hD hLD βQ j5 ιC hC h5.2.2.2.2.1
  have hCl3 := g7Clauses_of_transport hD hLD βQ j3 ιC hC h3.2.2.2.2.1
  refine ⟨aQ, βQ, j5, j3, Tm5, c5, ε5, u5, Tm3, c3, ε3, u3, h5, h3, hF,
    fun r5 r3 h85 h83 => ⟨fun p hp hp5 => ?_, ?_⟩⟩
  · haveI : Fact p.Prime := ⟨hp⟩
    exact G15Ram.localData_of_g7 h85 hCl5
      (localGlue_at_u hR6 hTors (fun h2 => by subst h2; exact hU5) hp5 hD βQ j5 ιC hC h5 hCl5)
  · exact G15Ram.localData_of_g7 h83 hCl3
      (localGlue_at_u hR6 hTors (fun h2 => absurd h2 (by norm_num)) (by norm_num) hD βQ j3 ιC hC
        h3 hCl3)
end LTLocal

namespace HSyn
open CategoryTheory AlgebraicGeometry G0Split
/-- cm-branch's `linkedTateLocalNC_of_leaves3_hf` on `R6U` (d2a6b's `linkedTateLocal_of_leaves3_hf_u`, localized). -/
theorem linkedTateLocalNC_of_leaves3_hf_u (hR6 : _root_.HDec.D2A6.R6U) (h5 : PkgI2.TorsionStructure.{0})
    (hT : PkgI3.TateModuleFree) (hsp : FrobPiecesNeron.AbVarSpreadsOut)
    (hc : FrobPiecesNeron.ProperSmoothGenConnected) (hRed : PkgI2.ReductionTorsionBijective.{0})
    (hN : PkgI2.NeronMappingAbelianScheme.{0}) (hFS : CMBranch.FibreSimpleNC)
    (h6 : _root_.ZInQ.Contrib.OneProof.HomFreeC.HomFreeFiniteC) (hYu : QMLattice.YuB6Alg) :
    G0AssembleMod.LinkedTateLocalNC :=
  LTLocal.linkedTateLocalNC_of_D
    (LTLocal.linkedTateLocalDNC_of_tateBridge35_u hR6
      (ObjBridge.torsionStructure_iff.mpr h5) (@UnramRootsTask.unramRoots_all 2 _ 5 _)
      (@UnramRootsTask.unramRoots_all 2 _ 3 _)
      (FrobPiecesGood.tateBridge35_of_neron_nmp hT hsp hc hRed hN)
      (LTLocal.modelEndRank4NC_of_qmEndRank hFS (qmEndRank_of_leaves3_hf h6 hYu)))
    LTLocal.g7DegreeBound_gp4
end HSyn
end LT

/-! ## 4. After G7 at fibres without CM, on the `_u` research leaves and fold-c8's Galois pieces -/

section AG
namespace HSyn.G0AssembleMod
open CategoryTheory AlgebraicGeometry
open G0ModField
/-- cm-branch's `afterG7NC_of3_hf_pz_eb` on `ResearchLeaves3EBU` and `GaloisPiecesC8` (fold-c8's
`afterG7_of3_hf_pz_eb_u_c8`, localized). -/
theorem afterG7NC_of3_hf_pz_eb_u_c8 (r : ResearchLeaves3EBU) (t : TextbookLeavesHFPZ)
    (m : G0Galois.GaloisPiecesC8)
    (h9 : G0Galois.G9GlueNoT23)
    (hDF : G0ModNewform.DirichletOfFinite) (hCar : LadicCond.CarayolR17')
    (hSw : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p))
    (hL8 : LadicCond.SwanIntegral)
    (hAd : ∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p))
    (hG36 : ModelG3G6NC) (hLink : LinkedTateDataNC) : AfterG7NC := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hdata
  letI : NumberField L' := numberField_of_fd L'
  obtain ⟨h6, h3₅, h3₃⟩ := hG36 Y Φ π u P hctx L A ε N χ β L' hLL' hdata
  obtain ⟨Tm₅, c₅, ε₅, a₅, β₅, u₅, Tm₃, c₃, ε₃, a₃, β₃, u₃, h7₅, h7₃, hlink⟩ :=
    hLink Y Φ π u P hctx L A ε N χ β L' hLL' hdata
  have h2 : G0Galois.G2Out L' (T u) :=
    galoisG2Out_of_g7Data resQRange u P L A ε N χ β L' hLL' hdata
  obtain ⟨r₅, h8₅, -, -, h11₅, h12⟩ :=
    G0Galois.g8_g12_of_leaves3_hf_pz_eb_u_c8 r t m h9 _ (T u) h2 h6 h3₅ Tm₅ c₅ ε₅ a₅ β₅ u₅ h7₅
  obtain ⟨r₃, h8₃, -, -, h11₃⟩ :=
    G0Galois.g8_g11_hf r.r9a r.r9b t.t26 t.t6 HSyn.G0Split.semisimpleBaseChange r.r10 t.t11a
      t.t11b (G0Galois.g8Matrix_of_burnside m.burnside) h9 m.odd _ (T u) h2 h6 3 h3₃
      Tm₃ c₃ ε₃ a₃ β₃ u₃ h7₃
  obtain ⟨i, ιC, ι5, hspec⟩ := G0ModNewform.g12Spec_of_galois hDF _ _ _ r₅ r₃ h8₅ h8₃ h12
  obtain ⟨ι3, h14, h15⟩ := hlink r₅ r₃ h8₅ h8₃ i ιC ι5
  obtain ⟨M, J, hM, hJ, hMle, hCC⟩ :=
    G0ModNewform.modularConstituent_tail_G (newformLeaves_of3_hf_pz_eb_u r t hCar) t.t33 t.x1ModelExists
      hSw hL8 hAd _ u ⟨_, hspec ι3, h14, g15RamG_of_wild _ u h15 h11₅ h11₃⟩
  exact ⟨M, J, hM, hJ, hMle, (commonConstituent_copy' _ _).1 hCC⟩
end HSyn.G0AssembleMod
end AG

/-! ## 5. The non-CM branch on the `_u` research leaves -/

section NB
namespace CMBranch
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ ZInQ.JHeight HDec.LeafQM.AV HDec.ZInQ.DefFaltings
open HSyn HSyn.G0Split
open scoped Quaternion TensorProduct

/-- cm-branch's `nonCMBranch_of` on `ResearchLeaves3EBU` (`hom_of_common3_hf_pz_eb` -> d2a6b's
`hom_of_common3_hf_pz_eb_u`; the other fields read are the same). -/
theorem nonCMBranch_of_u (r : HSyn.ResearchLeaves3EBU) (t : HSyn.TextbookLeavesHFPZ)
    (hDimF : DimFinite) (hDim : DimBaseChange) (hPMH : ZInQ.H5Neron.ProductModelHeight)
    (hBC : StableHeightBaseChange) (hProdE : ProductExists) (hRev : ReverseIsogeny)
    (hThetaPt : ThetaPointOfFibre) (hCopies : HSyn.HeightCopiesAgree)
    (hSimp : FibreSimpleNC) (hMod : ModularConstituentNC) (h20 : R20Lower) : NonCMBranch := by
  have hBelyi : X1BelyiOnModel := x1BelyiOnModel_of_belyiX1 t.belyiX1
  have hAdd : HeightAdditivity := heightAdditivity_of_h5neron t.t41 r.h5.2 hPMH
  have hR18 : R18_JavanpeykarConcrete := r18Concrete_of r.r18 hCopies
  have hR22 : R22_PazukiConcrete := r22Concrete_of r.r22 hCopies
  intro Y Φ π h1 h2 hfib u hu hNC
  obtain ⟨y, P, hP, hy⟩ := hfib (OnePoint.some (algebraMap ℚ LeafQM.AV.Qbar (ZInQ.JHeight.Jmap u)))
  obtain ⟨L, emb, A, N, J, hiso, hN0, hJ1, hNQ, hdQ, hCC⟩ := hMod Y Φ π h1 h2 u hu hNC y P hP hy
  have hFib : FibreOver Y Φ π u L A := ⟨emb, y, P, hP, hy, hiso⟩
  have hA2 : A.dim = 2 := model_dim hDim emb A P.A hiso P.surface
  have hfin := r.h5.1
  have hx : ZInQ.DefFaltings.stableFaltingsHeight A = ZInQ.DefFaltings.faltingsHeight A :=
    (ZInQ.DefFaltings.faltingsHeight_coe hfin A).symm
  obtain ⟨K', z, hF1, hPaz⟩ := thetaPazuki hR22 hThetaPt Y Φ π h1 h2 u hu L A hFib hA2 _ hx
  refine ⟨K', z, ZInQ.DefFaltings.faltingsHeight A, hF1, hPaz, ?_⟩
  obtain ⟨f, hf⟩ := hom_of_common3_hf_pz_eb_u r t _ _ hCC
  obtain ⟨Z, g, hisoZ⟩ := t.t8 L.K _ _ (hSimp Y Φ π h1 h2 u hu hNC L A hFib) f hf
  obtain ⟨Pr, φ, hφ, hPprod, hdims⟩ :=
    isogenousProduct hDimF hProdE hRev L.K _ _ _ f g hisoZ
  obtain ⟨gJ, hgJ, hgN⟩ := dim_J1_le_of5 t34Le N hN0 J hJ1
  have hJLd : (((LeafAdopt.abVarEquiv ℚ).symm J).baseChange L.K).dim = (gJ : WithBot ℕ∞) :=
    (hDim ℚ L.K ((LeafAdopt.abVarEquiv ℚ).symm J)).trans hgJ
  have hALd : A.dim = ((2 : ℕ) : WithBot ℕ∞) := by rw [hA2]; rfl
  obtain ⟨gZ, hZd, hsum⟩ := hdims 2 gJ hALd hJLd
  have hxJ : ZInQ.DefFaltings.stableFaltingsHeight
      (((LeafAdopt.abVarEquiv ℚ).symm J).baseChange L.K) =
      ZInQ.DefFaltings.faltingsHeight ((LeafAdopt.abVarEquiv ℚ).symm J) := by
    rw [hBC ℚ L.K ((LeafAdopt.abVarEquiv ℚ).symm J)]
    exact (ZInQ.DefFaltings.faltingsHeight_coe hfin _).symm
  have hyP := (ZInQ.DefFaltings.faltingsHeight_coe hfin Pr).symm
  have hzZ := (ZInQ.DefFaltings.faltingsHeight_coe hfin ((LeafAdopt.abVarEquiv L.K).symm Z)).symm
  have hadd := hAdd L.K Pr A ((LeafAdopt.abVarEquiv L.K).symm Z) hPprod _ _ _ hx hzZ hyP
  have hJb := javanpeykarJ1_of_le hR18 hBelyi t34Le N hN0 J hJ1 gJ hgJ (by omega) _
    (ZInQ.DefFaltings.faltingsHeight_coe hfin _).symm
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN0
  have hgN' : (gJ : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hgN
  exact transfer_core r.r19 h20 r.r21 (((LeafAdopt.abVarEquiv ℚ).symm J).baseChange L.K) Pr A
    ((LeafAdopt.abVarEquiv L.K).symm Z) gJ gZ hJLd hZd (by omega) (by omega) φ hφ _ _ _ _ hxJ hyP
    hzZ hadd hN1 hNQ hJb hgN' hdQ

end CMBranch
end NB

/-! ## 6. `SixContactMin` at the live chain's base generation with the CM branch -/

section TOP
namespace HSyn
open CategoryTheory AlgebraicGeometry G0Split

/-- cm-branch's `sixContactMin_of_open4_cm` on the live chain's bundles at this generation (`OpenResearchLeaves2EBU`:
R6 = `D2A6.R6U`; `OpenAddedLeaves4PZC8`: `c8` for the Weil-pairing fields): the manuscript's CM branch (L581-631)
in place of FS5 (NoCM) in fold-c8's `sixContactMin_of_open4_hf_pz_eb_u_c8`. -/
theorem sixContactMin_of_open4_cm_u_c8 (r : OpenResearchLeaves2EBU) (t : OpenTextbookLeaves4HFPZ)
    (l : OpenAddedLeaves4PZC8) (g : OpenGlue4) (h20 : G0Split.R20Lower) (hYu : QMLattice.YuB6Alg)
    (hθ : PkgI1.QMHauptmodul → G0Split.ThetaPt.ThetaSplit.ThetaRatiosAtQM)
    (hSplit : CMBranch.CMFibreSplit) (hF : CMBranch.FowlerProp27) (hJ : CMBranch.CMjDegree)
    (hPG : CMBranch.CMPotentialGood) (h62 : CMBranch.CMHeight62) (hRP : CMBranch.ReducedCMPeriod)
    (hAddU : CMBranch.HeightAdditivityUpper) : ZInQ.SixContactMin :=
  let t2 := textbookLeaves2_of_open3_hf_pz (textbookLeaves3_of_open4_hf_pz t)
  let r3 := researchLeaves3_of_open2_eb_u r
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
      (G0ModField.KernelField.kernelFieldExistsNC_of_split_hf_u t.t6 r.r7a r.r6 t.t5 hYu
        G0ModField.KernelField.oMaximal endTransport_proved conjIsogMaps_proved3)
      UnramTate.unramifiedSup_mf
      (G0AssembleMod.afterG7NC_of3_hf_pz_eb_u_c8 r3 t3
        ⟨burnsideAbsIrred_proved3, r.r14,
          g9Glue_of_deRhamComparisonHT r.r10,
          G0Galois.g10Glue_of_conjTwist
            (G0Galois.conjTwistNontrivial_of_leaves t.t5 (tateModuleFree_of_t5' t.t5) t.t35
              (HomUnify.homLinearLift_of_corr t.homLatticeCorr)),
          G0Galois.g12Weight_of_senTwist l.senTwist l.finiteImageHT,
          l.c8,
          G0AssembleMod.resQFiniteIndex⟩
        (g9GlueNoT23_of_deRhamComparisonHT r.r10)
        (G0ModNewform.dirichletOfFinite_of_t17 t17_proved) r.r17
        Swan.swanIndependent_proved Swan.swanIntegral_proved
        Swan.adaptedExists_proved
        (HSyn.modelG3G6NC_of_leaves3U hFSNC r.r7a r.r6 t.t5)
        (G0AssembleMod.linkedTateDataNC_of_local t.t7
          (HSyn.linkedTateLocalNC_of_leaves3_hf_u r.r6 t.t5 (tateModuleFree_of_t5' t.t5)
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
  have hRev : ReverseIsogeny := G0RevIsog.reverseIsogeny_of_leaves3_eb_u r3 G0Split.dimFinite
  have hThetaPt : ThetaPointOfFibre := G0Split.ThetaPt.ThetaSplit.thetaPointOfFibre_of_qm_atQM
      (G0Split.FibreQM.fibreQMPeriod_main_rep r.r1r2 hMob l.qmHauptmodul
        t.t35 t2.t11a l.qmClassNumberOne (r.r1b r.r1r2) (periodMapGlue_of_leaves4 r.r1r2 t.t5 t.homLatticeCorr l.cmDescends)
        hauptmodulUnique_proved4
        (qmDenZeroCM3_of_leaves4 r.r4 l.gammaStarGen l.valenceBoundGammaStar) cPtsTransport_proved3)
      (hθ l.qmHauptmodul)
  have hCopies : HeightCopiesAgree := G0HeightCopies.heightCopiesAgree
  CMBranch.sixContactMin_of_branches (LeafQM.AV.exists_fibre_object (LeafAdopt.R1R2fp_of_rep r3.r1r2))
    (CMBranch.nonCMBranch_of_u r3 t3 hDimF hDim hPMH hBC hProdE hRev hThetaPt hCopies hFSNC hModNC h20)
    (CMBranch.cmBranchOut_of r3.h5.1 hDim (thetaPazuki (r22Concrete_of r3.r22 hCopies) hThetaPt)
      hSplit hF hJ hPG h62 hRP hAddU r3.r19 h20)

end HSyn
end TOP

end
end HDec
