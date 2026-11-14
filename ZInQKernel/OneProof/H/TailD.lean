import ZInQKernel.OneProof.H.TailC

namespace HDec

set_option maxHeartbeats 1000000

attribute [-instance] TauCeti.FinitePadicExtension.toAlgebra
  TauCeti.FinitePadicExtension.ofInstances TauCeti.FinitePadicExtension.toModuleFinite
  TauCeti.FinitePadicExtension.toValuativeExtension

section G0A2_z80_leaves3
-- (leaf-fold2: copied from scratch/g0-assemble2/parts/z80_leaves3.lean; 1 HDec name-resolution edits)
/-! ## g0-assemble2: `ResearchLeaves3`, the research bundle without placeholders

`HSyn.ResearchLeaves` (Leaves.lean) has two fields whose types are `opaque` placeholders,
`r1an : R01b_ComplexUniformization` and `r17 : R17_Carayol`: no proof of them can exist, so the
bundle cannot be inhabited, and neither of them is used by any proof. `ResearchLeaves3` is the
same structure (field names, types and docstrings copied) without these two fields, and with
`h5 : LeafAdopt.H5 = StableHeightFinite ∧ NeronModelMinimal` replaced by its first half
`h5fin` (the second is proved by h5-glue, part a90). Their concrete replacements are fields of
`GluePieces3`: `carayolR17 : LadicCond.CarayolR17'` and `r1bFamily` (fibre-qm-period).

The seven consumers of `r : ResearchLeaves` on the route are copied below with `r : ResearchLeaves3`
(names suffixed `3`); their proofs are the originals', verbatim (they use `r` only through
fields, and `r.h5` is `ResearchLeaves3.h5` below). -/

noncomputable section

namespace HSyn

open scoped MatrixGroups ModularForm

/-- **The research-level leaves, without placeholders** (g0-assemble2; see above). -/
structure ResearchLeaves3 : Prop where
  /-- R1 (a), (c), (d), `π₀(X₆) = 1` (rv-blueprints Q4), R1 at level one, R2 with biconditional CM
  clauses (Q5) and R5 on points of `X₆`, on one `Y₃`, `X₆` (leaf-qm-fp, repaired by leaf-adopt).
  Premise (rv-qm-polar Lemma P): for a QM pair `(A, ι)` in characteristic 0 there is exactly one
  principal polarization whose Rosati involution is `x ↦ μ⁻¹x̄μ` on `ι(𝒪)` (`μ = 2j + ij`, the
  type fixed by the PEL datum); see the definition. Checked by model reviews (rv-qm-polar), no
  human review. -/
  r1r2 : LeafAdopt.R1R2fpRep
  -- (g0-assemble2) `r1an : R01b_ComplexUniformization` (an `opaque` placeholder) removed: unused;
  -- its concrete family form is `GluePieces3.r1bFamily` (fibre-qm-period).
  /-- R1(d), Shimura reciprocity, object form (leaf-qm-fp; premise Lemma P, rv-qm-polar). -/
  r1rec : LeafQM.AV.R1rec
  /-- R3, Lin–Yang over `ℂ`, existential and polarization-free (leaf-push2; premise Lemma P). -/
  r3 : ZInQ.LeafPush2.R03_LinYang
  r4 : PkgI1.ThetaModularity
  /-- R5(ii), González–Rotger Thm 5.12, fields of moduli (= rv-blueprints' R5fpStrong, Q2;
  premise Lemma P, rv-qm-polar). -/
  r5 : LeafQM.AV.R5fp
  /-- R5(i), González–Rotger Prop. 5.6, `#CM(R) = 2^b h(R)` (premise Lemma P, rv-qm-polar). -/
  r5count : LeafQM.AV.R5fpCount
  r6 : PkgI2.RaynaudCriterion.{0}
  r7a : PkgI2.NeronOggShafarevich.{0}
  r7b : PkgI2.SerreTatePotentialGood.{0}
  r8 : PkgI2.GrothendieckMonodromy.{0}
  r9a : PkgI3.FaltingsSemisimple
  r9b : PkgI3.FaltingsTate
  r10 : PkgI4.DeRhamComparison
  /-- R11 (Berger) and R12 (Pan) enter through their joint consequence: Pan's theorem with "de Rham
  at `p`" in place of "potentially semistable at `p`" (pkg-I4). `B_st` is not needed by the glue.
  Both theorems remain separate leaves in the count. -/
  r11r12 : PkgI4.PanBerger
  r13 : PkgI4.EigenformHT
  r14 : EigenformRepExists
  r15 : DeligneSerreConseq
  /-- R16, Eichler–Shimura in `J₁(N)`, existential form for every `K_N` model (leaf-modcurves). -/
  r16 : LeafModCurves.R16_EichlerShimuraJ1'
  -- (g0-assemble2) `r17 : R17_Carayol` (an `opaque` placeholder) removed: unused; its concrete form
  -- is `GluePieces3.carayolR17` (`LadicCond.CarayolR17'`).
  /-- R18, Javanpeykar, over leaf-push2's stable Faltings height on `PkgI3.AbVar` (with H5). -/
  r18 : ZInQ.LeafPush2.R18_Javanpeykar
  /-- R19-R21 over def-faltings' `stableFaltingsHeight`. Its value is `⊤` (no metrized model) or
  the stable Faltings height in Faltings' normalization, so R19-R21 are true for the definition;
  they say something only together with `h5` (`StableHeightFinite`), which is where a defect of
  the definition would surface, as a false leaf (rv-leaves48, `RvLeaves48D`). -/
  r19 : ZInQ.DefFaltings.R19_GaudronRemond
  r20 : ZInQ.DefFaltings.R20_FaltingsLemma5
  r21 : ZInQ.DefFaltings.R21_Bost
  /-- R22, Pazuki's upper half, over all uniformizations and period matrices (leaf-push2). -/
  r22 : ZInQ.LeafPush2.R22_Pazuki
  /-- H5's finiteness half (rv-blueprints F2): the stable height is finite (g0-assemble2: the
  other half, `NeronModelMinimal`, is proved by h5-glue, `ZInQ.H5Glue.neronModelMinimal`). -/
  h5fin : ZInQ.DefFaltings.StableHeightFinite


/-- H5 from its finiteness half and h5-glue's `NeronModelMinimal`. -/
theorem ResearchLeaves3.h5 (r : ResearchLeaves3) : LeafAdopt.H5 :=
  ⟨r.h5fin, ZInQ.H5Glue.neronModelMinimal⟩

/-- `ResearchLeaves3` is weaker than `ResearchLeaves`. -/
theorem researchLeaves3_of (r : ResearchLeaves) : ResearchLeaves3 :=
  { r1r2 := r.r1r2,
    r1rec := r.r1rec,
    r3 := r.r3,
    r4 := r.r4,
    r5 := r.r5,
    r5count := r.r5count,
    r6 := r.r6,
    r7a := r.r7a,
    r7b := r.r7b,
    r8 := r.r8,
    r9a := r.r9a,
    r9b := r.r9b,
    r10 := r.r10,
    r11r12 := r.r11r12,
    r13 := r.r13,
    r14 := r.r14,
    r15 := r.r15,
    r16 := r.r16,
    r18 := r.r18,
    r19 := r.r19,
    r20 := r.r20,
    r21 := r.r21,
    r22 := r.r22,
    h5fin := r.h5.1 }

end HSyn

namespace HSyn.G0RevIsog

theorem reverseIsogeny_of_leaves3 (r : HSyn.ResearchLeaves3) (hDimF : G0Split.DimFinite) :
    G0Split.ReverseIsogeny :=
  reverseIsogeny_of_exists (isogenyReverseExists_of_r19 r.r19 r.h5.1 hDimF)

end HSyn.G0RevIsog

namespace G0Galois

-- op-dedupe was: open PkgI4 (GaloisRep GaloisChar)
open _root_.PkgI4 (GaloisRep GaloisChar) -- op-dedupe

theorem g8_g12_of_leaves3 (r : HSyn.ResearchLeaves3) (t : HSyn.TextbookLeaves) (m : GaloisPieces)
    {K : Type} [Field K] [NumberField K] [IsGalois ℚ K] (A : PkgI3.AbVar K) (T : Finset ℕ)
    (h2 : G2Out K T) (h6 : G6Out A) (h3 : G3Out A 5 T)
    (Tm : PkgI4.GQ → Module.End (PadicAlgCl 5) (Vb A 5))
    (c ε : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 5) (a β : PkgI4.GQ → PadicAlgCl 5)
    (u : GlueDescent.MatrixUnits2 (PadicAlgCl 5) (Vb A 5))
    (h7 : G7Out A 5 Tm c ε a β u) :
    ∃ r₅ : GaloisRep 5 2, G8Out A 5 (GlueDescent.rho Tm a β) r₅ ∧ G9Out r₅ ∧ G10Out r₅ ∧
      G11Out T r₅ ∧ G12Out r₅ :=
  g8_g12 r.r9a r.r9b t.t26 t.t6 HSyn.G0Split.semisimpleBaseChange r.r10 t.t23 t.t11a t.t11b
    r.r11r12 r.r14 r.r13 r.r15 t.frobeniusDense HSyn.t19_proved t.t9 (g8Matrix_of_burnside m.burnside) m.deRham m.odd m.weight
    (g12Det_of m.r14det m.detTate m.finIndex (frobeniusDenseQ_of t.frobeniusDense))
    A T h2 h6 h3 Tm c ε a β u h7

end G0Galois

namespace HSyn.G0AssembleMod

open CategoryTheory AlgebraicGeometry
open G0ModField
open _root_.G0ModField (numberField_of_fd) -- op-dedupe

theorem newformLeaves_of3 (r : ResearchLeaves3) (t : TextbookLeaves)
    (hCar : LadicCond.CarayolR17') : G0ModNewform.NewformLeaves :=
  ⟨C9Rhof.eigenformTwist_of_hsyn t.t24, t.t25, C9Rhof.eigenformRepExists_of_hsyn r.r14, r.r16,
    hCar, r.r9a, r.r9b, t.t26, C9Rhof.frobeniusDense_of_hsyn t.frobeniusDense,
    TSkolemKW.C10.brauerNesbittChar0'⟩

theorem afterG7_of3 (r : ResearchLeaves3) (t : TextbookLeaves) (m : G0Galois.GaloisPieces)
    (hDF : G0ModNewform.DirichletOfFinite) (hCar : LadicCond.CarayolR17')
    (hSw : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p))
    (hL8 : LadicCond.SwanIntegral)
    (hAd : ∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p))
    (hG36 : ModelG3G6) (hLink : LinkedTateData) : AfterG7 := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hdata
  letI : NumberField L' := numberField_of_fd L'
  obtain ⟨h6, h3₅, h3₃⟩ := hG36 Y Φ π u P hctx L A ε N χ β L' hLL' hdata
  obtain ⟨Tm₅, c₅, ε₅, a₅, β₅, u₅, Tm₃, c₃, ε₃, a₃, β₃, u₃, h7₅, h7₃, hlink⟩ :=
    hLink Y Φ π u P hctx L A ε N χ β L' hLL' hdata
  have h2 : G0Galois.G2Out L' (T u) :=
    galoisG2Out_of_g7Data resQRange u P L A ε N χ β L' hLL' hdata
  obtain ⟨r₅, h8₅, -, -, h11₅, h12⟩ :=
    G0Galois.g8_g12_of_leaves3 r t m _ (T u) h2 h6 h3₅ Tm₅ c₅ ε₅ a₅ β₅ u₅ h7₅
  obtain ⟨r₃, h8₃, -, -, h11₃⟩ :=
    G0Galois.g8_g11 r.r9a r.r9b t.t26 t.t6 HSyn.G0Split.semisimpleBaseChange r.r10 t.t23 t.t11a
      t.t11b (G0Galois.g8Matrix_of_burnside m.burnside) m.deRham m.odd _ (T u) h2 h6 3 h3₃
      Tm₃ c₃ ε₃ a₃ β₃ u₃ h7₃
  obtain ⟨i, ιC, ι5, hspec⟩ := G0ModNewform.g12Spec_of_galois hDF _ _ _ r₅ r₃ h8₅ h8₃ h12
  obtain ⟨ι3, h14, h15⟩ := hlink r₅ r₃ h8₅ h8₃ i ιC ι5
  obtain ⟨M, J, hM, hJ, hMle, hCC⟩ :=
    G0ModNewform.modularConstituent_tail_G (newformLeaves_of3 r t hCar) t.t33 t.x1ModelExists
      hSw hL8 hAd _ u ⟨_, hspec ι3, h14, g15RamG_of_wild _ u h15 h11₅ h11₃⟩
  exact ⟨M, J, hM, hJ, hMle, (commonConstituent_copy' _ _).1 hCC⟩

end HSyn.G0AssembleMod

namespace HSyn

namespace G0Split

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ ZInQ.JHeight LeafQM.AV ZInQ.DefFaltings
open _root_.ZInQ (DefFaltings.AbVar DefFaltings.AnalyticUniformizationExists DefFaltings.AnalyticUniformizationUnique DefFaltings.EReal.add_coe_add_neg_coe DefFaltings.FinExt DefFaltings.Genus2Eq DefFaltings.Genus2Eq.Good DefFaltings.Genus2Eq.P DefFaltings.Genus2Eq.binDisc DefFaltings.GroupModel DefFaltings.GroupModel.IsAnalyticUniformization DefFaltings.GroupModel.IsNeronModel DefFaltings.GroupModel.Pts DefFaltings.GroupModel.cotangent DefFaltings.GroupModel.dCls DefFaltings.GroupModel.detLattice DefFaltings.GroupModel.dom DefFaltings.GroupModel.evalAt DefFaltings.GroupModel.exists_rep DefFaltings.GroupModel.genStalk DefFaltings.GroupModel.genericUnit DefFaltings.GroupModel.germAlong DefFaltings.GroupModel.height DefFaltings.GroupModel.height_eq DefFaltings.GroupModel.hodgeSpace DefFaltings.GroupModel.jacDet DefFaltings.GroupModel.jacDet_comp DefFaltings.GroupModel.omega DefFaltings.GroupModel.omegaAt DefFaltings.GroupModel.omegaAt_genericPt DefFaltings.GroupModel.ptC DefFaltings.GroupModel.semilinear_ext_wedge DefFaltings.GroupModel.specializes_genericUnit DefFaltings.GroupModel.structMap DefFaltings.GroupModel.unitSection DefFaltings.GroupModel.wedge DefFaltings.HermitianLattice DefFaltings.HermitianLattice.arakelovDegree DefFaltings.HermitianLattice.arakelovDegree_ofFractionalIdeal DefFaltings.HermitianLattice.arakelovDegree_rescale DefFaltings.HermitianLattice.degreeAt DefFaltings.HermitianLattice.degreeAt_eq DefFaltings.HermitianLattice.degreeAt_eq_arakelovDegree DefFaltings.HermitianLattice.degreeAt_smul DefFaltings.HermitianLattice.ofFractionalIdeal DefFaltings.HermitianLattice.rescale DefFaltings.HermitianLattice.secIndex_ne_zero DefFaltings.HodgeData DefFaltings.HodgeData.coeff_apply_ne_zero DefFaltings.HodgeData.hodgeBundle DefFaltings.HodgeData.modelHeight DefFaltings.HodgeData.modelHeight_eq DefFaltings.HodgeData.modelHeight_eq_add_of_le DefFaltings.HodgeData.modelHeight_eq_faltingsHeightGood DefFaltings.HodgeData.modelHeight_le_of_le DefFaltings.HodgeData.modelHeight_ofIdeal DefFaltings.HodgeData.modelHeight_ofIdeal_baseChange DefFaltings.HodgeData.modelHeight_of_span DefFaltings.HodgeData.modelHeight_recoord DefFaltings.HodgeData.norm DefFaltings.HodgeData.norm_sq DefFaltings.HodgeData.recoord DefFaltings.HodgeLatticeTheorem DefFaltings.IsIsogeny DefFaltings.MetrizedModel DefFaltings.MetrizedModel.modelHeight_eq_of_model_eq DefFaltings.NeronModelMinimal DefFaltings.PeriodAreaFormula DefFaltings.R19_GaudronRemond DefFaltings.R20_FaltingsLemma5 DefFaltings.R21_Bost DefFaltings.StableHeightFinite DefFaltings.absNorm_extendedHom DefFaltings.absNorm_map_ringOfIntegers DefFaltings.arakelovDegree_ofFractionalIdeal_baseChange DefFaltings.arakelovDegree_ofFractionalIdeal_mul DefFaltings.card_embeddings_over DefFaltings.covolume_comap_mul_det DefFaltings.covolume_gaussianPair DefFaltings.det_restrictScalars_complex DefFaltings.embCoeff DefFaltings.faltingsHeight DefFaltings.faltingsHeightEC DefFaltings.faltingsHeightGood DefFaltings.faltingsHeight_coe DefFaltings.finiteHeightPart DefFaltings.finrank_ringOfIntegers DefFaltings.gaussianPair DefFaltings.genericFibre DefFaltings.genericPt DefFaltings.grKappa DefFaltings.hypGram DefFaltings.hypGram_comp_add DefFaltings.hypVol DefFaltings.hypVol_one_comp_add DefFaltings.isogDeg DefFaltings.le_stableFaltingsHeight DefFaltings.modelHeight_ofIdeal_eq_faltingsHeightEC DefFaltings.modelHeight_ofIdeal_eq_faltingsHeightEC' DefFaltings.norm_algebraMap_tower DefFaltings.ptObj DefFaltings.ratCoeff DefFaltings.realify DefFaltings.secIndex DefFaltings.secIndex_mul_absNorm DefFaltings.secIndex_smul DefFaltings.stableFaltingsHeight DefFaltings.stableFaltingsHeightDeligne DefFaltings.stableFaltingsHeightDeligne_eq DefFaltings.stableFaltingsHeight_eq_faltingsHeightGood DefFaltings.stableFaltingsHeight_eq_iInf_height DefFaltings.stableFaltingsHeight_le DefFaltings.stableFaltingsHeight_ne_bot_of_R21 DefFaltings.sum_embeddings_comp DefFaltings.sum_log_norm_embeddings DefFaltings.sum_log_norm_embeddings_int DefFaltings.torusMetricSq DefFaltings.torusMetricSq_comap DefFaltings.torusMetricSq_eq_setIntegral DefFaltings.torusMetricSq_pos DefFaltings.torusMetricSq_smul DefFaltings.torus_setIntegral_indep H5Glue.GenericFibreStalkIso H5Glue.GroupModel.baseChange H5Glue.GroupModel.isNeronModel_iff H5Glue.GroupModelBaseChangeExists H5Glue.HeightAntitone H5Glue.HodgeLatticeNonzero H5Glue.HodgeMapBijective H5Glue.IsBaseChangeOf H5Glue.IsOpenSubgroupModel H5Glue.IsProductAbVar H5Glue.IsProductModel H5Glue.ModelHeightBaseChange H5Glue.NeronModelExists H5Glue.NeronProp H5Glue.NeronProp.lift H5Glue.NeronProp.of_iso H5Glue.NeronProp.tensor H5Glue.NeronProp.uniqueIso H5Glue.OmegaSpans H5Glue.OpenImmersionHeightLe H5Glue.OpenSubgroupHeight H5Glue.ProductGroupModelExists H5Glue.ProductModelHeight H5Glue.SemistableNeronIdentityComponent H5Glue.baseChange_map_bijective H5Glue.bcProd H5Glue.bijective_respectsIso H5Glue.compositum H5Glue.cotMap H5Glue.cotMap_bijective H5Glue.cotMap_dCls H5Glue.cotMap_omega H5Glue.cotMap_omegaAt H5Glue.detLattice_le_hodgeMap H5Glue.dom_comp H5Glue.evalAt_comp H5Glue.evalAt_res H5Glue.exists_smul_mem_omega H5Glue.fst_genericFibreUnit H5Glue.fst_genericFibre_unit H5Glue.genBC H5Glue.genBC_isMonHom H5Glue.genMap H5Glue.genMap_germ H5Glue.genMap_mem_maximalIdeal H5Glue.genMap_mem_maximalIdeal_iff H5Glue.genMap_structMap H5Glue.genericFibreStalkIso H5Glue.genericFibreUnit H5Glue.genericIso_of_openImmersion H5Glue.germAlong_comp_eventuallyEq H5Glue.groupModelBaseChangeExists H5Glue.heightAntitone H5Glue.heightAntitone_of H5Glue.heightAntitone_of_hodgeLatticeNonzero H5Glue.heightAntitone_of_omegaSpans H5Glue.hodgeLatticeNonzero_of_omegaSpans H5Glue.hodgeMap H5Glue.hodgeMapBijective H5Glue.hodgeMap_detLattice H5Glue.hodgeMap_wedge H5Glue.hodgeMap_wedgeGerm H5Glue.isAnalyticUniformization_comp H5Glue.isAnalyticUniformization_of_comp H5Glue.isIso_genMap H5Glue.isIso_of_openImmersion_self H5Glue.isIso_stalkSpecializes_genMap H5Glue.isMonHom_of_map H5Glue.isMonHom_pbCompHom H5Glue.isMonHom_pbCompInv H5Glue.isMonHom_pbEqIso H5Glue.isMonHom_prodComparisonIso H5Glue.isNeronModel_of_isProductModel H5Glue.isOpenImmersion_pullback_map H5Glue.jL H5Glue.jacDet_comp_genMap H5Glue.jacDet_comp_map H5Glue.map_genericUnit' H5Glue.map_span_singleton_toAddSubgroup H5Glue.map_zero_of_hom H5Glue.modelHeight_pullHodge_le H5Glue.neronModelMinimal H5Glue.neronModelMinimal_of_heightAntitone H5Glue.neron_lift H5Glue.neron_lift_isMonHom H5Glue.neron_map_injective H5Glue.omegaAt_le_cotMap H5Glue.omegaSpans H5Glue.omega_le_cotMap H5Glue.one_mem_dom H5Glue.openImmersionHeightLe H5Glue.openSubgroupHeight H5Glue.openSubgroupHeight_of H5Glue.pbCompHom H5Glue.pbCompInv H5Glue.pbCompIso H5Glue.pbEqIso H5Glue.productGroupModelExists H5Glue.ptCIso H5Glue.ptC_hom_apply H5Glue.ptsEquiv H5Glue.ptsEquiv_comp H5Glue.pts_comp_bijective H5Glue.pullHodge H5Glue.secIndex_le_of_map H5Glue.secIndex_ne_zero_of_mem H5Glue.smooth_tensor H5Glue.smooth_unit H5Glue.square1 H5Glue.square2 H5Glue.stableFaltingsHeight_add_le H5Glue.stableFaltingsHeight_add_le_of_productModelHeight H5Glue.stableFaltingsHeight_eq_neron_all H5Glue.stableFaltingsHeight_eq_neron_all' H5Glue.stalkIso_of_genericIso H5Glue.stalkSpecializes_self_apply H5Glue.stalkSpecializes_stalkSpecializes_apply H5Glue.stalk_ker_eq H5Glue.stalk_spec_eq H5Glue.stalkwise_fst_toGeneric H5Glue.stalkwise_tensor_localization H5Glue.tensorGen H5Glue.tensorGen_fst H5Glue.tensorGen_snd H5Glue.toGeneric_pt H5Glue.unitSection_comp H5Neron.GroupModel.IsNeronModel.lift H5Neron.GroupModel.IsNeronModel.uniqueIso H5Neron.GroupModel.isNeronModel_iff H5Neron.GroupModelBaseChangeExists H5Neron.IsBaseChangeOf H5Neron.IsOpenSubgroupModel H5Neron.IsProductAbVar H5Neron.IsProductModel H5Neron.ModelHeightBaseChange H5Neron.NeronModelExists H5Neron.NeronProp H5Neron.NeronProp.lift H5Neron.NeronProp.of_iso H5Neron.NeronProp.tensor H5Neron.NeronProp.uniqueIso H5Neron.OpenSubgroupHeight H5Neron.ProductGroupModelExists H5Neron.ProductModelHeight H5Neron.R19_zero H5Neron.R20_zero H5Neron.R21_zero H5Neron.SemistableNeronIdentityComponent H5Neron.bcProd H5Neron.bcUnitIso H5Neron.compositum H5Neron.covolume_fin_zero H5Neron.detLattice_zero H5Neron.glue_zero H5Neron.groupModel_height_zero H5Neron.hodgeZeroEquiv H5Neron.hodgeZeroEquiv_wedge0 H5Neron.hom_ext_of_iso_unit H5Neron.isIsogeny_id_zero H5Neron.isMonHom_of_iso_unit H5Neron.isMonHom_prodComparisonIso H5Neron.isNeronModel_of_isProductModel H5Neron.isogDeg_zero_le_one H5Neron.jL H5Neron.metrizedOf H5Neron.modelHeight_dim_zero H5Neron.neronModelExists_zero H5Neron.neronModelMinimal_zero H5Neron.neron_zero_iso_unit H5Neron.no_metrized_succ H5Neron.one_le_grKappa H5Neron.productGroupModelExists H5Neron.pts_subsingleton H5Neron.semistableNeronIdentityComponent_zero H5Neron.semσ H5Neron.stableFaltingsHeight_add_le H5Neron.stableFaltingsHeight_add_le' H5Neron.stableFaltingsHeight_eq_neron H5Neron.stableFaltingsHeight_eq_neron_all H5Neron.stableFaltingsHeight_zero H5Neron.stableHeightFinite_zero H5Neron.tensorGen H5Neron.tensorGen_fst H5Neron.tensorGen_snd H5Neron.trivHodge H5Neron.trivMetrized H5Neron.trivModel H5Neron.trivModel_isNeronModel H5Neron.wedge0 H5Neron.wedge0_ne_zero H5Neron.wedge_eq_wedge0 HeightBC.CotangentSpanBC HeightBC.D0 HeightBC.D0_add HeightBC.D0_add_apply HeightBC.D0_mul HeightBC.D0_mul_apply HeightBC.D0_sq HeightBC.D0_structMap_mul HeightBC.DetLatticeBC HeightBC.GermDerivation HeightBC.HodgeBCInjective HeightBC.HodgeLineBaseChange HeightBC.HodgeLineBaseChangeDescent HeightBC.HodgeLineDescentHalf HeightBC.HodgeSpanBC HeightBC.IsBaseChangeOf HeightBC.IsHodgeBaseChange HeightBC.IsMonBC HeightBC.JacobianPullbackSpan HeightBC.JacobianSemilinear HeightBC.MetrizationBaseChange HeightBC.ModelHeightBaseChange HeightBC.ModelHeightBaseChangeGE HeightBC.ModelHeightBaseChangeLE HeightBC.OmegaBaseChange HeightBC.PtsBaseChangeBij HeightBC.PtsBaseChangeMul HeightBC.UniformizationLift HeightBC.UniformizationLiftAnalytic HeightBC.appLE_top_top HeightBC.bO HeightBC.bO_appTop HeightBC.bO_genericPt HeightBC.bcAlt HeightBC.bcCot HeightBC.bcCot_dCls HeightBC.bcCot_omega HeightBC.bcCot_omegaAt HeightBC.bcCot_update HeightBC.bcExt HeightBC.bcExt_smul HeightBC.bcExt_ιMulti HeightBC.bcHodge HeightBC.bcHodge_detLattice HeightBC.bcHodge_smul HeightBC.bcHodge_tmul HeightBC.bcHodge_wedge HeightBC.bcMap HeightBC.bcMap_germ HeightBC.bcMap_mem_maximalIdeal HeightBC.bcMap_structMap HeightBC.bcProj HeightBC.bcProj_genericUnit HeightBC.bcProj_unit HeightBC.bcProj_w HeightBC.bcPts HeightBC.cotRes HeightBC.descentHalf_of_descent HeightBC.detLatticeBC_of_omega HeightBC.dom_bcPts HeightBC.evalAt_add HeightBC.evalAt_bcPts HeightBC.evalAt_mul HeightBC.evalAt_one_eq_zero HeightBC.evalAt_res HeightBC.evalAt_structSection HeightBC.exists_comp_eq HeightBC.exists_ringOfIntegers_of_algebraMap HeightBC.extRes HeightBC.g0_hodgeLine_iff HeightBC.germAlong_add_mul HeightBC.germAlong_bcPts_eventuallyEq HeightBC.germAlong_differentiableAt HeightBC.germAlong_eventuallyEq_rep HeightBC.germAlong_structMap HeightBC.germAlong_zero_of_mem HeightBC.germDerivation HeightBC.germDerivation_at HeightBC.hodgeLineBaseChangeDescent_of_glue HeightBC.hodgeLineBaseChange_of_descent HeightBC.hodgeLineBaseChange_of_final HeightBC.hodgeLineBaseChange_of_five HeightBC.hodgeLineBaseChange_of_four HeightBC.hodgeLineBaseChange_of_glue HeightBC.hodgeLineBaseChange_of_glue4 HeightBC.hodgeLineBaseChange_of_glue5 HeightBC.hodgeLineBaseChange_of_main HeightBC.hodgeSpanBC_of HeightBC.isAnalyticUniformization_bcPts HeightBC.isIso_stalkSpecializes_bcMap HeightBC.jacDet_bcPts HeightBC.jacobianPullbackSpan_of HeightBC.jacobianSemilinear HeightBC.jacobianSemilinear_of HeightBC.map_zero_of_hom HeightBC.metrizationBaseChange_of_hodgeLine HeightBC.modelHeightBaseChangeGE_of_descent HeightBC.modelHeightBaseChangeGE_of_descentHalf HeightBC.modelHeightBaseChangeGE_of_main HeightBC.modelHeightBaseChangeGE_of_two HeightBC.modelHeightBaseChangeLE_of_metrization HeightBC.modelHeightBaseChange_of_descent HeightBC.modelHeightBaseChange_of_final HeightBC.modelHeightBaseChange_of_five HeightBC.modelHeightBaseChange_of_four HeightBC.modelHeightBaseChange_of_glue HeightBC.modelHeightBaseChange_of_glue4 HeightBC.modelHeightBaseChange_of_glue5 HeightBC.modelHeightBaseChange_of_main HeightBC.modelHeight_eq_of_isHodgeBaseChange HeightBC.multilinear_mem_span HeightBC.one_mem_dom HeightBC.ptC_hom_apply HeightBC.ptC_hom_comp_bO HeightBC.ptsBaseChangeBij HeightBC.ptsBaseChangeMul HeightBC.secIndex_baseChange HeightBC.secIndex_map HeightBC.secIndex_ne_zero_of_baseChange HeightBC.secIndex_nsmul_mem HeightBC.span_bcHodge_le HeightBC.stalkSpecializes_self_apply' HeightBC.stalkSpecializes_stalkSpecializes_apply' HeightBC.uniformizationLift_of LeafPush2.CPts LeafPush2.Char2 LeafPush2.HasSexticModel LeafPush2.IC10 LeafPush2.IC2 LeafPush2.IC4 LeafPush2.IC6 LeafPush2.IgJ10 LeafPush2.IgJ2 LeafPush2.IgJ4 LeafPush2.IgJ6 LeafPush2.IsGenus2 LeafPush2.IsPeriodMatrix LeafPush2.IsSiegel LeafPush2.IsUniformization LeafPush2.LinYangTuple LeafPush2.OnQMLocus LeafPush2.T10_groupIso LeafPush2.T11a_RiemannEnd LeafPush2.T11b_Rigidity LeafPush2.T12_ComplexConjEigen LeafPush2.UniformizationExists LeafPush2.absLogHeight LeafPush2.cDom LeafPush2.cEvalAt LeafPush2.cptObj LeafPush2.dsq LeafPush2.exists_isComplexConj LeafPush2.ffAlgebra LeafPush2.ffStructMap LeafPush2.isSiegel_I LeafPush2.javanpeykarBound LeafPush2.javanpeykarBound_mono LeafPush2.javanpeykarBound_pos LeafPush2.linYangTuple_onQMLocus LeafPush2.linYang_j_eq LeafPush2.onQMLocus_of_linYangTuple LeafPush2.pazukiC2 LeafPush2.sextic LeafPush2.thetaConst) -- op-dedupe
open _root_.LeafQM.AV (CMExists HasCM24 HasCM24.of_iso HasCM3 HasCM3.of_iso HasCM4 HasCM4.of_iso IsBaseChangeOf IsBaseChangeOfPair IsFibreOf Level3 Level3.bcPt_pow_three Level3.eq_iff Level3.exists_mul_of_range_le Level3.ext' Level3.onto Level3.range_le Level3.rightMul Level3.rightMul_eq_self Level3.rightMul_rightMul Level3.torsor Level3.twist M3 M3.mk M3.rightMul M3.rightMul_rightMul M3.twist M3.twist_mk Pin.AutOExt.NormalizerFinite Pin.AutOExt.alpha_nat_smul Pin.AutOExt.autOInnerFinite_of_normalizer Pin.AutOExt.common_den Pin.AutOExt.conjUnit Pin.AutOExt.conj_of_skolem Pin.AutOExt.den_mul_int Pin.AutOExt.exists_nat_smul_mem Pin.AutOExt.extAlgEquiv Pin.AutOExt.extAlgHom Pin.AutOExt.extAlgHom_coe Pin.AutOExt.extAlgHom_symm_comp Pin.AutOExt.extDen Pin.AutOExt.extDen_mem Pin.AutOExt.extDen_pos Pin.AutOExt.extFun Pin.AutOExt.extFun_add Pin.AutOExt.extFun_algebraMap Pin.AutOExt.extFun_coe Pin.AutOExt.extFun_eq Pin.AutOExt.extFun_mul Pin.AutOExt.key_conj Pin.AutOExt.mem_O_of_int Pin.AutOExt.natCast_mul_eq_smul Pin.AutOExt.nat_smul_mem Pin.AutOExt.smul_mul_smul' Pin.AutOInnerFinite Pin.ConstOrOntoAlgClosed Pin.CurveRatFactor Pin.CurveSurj Pin.GeomCompConstOrOnto Pin.GeomCompFinite Pin.GeomCompInfinite Pin.GeomCompRatFactor Pin.IsNaturalRelabel Pin.Mob.eval_ne_zero_of_coprime Pin.Mob.exists_interp Pin.Mob.isCoprime_X_sub_C_of_eval_one Pin.Mob.natDegree_le_one_of_injective Pin.Mob.ratEval Pin.Mob.ratEval_eq_self Pin.Mob.wronskian_ne_zero Pin.MobiusGlue Pin.NormO.IsNorm Pin.NormO.IsNorm.inv Pin.NormO.IsNorm.mul Pin.NormO.T Pin.NormO.T_finite Pin.NormO.T_mul_ui Pin.NormO.T_mul_uj Pin.NormO.bas Pin.NormO.conjC Pin.NormO.descent Pin.NormO.dvd_of_prime_dvd_nrd Pin.NormO.dvd_of_smul_mem Pin.NormO.ei Pin.NormO.ej Pin.NormO.inv_eq Pin.NormO.isNorm_sc Pin.NormO.isNorm_ui Pin.NormO.isNorm_uj Pin.NormO.mulCoord_conjC Pin.NormO.mulCoord_conjC' Pin.NormO.mulCoord_smul_left Pin.NormO.mulCoord_smul_right Pin.NormO.normalizerFinite Pin.NormO.nrdZ Pin.NormO.nrdZ_ei Pin.NormO.nrdZ_ej Pin.NormO.nrdZ_mul Pin.NormO.nrdZ_ne_zero Pin.NormO.nrdZ_smul Pin.NormO.nrd_dvd_coords Pin.NormO.ofInt_scalar Pin.NormO.rearrange Pin.NormO.sc Pin.NormO.six_sq_identities Pin.NormO.smul_ofInt Pin.NormO.three_dvd_mulCoord_ej Pin.NormO.two_dvd_mulCoord_ei Pin.NormO.ui Pin.NormO.uj Pin.PinUnique Pin.QMFamily.transport Pin.QML3.isoTransport Pin.R1fpProps.fam Pin.R1fpProps.univ Pin.RatFactorAlgClosed Pin.SameTriple Pin.SameTripleMor Pin.SmoothCurveNoIsolatedPoint Pin.SmoothStalkDimOne Pin.TwistClassFinite Pin.autOInnerFinite Pin.autRelabel Pin.autRelabel_natural Pin.bcPt Pin.bcPt_ptOfSection Pin.bcPt_snd Pin.bcQbar Pin.bcSnd Pin.cm_objects_of_R1R2fp Pin.conjUnitIso Pin.curveFacts_of_algClosed Pin.curveFacts_of_comp Pin.curveFacts_of_leaves Pin.curveFacts_of_named Pin.curveRatFactor_of_comp Pin.curveSurj_of_comp Pin.exists_isOpen_singleton_of_finite_closedPoints Pin.exists_liftO_congr Pin.geomComp Pin.geomCompConstOrOnto_of Pin.geomCompFinite Pin.geomCompInfinite_of Pin.geomCompRatFactor_of Pin.isFibreOf_transport Pin.isOpen_connectedComponent_of_noetherian Pin.level3_finite Pin.phi_part Pin.pointwise_of_witness Pin.pointwise_of_witness_mor Pin.ptOf Pin.ptOfSection Pin.r1fpPin_aut Pin.r1fpPin_relabel_iff Pin.r2fp_aut Pin.relabel Pin.relabel_geometric Pin.relabel_is_morphism Pin.sameTripleMor_of_mobius Pin.sameTriple_aut Pin.smoothCurveNoIsolatedPoint_of Pin.transfer_exists Pin.transfer_pointwise Pin.transfer_pointwise_mor Pin.transportLevel Pin.twistClassFinite Pin.twistClassFinite_of Pin.val_bcPt PtEquiv QMFamily QMIso QMIso.nonempty_abVarIso QMIso.refl QMIso.symm QMIso.trans QML3 QML3.Iso QML3.Iso.refl QML3.Iso.rightMul QML3.Iso.symm QML3.Iso.trans QML3.Iso.twist QML3.forget QML3.rightMul QML3.rightMul_A QML3.rightMul_rightMul QML3.twist QML3.twist_A QMLeaves QMPair QMPair.twist QMStr QMStr.twist Qbar R1R2fp R1R2fp_Y R1famProps R1fp R1fpProps R1fp_of_R1R2fp R1heckeProps R1rec R1recProps R1univProps R2X6Props R2fpProps R2fpProps_of_X6 R5fp R5fpCount R5fpWeak R5fpWeak_of_R5fp R5ptProps ToP1 ToP1.comp ToP1.val ToP1.val_comp ToP1.val_comp_right UnramifiedAbove5 X6Props X6Surj act_mul_apply bcPt bcPt_injective cm_of_val com comEquiv com_twist conductor conjHom conjHom_iota conjHom_mem_com conjHom_symm_apply conj_iso_of_rational conj_twist_of_rational endPt exists_fibre_object fibre_conjugates_isomorphic fieldMap fieldOfModuli3 fieldOfModuliPair fieldPt galAct_bcPt hI hIJ hJ hasCM24_twist hasCM3_twist hasCM4_twist hrat inertCount6 intCast_mem_com isoSetoid leaves_on_one_witness liftO not_qmStr_zero ofInt_injective ofInt_sub oi oi_mul_oi oj oj_mul_oi_add oj_mul_oj pairSetoid qmAct residueImage residue_unramified_over_branch specMap_flat specMap_surjective specToEquivOfField_comp specToEquivOfField_comp_right stab3 stabPair three_mul_ofInt toKbar unramified_over_branch) -- op-dedupe
open _root_.ZInQ.DefFaltings (AbVar AnalyticUniformizationExists AnalyticUniformizationUnique EReal.add_coe_add_neg_coe FinExt Genus2Eq Genus2Eq.Good Genus2Eq.P Genus2Eq.binDisc GroupModel GroupModel.IsAnalyticUniformization GroupModel.IsNeronModel GroupModel.Pts GroupModel.cotangent GroupModel.dCls GroupModel.detLattice GroupModel.dom GroupModel.evalAt GroupModel.exists_rep GroupModel.genStalk GroupModel.genericUnit GroupModel.germAlong GroupModel.height GroupModel.height_eq GroupModel.hodgeSpace GroupModel.jacDet GroupModel.jacDet_comp GroupModel.omega GroupModel.omegaAt GroupModel.omegaAt_genericPt GroupModel.ptC GroupModel.semilinear_ext_wedge GroupModel.specializes_genericUnit GroupModel.structMap GroupModel.unitSection GroupModel.wedge HermitianLattice HermitianLattice.arakelovDegree HermitianLattice.arakelovDegree_ofFractionalIdeal HermitianLattice.arakelovDegree_rescale HermitianLattice.degreeAt HermitianLattice.degreeAt_eq HermitianLattice.degreeAt_eq_arakelovDegree HermitianLattice.degreeAt_smul HermitianLattice.ofFractionalIdeal HermitianLattice.rescale HermitianLattice.secIndex_ne_zero HodgeData HodgeData.coeff_apply_ne_zero HodgeData.hodgeBundle HodgeData.modelHeight HodgeData.modelHeight_eq HodgeData.modelHeight_eq_add_of_le HodgeData.modelHeight_eq_faltingsHeightGood HodgeData.modelHeight_le_of_le HodgeData.modelHeight_ofIdeal HodgeData.modelHeight_ofIdeal_baseChange HodgeData.modelHeight_of_span HodgeData.modelHeight_recoord HodgeData.norm HodgeData.norm_sq HodgeData.recoord HodgeLatticeTheorem IsIsogeny MetrizedModel MetrizedModel.modelHeight_eq_of_model_eq NeronModelMinimal PeriodAreaFormula R19_GaudronRemond R20_FaltingsLemma5 R21_Bost StableHeightFinite absNorm_extendedHom absNorm_map_ringOfIntegers arakelovDegree_ofFractionalIdeal_baseChange arakelovDegree_ofFractionalIdeal_mul card_embeddings_over covolume_comap_mul_det covolume_gaussianPair det_restrictScalars_complex embCoeff faltingsHeight faltingsHeightEC faltingsHeightGood faltingsHeight_coe finiteHeightPart finrank_ringOfIntegers gaussianPair genericFibre genericPt grKappa hypGram hypGram_comp_add hypVol hypVol_one_comp_add isogDeg le_stableFaltingsHeight modelHeight_ofIdeal_eq_faltingsHeightEC modelHeight_ofIdeal_eq_faltingsHeightEC' norm_algebraMap_tower ptObj ratCoeff realify secIndex secIndex_mul_absNorm secIndex_smul stableFaltingsHeight stableFaltingsHeightDeligne stableFaltingsHeightDeligne_eq stableFaltingsHeight_eq_faltingsHeightGood stableFaltingsHeight_eq_iInf_height stableFaltingsHeight_le stableFaltingsHeight_ne_bot_of_R21 sum_embeddings_comp sum_log_norm_embeddings sum_log_norm_embeddings_int torusMetricSq torusMetricSq_comap torusMetricSq_eq_setIntegral torusMetricSq_pos torusMetricSq_smul torus_setIntegral_indep) -- op-dedupe

theorem hom_of_common3 (r : ResearchLeaves3) (t : TextbookLeaves) {K : Type} [Field K]
    [NumberField K] (A J : PkgI3.AbVar K) (h : CommonConstituent A J) :
    ∃ f : PkgI3.AbVar.Hom A J, f ≠ 0 := by
  obtain ⟨ℓ, _, E, _, _, U, U', e, hU, he⟩ := h
  exact PkgI3.E1_exists_hom_ne_zero r.r9a r.r9b t.t26 semisimpleBaseChange A J ℓ E U U' hU e he

end G0Split

open G0Split in
theorem glueOutputs_of_leaves3 (r : ResearchLeaves3) (t : TextbookLeaves) (gp : GluePieces) :
    GlueAssembly.GlueOutputs ZInQ.Mult.S_mul := by
  obtain ⟨hDimF, hDim, hSimp, hPMH, hBC, hProdE, hRev, hThetaPt, hMod, hCopies⟩ := gp
  have hBelyi : X1BelyiOnModel := x1BelyiOnModel_of_belyiX1 t.belyiX1
  have hAdd : HeightAdditivity := heightAdditivity_of_h5neron t.t41 r.h5.2 hPMH
  have hR18 : R18_JavanpeykarConcrete := r18Concrete_of r.r18 hCopies
  have hR22 : R22_PazukiConcrete := r22Concrete_of r.r22 hCopies
  -- A4: the moduli data and an object over every value
  obtain ⟨Y, Φ, π, h1, h2, hfib⟩ :=
    LeafQM.AV.exists_fibre_object (LeafAdopt.R1R2fp_of_rep r.r1r2)
  intro u hu
  obtain ⟨y, P, hP, hy⟩ := hfib (OnePoint.some (algebraMap ℚ Qbar (ZInQ.JHeight.Jmap u)))
  -- G2-G16 (missing piece 10, `ModularConstituent`): the field `L'`, the model `A`, the level `N`, `J₁(N)`
  obtain ⟨L, emb, A, N, J, hiso, hN0, hJ1, hNQ, hdQ, hCC⟩ := hMod Y Φ π h1 h2 u hu y P hP hy
  have hFib : FibreOver Y Φ π u L A := ⟨emb, y, P, hP, hy, hiso⟩
  have hA2 : A.dim = 2 := model_dim hDim emb A P.A hiso P.surface
  -- H5: the stable height of `A` is real
  have hfin := r.h5.1
  have hx : ZInQ.DefFaltings.stableFaltingsHeight A = ZInQ.DefFaltings.faltingsHeight A :=
    (ZInQ.DefFaltings.faltingsHeight_coe hfin A).symm
  -- G19: the theta point (missing piece 9, `ThetaPointOfFibre`) and Pazuki (R22)
  obtain ⟨K', z, hF1, hPaz⟩ := thetaPazuki hR22 hThetaPt Y Φ π h1 h2 u hu L A hFib hA2 _ hx
  refine ⟨K', z, ZInQ.DefFaltings.faltingsHeight A, hF1, hPaz, Or.inl ?_⟩
  -- E1: a nonzero homomorphism `A → J₁(N)_{L'}`
  obtain ⟨f, hf⟩ := hom_of_common3 r t _ _ hCC
  -- G5-G6 (missing piece 4, `FibreSimple`): `A` simple; T8: Poincaré
  obtain ⟨Z, g, hisoZ⟩ := t.t8 L.K _ _ (hSimp Y Φ π h1 h2 u hu L A hFib) f hf
  -- G17 after Poincaré (`isogenousProduct`, from missing pieces 1, 7, 8): `A × Z`, the isogeny `J₁(N)_{L'} → A × Z`
  obtain ⟨Pr, φ, hφ, hPprod, hdims⟩ :=
    isogenousProduct hDimF hProdE hRev L.K _ _ _ f g hisoZ
  -- E2: `dim J₁(N) ≤ N²`
  obtain ⟨gJ, hgJ, hgN⟩ := LeafModCurves.dim_J1_le t.t34 N hN0 J hJ1
  have hJLd : (((LeafAdopt.abVarEquiv ℚ).symm J).baseChange L.K).dim = (gJ : WithBot ℕ∞) :=
    (hDim ℚ L.K ((LeafAdopt.abVarEquiv ℚ).symm J)).trans hgJ
  have hALd : A.dim = ((2 : ℕ) : WithBot ℕ∞) := by rw [hA2]; rfl
  obtain ⟨gZ, hZd, hsum⟩ := hdims 2 gJ hALd hJLd
  -- heights (H5; missing pieces 5, 6; R18 with missing pieces 2, 3)
  have hxJ : ZInQ.DefFaltings.stableFaltingsHeight
      (((LeafAdopt.abVarEquiv ℚ).symm J).baseChange L.K) =
      ZInQ.DefFaltings.faltingsHeight ((LeafAdopt.abVarEquiv ℚ).symm J) := by
    rw [hBC ℚ L.K ((LeafAdopt.abVarEquiv ℚ).symm J)]
    exact (ZInQ.DefFaltings.faltingsHeight_coe hfin _).symm
  have hyP := (ZInQ.DefFaltings.faltingsHeight_coe hfin Pr).symm
  have hzZ := (ZInQ.DefFaltings.faltingsHeight_coe hfin ((LeafAdopt.abVarEquiv L.K).symm Z)).symm
  have hadd := hAdd L.K Pr A ((LeafAdopt.abVarEquiv L.K).symm Z) hPprod _ _ _ hx hzZ hyP
  have hJb := javanpeykarJ1 hR18 hBelyi t.t34 N hN0 J hJ1 gJ hgJ (by omega) _
    (ZInQ.DefFaltings.faltingsHeight_coe hfin _).symm
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN0
  have hgN' : (gJ : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hgN
  -- E3-E4 (proved from R19-R21)
  exact transfer_core r.r19 r.r20 r.r21 (((LeafAdopt.abVarEquiv ℚ).symm J).baseChange L.K) Pr A
    ((LeafAdopt.abVarEquiv L.K).symm Z) gJ gZ hJLd hZd (by omega) (by omega) φ hφ _ _ _ _ hxJ hyP
    hzZ hadd hN1 hNQ hJb hgN' hdQ

/-- **G0 with `ResearchLeaves3`** (`sixContactMin_of_leaves` of Leaves.lean, copied). -/
theorem sixContactMin_of_leavesR3 (r : ResearchLeaves3) (t : TextbookLeaves) (gp : GluePieces) :
    ZInQ.SixContactMin :=
  sixContactMin_of_glueOutputs (glueOutputs_of_leaves3 r t gp)

end HSyn

end

end G0A2_z80_leaves3

section G0A2_z85_modelg3g6
-- (leaf-fold2: copied from scratch/g0-assemble2/parts/z85_modelg3g6.lean; 0 HDec name-resolution edits)
/-! ## g0-assemble2: g0-assemble's `ModelG3G6` split

`ModelG3G6` (part 87) asks, on G7's model `A_{L'}`: `G6Out` (`End` a division ring, and
noncommutative) and `G3Out` at `ℓ = 5, 3`. The division-ring half is NoCM on the model; it follows
from g0-split's piece `FibreSimple` (which `GluePieces3` already supplies through FS5), because
G7's model is a `FibreOver` of the fibre context (G7Data's last clause `IsModelOver`). What remains
is split into two smaller glue Props. -/

noncomputable section

namespace HSyn.G0AssembleMod

open CategoryTheory AlgebraicGeometry
open G0ModField
open _root_.G0ModField (numberField_of_fd) -- op-dedupe

/-- **Glue: `End(A_{L'})` is noncommutative** on G7's model (g0-assemble2). Elementary given the QM
structure of `IsQMModel` (`ι(𝒪) ⊆ End(PK.A)`, base change `End(PK.A) → End(A_{L'})`, unram-tate's
`endBaseChange`, and `[24] ≠ 0`); not formalized. No NoCM content. -/
def ModelNoncomm : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : LeafQM.AV.PtEquiv Y) (π : LeafQM.AV.ToP1 Y.left)
    (u : ℚ) (P : LeafQM.AV.QML3 Qbar), FibreCtx Y Φ π u P →
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    ∃ x y : PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')), x * y ≠ y * x

/-- **Glue G3 on G7's model** (g0-assemble2; the G3 half of `ModelG3G6`): inertia at primes outside
`T(u)` acts trivially on `ℚ̄_ℓ ⊗ V_ℓ(A_{L'})`, `ℓ = 5, 3` (good reduction of the QM model away from
`T`, `QML3.goodReduction`, with Néron–Ogg–Shafarevich R7a). -/
def ModelG3 : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : LeafQM.AV.PtEquiv Y) (π : LeafQM.AV.ToP1 Y.left)
    (u : ℚ) (P : LeafQM.AV.QML3 Qbar), FibreCtx Y Φ π u P →
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    letI : NumberField L' := numberField_of_fd L'
    G0Galois.G3Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5 (T u) ∧
    G0Galois.G3Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3 (T u)

/-- **`ModelG3G6` from `FibreSimple`, `ModelNoncomm` and `ModelG3`** (g0-assemble2). The
`EndDivision` clause of G6 is `FibreSimple` at the `FibreOver` given by G7Data's `IsModelOver`. -/
theorem modelG3G6_of (hFS : G0Split.FibreSimple) (hNC : ModelNoncomm) (hG3 : ModelG3) :
    ModelG3G6 := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hD
  letI : NumberField L' := numberField_of_fd L'
  obtain ⟨h1, h2, hu, y, hy, hπ⟩ := hctx
  have hdiv := hFS Y Φ π h1 h2 u hu ⟨L'⟩
    ((LeafAdopt.abVarEquiv L').symm (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')))
    ⟨algebraMap L' Qbar, y, P, hy, hπ, hD.2.2.2.2.2.2.2.2.2.2.2.1⟩
  rw [Equiv.apply_symm_apply] at hdiv
  obtain ⟨g5, g3⟩ := hG3 Y Φ π u P ⟨h1, h2, hu, y, hy, hπ⟩ L A ε N χ β L' hLL' hD
  exact ⟨⟨hdiv, hNC Y Φ π u P ⟨h1, h2, hu, y, hy, hπ⟩ L A ε N χ β L' hLL' hD⟩, g5, g3⟩

end HSyn.G0AssembleMod

end

end G0A2_z85_modelg3g6

section G0A2_z86_noncomm
-- (leaf-fold2: copied from scratch/g0-assemble2/parts/z86_noncomm.lean; 0 HDec name-resolution edits)
/-! ## g0-assemble2: `ModelNoncomm` proved from `MulIsogeny`

On G7's model `A_{L'} = (PK.A)_{L'}` (`IsQMModel`), let `ψ : 𝒪 → End(A_{L'})` be `ι` followed by
unram-tate's base-change ring maps `endBC`. If `ψ(i)` and `ψ(j)` commuted, then `ij = -ji` would give
`2·ψ(j)ψ(i) = 0`, hence `12 = 2·ψ(j)²·ψ(i)² = 0` in `End(A_{L'})` (`i² = 2`, `j² = -3`). But
`[12]` is an isogeny (`MulIsogeny`), so `0 = [12]` would be surjective; it factors through
`Spec L'` (a point), so `A_{L'}` would be a point, while `dim A_{L'} = 2` (`model_dim`). -/

noncomputable section

namespace HSyn.G0AssembleMod

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open G0ModField
open _root_.G0ModField (numberField_of_fd) -- op-dedupe

/-- An abelian variety of dimension `2` is not a point: the zero endomorphism (`1` in the
convolution monoid, `toUnit ≫ η`) is not surjective. -/
theorem not_surjective_zero_hom {K : Type} [Field K] (A : PkgI3.AbVar K) (hA : A.dim = 2) :
    ¬ Surjective ((0 : PkgI3.AbVar.End A).hom).left := by
  intro hs
  have hsub : Subsingleton A.X.left := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨a', rfl⟩ := hs.surj a
    obtain ⟨b', rfl⟩ := hs.surj b
    have h0 : ((0 : PkgI3.AbVar.End A).hom) = toUnit A.X ≫ η[A.X] := rfl
    rw [h0, Over.comp_left, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    congr 1
    haveI : Subsingleton (PrimeSpectrum K) := inferInstance
    exact Subsingleton.elim (α := PrimeSpectrum K) _ _
  have hle := topologicalKrullDim_zero_of_discreteTopology A.X.left
  have h2 : topologicalKrullDim A.X.left = 2 := hA
  rw [h2] at hle
  exact absurd hle (by decide)

/-- **`ModelNoncomm` is proved** from g0-fibresimple's `MulIsogeny` (here from mul-rigidity's leaf
`MulEtale`) and g0-dim's proved `DimBaseChange`. -/
theorem modelNoncomm_of_mulIsogeny (hMul : G0FibreSimple.MulIsogeny) : ModelNoncomm := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hD
  letI : NumberField L' := numberField_of_fd L'
  haveI : CharZero L' := charZero_of_injective_algebraMap (algebraMap ℚ L').injective
  have hdim : (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2 :=
    G0Split.model_dim G0Split.dimBaseChange (algebraMap L' Qbar)
      ((LeafAdopt.abVarEquiv L').symm (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')))
      P.A hD.2.2.2.2.2.2.2.2.2.2.2.1 P.surface
  obtain ⟨K, hKL, PK, -, rfl⟩ := hD.1
  set ψ : LeafQM.O →+* PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _
      (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) L' _ (incAlg hLL')) :=
    (@UnramTate.endBC L _ _ L' _ (incAlg hLL')).comp
      ((@UnramTate.endBC K _ PK.A L _ (incAlg hKL)).comp PK.q.iota) with hψ
  refine ⟨ψ UnramTate.iO, ψ UnramTate.jO, fun h => ?_⟩
  set x := ψ UnramTate.jO
  set y := ψ UnramTate.iO
  have hy2 : y * y = 2 := by
    rw [← map_mul, UnramTate.iO_sq, map_add, map_one]; norm_num
  have hx2 : x * x = -3 := by
    rw [← map_mul, UnramTate.jO_sq, map_neg, map_add, map_add, map_one]; norm_num
  have hanti : y * x = -(x * y) := by
    rw [← map_mul, ← map_mul, UnramTate.iO_jO, map_neg]
  have hxy : x * y = -(x * y) := h.symm.trans hanti
  have h2 : (2 : PkgI3.AbVar.End _) * (x * y) = 0 := by
    rw [two_mul]; nth_rewrite 2 [hxy]; exact add_neg_cancel _
  have h3 : x * ((2 : PkgI3.AbVar.End _) * (x * y)) * y = 0 := by rw [h2, mul_zero, zero_mul]
  have h4 : x * ((2 : PkgI3.AbVar.End _) * (x * y)) * y = 2 * (x * x) * (y * y) := by
    noncomm_ring
  rw [h4, hx2, hy2] at h3
  have h12 : ((12 : ℤ) : PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _
        (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) L' _ (incAlg hLL'))) = 0 := by
    have : (2 : PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _
        (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) L' _ (incAlg hLL'))) * -3 * 2 =
        -((12 : ℤ) : PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _
        (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) L' _ (incAlg hLL'))) := by
      push_cast; norm_num
    rw [this, neg_eq_zero] at h3
    exact h3
  have hiso := hMul L' (@PkgI3.AbVar.baseChange L _
    (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) L' _ (incAlg hLL')) 12 (by norm_num)
  rw [h12] at hiso
  exact not_surjective_zero_hom _ hdim hiso.2

end HSyn.G0AssembleMod

end

end G0A2_z86_noncomm

section G0A2_z90_bundle3
-- (leaf-fold2: copied from scratch/g0-assemble2/parts/z90_bundle3.lean; 0 HDec name-resolution edits)
/-! ## g0-assemble2: `GluePieces` from `GluePieces3`

Task g0-assemble2, 2026-11-13. g0-assemble's `GluePieces2` (27 fields) with every wave-27 result
applied (parts a10-a80 above). Each field of `GluePieces3` is a named `def … : Prop` of a wave-26
or wave-27 task, copied verbatim in that task's part; kinds and sources are in
`docs/research/g0-assemble2.md` §2 (LEAF = published theorem, LEAF? = leaf candidate, GLUE = to be
proved by the project). -/

noncomputable section

namespace HSyn

open G0Split

/-- **The named Props left after waves 26-27** (g0-assemble2). -/
structure GluePieces3 : Prop where
  -- FibreSimple (FS1-FS5)
  /-- mul-rigidity, LEAF (Mumford §4 Appl. 2, §6; Milne Thm 8.2, char 0; UNVERIFIED locators):
  `[n]` is étale for `n ≠ 0`. -/
  mulEtale : MulRigidity.MulEtale
  /-- fs5-nocm N1b′, LEAF (Shimura's description of CM points; UNVERIFIED locator). -/
  cmOptimalEmbedding : FS5NoCM.CMOptimalEmbedding
  /-- fs5-nocm N2, GLUE (Kummer fibre of `X₆`). -/
  x6KummerFibre : FS5NoCM.X6KummerFibre
  /-- curve-facts C1b, GLUE (dimension theory of smooth curves). -/
  smoothStalkDimOne : LeafQM.AV.Pin.SmoothStalkDimOne
  /-- curve-facts C2K, LEAF (Hartshorne II.6.8, UNVERIFIED numbering). -/
  constOrOntoAlgClosed : LeafQM.AV.Pin.ConstOrOntoAlgClosed
  /-- curve-facts C3K, GLUE (textbook consequence). -/
  ratFactorAlgClosed : LeafQM.AV.Pin.RatFactorAlgClosed
  -- ProductModelHeight (P2)
  /-- product-height S-an, GLUE (elementary analysis). -/
  productUnifSplits : ZInQ.ProductHeight.ProductUnifSplits
  /-- product-height S-alg, GLUE (Hodge theory of a product). -/
  productMetrizationOfProductUnif : ZInQ.ProductHeight.ProductMetrizationOfProductUnif
  -- StableHeightBaseChange (H4a)
  /-- height-bc, GLUE. -/
  hodgeBCInjective : ZInQ.HeightBC.HodgeBCInjective
  /-- height-bc, GLUE. -/
  cotangentSpanBC : ZInQ.HeightBC.CotangentSpanBC
  /-- height-bc, GLUE. -/
  omegaBaseChange : ZInQ.HeightBC.OmegaBaseChange
  /-- height-bc, GLUE. -/
  uniformizationLiftAnalytic : ZInQ.HeightBC.UniformizationLiftAnalytic
  -- ThetaPointOfFibre
  /-- g0-thetapoint, LEAF? (Shimura 1976 / Mumford Tata II; UNVERIFIED). -/
  thetaRatiosAlgebraic : G0Split.ThetaPt.ThetaRatiosAlgebraic
  /-- fibre-qm-period, LEAF? (pkg-I1's composite leaf). -/
  qmHauptmodul : PkgI1.QMHauptmodul
  /-- fibre-qm-period, LEAF (Eichler class number one, lattice form). -/
  qmClassNumberOne : G0Split.FibreQM.QMClassNumberOne
  /-- fibre-qm-period, LEAF (R1(b) in family form), for the triple of the leaf bundle. -/
  r1bFamily : ∀ h : LeafAdopt.R1R2fpRep,
    G0Split.FibreQM.R1bFamily (G0Split.FibreQM.ownY (LeafAdopt.R1R2fp_of_rep h))
      (G0Split.FibreQM.ownΦ (LeafAdopt.R1R2fp_of_rep h))
      (G0Split.FibreQM.ownπ (LeafAdopt.R1R2fp_of_rep h))
  /-- fibre-qm-period, GLUE, for the triple of the leaf bundle. -/
  periodMapGlue : ∀ h : LeafAdopt.R1R2fpRep,
    G0Split.FibreQM.PeriodMapGlue (G0Split.FibreQM.ownY (LeafAdopt.R1R2fp_of_rep h))
      (G0Split.FibreQM.ownΦ (LeafAdopt.R1R2fp_of_rep h))
      (G0Split.FibreQM.ownπ (LeafAdopt.R1R2fp_of_rep h))
  /-- fibre-qm-period, GLUE. -/
  hauptmodulUnique : G0Split.FibreQM.HauptmodulUnique
  /-- fibre-qm-period, LEAF? (Lin–Yang's divisor of `ψ₄`). -/
  qmDenZeroCM3 : G0Split.FibreQM.QMDenZeroCM3
  /-- fibre-qm-period, GLUE. -/
  cPtsTransport : G0Split.FibreQM.CPtsTransport
  -- ModularConstituent: G2 (fibre-cover), G4 (kernel-field)
  /-- fibre-cover, GLUE (Prop. TS for every admissible cover). -/
  propTSAll : G0ModField.PropTSAll
  /-- fibre-cover, GLUE (Neukirch; compositum of conjugates). -/
  unramifiedConjugates : G0ModField.UnramifiedConjugates
  /-- kernel-field 4a′, GLUE (pure algebra: `𝒪` is maximal). -/
  oMaximal : G0ModField.KernelField.OMaximal
  /-- kernel-field 4b, GLUE. -/
  endTransport : G0ModField.KernelField.EndTransport
  /-- kernel-field, GLUE (the conjugacy maps, geometric part). -/
  conjIsogMaps : G0ModField.KernelField.ConjIsogMaps
  -- ModularConstituent: G8-G12 (g0-mod-galois, g10-odd, conj-twist, g12-det)
  /-- g0-mod-galois, LEAF (Burnside). -/
  burnsideAbsIrred : G0Galois.BurnsideAbsIrred
  /-- g0-mod-galois, LEAF (R14 with its determinant clause). -/
  r14Det : G0Galois.R14Det
  /-- g9-derham F2, GLUE: base change of an abelian variety along a field embedding in
  characteristic 0, with `V_ℓ` Galois-compatible (Mumford §4, §6; EGA IV 4.1.4). -/
  g9AbVarBaseChange : ZInQ.Contrib.G9.G9Bridge.AbVarBaseChange
  /-- g9-derham F1, LEAF (the vanishing half of the Hodge–Tate decomposition of `V_p(A)`, Tate 1967,
  Faltings 1988; g9-derham recommends adding it to R10): HT multiplicities vanish off `{0, -1}`. -/
  g9R10Weights : ZInQ.Contrib.G9.G9Bridge.R10Weights
  /-- conj-twist N1-surj, GLUE. -/
  artinTorsionSurj : G0Galois.ArtinTorsionSurj
  /-- conj-twist N2, LEAF (Birkenhake–Lange Prop. 1.2.1, UNVERIFIED). -/
  homLinearLift : G0Galois.HomLinearLift
  /-- conj-twist N3a, GLUE. -/
  conjUniformization : G0Galois.ConjUniformization
  /-- g12-det, LEAF (Sen 1980). -/
  senTwist : G0Galois.SenTwist
  /-- g12-det, LEAF (Tate 1967, Ax–Sen–Tate). -/
  finiteImageHT : G0Galois.FiniteImageHT
  /-- weil-pairing (used by g12-det), LEAF (T9 restated; Mumford §§6, 8, 20, 23). -/
  t09SymmIsogenyExists : WeilPairing.T09_SymmIsogenyExists
  /-- weil-pairing, LEAF (Mumford §7-8). -/
  isogenyQuasiInverse : WeilPairing.IsogenyQuasiInverse
  /-- weil-pairing, LEAF (Mumford §4 Appl. 2). -/
  divisiblePoints : WeilPairing.DivisiblePoints
  -- ModularConstituent: G13-G16
  /-- R17 concretely, LEAF (Carayol 1986, Thm (A)). -/
  carayolR17 : LadicCond.CarayolR17'
  -- ModularConstituent: joint glue on G7's data (g0-assemble)
  /-- g0-assemble2, GLUE: G3 on G7's model (the remaining half of g0-assemble's `ModelG3G6`; its
  G6 half is proved from `FibreSimple` and `MulIsogeny`, parts z85, z86). -/
  modelG3 : G0AssembleMod.ModelG3
  /-- g0-assemble2 (from g14-trace, g15-ram), GLUE: linked Tate data with the Frobenius link and
  the local data (replaces g0-assemble's `LinkedTateData`). -/
  linkedTateLocal : G0AssembleMod.LinkedTateLocal

/-- fs5-nocm's `R1R2fpFull` is the leaf bundle's `R1R2fp` after pin-apply (same clauses). -/
theorem r1r2fpFull_of (r : ResearchLeaves3) : FS5NoCM.R1R2fpFull := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, h⟩ := LeafAdopt.R1R2fp_of_rep r.r1r2
  exact ⟨Y, Φ, X, Ψ, fY, π₆, h⟩

/-- fs5-nocm's `FibreComTrivialFull` is g0-fibresimple's `FibreComTrivial` over Leaves.lean after
pin-apply (`R1fpPropsFull` and `R1fpProps` have the same text). -/
theorem fibreComTrivial_of_full (h : FS5NoCM.FibreComTrivialFull) :
    G0FibreSimple.FibreComTrivial :=
  fun Y Φ π h1 => h Y Φ π h1

/-- `MobiusGlue` from the curve facts (curve-facts, mobius-glue) and T5. -/
theorem mobiusGlue_of_gp3 (t : TextbookLeaves) (gp : GluePieces3) : LeafQM.AV.Pin.MobiusGlue :=
  LeafQM.AV.Pin.mobiusGlue_of_curves'
    (LeafQM.AV.Pin.curveFacts_of_leaves gp.smoothStalkDimOne gp.constOrOntoAlgClosed
      gp.ratFactorAlgClosed).1
    (LeafQM.AV.Pin.curveFacts_of_leaves gp.smoothStalkDimOne gp.constOrOntoAlgClosed
      gp.ratFactorAlgClosed).2
    t.t5

/-- FS5 (NoCM on the fibre) from `GluePieces3` (fs5-nocm). -/
theorem fibreComTrivial_of_gp3 (r : ResearchLeaves3) (t : TextbookLeaves) (gp : GluePieces3) :
    G0FibreSimple.FibreComTrivial :=
  fibreComTrivial_of_full (FS5NoCM.fibreComTrivialFull_of_leaves'' (r1r2fpFull_of r)
    (mobiusGlue_of_gp3 t gp) t.t27 t.t6 gp.cmOptimalEmbedding gp.x6KummerFibre r.r5count)

/-- `FibreSimple` from `GluePieces3` (fs1-descend, mul-rigidity, fs5-nocm). -/
theorem fibreSimple_of_gp3 (r : ResearchLeaves3) (t : TextbookLeaves) (gp : GluePieces3) :
    G0Split.FibreSimple :=
  G0FibreSimple.fibreSimple_of_leaves t
    (MulRigidity.mulIsogeny_of_mulEtale gp.mulEtale) G0FibreSimple.rigidityHom
    ⟨G0FibreSimple.finiteDescends_proof, fibreComTrivial_of_gp3 r t gp⟩

/-- **`GluePieces` from `GluePieces3` and the leaf bundles** (g0-assemble2). -/
theorem gluePieces_of_gluePieces3 (r : ResearchLeaves3) (t : TextbookLeaves) (gp : GluePieces3) :
    GluePieces where
  dimFinite := G0Split.dimFinite
  dimBaseChange := G0Split.dimBaseChange
  fibreSimple := fibreSimple_of_gp3 r t gp
  productModelHeight := ZInQ.ProductHeight.productModelHeight_of_splits gp.productUnifSplits
    gp.productMetrizationOfProductUnif
  stableHeightBaseChange := G0StableBC.stableHeightBaseChange_of_hodgeLine
    (ZInQ.HeightBC.g0_hodgeLine_iff.mpr (ZInQ.HeightBC.hodgeLineBaseChange_of_glue4
      gp.hodgeBCInjective gp.cotangentSpanBC gp.omegaBaseChange gp.uniformizationLiftAnalytic))
  productExists := G0Product.productExists
  reverseIsogeny := G0RevIsog.reverseIsogeny_of_leaves3 r G0Split.dimFinite
  thetaPoint := G0Split.ThetaPt.thetaPointOfFibre_of_qm_ratios
    (G0Split.FibreQM.fibreQMPeriod_main_rep r.r1r2 (mobiusGlue_of_gp3 t gp) gp.qmHauptmodul
      t.t35 t.t11a gp.qmClassNumberOne (gp.r1bFamily r.r1r2) (gp.periodMapGlue r.r1r2)
      gp.hauptmodulUnique gp.qmDenZeroCM3 gp.cPtsTransport)
    gp.thetaRatiosAlgebraic
  modularConstituent := modularConstituent_of_field t
    (G0ModField.fibreCoverExists_of_propTSAll' t.t5 gp.propTSAll gp.unramifiedConjugates)
    (G0ModField.KernelField.kernelFieldExists_of_split'' t.t6 r.r7a r.r6 t.t5 t.t27
      (fibreComTrivial_of_gp3 r t gp) gp.oMaximal gp.endTransport gp.conjIsogMaps)
    UnramTate.unramifiedSup_mf
    (G0AssembleMod.afterG7_of3 r t
      ⟨gp.burnsideAbsIrred, gp.r14Det,
        ZInQ.Contrib.G9.g9Glue_of_abVarBaseChange gp.g9AbVarBaseChange gp.g9R10Weights,
        G0Galois.g10Glue_of_conjTwist (G0Galois.conjTwistNontrivial_main t.t26 t.t35
          gp.artinTorsionSurj gp.homLinearLift gp.conjUniformization),
        G0Galois.g12Weight_of_senTwist gp.senTwist gp.finiteImageHT,
        G0Galois.detTate_of_leaves gp.t09SymmIsogenyExists gp.isogenyQuasiInverse
          gp.divisiblePoints t.t26,
        G0AssembleMod.resQFiniteIndex⟩
      (G0ModNewform.dirichletOfFinite_of_t17 t.t17) gp.carayolR17
      Swan.swanIndependent_proved Swan.swanIntegral_proved
      Swan.adaptedExists_proved
      (G0AssembleMod.modelG3G6_of (fibreSimple_of_gp3 r t gp)
        (G0AssembleMod.modelNoncomm_of_mulIsogeny
          (MulRigidity.mulIsogeny_of_mulEtale gp.mulEtale)) gp.modelG3)
      (G0AssembleMod.linkedTateData_of_local t.t7 gp.linkedTateLocal))
  heightCopies := G0HeightCopies.heightCopiesAgree

/-- **G0 after waves 26-27** (g0-assemble2): the leaf bundles (`ResearchLeaves3`: no `opaque`
placeholder) and `GluePieces3` imply `ZInQ.SixContactMin`. -/
theorem sixContactMin_of_leaves3 (r : ResearchLeaves3) (t : TextbookLeaves) (gp : GluePieces3) :
    ZInQ.SixContactMin :=
  sixContactMin_of_leavesR3 r t (gluePieces_of_gluePieces3 r t gp)

/-- The same with Leaves.lean's `ResearchLeaves` (which implies `ResearchLeaves3`). -/
theorem sixContactMin_of_leaves3' (r : ResearchLeaves) (t : TextbookLeaves) (gp : GluePieces3) :
    ZInQ.SixContactMin :=
  sixContactMin_of_leaves3 (researchLeaves3_of r) t gp

end HSyn

end

#print axioms HSyn.gluePieces_of_gluePieces3
#print axioms HSyn.sixContactMin_of_leaves3
#print axioms HSyn.sixContactMin_of_leaves3'
#print axioms HSyn.researchLeaves3_of

end G0A2_z90_bundle3

end HDec
