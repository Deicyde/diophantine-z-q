import Mathlib
import ZInQKernel.Hypotheses.JHeight
import ZInQKernel.Compiler.Precision.HeightConstant
import ZInQKernel.Contrib.BrauerT14T15.Main
import ZInQKernel.Contrib.LocalKW.T30
import ZInQKernel.Contrib.KroneckerWeber.Leaves
import ZInQKernel.Contrib.Chebotarev.FrobeniusDense
import ZInQKernel.Contrib.Different.Global
import ZInQKernel.Contrib.T25.NewformOfEigenform
import ZInQKernel.Contrib.T31.Main
import ZInQKernel.HDecomp.Textbook.BrauerNesbitt
import ZInQKernel.Multiplication.Certificate.ConstantsProperties
import ZInQKernel.Progressions.Final.Instance
import ZInQKernel.Size.Constants.T
import ZInQKernel.HDecomp.Textbook.Igusa.Forward
import ZInQKernel.HDecomp.A6.A6
import ZInQKernel.HDecomp.Objects
import ZInQKernel.Contrib.HeightBC.G0StableBC
import ZInQKernel.HDecomp.I3Linalg.C2
import ZInQKernel.HDecomp.C10.Trace
import ZInQKernel.HDecomp.Conductor.LadicCond
import ZInQKernel.HDecomp.ModCurves.C9
import ZInQKernel.HDecomp.Conductor.I6Base
import ZInQKernel.HDecomp.Conductor.ArtinUpper
import ZInQKernel.HDecomp.Conductor.Breaks
import ZInQKernel.HDecomp.Conductor.D1Local
import ZInQKernel.HDecomp.Conductor.Dyadic
import ZInQKernel.HDecomp.Conductor.Level
import ZInQKernel.HDecomp.Assembly
import ZInQKernel.HDecomp.Assembly.C8
import ZInQKernel.HDecomp.Assembly.E1Lin
import ZInQKernel.HDecomp.Assembly.E2Index
import ZInQKernel.HDecomp.Assembly.F3Glue
import ZInQKernel.HDecomp.Descent.ProjRep
import ZInQKernel.HDecomp.Descent.B1Quat
import ZInQKernel.HDecomp.Descent.Cochain
import ZInQKernel.HDecomp.Descent.Constants
import ZInQKernel.HDecomp.Descent.Chi
import ZInQKernel.HDecomp.Descent.B2Glue
import ZInQKernel.HDecomp.Descent.B2Assembly
import ZInQKernel.HDecomp.Descent.B3Assembly
import ZInQKernel.HDecomp.Repo.A1Quaternion
import ZInQKernel.HDecomp.Repo.TorsionFree
import ZInQKernel.HDecomp.Repo.PRArith
import ZInQKernel.HDecomp.Repo.Numerics
import ZInQKernel.HDecomp.C10.C10
import ZInQKernel.HDecomp.B3Unram.B3b
import ZInQKernel.HDecomp.B3Unram.T32a
import ZInQKernel.HDecomp.QM.Structures
import ZInQKernel.HDecomp.QM.Pairs
import ZInQKernel.HDecomp.QM.Leaves
import ZInQKernel.HDecomp.QM.Pin
import ZInQKernel.HDecomp.ModCurves.Genus
import ZInQKernel.HDecomp.ModCurves.Defs
import ZInQKernel.HDecomp.ModCurves.Leaves
import ZInQKernel.HDecomp.ModCurves.Glue
import ZInQKernel.HDecomp.Faltings.HodgeData
import ZInQKernel.HDecomp.Faltings.IdealLines
import ZInQKernel.HDecomp.Faltings.Models
import ZInQKernel.HDecomp.Faltings.Height
import ZInQKernel.HDecomp.Faltings.Leaves
import ZInQKernel.HDecomp.LeafPush2.R18
import ZInQKernel.HDecomp.LeafPush2.R22
import ZInQKernel.HDecomp.LeafPush2.R3
import ZInQKernel.HDecomp.LeafPush2.T
import ZInQKernel.HDecomp.Textbook.Different
import ZInQKernel.HDecomp.Textbook.SkolemNoether
import ZInQKernel.HDecomp.Textbook.FrobeniusDense
import ZInQKernel.HDecomp.Textbook.KroneckerWeberUse
import ZInQKernel.HDecomp.Conductor.SqrtChar
import ZInQKernel.HDecomp.Sqrt.SqrtLocal
import ZInQKernel.HDecomp.Sqrt.Disj
import ZInQKernel.HDecomp.Textbook.T30SqrtCrit
import ZInQKernel.HDecomp.Textbook.T10Etale
import ZInQKernel.HDecomp.Faltings.H5Neron
import ZInQKernel.HDecomp.ModCurves.X1Belyi
import ZInQKernel.HDecomp.I3Linalg.TateBC
import ZInQKernel.HDecomp.ModCurves.E1Sub
import ZInQKernel.HDecomp.I3Linalg.RhoCont

-- op-compact: aliases `HDec.T.x := T.x` for the copies deleted by op-dedupe (first used here)
namespace HDec.PkgI1 export _root_.PkgI1 (IgusaClebschSeparation J10 J2 J4 J6 j10Data lyVec sexticAct) end HDec.PkgI1
namespace HDec.GlueA6Alg export _root_.GlueA6Alg (Alg.E Alg.E_inj Alg.E_inv Alg.E_mem Alg.E_mul Alg.E_one Alg.E_pow Alg.E_symm Alg.Q Alg.Q_natCast Alg.R Alg.V Alg.core Alg.dvd_of_dvd_two_mul Alg.endV Alg.endV_E Alg.eq_three_mul_of_cast_eq_zero Alg.eq_three_smul_of_red_eq_zero Alg.exists_valuationSubring_comap_eq Alg.f3_aniso Alg.f3_indep Alg.lift3 Alg.mem_inv Alg.mem_map Alg.mem_mul Alg.mem_pow Alg.nine_dvd_Q Alg.nine_dvd_of_dvd_two_mul Alg.quat_base Alg.quat_sq_dvd Alg.red Alg.red.congr_simp Alg.redMap Alg.redMap.congr_simp Alg.red_add Alg.red_lift3 Alg.red_map Alg.red_neg Alg.red_smul Alg.red_sub Alg.symm_E Alg.three_dvd_Q Alg.three_pow_eq_zero Alg.three_prime Alg.zmod3_aniso Alg.φ Alg.φ_add_smul Alg.φ_smul Alg.φ_smul_left Alg.φ_sub Alg.φ_sub_left Alg.φ_zero) end HDec.GlueA6Alg
namespace HDec.PkgI2 export _root_.PkgI2 (AbhyankarDVR CharpolyIndependentOfEll D2_fixed_of_raynaud GrothendieckMonodromy HasGoodReduction HomRankBound InertiaTrivialOn IsAbelianScheme IsAbelianScheme.casesOn IsAbelianScheme.geomConnected IsAbelianScheme.mk IsAbelianScheme.proper IsAbelianScheme.rec IsAbelianScheme.recOn IsAbelianScheme.smooth IsAbelianVariety IsAbelianVariety.casesOn IsAbelianVariety.geomIntegral IsAbelianVariety.mk IsAbelianVariety.proper IsAbelianVariety.rec IsAbelianVariety.recOn IsAbelianVariety.smooth IsInertia IsReductionOf NeronMappingAbelianScheme NeronOggShafarevich Pts PurityBranchLocus RaynaudCriterion ReductionTorsionBijective SerreTatePotentialGood TorsionStructure UnipSq baseChange fixed_of_unipSq_of_iterate galAct galAct_inv galAct_mul galAct_one galAct_pow galHom inertiaTrivial_of_goodReduction specOver toW torsion) end HDec.PkgI2
namespace HDec.GlueI3 export _root_.GlueI3 (EquivariantDescent SemisimpleBaseChange absolutelyIrreducible_of_finrank_commOf_prod_le_four blockMap blockMap_injective commBaseChange commOf commOf_baseChange_le_range equivariantDescent exists_equivariant_ne_zero_of_baseChange exists_equivariant_ne_zero_of_common finrank_commOf_baseChange_le finrank_commOf_eq_one_of_prod_le_four finrank_commOf_le_of_equiv id_mem_commOf isIrreducible_of_commutant_scalar isIrreducible_of_finrank_commOf_prod_le_four isSemisimple_of_surjective projection_comm repBaseChange scalar_commOf_baseChange scalar_of_finrank_commOf_eq_one semisimpleBaseChange) end HDec.GlueI3
namespace HDec.PkgI3 export _root_.PkgI3 (Tate.T Tate.continuous_map_action Tate.continuous_of_linearMap_padicInt Tate.coord_eq_zero_iff Tate.coord_eq_zero_of_le Tate.ell_smul_succ Tate.isOpen_coord_eq Tate.map Tate.map_apply Tate.map_bijective Tate.map_injective Tate.mem_range_of_ell_smul Tate.mem_range_of_pow_smul Tate.mem_range_of_smul Tate.nhds_zero_hasBasis Tate.nsmul_congr Tate.pow_smul_eq_zero Tate.pow_smul_shift Tate.smulSeq Tate.smulSeq_congr Tate.smulSeq_mem Tate.smul_apply Tate.val_cast AbVar AbVar.End AbVar.End0 AbVar.Hom AbVar.Hom.ext' AbVar.Hom.hom AbVar.Hom.hom_add AbVar.Hom.hom_mk' AbVar.Hom.hom_zero AbVar.Hom.mk' AbVar.Hom.mk'.congr_simp AbVar.IsGalEquivariant AbVar.IsIsogenyMor AbVar.Pt AbVar.T AbVar.V AbVar.X AbVar.baseChange AbVar.casesOn AbVar.ctorIdx AbVar.dim AbVar.galAct AbVar.galHom AbVar.galHom_mul AbVar.galHom_one AbVar.galRep AbVar.galT AbVar.geomInt AbVar.geometricallyIntegral_id_spec AbVar.grp AbVar.homGroup AbVar.homT AbVar.instIsMonHomOverSchemeSpecOfHom AbVar.instRingEnd AbVar.mk AbVar.mk.inj AbVar.mk.injEq AbVar.mk.noConfusion AbVar.mk.sizeOf_spec AbVar.noConfusion AbVar.noConfusionType AbVar.origin AbVar.proper AbVar.ptMap AbVar.ptObj AbVar.rec AbVar.recOn AbVar.smooth AbVar.structMapOn AbVar.tateHom AbVar.tateHomZl AbVar.zero C2_absolutelyIrreducible CharPolyIndepOfEll E1_exists_hom_ne_zero E1_exists_hom_ne_zero' EndDivision FaltingsSemisimple FaltingsTate HomFreeFinite I3Leaves I3Leaves.casesOn I3Leaves.charPolyIndepOfEll I3Leaves.faltingsSemisimple I3Leaves.faltingsTate I3Leaves.homFreeFinite I3Leaves.mk I3Leaves.poincare I3Leaves.qmDichotomy I3Leaves.rec I3Leaves.recOn I3Leaves.tateModuleFree PoincareReducibility QMDichotomyYu QuatIndefinite RhoCont.continuous_act RhoCont.continuous_galRep RhoCont.continuous_galT RhoCont.continuous_one_tmul RhoCont.continuous_orbit RhoCont.continuous_toMatrix_galRep RhoCont.continuous_trace_galRep RhoCont.exists_openSubgroup_galAct_eq RhoCont.galAct_mul RhoCont.instTopologicalSpacePt RhoCont.instTopologicalSpaceV RhoCont.stalkClosedPointTo_comp_galois TateModuleFree continuous_galRep_of_tateModuleFree equivEnd equivEnd_eq_commOf exists_hom_ne_zero_of_equivariant finrank_equivEnd homT_galT qmDichotomy_B6 quatIndefinite_two_neg_three range_tateHomZl_subset trace_eq_trace_of_ell trace_indep_of_ell) end HDec.PkgI3
namespace HDec.PkgI4 export _root_.PkgI4 (CF EigenformRepExists EigenformTwist GQ GQp GaloisChar GaloisChar.casesOn GaloisChar.continuous_toHom GaloisChar.ctorIdx GaloisChar.mk GaloisChar.mk.inj GaloisChar.mk.injEq GaloisChar.mk.noConfusion GaloisChar.mk.sizeOf_spec GaloisChar.noConfusion GaloisChar.noConfusionType GaloisChar.rec GaloisChar.recOn GaloisChar.toHom GaloisRep GaloisRep.AttachedTo GaloisRep.AttachedUpToTwist GaloisRep.FinitelyRamified GaloisRep.IsIrreducible GaloisRep.IsOdd GaloisRep.IsSemisimple GaloisRep.UnramifiedAt GaloisRep.casesOn GaloisRep.continuous_toHom GaloisRep.ctorIdx GaloisRep.mat GaloisRep.mk GaloisRep.mk.inj GaloisRep.mk.injEq GaloisRep.mk.noConfusion GaloisRep.mk.sizeOf_spec GaloisRep.noConfusion GaloisRep.noConfusionType GaloisRep.rec GaloisRep.recOn GaloisRep.restrictLocal GaloisRep.toHom HasNebentypus IsArithFrob IsComplexConj IsNewform IsNormalizedEigenform LiesOver NewformOfEigenform Qbar coeff decomp oldSpace scaleH) end HDec.PkgI4
namespace HDec.PkgI6 export _root_.PkgI6 (BrauerHasse2 BrauerHasse2C BrauerNesbittChar0 BrauerReciprocity2 BrauerReciprocity2C ChebotarevExists DifferentBound H2TwoClasses HerbrandQuotient HerbrandTransitivity HilbertDifferentFormula IsCoboundary2 IsCoboundary2.sub IsCocycle2 IsCocycle2.resC IsCocycle2.sub LocalH2Card LocalH2CardC LocalKroneckerWeber LocalReciprocityUpper MonogenicDVR SkolemNoether TraceContainsRamificationIdx Z2 artinConductor artinConductor.congr_simp artinConductor_le_of_upper cob_of_same_finite_support codimInv codimInv_eq_zero codimInv_le differentBound differentBound_of_trace eq_of_ne_zero_of_card_two eq_of_same_finite_support g0_pos hInt hInt.congr_simp hInt_anti hInt_ge hInt_zero herbrandPhi herbrandPhi.congr_simp herbrandPhi_eq herbrandQuotient herbrandTransitivity hilbertDifferentFormula hilbertDifferentFormula_of_dvr hilbertDifferentFormula_of_monogenicDVR loc locInf locP lowerRam lowerRam.congr_simp lowerRamR lowerRamR.congr_simp lowerRamR_anti lowerRamR_nat lowerRam_anti lowerRam_tower mem_lowerRam monogenicDVR phi_nat_ge phi_strictMono phi_sub_ge phi_zero resC skolemNoether_aut sum_hInt_le traceContainsRamificationIdx unitFiltration upperRam upperRam_phi_nat) end HDec.PkgI6
namespace HDec.GlueConductor export _root_.GlueConductor (D1_genuine HilbertDifferentFormula SerreDifferentBound artin_le card_GL4_F3 card_GL4_F5 char_trivial_of_odd_pgroup contactSupport_pos' delta exists_fourth_root exists_sq_eq_one_add factorial_le_two_pow_sq fourth_pow_mem herbrand_integral level_le max_le_U0 one_add_log_factorial_le padicValNat_le_log_two padicValNat_le_sq phi phi_le_self phi_le_two_delta phi_mono phi_succ phi_zero pow_card_eq_one_of_pgroup prod_small_le ramCard ramGroup spanNatPrime_isPrime swan_eq_zero_of_tame swan_le two_add_two_U0_le_E0 two_delta_le upper_break_le wild_trivial_of_tame) end HDec.GlueConductor
namespace HDec.GlueD1Local export _root_.GlueD1Local (D1_krasner D1_krasner' D1_local D1_local' card_decompGroup card_le_factorial_index_of_normalCore_eq_bot decompGroup fixingSubgroup_mul_decompGroup index_localSub index_normalCore_le_factorial_index localSub localSubEquiv normalCore_fixingSubgroup_eq_bot normalCore_subgroupOf_eq_bot ramificationIdx_le_card_decompGroup ramificationIdx_le_factorial_local ramificationIdx_le_factorial_of_unique) end HDec.GlueD1Local
namespace HDec.GlueAssembly export _root_.GlueAssembly (CMOutput NF NF.K NF.casesOn NF.ctorIdx NF.fld NF.mk NF.mk.inj NF.mk.injEq NF.mk.noConfusion NF.mk.sizeOf_spec NF.nf NF.noConfusion NF.noConfusionType NF.rec NF.recOn NonCMOutput PhiK PhiK_eval PhiNat PhiNat_eval_one PhiNat_homogeneous SixContactMinAt baseChange_invariant_eq_zero cast_ccm cm_branch_nat cm_numerics coeff_sum_le coord_lTensor finitePlace_max_eq_one finite_range_of_finiteIndex finite_range_of_sq firstColMod firstColMod_eq_iff firstCol_algebra heightQ_heightD_ge iSup_fin_two index_Gamma1_le invariants_ne_bot_of_baseChange logHeight_Phi_le logHeight_le_log_mulHeightL2 logHeight_sixteen_eq logHeight₁_Phi_le logHeight₁_algebraMap_rat log_3779136_le log_sixteen_le log_two_mul_bcm_le max_one_hA_le max_one_hA_le_cm max_one_hA_le_noncm mulHeightBound_PhiK_le mulHeightL2 mulHeight_intPair mulHeight_le_mulHeightL2 mulHeight_rootsOfUnity_mul one_le_heightD_real ratHeight_le_of_theta sixContactMinAt_of_jHeightBound sum_coeff_eq_eval_one transfer_numerics transfer_of_level twist_finite weight_match weight_match_coh) end HDec.GlueAssembly
namespace HDec.ZInQ export _root_.ZInQ (DefFaltings.AbVar DefFaltings.AnalyticUniformizationExists DefFaltings.AnalyticUniformizationUnique DefFaltings.EReal.add_coe_add_neg_coe DefFaltings.FinExt DefFaltings.FinExt.L DefFaltings.FinExt.algebra DefFaltings.FinExt.casesOn DefFaltings.FinExt.ctorIdx DefFaltings.FinExt.field DefFaltings.FinExt.mk DefFaltings.FinExt.mk.inj DefFaltings.FinExt.mk.injEq DefFaltings.FinExt.mk.noConfusion DefFaltings.FinExt.mk.sizeOf_spec DefFaltings.FinExt.noConfusion DefFaltings.FinExt.noConfusionType DefFaltings.FinExt.numberField DefFaltings.FinExt.rec DefFaltings.FinExt.recOn DefFaltings.Genus2Eq DefFaltings.Genus2Eq.Good DefFaltings.Genus2Eq.P DefFaltings.Genus2Eq.binDisc DefFaltings.Genus2Eq.casesOn DefFaltings.Genus2Eq.ctorIdx DefFaltings.Genus2Eq.deg_f DefFaltings.Genus2Eq.deg_h DefFaltings.Genus2Eq.f DefFaltings.Genus2Eq.h DefFaltings.Genus2Eq.mk DefFaltings.Genus2Eq.mk.inj DefFaltings.Genus2Eq.mk.injEq DefFaltings.Genus2Eq.mk.noConfusion DefFaltings.Genus2Eq.mk.sizeOf_spec DefFaltings.Genus2Eq.noConfusion DefFaltings.Genus2Eq.noConfusionType DefFaltings.Genus2Eq.rec DefFaltings.Genus2Eq.recOn DefFaltings.GroupModel DefFaltings.GroupModel.G DefFaltings.GroupModel.IsAnalyticUniformization DefFaltings.GroupModel.IsNeronModel DefFaltings.GroupModel.Pts DefFaltings.GroupModel.casesOn DefFaltings.GroupModel.cotangent DefFaltings.GroupModel.ctorIdx DefFaltings.GroupModel.dCls DefFaltings.GroupModel.detLattice DefFaltings.GroupModel.dom DefFaltings.GroupModel.evalAt DefFaltings.GroupModel.exists_rep DefFaltings.GroupModel.gen DefFaltings.GroupModel.genStalk DefFaltings.GroupModel.gen_hom DefFaltings.GroupModel.genericUnit DefFaltings.GroupModel.germAlong DefFaltings.GroupModel.grp DefFaltings.GroupModel.height DefFaltings.GroupModel.height_eq DefFaltings.GroupModel.hodgeSpace DefFaltings.GroupModel.instAddCommGroupCotangent DefFaltings.GroupModel.instModuleCarrierGenStalkCotangent DefFaltings.GroupModel.instModuleRingOfIntegersCotangent DefFaltings.GroupModel.jacDet DefFaltings.GroupModel.jacDet_comp DefFaltings.GroupModel.mk DefFaltings.GroupModel.mk.inj DefFaltings.GroupModel.mk.injEq DefFaltings.GroupModel.mk.noConfusion DefFaltings.GroupModel.mk.sizeOf_spec DefFaltings.GroupModel.noConfusion DefFaltings.GroupModel.noConfusionType DefFaltings.GroupModel.omega DefFaltings.GroupModel.omegaAt DefFaltings.GroupModel.omegaAt_genericPt DefFaltings.GroupModel.ptC DefFaltings.GroupModel.qc DefFaltings.GroupModel.rec DefFaltings.GroupModel.recOn DefFaltings.GroupModel.semilinear_ext_wedge DefFaltings.GroupModel.separated DefFaltings.GroupModel.smooth DefFaltings.GroupModel.specializes_genericUnit DefFaltings.GroupModel.structMap DefFaltings.GroupModel.unitSection DefFaltings.GroupModel.wedge DefFaltings.HermitianLattice DefFaltings.HermitianLattice.arakelovDegree DefFaltings.HermitianLattice.arakelovDegree_ofFractionalIdeal DefFaltings.HermitianLattice.arakelovDegree_rescale DefFaltings.HermitianLattice.casesOn DefFaltings.HermitianLattice.ctorIdx DefFaltings.HermitianLattice.degreeAt DefFaltings.HermitianLattice.degreeAt_eq DefFaltings.HermitianLattice.degreeAt_eq_arakelovDegree DefFaltings.HermitianLattice.degreeAt_smul DefFaltings.HermitianLattice.finrank_eq_one DefFaltings.HermitianLattice.isLattice DefFaltings.HermitianLattice.lattice DefFaltings.HermitianLattice.mk DefFaltings.HermitianLattice.mk.congr_simp DefFaltings.HermitianLattice.mk.inj DefFaltings.HermitianLattice.mk.injEq DefFaltings.HermitianLattice.mk.noConfusion DefFaltings.HermitianLattice.mk.sizeOf_spec DefFaltings.HermitianLattice.noConfusion DefFaltings.HermitianLattice.noConfusionType DefFaltings.HermitianLattice.norm DefFaltings.HermitianLattice.norm_pos DefFaltings.HermitianLattice.norm_smul DefFaltings.HermitianLattice.ofFractionalIdeal DefFaltings.HermitianLattice.ofFractionalIdeal.congr_simp DefFaltings.HermitianLattice.rec DefFaltings.HermitianLattice.recOn DefFaltings.HermitianLattice.rescale DefFaltings.HermitianLattice.secIndex_ne_zero DefFaltings.HodgeData DefFaltings.HodgeData.casesOn DefFaltings.HodgeData.coeff DefFaltings.HodgeData.coeff_apply_ne_zero DefFaltings.HodgeData.coeff_ne_zero DefFaltings.HodgeData.ctorIdx DefFaltings.HodgeData.finrank_eq_one DefFaltings.HodgeData.hodgeBundle DefFaltings.HodgeData.isLattice DefFaltings.HodgeData.lattice DefFaltings.HodgeData.mk DefFaltings.HodgeData.mk.congr_simp DefFaltings.HodgeData.mk.inj DefFaltings.HodgeData.mk.injEq DefFaltings.HodgeData.mk.noConfusion DefFaltings.HodgeData.mk.sizeOf_spec DefFaltings.HodgeData.modelHeight DefFaltings.HodgeData.modelHeight_eq DefFaltings.HodgeData.modelHeight_eq_add_of_le DefFaltings.HodgeData.modelHeight_eq_faltingsHeightGood DefFaltings.HodgeData.modelHeight_le_of_le DefFaltings.HodgeData.modelHeight_ofIdeal DefFaltings.HodgeData.modelHeight_ofIdeal_baseChange DefFaltings.HodgeData.modelHeight_of_span DefFaltings.HodgeData.modelHeight_recoord DefFaltings.HodgeData.noConfusion DefFaltings.HodgeData.noConfusionType DefFaltings.HodgeData.norm DefFaltings.HodgeData.norm_sq DefFaltings.HodgeData.periods DefFaltings.HodgeData.periods_discrete DefFaltings.HodgeData.periods_isZLattice DefFaltings.HodgeData.rec DefFaltings.HodgeData.recOn DefFaltings.HodgeData.recoord DefFaltings.HodgeLatticeTheorem DefFaltings.IsIsogeny DefFaltings.MetrizedModel DefFaltings.MetrizedModel.arch DefFaltings.MetrizedModel.casesOn DefFaltings.MetrizedModel.ctorIdx DefFaltings.MetrizedModel.hodge DefFaltings.MetrizedModel.lattice_eq DefFaltings.MetrizedModel.mk DefFaltings.MetrizedModel.mk.inj DefFaltings.MetrizedModel.mk.injEq DefFaltings.MetrizedModel.mk.noConfusion DefFaltings.MetrizedModel.mk.sizeOf_spec DefFaltings.MetrizedModel.model DefFaltings.MetrizedModel.modelHeight_eq_of_model_eq DefFaltings.MetrizedModel.noConfusion DefFaltings.MetrizedModel.noConfusionType DefFaltings.MetrizedModel.rec DefFaltings.MetrizedModel.recOn DefFaltings.NeronModelMinimal DefFaltings.PeriodAreaFormula DefFaltings.R19_GaudronRemond DefFaltings.R20_FaltingsLemma5 DefFaltings.R21_Bost DefFaltings.StableHeightFinite DefFaltings.absNorm_extendedHom DefFaltings.absNorm_map_ringOfIntegers DefFaltings.arakelovDegree_ofFractionalIdeal_baseChange DefFaltings.arakelovDegree_ofFractionalIdeal_mul DefFaltings.card_embeddings_over DefFaltings.covolume_comap_mul_det DefFaltings.covolume_gaussianPair DefFaltings.det_restrictScalars_complex DefFaltings.embCoeff DefFaltings.faltingsHeight DefFaltings.faltingsHeightEC DefFaltings.faltingsHeightGood DefFaltings.faltingsHeight_coe DefFaltings.finiteHeightPart DefFaltings.finrank_ringOfIntegers DefFaltings.gaussianPair DefFaltings.genericFibre DefFaltings.genericPt DefFaltings.grKappa DefFaltings.hypGram DefFaltings.hypGram_comp_add DefFaltings.hypVol DefFaltings.hypVol_one_comp_add DefFaltings.isogDeg DefFaltings.le_stableFaltingsHeight DefFaltings.modelHeight_ofIdeal_eq_faltingsHeightEC DefFaltings.modelHeight_ofIdeal_eq_faltingsHeightEC' DefFaltings.norm_algebraMap_tower DefFaltings.ptObj DefFaltings.ratCoeff DefFaltings.realify DefFaltings.secIndex DefFaltings.secIndex_mul_absNorm DefFaltings.secIndex_smul DefFaltings.stableFaltingsHeight DefFaltings.stableFaltingsHeightDeligne DefFaltings.stableFaltingsHeightDeligne_eq DefFaltings.stableFaltingsHeight_eq_faltingsHeightGood DefFaltings.stableFaltingsHeight_eq_iInf_height DefFaltings.stableFaltingsHeight_le DefFaltings.stableFaltingsHeight_ne_bot_of_R21 DefFaltings.sum_embeddings_comp DefFaltings.sum_log_norm_embeddings DefFaltings.sum_log_norm_embeddings_int DefFaltings.torusMetricSq DefFaltings.torusMetricSq_comap DefFaltings.torusMetricSq_eq_setIntegral DefFaltings.torusMetricSq_pos DefFaltings.torusMetricSq_smul DefFaltings.torus_setIntegral_indep H5Neron.GroupModel.IsNeronModel.lift H5Neron.GroupModel.IsNeronModel.uniqueIso H5Neron.GroupModel.isNeronModel_iff H5Neron.GroupModelBaseChangeExists H5Neron.IsBaseChangeOf H5Neron.IsOpenSubgroupModel H5Neron.IsProductAbVar H5Neron.IsProductModel H5Neron.ModelHeightBaseChange H5Neron.NeronModelExists H5Neron.NeronProp H5Neron.NeronProp.lift H5Neron.NeronProp.of_iso H5Neron.NeronProp.tensor H5Neron.NeronProp.uniqueIso H5Neron.OpenSubgroupHeight H5Neron.ProductGroupModelExists H5Neron.ProductModelHeight H5Neron.R19_zero H5Neron.R20_zero H5Neron.R21_zero H5Neron.SemistableNeronIdentityComponent H5Neron.bcProd H5Neron.bcUnitIso H5Neron.compositum H5Neron.covolume_fin_zero H5Neron.detLattice_zero H5Neron.glue_zero H5Neron.groupModel_height_zero H5Neron.hodgeZeroEquiv H5Neron.hodgeZeroEquiv_wedge0 H5Neron.hom_ext_of_iso_unit H5Neron.isIsogeny_id_zero H5Neron.isMonHom_of_iso_unit H5Neron.isMonHom_prodComparisonIso H5Neron.isNeronModel_of_isProductModel H5Neron.isogDeg_zero_le_one H5Neron.jL H5Neron.metrizedOf H5Neron.modelHeight_dim_zero H5Neron.neronModelExists_zero H5Neron.neronModelMinimal_zero H5Neron.neron_zero_iso_unit H5Neron.no_metrized_succ H5Neron.one_le_grKappa H5Neron.productGroupModelExists H5Neron.pts_subsingleton H5Neron.semistableNeronIdentityComponent_zero H5Neron.semσ H5Neron.stableFaltingsHeight_add_le H5Neron.stableFaltingsHeight_add_le' H5Neron.stableFaltingsHeight_eq_neron H5Neron.stableFaltingsHeight_eq_neron_all H5Neron.stableFaltingsHeight_zero H5Neron.stableHeightFinite_zero H5Neron.tensorGen H5Neron.tensorGen_fst H5Neron.tensorGen_snd H5Neron.trivHodge H5Neron.trivMetrized H5Neron.trivModel H5Neron.trivModel_isNeronModel H5Neron.wedge0 H5Neron.wedge0_ne_zero H5Neron.wedge_eq_wedge0 LeafPush2.CPts LeafPush2.Char2 LeafPush2.HasSexticModel LeafPush2.IC10 LeafPush2.IC2 LeafPush2.IC4 LeafPush2.IC6 LeafPush2.IgJ10 LeafPush2.IgJ2 LeafPush2.IgJ4 LeafPush2.IgJ6 LeafPush2.IsGenus2 LeafPush2.IsPeriodMatrix LeafPush2.IsSiegel LeafPush2.IsUniformization LeafPush2.LinYangTuple LeafPush2.OnQMLocus LeafPush2.T10_groupIso LeafPush2.T11a_RiemannEnd LeafPush2.T11b_Rigidity LeafPush2.T12_ComplexConjEigen LeafPush2.UniformizationExists LeafPush2.absLogHeight LeafPush2.cDom LeafPush2.cEvalAt LeafPush2.cptObj LeafPush2.dsq LeafPush2.exists_isComplexConj LeafPush2.ffAlgebra LeafPush2.ffStructMap LeafPush2.isSiegel_I LeafPush2.javanpeykarBound LeafPush2.javanpeykarBound_mono LeafPush2.javanpeykarBound_pos LeafPush2.linYangTuple_onQMLocus LeafPush2.linYang_j_eq LeafPush2.onQMLocus_of_linYangTuple LeafPush2.pazukiC2 LeafPush2.sextic LeafPush2.thetaConst) end HDec.ZInQ
namespace HDec.GlueDescent export _root_.GlueDescent (B2.IsSignCocycle B2.SignCob B2.dB B2.dB_inv B2.dB_mul B2.exists_beta B2.isSignCocycle_dB B2.isSignCocycle_inv B2.isSignCocycle_mul B2.isSignCocycle_pull B2.pull B2.pull_dB B2.signCob_dB_iff B2.signCob_inv B2.signCob_mul B2Q.GQ B2Q.GQp B2Q.InflatedFrom B2Q.LeafHasse B2Q.LeafLocalTwo B2Q.LeafSqrtCrit B2Q.LeafUnramified B2Q.UnramifiedAt B2Q.act B2Q.act_mul B2Q.b2_of_leaves B2Q.cast_cast_of_dvd B2Q.chiLevel_pos B2Q.chi_toUnitHom_crt B2Q.cyc B2Q.cyc.congr_simp B2Q.cyc_eq_of_agree B2Q.cyc_isLocallyConstant B2Q.exists_crt_unit B2Q.galChar B2Q.galChar.congr_simp B2Q.galChar_isLocallyConstant B2Q.isLocallyConstant_of_openSubgroup B2Q.lev_eq_pow B2Q.resp B2Q.resp_continuous B2Q.sqrtU B2Q.sqrtU_sq B2Q.toRingAut B3Q.GQL B3Q.b3_degree_le_QM B3Q.b3_of_leaves B3Q.inflatedNormalized_of B3Q.mem_GQL B3Q.orderOf_pos_dirichlet B6 B6_commute_i_j B6_inner B6_isCentral B6_isSimpleRing B6_star_mul InflatedNormalized IsCochainFor LeafSkolemNoether MatrixUnits2 MatrixUnits2.W MatrixUnits2.casesOn MatrixUnits2.ctorIdx MatrixUnits2.e MatrixUnits2.e00_of_mem MatrixUnits2.e_apply_e MatrixUnits2.finrank_W MatrixUnits2.mapsTo_W MatrixUnits2.mem_W_of_e0 MatrixUnits2.mk MatrixUnits2.mk.inj MatrixUnits2.mk.injEq MatrixUnits2.mk.noConfusion MatrixUnits2.mk.sizeOf_spec MatrixUnits2.mul_e MatrixUnits2.noConfusion MatrixUnits2.noConfusionType MatrixUnits2.rec MatrixUnits2.recOn MatrixUnits2.splitEquiv MatrixUnits2.splitEquiv_intertwines MatrixUnits2.sum_diag aniso_int aniso_rat boundary_sq chi chiLevel cochain_conj cochain_mul_kernel cochain_mul_left cochain_mul_right cochain_of_boundary_eq cochain_one cocycle_of_projective commute_adjoin contactSupport_pos degree_le_QM exists_chi exists_odd_char heightD_pos index_kernel_le inertia_le_kernel kernelSubgroup kernelSubgroup_le kernelSubgroup_normal lev lev_dvd_chiLevel mem_kernelSubgroup oddChar oddChar_neg_one orderOf_dvd_totient orderOf_prod_dvd prod_S_le prod_odd_le prod_odd_le_aux prod_totient_lev_le qi qj ramSet relindex_kernel_le restrictHom rho rhoRep rho_commute rho_eq_act rho_map_mul sign_cocycle sign_normalization sign_sq_eq_one ten_le_heightE0 three_dvd_of_form totient_lev twist twist_kills_inertia twist_sq two_lt_lev zmod3_aniso) end HDec.GlueDescent
namespace HDec.GlueRepo export _root_.GlueRepo (A1.B A1.E A1.E_antisymm A1.E_comb A1.E_ros A1.E_self A1.O A1.card_units_mod3 A1.comb A1.combMul A1.comb_eq A1.comb_mul A1.conj3 A1.conj3_mul3 A1.descent A1.det_gram_E A1.det_trace_form A1.e A1.e_mem A1.gram_E A1.half_one_add_mem A1.inv_mul_self A1.isUnit3_iff A1.module_eq_zero A1.mul3 A1.mul3_conj3 A1.mul3_smul_left A1.mul3_smul_right A1.mul_star_eq A1.no_trd_zero_nrd_two A1.norm_descent A1.nrd A1.nrd3 A1.nrd3_mul A1.nrd3_one A1.nrd_eq A1.nrd_mul A1.nrd_ne_zero A1.one3 A1.red3 A1.red3_mul A1.ros A1.ros_add A1.ros_mem A1.ros_mul A1.ros_ros A1.star_mem A1.trace_form A1.trd A1.trd_eq A1.trd_mul_ros A1.trd_mul_ros_pos A1.μ A1.μ_mul_μ A1.μ_mul_μinv A1.μinv A1.μinv_mul_μ Numerics.a3_numerals Numerics.a8_degree Numerics.a8_field Numerics.a8_rank Numerics.splitting_degree_le PR.Fh PR.Fq PR.Fq_ne_zero PR.G6_sub_F2 PR.Gh PR.Gq PR.Gq_ne_zero PR.Hh PR.Hq PR.Hq_ne_zero PR.J_add PR.J_ne_branch PR.J_ne_zero PR.Jmap PR.Jmap_eq PR.bez_FG PR.bez_FH PR.bez_GH PR.bezout_not PR.div_gcd_eq_one_iff PR.fibre_free PR.fibre_iff PR.final_nat PR.h₁_ne_zero PR.h₂_ne_zero PR.inertia_orders_eq_one_iff PR.inertia_trivial_iff PR.inertia_trivial_iff_not_dvd PR.not_dvd_smoothBound PR.not_sq_of_odd_val PR.padicValRat_int_eq_zero PR.pair_not PR.quad_ne_zero PR.smoothBound PR.smooth_ne_zero PR.t_eq PR.t_sub_one PR.tq PR.val3_10800 PR.val3_43200 PR.vpos_iff TorsionFree.CommCore.cancel_three_pow TorsionFree.CommCore.eq_one_of_pow_eq_one TorsionFree.CommCore.eq_zero_of_step TorsionFree.CommCore.one_add_pow_expand TorsionFree.CommCore.step_coprime TorsionFree.CommCore.step_three TorsionFree.adjoinCommRing TorsionFree.card_le_three_pow TorsionFree.eq_one_of_pow_eq_one TorsionFree.injective_mod_three TorsionFree.matrix_eq_one TorsionFree.matrix_int_eq_one TorsionFree.matrix_padic_eq_one TorsionFree.padic_subgroup_trivial TorsionFree.three_pow_mul) end HDec.GlueRepo
namespace HDec.ObjBridge export _root_.ObjBridge (AbhyankarDVR CharPolyIndepOfEll CharpolyIndependentOfEll End End0 EndDivision FaltingsSemisimple FaltingsTate GrothendieckMonodromy Hom HomFreeFinite HomRankBound I3Leaves I3Leaves.casesOn I3Leaves.charPolyIndepOfEll I3Leaves.faltingsSemisimple I3Leaves.faltingsTate I3Leaves.homFreeFinite I3Leaves.mk I3Leaves.poincare I3Leaves.qmDichotomy I3Leaves.rec I3Leaves.recOn I3Leaves.tateModuleFree NeronMappingAbelianScheme NeronOggShafarevich PoincareReducibility PurityBranchLocus QMDichotomyYu RaynaudCriterion ReductionTorsionBijective SerreTatePotentialGood T TateModuleFree TorsionStructure V abhyankarDVR_iff charPolyIndepOfEll_iff charPolyIndepOfEll_iff_grp charpolyIndependentOfEll_iff dim endDivision_iff endMulEquiv equivEnd exists_abVar_iff exists_hom_ne_one_of_equivariant faltingsSemisimple_iff faltingsTate_iff finrank_equivEnd forall_abVar_iff forall_hom_iff forall₂_abVar_iff galAct_eq galHom_eq galRep grothendieckMonodromy_iff grpOfHom grpOfHom_homOfGrp grpOfHom_hom_hom homEquiv homFreeFinite_iff homOfGrp homOfGrp_bijective homOfGrp_comp_end homOfGrp_comp_hom homOfGrp_eq_zero_iff homOfGrp_grpOfHom homOfGrp_hom homOfGrp_id homOfGrp_injective homRankBound_iff homT_comp homT_galT homT_id hom_eq_zero_iff hom_sum_zsmul i3Leaves_iff isAbelianVariety_baseChange isCommMonObj mem_torsion_iff neronMappingAbelianScheme_iff neronOggShafarevich_iff ofGrp ofGrp_baseChange ofGrp_toGrp poincareReducibility_iff ptMap_homOfGrp pts_eq purityBranchLocus_iff qmDichotomyYu_iff range_tateHomZl_subset raynaudCriterion_iff reductionTorsionBijective_iff serreTatePotentialGood_iff tateHomZl tateModuleFree_iff toGrp toGrp_ofGrp torsionStructure_iff) end HDec.ObjBridge
namespace HDec.GlueC10 export _root_.GlueC10 (BrauerNesbittChar0 ChebotarevExists FrobDense FrobExistsAt FrobExistsFinite FrobLift FrobOn GQ IsFrobAt IsUnramFrob Qbar Zbar c10 card_quot continuous_trace eq_of_eq_on_frob frobDense frobDense_of_chebotarev frobExistsAt_of_finite frobExistsFinite frobLift frobLift_of_frobExistsAt frobOn_anti isClosed_frobOn isUnramFrob_all iso_of_trace_eq_frob_finite iso_of_trace_eq_on_frob iso_three_of_five semisimple_of_le toZbar toZbar_coe toZbar_injective trace_eq_matrix trace_half) end HDec.GlueC10
namespace HDec.LeafPush export _root_.LeafPush (GQ IsAtPrime T32a_TameQuadratic T32b_QuadraticRamification inertiaQ) end HDec.LeafPush
namespace HDec.GlueB3Unram export _root_.GlueB3Unram (B CycUnram Gal GalUnramifiedOutside LeafB3a LeafB3b LeafConj LeafFinRam LiesOver act_zeta beta_conj beta_mul_left beta_one centerIdeal centerIdeal_smul centerIdeal_under char_eq_sgn_zpow coe_smul cycUnram emb embW emb_mem etaG etaG.congr_simp etaG_apply etaG_continuous etaP etaP_isLocallyConstant etaP_sq etaP_unram exists_frac exists_inertia_neg exists_int_anti exists_int_of_fixed exists_kummer exists_neg_of_sq exists_smul_eq finRam galChar_unram gaussP gaussP_sq gaussP_transform inertiaGQ inertia_conj inertia_le_of_unramifiedAt inertia_val_sub_lt_one isAtPrime_comap isIntegral_intCast isIntegral_smul kerSub le_of_center leafB3a leafB3a_of_t32a leafB3b leafConj legChar liesOver_of_isAtPrime mem_centerIdeal mem_inertia_of_center mem_kerSub mem_of_isIntegral neg_ne_self_of_ne_zero neg_one_ne_one_C not_dvd_two_of_odd not_inertia_neg not_isSquare_of_squarefree one_isLocallyConstant pow_eq_zpow_aux prod_isLocallyConstant residue_inertia residue_natCast_ne_zero residue_prime_eq_zero rootOfUnity_mem sgnG sgnG_spec sgnHom sgnHom_apply smul_sq_cases t32a t32b toW unit_cast_cases units_sq_eq_one unramifiedAt_of_not_dvd_discr unramified_outside unramified_outside_b3a unramified_outside_final unramified_outside_noLeaf unramified_outside_of_leaves unramified_outside_of_unramifiedAt unramified_outside_t32a val_intCast val_intCast_eq_one val_intCast_le_one val_int_eq_pow val_le_one_of_isIntegral val_lt_one_iff val_natCast_ne_zero val_pow_eq_zpow val_rat_eq_zpow val_smul_lt_one_iff val_sq_eq val_sub_lt_one) end HDec.GlueB3Unram
namespace HDec.LeafQM export _root_.LeafQM (AV.CMExists AV.HasCM24 AV.HasCM24.of_iso AV.HasCM3 AV.HasCM3.of_iso AV.HasCM4 AV.HasCM4.of_iso AV.IsBaseChangeOf AV.IsBaseChangeOfPair AV.IsFibreOf AV.Level3 AV.Level3.bcPt_pow_three AV.Level3.casesOn AV.Level3.ctorIdx AV.Level3.eq_iff AV.Level3.eta AV.Level3.exists_mul_of_range_le AV.Level3.ext' AV.Level3.ker AV.Level3.linear AV.Level3.mk AV.Level3.mk.congr_simp AV.Level3.mk.inj AV.Level3.mk.injEq AV.Level3.mk.noConfusion AV.Level3.mk.sizeOf_spec AV.Level3.noConfusion AV.Level3.noConfusionType AV.Level3.onto AV.Level3.range_le AV.Level3.rec AV.Level3.recOn AV.Level3.rightMul AV.Level3.rightMul_eq_self AV.Level3.rightMul_rightMul AV.Level3.torsor AV.Level3.twist AV.M3 AV.M3.mk AV.M3.rightMul AV.M3.rightMul_rightMul AV.M3.twist AV.M3.twist_mk AV.Pin.IsNaturalRelabel AV.Pin.MobiusGlue AV.Pin.PinUnique AV.Pin.QMFamily.transport AV.Pin.R1fpProps.fam AV.Pin.R1fpProps.univ AV.Pin.SameTriple AV.Pin.SameTripleMor AV.Pin.autRelabel AV.Pin.autRelabel_natural AV.Pin.cm_objects_of_R1R2fp AV.Pin.isFibreOf_transport AV.Pin.phi_part AV.Pin.pointwise_of_witness AV.Pin.pointwise_of_witness_mor AV.Pin.r1fpPin_aut AV.Pin.r1fpPin_relabel_iff AV.Pin.r2fp_aut AV.Pin.relabel AV.Pin.relabel_geometric AV.Pin.relabel_is_morphism AV.Pin.sameTripleMor_of_mobius AV.Pin.sameTriple_aut AV.Pin.transfer_exists AV.Pin.transfer_pointwise AV.Pin.transfer_pointwise_mor AV.PtEquiv AV.QMFamily AV.QMFamily.F AV.QMFamily.casesOn AV.QMFamily.ctorIdx AV.QMFamily.eta AV.QMFamily.eta_sec AV.QMFamily.iota AV.QMFamily.iota_over AV.QMFamily.mk AV.QMFamily.mk.inj AV.QMFamily.mk.injEq AV.QMFamily.mk.noConfusion AV.QMFamily.mk.sizeOf_spec AV.QMFamily.noConfusion AV.QMFamily.noConfusionType AV.QMFamily.proper AV.QMFamily.rec AV.QMFamily.recOn AV.QMFamily.smooth AV.QMIso AV.QMIso.casesOn AV.QMIso.ctorIdx AV.QMIso.equivariant AV.QMIso.left AV.QMIso.mk AV.QMIso.mk.inj AV.QMIso.mk.injEq AV.QMIso.mk.noConfusion AV.QMIso.mk.sizeOf_spec AV.QMIso.noConfusion AV.QMIso.noConfusionType AV.QMIso.nonempty_abVarIso AV.QMIso.rec AV.QMIso.recOn AV.QMIso.refl AV.QMIso.right AV.QMIso.symm AV.QMIso.trans AV.QMIso.φ AV.QMIso.ψ AV.QML3 AV.QML3.A AV.QML3.Iso AV.QML3.Iso.casesOn AV.QML3.Iso.ctorIdx AV.QML3.Iso.equivariant AV.QML3.Iso.left AV.QML3.Iso.level AV.QML3.Iso.mk AV.QML3.Iso.mk.inj AV.QML3.Iso.mk.injEq AV.QML3.Iso.mk.noConfusion AV.QML3.Iso.mk.sizeOf_spec AV.QML3.Iso.noConfusion AV.QML3.Iso.noConfusionType AV.QML3.Iso.rec AV.QML3.Iso.recOn AV.QML3.Iso.refl AV.QML3.Iso.right AV.QML3.Iso.rightMul AV.QML3.Iso.symm AV.QML3.Iso.trans AV.QML3.Iso.twist AV.QML3.Iso.φ AV.QML3.Iso.ψ AV.QML3.casesOn AV.QML3.ctorIdx AV.QML3.e AV.QML3.forget AV.QML3.mk AV.QML3.mk.congr_simp AV.QML3.mk.inj AV.QML3.mk.injEq AV.QML3.mk.noConfusion AV.QML3.mk.sizeOf_spec AV.QML3.noConfusion AV.QML3.noConfusionType AV.QML3.q AV.QML3.rec AV.QML3.recOn AV.QML3.rightMul AV.QML3.rightMul_A AV.QML3.rightMul_rightMul AV.QML3.surface AV.QML3.twist AV.QML3.twist_A AV.QMLeaves AV.QMLeaves.casesOn AV.QMLeaves.mk AV.QMLeaves.r1r2 AV.QMLeaves.r1rec AV.QMLeaves.r5 AV.QMLeaves.r5count AV.QMLeaves.rec AV.QMLeaves.recOn AV.QMPair AV.QMPair.A AV.QMPair.casesOn AV.QMPair.ctorIdx AV.QMPair.mk AV.QMPair.mk.inj AV.QMPair.mk.injEq AV.QMPair.mk.noConfusion AV.QMPair.mk.sizeOf_spec AV.QMPair.noConfusion AV.QMPair.noConfusionType AV.QMPair.q AV.QMPair.rec AV.QMPair.recOn AV.QMPair.surface AV.QMPair.twist AV.QMStr AV.QMStr.casesOn AV.QMStr.ctorIdx AV.QMStr.injective AV.QMStr.iota AV.QMStr.mk AV.QMStr.mk.congr_simp AV.QMStr.mk.inj AV.QMStr.mk.injEq AV.QMStr.mk.noConfusion AV.QMStr.mk.sizeOf_spec AV.QMStr.noConfusion AV.QMStr.noConfusionType AV.QMStr.rec AV.QMStr.recOn AV.QMStr.twist AV.Qbar AV.R1R2fp AV.R1R2fp_Y AV.R1famProps AV.R1fp AV.R1fpProps AV.R1fp_of_R1R2fp AV.R1heckeProps AV.R1rec AV.R1recProps AV.R1univProps AV.R2X6Props AV.R2fpProps AV.R2fpProps_of_X6 AV.R5fp AV.R5fpCount AV.R5fpWeak AV.R5fpWeak_of_R5fp AV.R5ptProps AV.ToP1 AV.ToP1.U AV.ToP1.V AV.ToP1.basicOpen_f AV.ToP1.basicOpen_g AV.ToP1.casesOn AV.ToP1.comp AV.ToP1.cover AV.ToP1.ctorIdx AV.ToP1.f AV.ToP1.g AV.ToP1.inv AV.ToP1.mk AV.ToP1.mk.inj AV.ToP1.mk.injEq AV.ToP1.mk.noConfusion AV.ToP1.mk.sizeOf_spec AV.ToP1.noConfusion AV.ToP1.noConfusionType AV.ToP1.rec AV.ToP1.recOn AV.ToP1.val AV.ToP1.val_comp AV.ToP1.val_comp_right AV.UnramifiedAbove5 AV.X6Props AV.X6Surj AV.act_mul_apply AV.bcPt AV.bcPt_injective AV.cm_of_val AV.com AV.comEquiv AV.com_twist AV.conductor AV.conjHom AV.conjHom_iota AV.conjHom_mem_com AV.conjHom_symm_apply AV.conj_iso_of_rational AV.conj_twist_of_rational AV.endPt AV.exists_fibre_object AV.fibre_conjugates_isomorphic AV.fieldMap AV.fieldOfModuli3 AV.fieldOfModuliPair AV.fieldPt AV.galAct_bcPt AV.hI AV.hIJ AV.hJ AV.hasCM24_twist AV.hasCM3_twist AV.hasCM4_twist AV.hrat AV.inertCount6 AV.inertCount6.congr_simp AV.intCast_mem_com AV.isoSetoid AV.leaves_on_one_witness AV.liftO AV.not_qmStr_zero AV.ofInt_injective AV.ofInt_sub AV.oi AV.oi_mul_oi AV.oj AV.oj_mul_oi_add AV.oj_mul_oj AV.pairSetoid AV.qmAct AV.residueImage AV.residue_unramified_over_branch AV.specMap_flat AV.specMap_surjective AV.specToEquivOfField_comp AV.specToEquivOfField_comp_right AV.stab3 AV.stabPair AV.three_mul_ofInt AV.toKbar AV.unramified_over_branch B InO O O_nontrivial mulCoord ofInt ofInt_add ofInt_mul ofInt_neg ofInt_one ofInt_zero) end HDec.LeafQM
namespace HDec.LeafModCurves export _root_.LeafModCurves (BelyiX1 Cosets DimJ1Genus Ej EjBar Ej_j IsBelyiFunction IsCurve IsCurve.casesOn IsCurve.geomConnected IsCurve.mk IsCurve.proper IsCurve.rec IsCurve.recOn IsCurve.smooth IsFrobAt IsJ1 IsJacobian IsJacobian.base IsJacobian.casesOn IsJacobian.mk IsJacobian.rec IsJacobian.recOn IsJacobian.unique IsJacobian.univ IsX1Model JacobianExists Kbar ModCurveLeaves ModCurveLeaves.casesOn ModCurveLeaves.dimJ1 ModCurveLeaves.jac ModCurveLeaves.mk ModCurveLeaves.r16 ModCurveLeaves.rec ModCurveLeaves.recOn ModCurveLeaves.x1 Qj R16_EichlerShimuraJ1' RatPt SpecQ VSurjOfSurjective X1ModelExists X_sub_1728_ne_zero Y1j belyiDeg belyiDeg_Gamma1_le belyiDeg_le_index coeffField coeff_mem_coeffField dim_J1_le dualAct dualAct_mem dualAct_mul dualAct_one eigenFun embOf embOf_spec endV endV_comm exists_J1 exists_J1_dim_le exists_J1_quotient exists_preimage fieldX1 finrank_rhoF frobOn frobOn_mul frobOn_one g13_constituent galRep_apply genus genus_Gamma1 genus_Gamma1_le genus_le homV homVAdd homVAdd_apply homV_galRep isFrobAt_of_isArithFrob jLineToField jMap le_pmSubgroup neg_one_mem_pmSubgroup nu2 nu2_Gamma1 nu3 nu3_Gamma1 nuInf nuInf_pos pmSubgroup pullback pullback_dualAct pullback_injective rhoF rhoF_attached rhoF_traces smul_mk_eq_iff trace_ST_inv trace_S_inv trace_conj trace_mem_pmGamma1 trace_rhoF xCoord zbar_mem) end HDec.LeafModCurves
namespace HDec.TDifferent export _root_.TDifferent (adjoin_fractionRing_eq_top adjoin_tower_eq_top aeval_derivative_minpoly_eq_prod card_eq_sum card_lowerRam_zero card_sub_one_eq card_tower_eq ceil_toNat_lt_iff coset_min exists_adjoin_eq_top exists_intTrace_eq_ramificationIdx exists_limit exists_phiF_eq exists_root_of_residue fiber_sum filtR filtR_zero finite_algEquiv finite_tower herbrandPhi_eq_phiF herbrand_lemma herbrand_quotient herbrand_trans hilbertDifferentFormula_of_adjoin_eq_top integral_indicator_Iic isGaloisGroup_algEquiv isGaloisGroup_tower map_maximalIdeal_eq_pow maximalIdeal_eq_span_of_mem_of_notMem maximalIdeal_pow_le_iff mem_inertia_iff_of_adjoin minpoly_map_eq_prod nQ_eq phiExpl phiF phiF_eq_phiExpl phiF_formula phiF_ge phiF_mono phiF_neg_one phiF_strictMono phiF_trans phiF_zero repr_mem_of_mem_smul_top resHom resHom.congr_simp resHom_apply resHom_eq_one_iff resHom_surjective sInf_phiF sInf_phiF_of_le span_eq_maximalIdeal_pow span_sub_eq_span_prod sum_card_sub_one tower_data upper_map) end HDec.TDifferent
namespace HDec.TSkolemKW export _root_.TSkolemKW (HS.FrobeniusDense HS.LocMem HS.exists_frac_or_inv HS.frobeniusDense_of_chebotarev HS.frobeniusDense_of_frobDense HS.gZ HS.gZ_coe HS.liesOver_and_isArithFrob HS.locMem_or_inv HS.mem_zbarLoc HS.natCast_mem HS.one_notMem HS.zbarLoc HSynBrauerNesbitt HSynSkolemNoether KW.KroneckerWeber KW.KroneckerWeberCyclic KW.agree_of_cycChar_eq KW.card_rootsOfUnity_qbar KW.cycChar KW.cycChar_spec KW.cycChar_surjective KW.dirichletCharacter_of_kroneckerWeberCyclic KW.eq_of_agree_on_roots KW.eq_of_agree_on_roots_cyclic KW.exists_isPrimitiveRoot_qbar KW.fixes_of_embeds KW.isOpen_ker_of_continuous KW.ker_ge_of_kroneckerWeber KW.ker_ge_of_kroneckerWeberCyclic KW.kroneckerWeberCyclic_of_kroneckerWeber KW.toRingAut Twist Twist.instAddCommGroup Twist.instModule Twist.instModule_1 Twist.isScalarTower Twist.of Twist.smul_of act act.congr_simp act_pow brauerNesbitt_module exists_injective_of_trace_eq fd_sub hsynBrauerNesbitt hsynSkolemNoether isNilpotent_of_trace_pow_eq_zero isSemisimpleModule_repOfGL isSimpleRing_tensor leafSkolemNoether nonempty_linearEquiv_of_finrank_eq repOfGL repOfGL_apply skolemNoether trace_act_equiv trace_act_prod) end HDec.TSkolemKW
namespace HDec.GlueI6Rest export _root_.GlueI6Rest (exists_half_iff) end HDec.GlueI6Rest
namespace HDec.GlueSqrtLocal export _root_.GlueSqrtLocal (Gbig Gsmall actLower actLower_apply apply_eq_pow_actLower autToPow_eq_of_apply card_quotient_maximalIdeal cast_eq_zero_of_two_nsmul cyclotomic_prime_pow_comp_isEisensteinAt_padicInt cyclotomic_prime_pow_irreducible_padic dvd_of_sq_eq_one dvd_sub_or_add_of_dvd_sq_sub_one dvd_sub_or_add_of_dvd_sq_sub_one_odd eq_of_pow_eq_one_of_sub_mem exists_frobenius exists_half_iff finrank_eq_orderOf finrank_eq_totient galCommGroup galEquivUnits gal_sqrt_criterion gal_sqrt_criterion_lower intCast_eq_one_or_neg_one isCyclic_gal isIntegral_iff_spectralNorm_le_one isLocalRing_integralClosure pow_frobenius pow_frobenius_of_isLocalRing proj proj_apply proj_two_torsion range_autToPow_eq_zpowers range_autToPow_eq_zpowers' redU redU_neg_one redU_sq_eq_one redU_val spectralNorm_mul' sqrt_criterion_finite tauNeg tauNeg_mul_self tauNeg_sq units_sq_eq_one_odd) end HDec.GlueSqrtLocal
namespace HDec.GlueSqrtDisj export _root_.GlueSqrtDisj (card_quotient_maximalIdeal card_subgroup_prod coprime_pow_sub_one dvd_pow_orderOf_sub_one eq_of_pow_eq_one_of_sub_mem exists_tau finrank_eq_totient_mul_orderOf fix_of_autToPow_eq_one galCommGroup galEquivProd galToProd galToProd.congr_simp galToProd_fst_spec galToProd_injective galToProd_restrict galToProd_snd_spec isCyclotomicExtension_muField le_muField_of_lkw level_dvd muAlgebra muField muField_le_level muField_mono neZero_pow neZero_prime orderOf_unit_pow_sub_one prime_mem_pow_totient range_galToProd sqrt_criterion_level sqrt_criterion_level_pow sqrt_criterion_muField totient_mul_orderOf_le_finrank zeta_pow_m zeta_pow_pk) end HDec.GlueSqrtDisj
namespace HDec.T30 export _root_.T30 (Gp act_crt act_of_gal act_of_galToProd_tau actp chi_of_sqrt' coe_algebraMap_mu complexUnits_pow_surj cyc_eq_one_of_restrict cyc_of_torsion cyc_resp_eq cyc_resp_eq_one cyc_resp_eq_u dvd_val_sub exists_decomp exists_emb exists_sqrt_iff fix_of_galToProd_one intCast_val leafSqrtCrit_of_localKroneckerWeber leafSqrtCrit_of_t16a ne_zero_of_pow_eq_one pow_val_neg_one pow_val_one restrictNormal_compat restrict_restrict_compat restrict_sq_eq_one sqrtCrit_at sqrt_of_chi' sqrt_of_inflated zpow_congr_of_dvd) end HDec.T30
namespace HDec.T10Etale export _root_.T10Etale (AKbar F F.congr_simp H0Equiv H0Equiv_smul T10_TateDuality T10_linIso T10_linIso_of_tateDuality T10_linIso_zero adjL adjR constIso ellIso ellIso_smulEnd ext_postcomp_iso_bijective ext_precomp_iso_bijective galAut galAut_mul galAut_one galH galIso galIso_inv_mul galIso_mul isTerminalImg isTerminalProEt mem_topology_iff nontrivial_H0 piX proEtEquiv proEtMap sheafEquiv smulEnd smulEnd_add smulEnd_mul smulEnd_one smulEnd_zero smulHom smulHom_add smulHom_apply smulHom_mul smulHom_one smulHom_zero smul_def specAlg specAut specAut_comp specAut_mul specAut_one subsingleton_T_zero terminalProEt transport transport_H0 transport_bijective transport_homEquiv transport_mk₀ transport_smul transportₗ unit_ellIso_sections weaklyEtale_hom) end HDec.T10Etale
namespace HDec.X1Belyi export _root_.X1Belyi (ConstantFieldIsQ CurveOfFunctionFieldQ GoodReductionUnramified HasRationalPlace TorsionStructure X1ConstantField X1Leaves X1Leaves.casesOn X1Leaves.constants X1Leaves.curve X1Leaves.cusp X1Leaves.goodRed X1Leaves.mk X1Leaves.rec X1Leaves.recOn X1Leaves.torsion X1RationalCusp belyiX1_of_leaves exists_addOrderOf finrank_fieldX1_le map_mem_nTors modCurveLeaves_of nTors nTors_card ratHom scaleEquiv scaleEquiv_apply scaleEquiv_symm_X scaleEquiv_symm_X_sub scale_not_dvd transcendental_X_div x1ModelExists_and_belyiX1 x1ModelExists_of_leaves xCoord_map) end HDec.X1Belyi
namespace HDec.E1Sub export _root_.E1Sub (E1_R16 baseChange_surjective evalEig evalEigE evalEigE_equivariant evalEigE_surjective exists_res exists_subrep_equiv_of_surjective g13_constituent' galHomK galHom_ptUnit homT_comp homVK homVK_galRep homVK_surjective isCompl_toSubmodule isReduced_left precomp precompPt precompPt_injective precomp_hom precomp_injective ptUnit ptUnit.congr_simp res res_spec rhoFL rhoFL_subrep_JL rhoF_semisimple_of_surj rhoF_subrep_J rhoF_subrep_JL rhoF_subrep_of_surj specHom specHom_galHom tateHomZl_precomp vSurjOfSurjective) end HDec.E1Sub
namespace HDec.C9Rhof export _root_.C9Rhof (FrobeniusDense c10_via_c9 c9 c9_R14 c9_core c9_r5 continuous_coord eq_of_eq_on_arithFrob ev ev_apply finiteDimensional_V isSemisimple_of_isIrreducible iso_of_arithFrob quotMap quotMap_equivariant quotMap_surjective rhoF_continuous rhoF_ev rhoF_isSemisimpleModule rhoF_semisimple semisimple_of_complements toMatrix_toRep toRep toRep_apply toRep_continuous toRep_semisimple trace_eq_of_arithFrob trace_toRep) end HDec.C9Rhof

/-!
# H = `ZInQ.SixContactMin` decomposed into literature leaves and glue (synthesis)

Companion of `docs/research/h-decomposition.md`. Check with
`lake env lean scratch/h-decomposition/Leaves.lean`.

Layout (each block copied verbatim from a report's compiled draft, inside its own section).
* `PkgI1` (pkg-I1): the quaternion order, genus-2 theta constants, Igusa invariants; the leaves
  `ThetaModularity` (R4), `QMHauptmodul` (a consequence of R2-R4, not counted as a leaf),
  `IgusaClebschSeparation` (T28); proved glue for A1, A5, A7, A10, F1.
* `PkgI2` (pkg-I2): abelian varieties as `Grp (Over (Spec K))`, good reduction as abelian schemes,
  torsion points with Galois/inertia action; the reduction-theory leaves; two proved consequences.
* `PkgI3` (pkg-I3): bundled abelian varieties `AbVar` with `Hom`, Tate modules `T_ℓ`, `V_ℓ` and the
  Galois representation; Faltings 1983 (R9) and Mumford's theorems; proved E1 and C2 glue.
* `PkgI4` (pkg-I4): the `G_{ℚ_p}`-action on `ℂ_p` and on Mathlib's `BDeRham`, the de Rham predicate,
  Hodge–Tate multiplicities; the modularity leaves (`DeRhamComparison`, `PanBerger`, `EigenformHT`,
  `NewformOfEigenform`, `CarayolUnramified`) and templates. Its copy of pkg-I3 is renamed `PkgI4.I3`.
* `PkgI6` (pkg-I6): continuous Galois cohomology leaves for B2, local Kronecker–Weber, local
  reciprocity with upper numbering, ramification leaves; the proved Brauer step of B2.
* `GlueConductor` (glue-conductor): the elementary core of D1-D5, proved; two different-ideal
  leaves stated over Mathlib.
* `GlueAssembly` (glue-assembly): F2 on Mathlib's Weil heights, E2-E4/F3 arithmetic, the final
  constant and F4: `GlueOutputs S → SixContactMinAt S`, proved; C8, E1, E2, F3 glue.
* `GlueDescent` (glue-descent): B1/C1 algebra, B2-B3 over Mathlib's `G_ℚ` from four leaves
  (`GlueDescent.B3Q.b3_degree_le_QM`, proved).
* `GlueRepo` (glue-repo): the quaternion order, `1 + 3M_r(ℤ₃)` torsion-free, the arithmetic of
  Lemma PR(i), Minkowski's bound, the NoCM fibre computation (proved).
* `HSyn` §0-§1 (from the hdec-faithful draft): the absolute Galois group of `ℚ`, places,
  Frobenius, continuous `GL_n(ℚ̄_ℓ)`-representations, cusp forms with nebentypus, normalized
  eigenforms, and the leaves statable over them.
* `HSyn` §2: the remaining placeholders (`opaque … : Prop`; since leaf-adopt3 only R1(b) and
  R17). **A placeholder carries no content**: it is an uninterpreted proposition whose docstring
  records the exact statement and reference. A theorem with a placeholder among its hypotheses
  says nothing until the placeholder is replaced by a genuine statement.
* `HSyn` §3: the leaves bundled (`ResearchLeaves`, `TextbookLeaves`), the glue pieces bundled
  (`GluePieces`, leaf-adopt3) and the top-level theorem
  `sixContactMin_of_leaves : ResearchLeaves → TextbookLeaves → GluePieces → ZInQ.SixContactMin`,
  which is `glueOutputs_of_leaves` (glue G1-G17, G19: **proved** from the bundles, g0-split, folded
  by leaf-adopt3) followed by glue-assembly's proved `GlueOutputs Mult.S_mul → SixContactMin`
  (G18-G20, checked against the real `ZInQ.SixContactMin`). `GlueOutputs` is a numerical
  interface, not a leaf.

**leaf-adopt3 (2026-11-13): the file has no `sorry`.** The paragraph below is historical.
Before leaf-adopt3 the only `sorry` in the file was `glueOutputs_of_leaves` (hsyn-fix, after the reviews): A6
(`PkgI2.goodReduction_of_QM_rational3`, rv-a6-route), D4 (`PkgI6.artinConductor_le_of_upper`,
glue-I6-rest) and D3 (`PkgI6.sq_principalUnits`) are now proved. Their remaining assumptions are
explicit hypotheses: the glue Prop `PkgI2.QuatUnipotentTrivial` (pure algebra, paper proof in
rv-a6-route §3) for A6, and the glue Prop `GlueI3.SemisimpleBaseChange` (standard algebra) for
glue-I3-linalg's `PkgI3.C2_absolutelyIrreducible` and `PkgI3.E1_exists_hom_ne_zero`.
`scratch/hsyn/assemble.py` no longer reproduces this file (hsyn-fix edited it by hand).

hsyn-fold (2026-11-12) added, each in its own section: `GlueA6Alg.Alg` and
`PkgI2.quatUnipotentTrivial` (glue-a6-alg; A6 now needs only its three leaves, and
`PkgI2.QuatUnipotentTrivial` is no longer a hypothesis anywhere), `PkgI3.trace_indep_of_ell` and
`GlueC10` (glue-c10), `GlueD1Local` (glue-d1-local), `LeafPush` and `PkgI4.T23_FontaineClosure`
(leaf-push; the five placeholders R8, T9, T23, T29, T32 are replaced in the bundles), and
obj-bridge's §C-§E as `ObjBridge` (its §F does not compile here; see the comment there). The
paragraph above is otherwise as hsyn-fix left it: the only remaining glue Prop hypothesis is
`GlueI3.SemisimpleBaseChange`.

leaf-adopt (2026-11-12) added, each in its own section after `LeafPushSec`: `GlueT32aSec`
(glue-t32a with glue-b3b: T32 is proved glue, `HSyn.t32a_glue`, `t32b_glue`), `LeafQMSec`
(leaf-qm-fp: R1 (a), (c), (d), R2, R5 in field-point form), `LeafModCurvesSec` (leaf-modcurves: R16,
`JacobianExists` = T33, `DimJ1Genus` = T34), `DefFaltingsSec` (def-faltings: the stable Faltings
height, R19-R21), and `LeafAdoptSec` (rv-blueprints' repairs Q2, Q4, Q5, M1, F2: `R1R2fpRep`,
`R1pi0Props`, `R2X6PropsIff`, `R5fpStrong`, `H5`, and the bridge `abVarEquiv`).

leaf-adopt2 (2026-11-12) added `LeafPush2Sec` after `LeafAdoptSec`: scratch/leaf-push2 copied
verbatim, with R3 (`ZInQ.LeafPush2.R03_LinYang`), R18 (`R18_Javanpeykar`), R22 (`R22_Pazuki`),
T11 (`T11a_RiemannEnd`, `T11b_Rigidity`), the new textbook leaf T35 (`UniformizationExists`,
AN3 for abelian varieties) and the glue target `T12_ComplexConjEigen` (T12 is now glue). The
placeholders are now R1(b), R17, T10 (3 `opaque`). The Shimura-curve leaves (R1, R2, R5) and
R3 rest on Lemma QP of rv-qm-polar (type `μ` fixed, characteristic 0, `𝒪` maximal), a published
input folded into each leaf because polarizations cannot be stated in Lean yet; the height
leaves (R18-R22) say something only together with H5: where the height is `⊤` (no metrized
model) R19, R20, R22 are vacuous and R21 is trivial, so a defect of the definition surfaces as a
false H5 (`StableHeightFinite`) or a false R18 (which asserts `h < ⊤`), not as vacuity
(rv-leaves48 P1, compiled for R19-R21 and H5); see the docstrings,
`docs/research/leaf-adopt.md` and `docs/research/leaf-adopt2.md`.

leaf-adopt3 (2026-11-13) folded in wave 25 and g0-split, each in its own section:
`GlueSSBCSec` (glue-ssbc's `SemisimpleBaseChange`, before `HSyn`); between `HSyn` §2 and the bundles,
`TDifferentSec` (T20, T21 local forms and T22 proved), `TSkolemKWSec` (T13, T19 proved; T18's
density form from `ChebotarevExists`; T17 narrowed to `KroneckerWeberCyclic`; `c10_of_chebotarev`),
`T30Sec` (T30 from T16(a), with copies of the kernel's `GlueI6Rest`, `GlueSqrtLocal`,
`GlueSqrtDisj`), `T10EtaleSec` (T10 concrete and Galois-equivariant), `Pi0X6Sec` (`R1pi0Props`
from clauses plus two Props; R1's clause kept), `HodgeLatticeSec` (`HodgeLatticeTheorem` from two
Props and `DimBaseChange`), `H5NeronSec` (H5's Néron identity from N1, N2 and glue; additivity),
`X1BelyiSec` (`X1ModelExists`, `BelyiX1` from five new leaves T36-T40), `E1SubSec`
(`VSurjOfSurjective` proved), `C9RhofSec` (C9 proved); and in §3 the proof of
`glueOutputs_of_leaves` (g0-split) with the bundle `GluePieces`. Bundle changes: `t10` concrete;
`t13`, `t19`, `t22a`, `t22b`, `t30` removed (proved, `HSyn.t13_proved` etc.); `t17`, `t18`
narrowed; new `x1` (T36-T40), `t41` (N1, Néron models exist). See
`docs/research/leaf-adopt3.md`.

No `axiom` declarations. Leaf numbering (R1-R22 and H5 research-level, T1-T41 textbook; T12, T13,
T19, T22, T30, T32 now glue, proved except T12) is that of the note's §2.
-/

namespace HDec

set_option maxHeartbeats 1000000

attribute [-instance] TauCeti.FinitePadicExtension.toAlgebra
  TauCeti.FinitePadicExtension.ofInstances TauCeti.FinitePadicExtension.toModuleFinite
  TauCeti.FinitePadicExtension.toValuativeExtension

section PkgI1Sec
/-! ### Copied from `scratch/pkg-I1/I1.lean` (compiled there). -/

open Complex Matrix

noncomputable section

namespace PkgI1

/-! ## §1 The quaternion datum (N5 L410-420) -/

/-- `B = (2,-3)`: Mathlib's `QuaternionAlgebra R c₁ c₂ c₃` has `i² = c₁ + c₂ i`, `j² = c₃`. -/
abbrev B := QuaternionAlgebra ℚ 2 0 (-3)

/-- `i`, `j`, `k = ij` in `B`. -/
def qi : B := ⟨0, 1, 0, 0⟩
def qj : B := ⟨0, 0, 1, 0⟩
def qk : B := ⟨0, 0, 0, 1⟩

/-- N5's ordered basis `(1, i, (1+j)/2, (i+ij)/2)` of the maximal order `𝒪`. -/
def oBasis : Fin 4 → B := ![⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨1/2, 0, 1/2, 0⟩, ⟨0, 1/2, 0, 1/2⟩]

/-- Membership in `𝒪 = ℤ⟨1, i, (1+j)/2, (i+ij)/2⟩`. -/
def InO (x : B) : Prop := ∃ n : Fin 4 → ℤ, x = ∑ k, (n k : ℚ) • oBasis k

/-- `μ = 2j + ij`. -/
def mu : B := ⟨0, 0, 2, 1⟩

/-- `μ⁻¹ = -μ/6`, since `μ² = -6`. -/
def muInv : B := ⟨0, 0, -1/3, -1/6⟩

/-- Reduced trace. -/
def trd (x : B) : ℚ := 2 * x.re

theorem mu_sq : mu * mu = (⟨-6, 0, 0, 0⟩ : B) := by
  ext <;> simp [mu]; norm_num

theorem mu_mul_muInv : mu * muInv = 1 := by
  ext <;> simp [mu, muInv] <;> norm_num

/-- N5's Gram matrix (L413-415). -/
def gram : Matrix (Fin 4) (Fin 4) ℚ := !![0, 0, -1, 1; 0, 0, 1, -2; 1, -1, 0, 0; -1, 2, 0, 0]

/-- **A1 (glue, proved).** `Trd(μ⁻¹ x ȳ)` has N5's Gram matrix in N5's basis. -/
theorem gram_eq (r s : Fin 4) : trd (muInv * oBasis r * star (oBasis s)) = gram r s := by
  fin_cases r <;> fin_cases s <;> simp [trd, muInv, oBasis, gram] <;> norm_num

theorem gram_det : gram.det = 1 := by
  simp [gram, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  rw [show Fin.succAbove (2 : Fin 4) (2 : Fin 3) = 3 from rfl,
    show Fin.succAbove (3 : Fin 4) (2 : Fin 3) = 2 from rfl]
  norm_num

/-! ## §2 The real embedding and `Γ*` -/

/-- `ι(i) = [[√2,0],[0,-√2]]`. -/
def Mi : Matrix (Fin 2) (Fin 2) ℝ := !![√2, 0; 0, -√2]
/-- `ι(j) = [[0,-3],[1,0]]`. -/
def Mj : Matrix (Fin 2) (Fin 2) ℝ := !![0, -3; 1, 0]

/-- The real embedding `ι : B → M₂(ℝ)` (a ring homomorphism: `qm_embed.py` checks it on the
basis; `Mi² = 2`, `Mj² = -3`, `Mi Mj = -Mj Mi`). -/
def iota (x : B) : Matrix (Fin 2) (Fin 2) ℝ :=
  (x.re : ℝ) • 1 + (x.imI : ℝ) • Mi + (x.imJ : ℝ) • Mj + (x.imK : ℝ) • (Mi * Mj)

/-- `x ∈ B` is invertible and normalizes `𝒪`. -/
def NormalizesO (x : B) : Prop :=
  ∃ y : B, x * y = 1 ∧ y * x = 1 ∧ ∀ z : B, InO z → InO (x * z * y) ∧ InO (y * z * x)

/-- `Γ* = ι(N_B(𝒪)⁺)` acting on `ℍ`; modulo scalars this is the group of the Atkin–Lehner
quotient `X₆/W` (positive reduced norm = positive determinant). -/
def GammaStar : Set (GL (Fin 2) ℝ) :=
  {γ | ∃ x : B, NormalizesO x ∧ (γ : Matrix (Fin 2) (Fin 2) ℝ) = iota x ∧
    0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det}

/-! ## §3 Siegel upper half-space and theta constants -/

/-- The Siegel upper half-space of degree 2. -/
def SiegelH2 : Set (Matrix (Fin 2) (Fin 2) ℂ) :=
  {Ω | Ωᵀ = Ω ∧ (Ω.map Complex.im).PosDef}

/-- A half-integral characteristic `m = (a, b)`, `a b ∈ {0,1}²`. -/
abbrev Char2 := (Fin 2 → Fin 2) × (Fin 2 → Fin 2)

/-- Theta constant `θ_m(Ω) = Σ_{n ∈ ℤ²} exp(πi (n+a/2)ᵀΩ(n+a/2) + πi (n+a/2)ᵀ b)`. -/
def thetaConst (m : Char2) (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  ∑' n : Fin 2 → ℤ,
    let v : Fin 2 → ℂ := fun k => (n k : ℂ) + ((m.1 k : ℕ) : ℂ) / 2
    Complex.exp (Real.pi * I * (v ⬝ᵥ (Ω *ᵥ v)) + Real.pi * I * (v ⬝ᵥ fun k => ((m.2 k : ℕ) : ℂ)))

/-- The ten even characteristics (`aᵀb ≡ 0 mod 2`). -/
def evenChars : Finset Char2 :=
  Finset.univ.filter fun m => ((m.1 0 : ℕ) * (m.2 0 : ℕ) + (m.1 1 : ℕ) * (m.2 1 : ℕ)) % 2 = 0

theorem card_evenChars : evenChars.card = 10 := by decide

/-- `Σ_{m even} θ_m⁸` (`= 4ψ₄`). -/
def thetaSum8 (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := ∑ m ∈ evenChars, thetaConst m Ω ^ 8

/-- `∏_{m even} θ_m²` (`= -2¹⁴χ₁₀`). -/
def thetaProd2 (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := ∏ m ∈ evenChars, thetaConst m Ω ^ 2

/-- Numerator of F1: `3779136·(∏θ_m)⁴`. -/
def jNum (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := 3779136 * thetaProd2 Ω ^ 2

/-- Denominator of F1: `(Σθ_m⁸)⁵`. -/
def jDen (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := thetaSum8 Ω ^ 5

/-- The action of `Sp₄` on degree-2 matrices: `(AΩ+B)(CΩ+D)⁻¹`. -/
def spAct (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) (Ω : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  let Mc := M.map (Int.cast : ℤ → ℂ)
  (Mc.toBlocks₁₁ * Ω + Mc.toBlocks₁₂) * (Mc.toBlocks₂₁ * Ω + Mc.toBlocks₂₂)⁻¹

/-- The automorphy factor `det(CΩ+D)`. -/
def spFactor (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) (Ω : Matrix (Fin 2) (Fin 2) ℂ) :
    ℂ :=
  let Mc := M.map (Int.cast : ℤ → ℂ)
  (Mc.toBlocks₂₁ * Ω + Mc.toBlocks₂₂).det

/-! ## §4 The modular embedding of N5's QM datum (`qm_embed.py`)

For `τ ∈ ℍ` put `v_τ = (τ, 1)ᵀ` and `Λ_τ = ι(𝒪)v_τ ⊂ ℂ²`, with Riemann form
`E(ι(x)v_τ, ι(y)v_τ) = Trd(μ⁻¹xȳ)`. In N5's basis the Gram matrix is `[[0,P],[-Pᵀ,0]]` with
`P = [[-1,1],[1,-2]]`, `P⁻¹ = [[-2,-1],[-1,-1]]`. So `e = (ι(1)v, ι(i)v)` and
`f' = (ι((1+j)/2)v, ι((i+ij)/2)v)·P⁻¹` is a symplectic basis, and `Ω(τ) = F'(τ)⁻¹E(τ)` is a
period matrix of the principally polarized QM surface `A_τ = ℂ²/Λ_τ` (symmetric with positive
definite imaginary part: VERIFIED numerically; the other normalization `E⁻¹F'` belongs to `-E`). -/

/-- `ι(x)·(τ, 1)ᵀ`. -/
def latVec (x : B) (τ : ℂ) : Fin 2 → ℂ := (iota x).map (fun r : ℝ => (r : ℂ)) *ᵥ ![τ, 1]

/-- `E(τ)`: columns `ι(1)v_τ`, `ι(i)v_τ`. -/
def Emat (τ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun r c => ![latVec (oBasis 0) τ, latVec (oBasis 1) τ] c r

/-- `F₀(τ)`: columns `ι((1+j)/2)v_τ`, `ι((i+ij)/2)v_τ`. -/
def F0mat (τ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun r c => ![latVec (oBasis 2) τ, latVec (oBasis 3) τ] c r

/-- `P⁻¹` for `P = [[-1,1],[1,-2]]`. -/
def Pinv : Matrix (Fin 2) (Fin 2) ℂ := !![-2, -1; -1, -1]

/-- The period matrix `Ω(τ) = (F₀(τ)P⁻¹)⁻¹E(τ)` of the QM surface at `τ`. -/
def Omega (τ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := (F0mat τ * Pinv)⁻¹ * Emat τ

/-! ## §5 LEAF: theta modularity (Igusa) -/

/-- **LEAF (Igusa).** `ψ₄ = 2⁻²Σθ_m⁸` and `χ₁₀ = -2⁻¹⁴∏θ_m²` are Siegel modular forms of
weight 4 and 10 for `Sp₄(ℤ)`: for `M = [[A,B],[C,D]] ∈ Sp₄(ℤ)` and `Ω ∈ 𝔥₂`,
`Σθ⁸(M·Ω) = det(CΩ+D)⁴ Σθ⁸(Ω)` and `∏θ²(M·Ω) = det(CΩ+D)¹⁰ ∏θ²(Ω)`.
Sources: Igusa, *On Siegel modular forms of genus two*, Amer. J. Math. 84 (1962), and *Modular
forms and projective invariants*, Amer. J. Math. 89 (1967) (the theta expressions of `ψ₄`,
`χ₁₀`; pages UNVERIFIED); the theta transformation formula (Igusa, *Theta functions*, 1972,
Ch. V, UNVERIFIED). Exact form (signs, weights) VERIFIED numerically on five generators of
`Sp₄(ℤ)` (`theta_modular.py`). -/
def ThetaModularity : Prop :=
  ∀ M ∈ Matrix.symplecticGroup (Fin 2) ℤ, ∀ Ω ∈ SiegelH2,
    thetaSum8 (spAct M Ω) = spFactor M Ω ^ 4 * thetaSum8 Ω ∧
    thetaProd2 (spAct M Ω) = spFactor M Ω ^ 10 * thetaProd2 Ω

/-- **Glue (proved).** The F1 ratio `jNum/jDen` is `Sp₄(ℤ)`-invariant (cross-multiplied), so the
value of F1's theta expression does not depend on the choice of symplectic basis ("permitted
changes of theta structure", N5 L937-938). -/
theorem thetaRatio_invariant (h : ThetaModularity) :
    ∀ M ∈ Matrix.symplecticGroup (Fin 2) ℤ, ∀ Ω ∈ SiegelH2,
      jNum (spAct M Ω) * jDen Ω = jNum Ω * jDen (spAct M Ω) := by
  intro M hM Ω hΩ
  obtain ⟨h1, h2⟩ := h M hM Ω hΩ
  simp only [jNum, jDen, h1, h2]
  ring

/-! ## §6 LEAF: the QM Hauptmodul (A2 and F1, analytic form) -/

/-- **LEAF, COMPOSITE (rv-leaves-a: faithful, but not printed as one theorem; Baba–Granath 2008
Thm 2.1 and the datum of §3 only, not Props. 3.7-3.10; Lin–Yang 2020, arXiv v1 Example 29 (formerly
cited as Ex. 30, v1's discriminant-14 example; corrected 2026-11-12 by loc-fix) with eqs. (13)-(14);
Igusa 1967; Lauter–Naehrig–Yang 2015 §2.2).** On the QM locus, F1's theta expression
`j_θ = 3779136(∏θ_m)⁴/(Σθ_m⁸)⁵ ∘ Ω` is a Hauptmodul of `Γ*\ℍ = X₆/W`, with value `0` at the
CM points of discriminant `-4`, a pole at those of discriminant `-3`, and value `-16/27` at
those of discriminant `-24`.

Formally: there is a continuous `f : ℍ → ℂ ∪ {∞}` equal to `jNum/jDen ∘ Ω` wherever the
denominator is nonzero (so `f` is the meromorphic quotient), whose fibres are exactly the
`Γ*`-orbits, which is surjective, and which takes the three values at the fixed points of
`ι(x)` for `x ∈ 𝒪` with `x² = -1`, `x² - x + 1 = 0`, `x² = -6` respectively (the CM points of
the maximal orders of discriminants `-4, -3, -24`; every such point is the unique elliptic point
of `Γ*` of order 4, 6, 2).

Faithfulness: `Ω` is a period matrix of the polarized QM surface at `τ` (§4); Lin–Yang's
divisors of `ψ₄` and `χ₁₀` on the QM curve `X ≅ P¹` make `χ₁₀²/ψ₄⁵` a degree-one function with
zero at `P₋₄` and pole at `P₋₃`, and Igusa's theta expressions turn `16·144⁵χ₁₀²/ψ₄⁵` into
`jNum/jDen` (§7). This leaf is weaker than what N5 uses at A2: it says nothing about the
`ℚ`-structure (the canonical model; see `docs/research/pkg-I1.md`, leaf I1-a). Numerically
VERIFIED (`qm_embed.py`): invariance under five generators of `Γ*` and a non-torsion unit of
`𝒪¹`; `j_θ = 0` at `√2 + i`, a pole of order 6 in `τ` at `i√3`, `j_θ = -16/27` at `i√(9+6√2)`,
and `j_θ = 81/64` at the disc `-19` point. -/
def QMHauptmodul : Prop :=
  ∃ f : UpperHalfPlane → OnePoint ℂ, Continuous f ∧
    (∀ τ : UpperHalfPlane, jDen (Omega τ) ≠ 0 →
      f τ = ((jNum (Omega τ) / jDen (Omega τ) : ℂ) : OnePoint ℂ)) ∧
    (∀ τ τ' : UpperHalfPlane, f τ = f τ' ↔ ∃ γ ∈ GammaStar, γ • τ = τ') ∧
    Function.Surjective f ∧
    (∀ x : B, InO x → x * x = -1 → ∀ γ : GL (Fin 2) ℝ,
      (γ : Matrix (Fin 2) (Fin 2) ℝ) = iota x → ∀ τ : UpperHalfPlane, γ • τ = τ →
        f τ = ((0 : ℂ) : OnePoint ℂ)) ∧
    (∀ x : B, InO x → x * x - x + 1 = 0 → ∀ γ : GL (Fin 2) ℝ,
      (γ : Matrix (Fin 2) (Fin 2) ℝ) = iota x → ∀ τ : UpperHalfPlane, γ • τ = τ →
        f τ = (OnePoint.infty : OnePoint ℂ)) ∧
    (∀ x : B, InO x → x * x = -6 → ∀ γ : GL (Fin 2) ℝ,
      (γ : Matrix (Fin 2) (Fin 2) ℝ) = iota x → ∀ τ : UpperHalfPlane, γ • τ = τ →
        f τ = ((-16/27 : ℂ) : OnePoint ℂ))

/-! ## §7 F1 algebra (glue, proved)

Lin–Yang's Igusa vector in a weighted representative with scale `λ`
(`J₂ = 12(j+1)λ`, `J₄ = 6(j²+j+1)λ²`, `J₁₀ = j³λ⁵`), Igusa's `ψ₄ = J₂² - 24J₄`, `χ₁₀ = -J₁₀/4`
(eq. (13)-(14) as used at N5 L911-915), and LNY's theta conventions `ψ₄ = Σ/4`, `χ₁₀ = -Π/2¹⁴`
(`Σ = Σθ⁸`, `Π = ∏θ²`) give `j·Σ⁵ = 3779136·Π²`, i.e. N5's
`j = 16·144⁵χ₁₀²/ψ₄⁵ = 3779136(∏θ)⁴/(Σθ⁸)⁵`. -/
theorem f1_algebra {K : Type*} [Field K] [CharZero K] (j lam J2 J4 J10 Sig Pi : K)
    (hJ2 : J2 = 12 * (j + 1) * lam) (hJ4 : J4 = 6 * (j ^ 2 + j + 1) * lam ^ 2)
    (hJ10 : J10 = j ^ 3 * lam ^ 5)
    (hpsi : J2 ^ 2 - 24 * J4 = Sig / 4) (hchi : -J10 / 4 = -Pi / 2 ^ 14) :
    j * Sig ^ 5 = 3779136 * Pi ^ 2 := by
  have hS : Sig = 576 * j * lam ^ 2 := by
    rw [hJ2, hJ4] at hpsi; linear_combination (-4 : K) * hpsi
  have hP : Pi = 4096 * j ^ 3 * lam ^ 5 := by
    rw [hJ10] at hchi; linear_combination (16384 : K) * hchi
  rw [hS, hP]; ring

/-- The constant: `16·144⁵·2⁻²⁸/2⁻¹⁰ = 3779136` (N5 L922-923). -/
theorem f1_constant : (16 * 144 ^ 5 : ℚ) / 2 ^ 18 = 3779136 := by norm_num

/-! ## §8 The pull-back `J(u)` (N5 L381-386, L510-516, L538-541) -/

def Fu (u : ℚ) : ℚ := u * (u + 15) * (u + 20) * (u + 24) * (u + 30) * (u + 60)
def Gu (u : ℚ) : ℚ := 7 * u ^ 2 + 300 * u + 3600
def Hu (u : ℚ) : ℚ :=
  (u ^ 2 - 60 * u - 1800) * (13 * u ^ 2 + 480 * u + 3600) * (11 * u ^ 2 + 600 * u + 7200)
/-- `J(u) = -57600F(u)²/G(u)⁶`. -/
def Ju (u : ℚ) : ℚ := -57600 * Fu u ^ 2 / Gu u ^ 6

/-- **Glue (proved).** `G⁶ - 97200F² = H²` (N5 L514-516). -/
theorem G6_sub_F2 (u : ℚ) : Gu u ^ 6 - 97200 * Fu u ^ 2 = Hu u ^ 2 := by
  simp only [Gu, Fu, Hu]; ring

/-- No rational square root of `3`. -/
theorem rat_sq_ne_three (r : ℚ) : r ^ 2 ≠ 3 := by
  intro h
  have hirr : Irrational (√(3 : ℕ)) := Nat.prime_three.irrational_sqrt
  have h3 : ((r : ℝ)) ^ 2 = 3 := by exact_mod_cast h
  apply hirr
  refine ⟨|r|, ?_⟩
  push_cast
  rw [← Real.sqrt_sq_eq_abs, h3]

theorem quad_ne_zero (u : ℚ) :
    u ^ 2 - 60 * u - 1800 ≠ 0 ∧ 13 * u ^ 2 + 480 * u + 3600 ≠ 0 ∧
      11 * u ^ 2 + 600 * u + 7200 ≠ 0 := by
  refine ⟨fun h => rat_sq_ne_three ((2 * u - 60) / 60) ?_,
    fun h => rat_sq_ne_three ((26 * u + 480) / 120) ?_,
    fun h => rat_sq_ne_three ((22 * u + 600) / 120) ?_⟩
  · field_simp; linear_combination 4 * h
  · field_simp; linear_combination 52 * h
  · field_simp; linear_combination 44 * h

theorem Hu_ne_zero (u : ℚ) : Hu u ≠ 0 := by
  obtain ⟨h1, h2, h3⟩ := quad_ne_zero u
  exact mul_ne_zero (mul_ne_zero h1 h2) h3

theorem Gu_ne_zero (u : ℚ) : Gu u ≠ 0 := by
  unfold Gu; nlinarith [sq_nonneg (7 * u + 150)]

/-- **Glue (proved).** For `u ∈ ℚ \ 𝒞`, `J(u) ≠ 0` (finite since `G(u) ≠ 0`). -/
theorem Ju_ne_zero (u : ℚ) (hu : u ∉ ({0, -15, -20, -24, -30, -60} : Set ℚ)) : Ju u ≠ 0 := by
  have hF : Fu u ≠ 0 := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hu
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hu
    simp only [Fu]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_) ?_) ?_
    · exact h0
    all_goals intro h; first
      | exact h1 (by linarith) | exact h2 (by linarith) | exact h3 (by linarith)
      | exact h4 (by linarith) | exact h5 (by linarith)
  unfold Ju
  exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hF)) (pow_ne_zero 6 (Gu_ne_zero u))

/-- **Glue (proved).** `J(u) + 16/27 = 16H(u)²/(27G(u)⁶)`. -/
theorem Ju_add (u : ℚ) : Ju u + 16 / 27 = 16 * Hu u ^ 2 / (27 * Gu u ^ 6) := by
  have hG : Gu u ≠ 0 := Gu_ne_zero u
  rw [← G6_sub_F2 u]; unfold Ju; field_simp; ring

/-- **Glue (proved).** For every rational `u`, `J(u)` is not the branch value `-16/27`: the
fibre over `J(u)` lies where `Y₃ → P¹_j` is étale (A5, A7; h-trust A5 last item). -/
theorem Ju_ne_branch (u : ℚ) : Ju u ≠ -16 / 27 := by
  intro h
  have h2 := Ju_add u
  rw [h] at h2
  have : 16 * Hu u ^ 2 / (27 * Gu u ^ 6) ≠ 0 :=
    div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 (Hu_ne_zero u)))
      (mul_ne_zero (by norm_num) (pow_ne_zero 6 (Gu_ne_zero u)))
  exact this (by rw [← h2]; norm_num)

/-! ### CM elements of `𝒪` (the hypotheses of the three value clauses of `QMHauptmodul` are
satisfiable; glue, proved) -/

theorem inO_of (x : B) (n : Fin 4 → ℤ) (h : x = ∑ k, (n k : ℚ) • oBasis k) : InO x := ⟨n, h⟩

/-- `i + j ∈ 𝒪`, `(i+j)² = -1` (disc `-4`). -/
theorem cm4 : InO ⟨0, 1, 1, 0⟩ ∧ (⟨0, 1, 1, 0⟩ : B) * ⟨0, 1, 1, 0⟩ = -1 := by
  refine ⟨inO_of _ ![-1, 1, 2, 0] ?_, ?_⟩
  · ext <;> simp [oBasis, Fin.sum_univ_four] <;> norm_num
  · ext <;> simp <;> norm_num

/-- `ω = (1+j)/2 ∈ 𝒪`, `ω² - ω + 1 = 0` (disc `-3`). -/
theorem cm3 : InO ⟨1/2, 0, 1/2, 0⟩ ∧
    (⟨1/2, 0, 1/2, 0⟩ : B) * ⟨1/2, 0, 1/2, 0⟩ - ⟨1/2, 0, 1/2, 0⟩ + 1 = 0 := by
  refine ⟨inO_of _ ![0, 0, 1, 0] ?_, ?_⟩
  · ext <;> simp [oBasis, Fin.sum_univ_four]
  · ext <;> simp <;> norm_num

/-- `μ = 2j + ij ∈ 𝒪`, `μ² = -6` (disc `-24`). -/
theorem cm24 : InO mu ∧ mu * mu = -6 := by
  refine ⟨inO_of _ ![-2, -1, 4, 2] ?_, ?_⟩
  · ext <;> simp [mu, oBasis, Fin.sum_univ_four] <;> norm_num
  · ext <;> simp [mu, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
      QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num

/-! ### Elkies' coordinate (A10 glue, proved): `t = 1 + 27J/16`, `t(u) = H²/G⁶`,
`t(u) - 1 = -3(180F/G³)²` (h-cm 4.1.1) -/

theorem elkies_t (u : ℚ) : 1 + 27 / 16 * Ju u = Hu u ^ 2 / Gu u ^ 6 := by
  have hG : Gu u ≠ 0 := Gu_ne_zero u
  rw [← G6_sub_F2 u]; unfold Ju; field_simp; ring

theorem elkies_t_sub_one (u : ℚ) : 27 / 16 * Ju u = -3 * (180 * Fu u / Gu u ^ 3) ^ 2 := by
  have hG : Gu u ≠ 0 := Gu_ne_zero u
  unfold Ju; field_simp; ring

/-! ## §9 Igusa invariants of binary sextics, and the Clebsch–Bolza–Igusa separation leaf

`J₂, J₄, J₆, J₁₀` of the genus-2 curve `y² = f(x)`, `f = Σ aᵢxⁱ` (`deg f ∈ {5, 6}`), in Igusa's
normalization as computed by PARI's `genus2igusa` (Igusa's invariants of the binary sextic
`4f`). The polynomials were found by exact interpolation on isobaric monomials and checked on 10
fresh random sextics against PARI; `J₁₀ = 2⁸·disc(f)` (`igusa_poly.py`, VERIFIED). -/

section Igusa
variable {K : Type*} [Field K]

end Igusa

/-- Spot checks against PARI `genus2igusa` (VERIFIED by `norm_num`). -/
example : J10 (K := ℚ) ![-1, 0, 0, 0, 0, 1, 0] = 800000 := by decide +kernel
example : J2 (K := ℚ) ![1, 1, 0, 0, 0, 0, 1] = -480 ∧ J4 (K := ℚ) ![1, 1, 0, 0, 0, 0, 1] = 5280 ∧
    J6 (K := ℚ) ![1, 1, 0, 0, 0, 0, 1] = 20480 ∧ J10 (K := ℚ) ![1, 1, 0, 0, 0, 0, 1] = -11143936 := by
  refine ⟨by norm_num [J2], by norm_num [J4], by norm_num [J6], ?_⟩
  decide +kernel
example : J2 (K := ℚ) ![2, -1, 3, 0, 1, -2, 1] = -896 ∧ J4 (K := ℚ) ![2, -1, 3, 0, 1, -2, 1] = 6976 ∧
    J6 (K := ℚ) ![2, -1, 3, 0, 1, -2, 1] = -303616 ∧
    J10 (K := ℚ) ![2, -1, 3, 0, 1, -2, 1] = -2288538368 := by
  refine ⟨by norm_num [J2], by norm_num [J4], by norm_num [J6], ?_⟩
  decide +kernel

/-- **Glue (proved), A7's algebraic step.** If two sextics over an algebraically closed field of
characteristic 0 both have Igusa vector proportional (with weights) to `lyVec j`, `j ≠ 0`, they
are equivalent, i.e. the curves are isomorphic. With Baba–Granath/Lin–Yang (leaf I1-d, not
statable today) this gives "all conjugates of `A` are geometrically isomorphic" for rational `j`. -/
theorem equiv_of_lyVec (hIC : IgusaClebschSeparation) (L : Type) [Field L] [IsAlgClosed L]
    [CharZero L] (j : L) (hj : j ≠ 0) (f g : Fin 7 → L) (lf lg : L) (hlf : lf ≠ 0) (hlg : lg ≠ 0)
    (hf : J2 f = lf * lyVec j 0 ∧ J4 f = lf ^ 2 * lyVec j 1 ∧ J6 f = lf ^ 3 * lyVec j 2 ∧
      J10 f = lf ^ 5 * lyVec j 3)
    (hg : J2 g = lg * lyVec j 0 ∧ J4 g = lg ^ 2 * lyVec j 1 ∧ J6 g = lg ^ 3 * lyVec j 2 ∧
      J10 g = lg ^ 5 * lyVec j 3) :
    ∃ M : Matrix (Fin 2) (Fin 2) L, M.det ≠ 0 ∧ ∃ e : L, e ≠ 0 ∧ g = sexticAct f M e := by
  have h3 : lyVec j 3 ≠ 0 := by simp [lyVec, hj]
  have hf10 : J10 f ≠ 0 := by rw [hf.2.2.2]; exact mul_ne_zero (pow_ne_zero 5 hlf) h3
  have hg10 : J10 g ≠ 0 := by rw [hg.2.2.2]; exact mul_ne_zero (pow_ne_zero 5 hlg) h3
  refine (hIC L f g hf10 hg10).2 ⟨lg / lf, div_ne_zero hlg hlf, ?_, ?_, ?_, ?_⟩
  · rw [hf.1, hg.1]; field_simp
  · rw [hf.2.1, hg.2.1]; field_simp
  · rw [hf.2.2.1, hg.2.2.1]; field_simp
  · rw [hf.2.2.2, hg.2.2.2]; field_simp

end PkgI1


end
end PkgI1Sec

section GlueA6AlgSec
/-! ### Copied from `scratch/glue-a6-alg/A6.lean` lines 47-521 (compiled there; hsyn-fold). -/

namespace GlueA6Alg.Alg

/-! ## 2. Independence over `𝔽₃` -/

/-! ## 3. The core: `T ≅ (ℤ/3^{2k})⁴` is cyclic over `Λ`, and `S - 1` is divisible by `3^k` -/

section Core

variable (k : ℕ)

variable {k}

end Core


/-! ## 4. Transport from a commutative group with `G[3^{2k}] ≅ (ℤ/3^{2k})⁴` -/

section Transport

variable {G : Type*} [CommGroup G] {q : ℕ} {M : Type*} [AddCommGroup M]
  (e : {x : G | x ^ q = 1} ≃ M)

variable {e}
variable (he : ∀ x y : {x : G | x ^ q = 1}, ∀ h : x.1 * y.1 ∈ {x : G | x ^ q = 1},
  e ⟨x.1 * y.1, h⟩ = e x + e y)
include he

end Transport

end GlueA6Alg.Alg

end GlueA6AlgSec

section PkgI2Sec
/-! ### Copied from `scratch/pkg-I2/I2.lean` (compiled there). -/

universe u

open CategoryTheory AlgebraicGeometry Limits
open scoped CategoryTheory.MonObj

namespace PkgI2

/-! ## 1. Purity of the branch locus (SGA 1 X 3.4; Stacks 0BMB), ring form -/

/-! ## 2. Abelian varieties, points, Galois action, inertia, good reduction -/

section AV

variable {K : Type u} [Field K]

end AV

/-! ## 3. Néron–Ogg–Shafarevich and potential good reduction (Serre–Tate 1968) -/

/-! ## 4. Semistable reduction: Grothendieck (SGA 7 IX 3.5, 3.6) and Raynaud (SGA 7 IX 4.7) -/

/-! ## 5. Néron mapping property for abelian schemes, and reduction of torsion -/

section Reduction

variable {K : Type u} [Field K]

end Reduction

/-! ## 6. Structure of torsion (Mumford, *Abelian varieties*, §4) -/

/-! ## 7. Abhyankar's lemma for discrete valuation rings -/

/-! ## 8. Characteristic polynomial independent of `ℓ` (Mumford §19, Thm 4; boundary with I3) -/

/-! ## 9. Glue proved from the leaves -/

section Glue

variable {K : Type u} [Field K]

/-! ## 10. rv-a6-route: A6 (Lemma PR(ii)) by the Raynaud route, from the leaves plus one
pure-algebra glue statement -/

/-- **Glue (pure algebra, not a leaf; to be proved by the project).** Let `G` be a commutative
group whose `3^{2k}`-torsion `T` is isomorphic to `(ℤ/3^{2k})⁴` (`k ≥ 1`), with endomorphisms
`I, J` satisfying `I² = 2`, `J² = -3`, `IJ = -JI` (so `T` is a module over `Λ = ℤ⟨i,j⟩`, whose
`3`-adic completion is the maximal order of the quaternion division algebra over `ℚ₃`), and an
endomorphism `S` commuting with `I, J` with `(S - 1)² = 0` on `T`. Then `S` is the identity on
the `3^k`-torsion. Proof (docs/research/rv-a6-route.md §3): `T/JT` is an `𝔽₉`-space of dimension
1 (dimension 2 would force `J = 3J'` on the free `ℤ/3^{2k}`-module `T`, whence `3·unit = 0`), so
`T` is cyclic, hence free of rank one over `Λ/3^{2k}` by counting; `S - 1` is right
multiplication by some `c` with `c² = 0`, so `v_Π(c) ≥ 2k`, `c ∈ 3^kΛ`, and `S - 1` kills
`3^k T = G[3^k]`. -/
def QuatUnipotentTrivial : Prop :=
  ∀ (G : Type u) [CommGroup G] (k : ℕ), 1 ≤ k → ∀ (I J S : G →* G),
    (∀ x, I (I x) = x ^ 2) → (∀ x, J (J x) * x ^ 3 = 1) → (∀ x, J (I x) * I (J x) = 1) →
    (∀ x, S (I x) = I (S x)) → (∀ x, S (J x) = J (S x)) →
    (∃ e : {x : G | x ^ (3 ^ (2 * k)) = 1} ≃ (Fin (2 * 2) → ZMod (3 ^ (2 * k))),
      ∀ x y : {x : G | x ^ (3 ^ (2 * k)) = 1},
        ∀ h : x.1 * y.1 ∈ {x : G | x ^ (3 ^ (2 * k)) = 1}, e ⟨x.1 * y.1, h⟩ = e x + e y) →
    (∀ x, x ^ (3 ^ (2 * k)) = 1 → S (S x) * (S x)⁻¹ * (S x)⁻¹ * x = 1) →
    ∀ x, x ^ (3 ^ k) = 1 → S x = x

-- hsyn-fold: proved in scratch/glue-a6-alg/A6.lean (copied).
open GlueA6Alg.Alg in
/-- **`QuatUnipotentTrivial` (proved).** -/
theorem quatUnipotentTrivial : QuatUnipotentTrivial.{u} := by
  intro G _ k hk I J S hI hJ hIJ hSI hSJ ⟨e₀, he₀⟩ hS x hx
  let e : {x : G | x ^ (Q k) = 1} ≃ V k := e₀
  have he : ∀ x y : {x : G | x ^ (Q k) = 1}, ∀ h : x.1 * y.1 ∈ {x : G | x ^ (Q k) = 1},
      e ⟨x.1 * y.1, h⟩ = e x + e y := he₀
  -- every `v` is `E a` with `a ∈ G[q]`
  have hv : ∀ v : V k, ∃ a : G, a ^ (Q k) = 1 ∧ E e a = v :=
    fun v => ⟨_, (e.symm v).2, E_symm e v⟩
  let IV := (endV he I).toZModLinearMap (Q k)
  let JV := (endV he J).toZModLinearMap (Q k)
  let SV := (endV he S).toZModLinearMap (Q k)
  have hIV : ∀ g, g ^ (Q k) = 1 → IV (E e g) = E e (I g) := fun g hg => endV_E he I g hg
  have hJV : ∀ g, g ^ (Q k) = 1 → JV (E e g) = E e (J g) := fun g hg => endV_E he J g hg
  have hSV : ∀ g, g ^ (Q k) = 1 → SV (E e g) = E e (S g) := fun g hg => endV_E he S g hg
  have mI := mem_map (q := Q k) I
  have mJ := mem_map (q := Q k) J
  have mS := mem_map (q := Q k) S
  have key := core hk IV JV SV
    (by
      intro v; obtain ⟨a, ha, rfl⟩ := hv v
      rw [hIV a ha, hIV _ (mI a ha), hI, E_pow he a ha, two_smul, two_smul])
    (by
      intro v; obtain ⟨a, ha, rfl⟩ := hv v
      rw [hJV a ha, hJV _ (mJ a ha)]
      have h := congrArg (E e) (hJ a)
      rw [E_mul he _ _ (mJ _ (mJ a ha)) (mem_pow a ha 3), E_pow he a ha, E_one he] at h
      rw [neg_smul, ofNat_smul_eq_nsmul]
      exact eq_neg_of_add_eq_zero_left h)
    (by
      intro v; obtain ⟨a, ha, rfl⟩ := hv v
      rw [hIV a ha, hJV _ (mI a ha), hJV a ha, hIV _ (mJ a ha)]
      have h := congrArg (E e) (hIJ a)
      rw [E_mul he _ _ (mJ _ (mI a ha)) (mI _ (mJ a ha)), E_one he] at h
      exact eq_neg_of_add_eq_zero_left h)
    (by
      intro v; obtain ⟨a, ha, rfl⟩ := hv v
      rw [hIV a ha, hSV _ (mI a ha), hSV a ha, hIV _ (mS a ha), hSI])
    (by
      intro v; obtain ⟨a, ha, rfl⟩ := hv v
      rw [hJV a ha, hSV _ (mJ a ha), hSV a ha, hJV _ (mS a ha), hSJ])
    (by
      intro v; obtain ⟨a, ha, rfl⟩ := hv v
      rw [hSV a ha, hSV _ (mS a ha)]
      have h := congrArg (E e) (hS a ha)
      have m1 := mS _ (mS a ha)
      have m2 := mem_inv _ (mS a ha)
      rw [E_mul he _ _ (mem_mul _ _ (mem_mul _ _ m1 m2) m2) ha,
        E_mul he _ _ (mem_mul _ _ m1 m2) m2, E_mul he _ _ m1 m2, E_inv he _ (mS a ha),
        E_one he] at h
      rw [← h]; module)
  have hxq : x ^ (Q k) = 1 := by
    show x ^ (3 ^ (2 * k)) = 1
    rw [two_mul, pow_add, pow_mul, hx, one_pow]
  have h3 : (3 : R k) ^ k • E e x = 0 := by
    have : (3 : R k) ^ k = ((3 ^ k : ℕ) : R k) := by push_cast; rfl
    rw [this, Nat.cast_smul_eq_nsmul, ← E_pow he x hxq, hx, E_one he]
  have := key (E e x) h3
  rw [hSV x hxq] at this
  exact E_inj e _ _ (mS x hxq) hxq this

section A6

/-- The Galois action of `σ` as a group endomorphism of `A(L)`. -/
noncomputable def galHomPts (A : Grp (Over (Spec (.of K)))) {L : Type u} [CommRing L]
    [Algebra K L] (σ : L ≃ₐ[K] L) : Pts A L →* Pts A L where
  toFun := galAct A σ
  map_one' := galAct_one A σ
  map_mul' := galAct_mul A σ

/-- A homomorphism of group objects `f : A ⟶ A` as a group endomorphism of `A(L)`. -/
noncomputable def endPts (A : Grp (Over (Spec (.of K)))) {L : Type u} [CommRing L]
    [Algebra K L] (f : A ⟶ A) : Pts A L →* Pts A L where
  toFun x := x ≫ f.hom.hom
  map_one' := MonObj.one_comp _
  map_mul' x y := MonObj.mul_comp x y _

/-- **Glue A6 (Lemma PR(ii), Raynaud route), proved from the leaves `NeronOggShafarevich`,
`RaynaudCriterion`, `TorsionStructure` and the pure-algebra glue `QuatUnipotentTrivial`.**
Same statement as `PkgI2.goodReduction_of_QM_rational3` (scratch/pkg-I2/I2.lean). -/
theorem goodReduction_of_QM_rational3_of_alg (hNOS : NeronOggShafarevich.{u})
    (hRay : RaynaudCriterion.{u}) (hTors : TorsionStructure.{u})
    (hAlg : QuatUnipotentTrivial.{u})
    (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K))
    (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O)
    (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A]
    (hdim : topologicalKrullDim A.X.left = ((2 : ℕ) : WithBot ℕ∞))
    (I J : A ⟶ A)
    (hI : ∀ x : Pts A (AlgebraicClosure K), (x ≫ I.hom.hom) ≫ I.hom.hom = x ^ 2)
    (hJ : ∀ x : Pts A (AlgebraicClosure K), (x ≫ J.hom.hom) ≫ J.hom.hom * x ^ 3 = 1)
    (hIJ : ∀ x : Pts A (AlgebraicClosure K),
      (x ≫ I.hom.hom) ≫ J.hom.hom * (x ≫ J.hom.hom) ≫ I.hom.hom = 1)
    (h3 : IsUnit (3 : O))
    (hrat : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      ∀ x ∈ torsion A (AlgebraicClosure K) 3, galAct A σ x = x) :
    HasGoodReduction A O := by
  have : IsProper A.X.hom := IsAbelianVariety.proper
  have : GeometricallyIntegral A.X.hom := IsAbelianVariety.geomIntegral
  have : IsCommMonObj A.X := isCommMonObj_of_isProper_of_geometricallyIntegral A.X
  have h3' : IsUnit ((3 : ℕ) : O) := by exact_mod_cast h3
  have h3K : ((3 : ℕ) : K) ≠ 0 := by
    intro h
    apply h3.ne_zero
    apply Subtype.val_injective
    have h' : (3 : K) = 0 := by exact_mod_cast h
    have e3 : ((3 : O) : K) = 3 := rfl
    rw [e3, h']
    rfl
  -- inertia acts trivially on `A[3^k]` for every `k ≥ 1`
  have key : ∀ k : ℕ, 1 ≤ k → InertiaTrivialOn A w (3 ^ k) := by
    intro k hk σ hσ x hx
    obtain ⟨e, he⟩ := hTors K A 2 (3 ^ (2 * k)) hdim (by positivity)
      (by rw [Nat.cast_pow]; exact pow_ne_zero _ h3K)
    exact hAlg (Pts A (AlgebraicClosure K)) k hk (endPts A I) (endPts A J) (galHomPts A σ)
      hI hJ hIJ (fun x => by
        simp only [galHomPts, endPts, MonoidHom.coe_mk, OneHom.coe_mk, galAct, Category.assoc])
      (fun x => by
        simp only [galHomPts, endPts, MonoidHom.coe_mk, OneHom.coe_mk, galAct, Category.assoc])
      ⟨e, he⟩ (fun y hy => hRay K O w hw A 3 le_rfl h3' hrat σ hσ 3 Nat.prime_three h3'
        (2 * k) y hy) x hx
  -- Néron–Ogg–Shafarevich (c) ⇒ (a)
  refine (hNOS K O w hw A).2.mpr ?_
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => 3 ^ (k + 1)) ?_ ?_
  · intro a b hab
    simpa using (Nat.pow_right_injective (by norm_num : 2 ≤ 3) hab)
  · intro k
    refine ⟨by positivity, ?_, key (k + 1) (by omega)⟩
    rw [Nat.cast_pow]; exact h3'.pow _

-- hsyn-fold: from scratch/glue-a6-alg/A6.lean.
/-- **Glue A6 (Lemma PR(ii), Raynaud route), proved from the three I2 leaves
`NeronOggShafarevich`, `RaynaudCriterion` and `TorsionStructure` alone** (the pure-algebra glue
`QuatUnipotentTrivial` is now a theorem). Same statement as
`PkgI2.goodReduction_of_QM_rational3` (scratch/pkg-I2/I2.lean). -/
theorem goodReduction_of_QM_rational3 (hNOS : NeronOggShafarevich.{u})
    (hRay : RaynaudCriterion.{u}) (hTors : TorsionStructure.{u})
    (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K))
    (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O)
    (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A]
    (hdim : topologicalKrullDim A.X.left = ((2 : ℕ) : WithBot ℕ∞))
    (I J : A ⟶ A)
    (hI : ∀ x : Pts A (AlgebraicClosure K), (x ≫ I.hom.hom) ≫ I.hom.hom = x ^ 2)
    (hJ : ∀ x : Pts A (AlgebraicClosure K), (x ≫ J.hom.hom) ≫ J.hom.hom * x ^ 3 = 1)
    (hIJ : ∀ x : Pts A (AlgebraicClosure K),
      (x ≫ I.hom.hom) ≫ J.hom.hom * (x ≫ J.hom.hom) ≫ I.hom.hom = 1)
    (h3 : IsUnit (3 : O))
    (hrat : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      ∀ x ∈ torsion A (AlgebraicClosure K) 3, galAct A σ x = x) :
    HasGoodReduction A O :=
  goodReduction_of_QM_rational3_of_alg hNOS hRay hTors quatUnipotentTrivial O w hw A hdim I J
    hI hJ hIJ h3 hrat

/-- **A6 without the auxiliary `w`**: the valuation subring of `K̄` over `O` exists
(`GlueA6Alg.Alg.exists_valuationSubring_comap_eq`), so it is not a hypothesis. -/
theorem goodReduction_of_QM_rational3' (hNOS : NeronOggShafarevich.{u})
    (hRay : RaynaudCriterion.{u}) (hTors : TorsionStructure.{u})
    (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A]
    (hdim : topologicalKrullDim A.X.left = ((2 : ℕ) : WithBot ℕ∞))
    (I J : A ⟶ A)
    (hI : ∀ x : Pts A (AlgebraicClosure K), (x ≫ I.hom.hom) ≫ I.hom.hom = x ^ 2)
    (hJ : ∀ x : Pts A (AlgebraicClosure K), (x ≫ J.hom.hom) ≫ J.hom.hom * x ^ 3 = 1)
    (hIJ : ∀ x : Pts A (AlgebraicClosure K),
      (x ≫ I.hom.hom) ≫ J.hom.hom * (x ≫ J.hom.hom) ≫ I.hom.hom = 1)
    (h3 : IsUnit (3 : O))
    (hrat : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      ∀ x ∈ torsion A (AlgebraicClosure K) 3, galAct A σ x = x) :
    HasGoodReduction A O := by
  obtain ⟨w, hw⟩ := GlueA6Alg.Alg.exists_valuationSubring_comap_eq (L := AlgebraicClosure K) O
  exact goodReduction_of_QM_rational3 hNOS hRay hTors O w hw A hdim I J hI hJ hIJ h3 hrat

end A6


end Glue

end PkgI2

end PkgI2Sec

section PkgI3Sec
/-! ### Copied from `scratch/pkg-I3/I3.lean` (compiled there). -/

noncomputable section

-- glue-I3-linalg (hsyn-fix): the linear-algebra glue of C2 and E1, from scratch/glue-I3-linalg/C2.lean §0.
/-! ## 0. Linear-algebra glue (copied from `scratch/glue-I3-linalg/Commutant.lean`, plus
`finrank_commOf_le_of_equiv` and `equivariantDescent`) -/

namespace GlueI3

open Representation

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]

/-! ### Extension of the coefficient field -/

/-! ### E1: a common constituent gives a nonzero equivariant map -/

end GlueI3


/-! ## 1. The `ℓ`-adic Tate module of an abelian group -/

namespace PkgI3.Tate

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (M : Type*) [AddCommGroup M]

variable {ℓ M}

variable {N : Type*} [AddCommGroup N]

end PkgI3.Tate

/-! ## 2. Abelian varieties, their Hom groups, points, Tate modules -/

namespace PkgI3

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

universe u

attribute [instance] AbVar.grp AbVar.proper AbVar.smooth AbVar.geomInt

namespace AbVar

variable {K : Type u} [Field K]

/-- Commutativity is a Mathlib theorem (Stacks 0BFD), not an assumption. -/
instance (A : AbVar K) : IsCommMonObj A.X :=
  isCommMonObj_of_isProper_of_geometricallyIntegral A.X

/-! ### Points over a field extension and the Galois action -/

variable (L : Type u) [Field L] [Algebra K L]

variable {L}

/-! ### `T_ℓ(A)`, `V_ℓ(A)` and the Galois representation -/

variable (ℓ : ℕ) [Fact ℓ.Prime]

variable {ℓ}

variable (ℓ)

end AbVar

end PkgI3

/-! ### Base change -/

namespace PkgI3.AbVar

open CategoryTheory AlgebraicGeometry Limits

variable {K : Type} [Field K]

end PkgI3.AbVar

/-! ## 3. The leaves of package I3

Each leaf is a `Prop` quantified over all fields (resp. number fields) and all abelian varieties
in the sense of `AbVar`; universe `0`. Locators: see `docs/research/pkg-I3.md`. -/

namespace PkgI3

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open AbVar Polynomial
open scoped Quaternion TensorProduct

end PkgI3

/-! ## 4. Glue checks: the leaves are usable with these definitions -/

namespace PkgI3

open CategoryTheory AlgebraicGeometry MonObj AbVar
open scoped TensorProduct

end PkgI3

-- glue-I3-linalg (hsyn-fix): C2 and E1 in pkg-I3's object layer, from scratch/glue-I3-linalg/C2.lean §5.
/-! ## 5. C2 in the object layer of pkg-I3 -/

namespace PkgI3

open GlueI3 AbVar

end PkgI3

-- hsyn-fold: C10 trace comparison, from scratch/glue-c10/Trace.lean (pkg-I3 copy dropped).
namespace PkgI3

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open AbVar Polynomial
open scoped TensorProduct

end PkgI3

end
end PkgI3Sec

section PkgI4Sec
/-! ### Copied from `scratch/pkg-I4/I4.lean` (compiled there). The copy of pkg-I3 inside it is renamed `PkgI4.I3`. -/

/-!
# Package I4 (modularity): leaves statable over Mathlib today

Draft for `docs/research/pkg-I4.md` (task pkg-I4, 2026-11-11). Check with
`lake env lean scratch/pkg-I4/I4.lean`.

* `PkgI4.Cp`, `PkgI4.DR` (first): `𝓞_ℂ_[p]` is `p`-adically complete (instances missing in
  Mathlib), and Mathlib's `BDeRhamPlus`/`BDeRham` are functorial (naturality of `untilt` and of
  Fontaine's `θ`, maps of adic completions, generators of `ker θ`). Used in §1b for the action of
  `G_{ℚ_p}` on `B_dR` and the **de Rham predicate**.
* §0 Galois side over `ℚ̄`: copied, with small changes, from `scratch/hdec-faithful/Leaves.lean`
  §0 (places as valuation subrings, inertia, arithmetic Frobenius, complex conjugation,
  continuous `GL_n(ℚ̄_ℓ)`-representations, characters).
* §1 **new**: the local Galois group `G_{ℚ_p}`, its action on Mathlib's `ℂ_[p]`, the
  `p`-adic cyclotomic character, and **Hodge–Tate multiplicities** (Tate–Sen definition through
  `(ℂ_p(i) ⊗ V)^{G_{ℚ_p}}`, written as a space of equivariant `ℚ_p`-linear maps `V → ℂ_p`).
* §2 modular side: cusp forms on `Γ₁(N)`, nebentypus, normalized eigenforms (Hecke recursion of
  the q-coefficients, as hdec-faithful), representations attached to eigenforms (trace form),
  and **new**: the old space and newforms.
* §1b **new**: the action of `G_{ℚ_p}` on `B_dR = BDeRham 𝓞_ℂ_[p] p`, `ℚ_p ⊆ B_dR` fixed by it,
  `D_dR`, and the **de Rham predicate** `IsDeRham` / `LocalIsDeRham` (genuine; no `sorry`).
* §3 the leaves of I4 that are statable now, as `def … : Prop` (none proved).
* §4 templates — functions of a missing predicate (`IsPst`, the conductor exponent) — and the
  leaf **`PanBerger`** = `PanFor LocalIsDeRham`, statable now. A template is **not** a leaf:
  `PanFor P` says nothing until `P` is the genuine potentially-semistable predicate.
* §5 small glue facts, proved.

Faithfulness caveat: `IsDeRham` and `htMult` are genuine definitions, but no theorem about them is
proved here (e.g. `B_dR^{G_{ℚ_p}} = ℚ_p`, Tate's `ℂ_p(i)^G = 0`). A definitional slip could make a
hypothesis unsatisfiable and a leaf vacuous; the standard non-vacuity checks are listed in
`docs/research/pkg-I4.md` §3.4.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace PkgI4.Cp

open Ideal

variable (p : ℕ) [hp : Fact p.Prime]

theorem mem_O_iff (x : ℂ_[p]) : x ∈ 𝓞_ℂ_[p] ↔ ‖x‖ ≤ 1 := by
  rw [PadicComplex.norm_eq_norm, Valuation.norm_def]
  change (PadicComplex.valued p).v x ≤ 1 ↔ _
  rw [← map_one (PadicComplex.valued p).v, ← Valuation.restrict_le_iff]
  simpa only [map_one, NNReal.coe_le_one] using
    ((Valuation.RankOne.strictMono (PadicComplex.valued p).v).le_iff_le (b := 1)).symm

theorem norm_p : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]),
    IsScalarTower.algebraMap_apply ℚ_[p] (PadicAlgCl p) ℂ_[p], ← PadicComplex.coe_eq,
    PadicComplex.norm_extends, PadicAlgCl.norm_extends, Padic.norm_p]

theorem norm_p_pos : 0 < ‖(p : ℂ_[p])‖ := by
  rw [norm_p]; exact inv_pos.mpr (by exact_mod_cast hp.1.pos)

theorem norm_p_lt_one : ‖(p : ℂ_[p])‖ < 1 := by
  rw [norm_p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.1.one_lt)

/-- `x ∈ p^n 𝓞` iff `‖x‖ ≤ ‖p‖^n`. -/
theorem mem_span_pow_iff (x : 𝓞_ℂ_[p]) (n : ℕ) :
    x ∈ span {(p : 𝓞_ℂ_[p])} ^ n ↔ ‖(x : ℂ_[p])‖ ≤ ‖(p : ℂ_[p])‖ ^ n := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨z, rfl⟩
    have hz : ‖(z : ℂ_[p])‖ ≤ 1 := (mem_O_iff p _).mp z.2
    have e : ((z * (p : 𝓞_ℂ_[p]) ^ n : 𝓞_ℂ_[p]) : ℂ_[p]) = (z : ℂ_[p]) * (p : ℂ_[p]) ^ n := by
      push_cast; rfl
    rw [e, norm_mul, norm_pow]
    calc ‖(z : ℂ_[p])‖ * ‖(p : ℂ_[p])‖ ^ n ≤ 1 * ‖(p : ℂ_[p])‖ ^ n := by gcongr
      _ = _ := one_mul _
  · intro h
    have hpn : (p : ℂ_[p]) ^ n ≠ 0 := pow_ne_zero _ (norm_pos_iff.mp (norm_p_pos p))
    refine ⟨⟨(x : ℂ_[p]) / (p : ℂ_[p]) ^ n, (mem_O_iff p _).mpr ?_⟩, ?_⟩
    · rw [norm_div, norm_pow, div_le_one (pow_pos (norm_p_pos p) n)]
      exact h
    · apply Subtype.ext
      push_cast
      field_simp


theorem smodEq_iff (x y : 𝓞_ℂ_[p]) (n : ℕ) :
    x ≡ y [SMOD (span {(p : 𝓞_ℂ_[p])} ^ n • ⊤ : Submodule 𝓞_ℂ_[p] 𝓞_ℂ_[p])] ↔
      ‖(x : ℂ_[p]) - (y : ℂ_[p])‖ ≤ ‖(p : ℂ_[p])‖ ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, mem_span_pow_iff]
  push_cast
  rfl

instance notIsUnit_p : Fact ¬IsUnit (p : 𝓞_ℂ_[p]) := ⟨fun h => by
  obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp h
  have hv' : (p : ℂ_[p]) * (v : ℂ_[p]) = 1 := by
    have := congrArg (fun z : 𝓞_ℂ_[p] => (z : ℂ_[p])) hv
    push_cast at this
    exact this
  have h1 : ‖(v : ℂ_[p])‖ ≤ 1 := (mem_O_iff p _).mp v.2
  have h2 : ‖(p : ℂ_[p])‖ * ‖(v : ℂ_[p])‖ = 1 := by rw [← norm_mul, hv', norm_one]
  have h3 : ‖(p : ℂ_[p])‖ * ‖(v : ℂ_[p])‖ < 1 :=
    calc ‖(p : ℂ_[p])‖ * ‖(v : ℂ_[p])‖ ≤ ‖(p : ℂ_[p])‖ * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact norm_p_lt_one p
  linarith⟩

theorem tendsto_norm_p_pow :
    Filter.Tendsto (fun n : ℕ => ‖(p : ℂ_[p])‖ ^ n) Filter.atTop (nhds 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (norm_p_lt_one p)

instance isHausdorff : IsHausdorff (span {(p : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p] where
  haus' x hx := by
    have h : ∀ n : ℕ, ‖(x : ℂ_[p])‖ ≤ ‖(p : ℂ_[p])‖ ^ n := fun n => by
      have := (smodEq_iff p x 0 n).mp (hx n)
      simpa using this
    have h0 : ‖(x : ℂ_[p])‖ ≤ 0 := ge_of_tendsto' (tendsto_norm_p_pow p) h
    exact Subtype.ext (by simpa using norm_le_zero_iff.mp h0)

instance isPrecomplete : IsPrecomplete (span {(p : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p] where
  prec' f hf := by
    set g : ℕ → ℂ_[p] := fun n => (f n : ℂ_[p])
    have hmn : ∀ m n, m ≤ n → ‖g m - g n‖ ≤ ‖(p : ℂ_[p])‖ ^ m := fun m n h =>
      (smodEq_iff p _ _ m).mp (hf h)
    have hcs : CauchySeq g := by
      refine cauchySeq_of_le_tendsto_0 (fun N => 2 * ‖(p : ℂ_[p])‖ ^ N) (fun n m N hn hm => ?_) ?_
      · rw [dist_eq_norm]
        calc ‖g n - g m‖ = ‖(g N - g m) - (g N - g n)‖ := by congr 1; ring
          _ ≤ ‖g N - g m‖ + ‖g N - g n‖ := norm_sub_le _ _
          _ ≤ ‖(p : ℂ_[p])‖ ^ N + ‖(p : ℂ_[p])‖ ^ N := add_le_add (hmn N m hm) (hmn N n hn)
          _ = 2 * ‖(p : ℂ_[p])‖ ^ N := by ring
      · simpa using (tendsto_norm_p_pow p).const_mul 2
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcs
    have hL1 : ‖L‖ ≤ 1 :=
      le_of_tendsto' (hL.norm) fun n => (mem_O_iff p _).mp (f n).2
    refine ⟨⟨L, (mem_O_iff p L).mpr hL1⟩, fun n => (smodEq_iff p _ _ n).mpr ?_⟩
    have ht : Filter.Tendsto (fun k => ‖g n - g k‖) Filter.atTop (nhds ‖g n - L‖) :=
      (tendsto_const_nhds.sub hL).norm
    exact le_of_tendsto ht (Filter.eventually_atTop.mpr ⟨n, fun k hk => hmn n k hk⟩)

instance isAdicComplete : IsAdicComplete (span {(p : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p] where

end PkgI4.Cp

namespace PkgI4.DR

open Ideal

variable {R S : Type*} [CommRing R] [CommRing S] (p : ℕ) [Fact p.Prime]

omit [Fact p.Prime] in
theorem span_p_le_comap (f : R →+* S) :
    span {(p : R)} ≤ (span {(p : S)}).comap f := by
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]
  exact Ideal.mem_span_singleton_self _

/-- `R/p → S/p` induced by `f`. -/
def modPMap (f : R →+* S) : ModP R p →+* ModP S p :=
  Ideal.quotientMap _ f (span_p_le_comap p f)

variable [Fact ¬IsUnit (p : R)] [Fact ¬IsUnit (p : S)]

/-- The tilt is functorial: `R♭ → S♭`. -/
def preTiltMap (f : R →+* S) : PreTilt R p →+* PreTilt S p :=
  Perfection.map p (modPMap p f)

theorem coeff_preTiltMap (f : R →+* S) (x : PreTilt R p) (n : ℕ) :
    Perfection.coeff _ p n (preTiltMap p f x) = modPMap p f (Perfection.coeff _ p n x) :=
  rfl

variable [IsAdicComplete (span {(p : R)}) R] [IsAdicComplete (span {(p : S)}) S]

/-- Naturality of `untilt`. -/
theorem untilt_preTiltMap (f : R →+* S) (x : PreTilt R p) :
    PreTilt.untilt (preTiltMap p f x) = f (PreTilt.untilt x) := by
  refine Perfection.teichmuller_spec fun n => ?_
  obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective (Perfection.coeff _ p n x)
  refine ⟨f w, ?_, ?_⟩
  · rw [coeff_preTiltMap, ← hw]
    rfl
  · have h := Perfection.teichmuller_sModEq (p := p) (I := span {(p : R)}) (x := x) (y := w) hw
    rw [SModEq.sub_mem] at h ⊢
    have h' := Ideal.mem_map_of_mem f h
    rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton, map_natCast, map_sub,
      map_pow] at h'
    have h'' := neg_mem h'
    rw [neg_sub] at h''
    exact h''

/-- **Naturality of Fontaine's `θ`**: `θ_S ∘ W(f♭) = f ∘ θ_R`. -/
theorem fontaineTheta_naturality (f : R →+* S) :
    (WittVector.fontaineTheta S p).comp (WittVector.map (preTiltMap p f)) =
      f.comp (WittVector.fontaineTheta R p) := by
  ext x
  refine (IsHausdorff.eq_iff_smodEq (I := span {(p : S)})).mpr fun n => ?_
  rw [smul_eq_mul, Ideal.mul_top, SModEq.idealQuotientMk]
  have key : (Ideal.Quotient.mk (span {(p : S)} ^ n)).comp
      ((WittVector.fontaineTheta S p).comp (WittVector.map (preTiltMap p f))) =
      (Ideal.Quotient.mk (span {(p : S)} ^ n)).comp (f.comp (WittVector.fontaineTheta R p)) := by
    refine WittVector.eq_of_apply_teichmuller_eq _ _ ⟨n, ?_⟩ fun y => ?_
    · rw [← map_natCast (Ideal.Quotient.mk (span {(p : S)} ^ n)), ← map_pow,
        Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow]
      exact Ideal.mem_span_singleton_self _
    · simp only [RingHom.comp_apply, WittVector.map_teichmuller,
        WittVector.fontaineTheta_teichmuller, untilt_preTiltMap]
  exact congrArg (fun g => g x) key


/-! ### Functoriality of adic completions of rings -/

section AdicMap

variable {A B : Type*} [CommRing A] [CommRing B] (J : Ideal A) (J' : Ideal B) (g : A →+* B)
  (hg : J ≤ J'.comap g)

include hg in
theorem pow_le_comap (n : ℕ) : J ^ n ≤ (J' ^ n).comap g := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr hg) n

theorem factorPow_evalₐ {m n : ℕ} (hle : m ≤ n) (x : AdicCompletion J A) :
    Ideal.Quotient.factorPow J hle (AdicCompletion.evalₐ J n x) = AdicCompletion.evalₐ J m x := by
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective J A x
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, ← AdicCompletion.Ideal.mk_eq_mk J hle]
  rfl

/-- `A ⧸ J^n`-components of the map `Â_J → B̂_{J'}`. -/
def adicMapAux (n : ℕ) : AdicCompletion J A →+* B ⧸ J' ^ n :=
  (Ideal.quotientMap (J' ^ n) g (pow_le_comap J J' g hg n)).comp
    (AdicCompletion.evalₐ J n : AdicCompletion J A →+* A ⧸ J ^ n)

theorem adicMapAux_compat {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow J' hle).comp (adicMapAux J J' g hg n) = adicMapAux J J' g hg m := by
  ext x
  simp only [RingHom.comp_apply, adicMapAux]
  erw [← factorPow_evalₐ J hle x]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ J n x)
  erw [← ha]
  rfl

/-- The ring map `Â_J → B̂_{J'}` induced by `g` with `g(J) ⊆ J'`. -/
def adicMap : AdicCompletion J A →+* AdicCompletion J' B :=
  AdicCompletion.liftRingHom J' (adicMapAux J J' g hg) (adicMapAux_compat J J' g hg)

end AdicMap

/-! ### Functoriality of `B_dR^+` -/

section BdR

/-- `W(R♭)[1/p] → W(S♭)[1/p]`. -/
def locMap (f : R →+* S) :
    Localization.Away (p : WittVector p (PreTilt R p)) →+*
      Localization.Away (p : WittVector p (PreTilt S p)) :=
  Localization.awayLift ((algebraMap _ _).comp (WittVector.map (preTiltMap p f))) _ (by
    rw [RingHom.comp_apply, map_natCast]
    exact IsLocalization.Away.algebraMap_isUnit _)

/-- `R[1/p] → S[1/p]`. -/
def locMapBase (f : R →+* S) : Localization.Away (p : R) →+* Localization.Away (p : S) :=
  Localization.awayLift ((algebraMap _ _).comp f) _ (by
    rw [RingHom.comp_apply, map_natCast]
    exact IsLocalization.Away.algebraMap_isUnit _)

/-- Naturality of `θ[1/p]`. -/
theorem fontaineThetaInvertP_naturality (f : R →+* S) :
    (fontaineThetaInvertP S p).comp (locMap p f) =
      (locMapBase p f).comp (fontaineThetaInvertP R p) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (p : WittVector p (PreTilt R p)))
  ext w
  simp only [RingHom.comp_apply, locMap, locMapBase, fontaineThetaInvertP,
    Localization.awayLift, IsLocalization.Away.lift, IsLocalization.lift_eq]
  rw [← RingHom.comp_apply (WittVector.fontaineTheta S p), fontaineTheta_naturality]
  rfl

theorem ker_le_comap_locMap (f : R →+* S) :
    RingHom.ker (fontaineThetaInvertP R p) ≤
      (RingHom.ker (fontaineThetaInvertP S p)).comap (locMap p f) := by
  intro x hx
  rw [Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply,
    fontaineThetaInvertP_naturality, RingHom.comp_apply, RingHom.mem_ker.mp hx, map_zero]

/-- **Functoriality of `B_dR^+`**: `B_dR^+(R) → B_dR^+(S)` for `f : R →+* S`. -/
def bdrPlusMap (f : R →+* S) : BDeRhamPlus R p →+* BDeRhamPlus S p :=
  adicMap _ _ (locMap p f) (ker_le_comap_locMap p f)

end BdR


/-! ### Inverse pairs, generators of `ker θ`, and the map on `B_dR` -/

section Inverse

variable (f : R →+* S) (g : S →+* R) (hgf : ∀ x, g (f x) = x)

include hgf in
theorem modPMap_comp_eq_id (y : ModP R p) : modPMap p g (modPMap p f y) = y := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  change Ideal.Quotient.mk _ (g (f x)) = _
  rw [hgf]

include hgf in
theorem preTiltMap_comp_eq_id (y : PreTilt R p) : preTiltMap p g (preTiltMap p f y) = y :=
  Perfection.ext fun n => by
    rw [coeff_preTiltMap, coeff_preTiltMap, modPMap_comp_eq_id p f g hgf]

include hgf in
theorem wittMap_comp_eq_id (y : WittVector p (PreTilt R p)) :
    WittVector.map (preTiltMap p g) (WittVector.map (preTiltMap p f) y) = y := by
  ext n
  rw [WittVector.map_coeff, WittVector.map_coeff, preTiltMap_comp_eq_id p f g hgf]

include hgf in
theorem locMap_comp_eq_id (y : Localization.Away (p : WittVector p (PreTilt R p))) :
    locMap p g (locMap p f y) = y := by
  have h : (locMap p g).comp (locMap p f) = RingHom.id _ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (p : WittVector p (PreTilt R p)))
    ext w
    simp only [RingHom.comp_apply, RingHom.id_apply, locMap, Localization.awayLift,
      IsLocalization.Away.lift, IsLocalization.lift_eq]
    rw [wittMap_comp_eq_id p f g hgf]
  exact congrArg (fun φ => φ y) h


include hgf in
/-- If `ker θ_R[1/p] = (a)`, then `ker θ_S[1/p] = (locMap f a)` (for an isomorphism `f`). -/
theorem ker_eq_span_locMap (hfg : ∀ y, f (g y) = y)
    (a : Localization.Away (p : WittVector p (PreTilt R p)))
    (ha : RingHom.ker (fontaineThetaInvertP R p) = Ideal.span {a}) :
    RingHom.ker (fontaineThetaInvertP S p) = Ideal.span {locMap p f a} := by
  apply le_antisymm
  · intro x hx
    have h1 : locMap p g x ∈ RingHom.ker (fontaineThetaInvertP R p) :=
      ker_le_comap_locMap p g hx
    rw [ha, Ideal.mem_span_singleton'] at h1
    obtain ⟨c, hc⟩ := h1
    rw [Ideal.mem_span_singleton']
    refine ⟨locMap p f c, ?_⟩
    rw [← map_mul, hc, locMap_comp_eq_id p g f hfg]
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    refine ker_le_comap_locMap p f ?_
    rw [ha]
    exact Ideal.mem_span_singleton_self a

end Inverse

section AdicOf

variable {A B : Type*} [CommRing A] [CommRing B] (J : Ideal A) (J' : Ideal B) (g : A →+* B)
  (hg : J ≤ J'.comap g)

theorem adicMap_evalₐ (n : ℕ) (x : AdicCompletion J A) :
    AdicCompletion.evalₐ J' n (adicMap J J' g hg x) = adicMapAux J J' g hg n x := by
  unfold adicMap
  exact AdicCompletion.evalₐ_liftRingHom _ _ (adicMapAux_compat J J' g hg) n x

theorem adicMap_of (x : A) :
    adicMap J J' g hg (AdicCompletion.of J A x) = AdicCompletion.of J' B (g x) := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [adicMap_evalₐ, AdicCompletion.evalₐ_of]
  simp only [adicMapAux, RingHom.comp_apply]
  erw [AdicCompletion.evalₐ_of]

end AdicOf

section BdRMap


/-- The submonoid of `B_dR^+(R)` inverted in Mathlib's `BDeRham R p`. -/
def genMonoid (T : Type*) [CommRing T] [Fact ¬IsUnit (p : T)]
    [IsAdicComplete (span {(p : T)}) T] : Submonoid (BDeRhamPlus T p) :=
  Submonoid.closure <| AdicCompletion.of (RingHom.ker (fontaineThetaInvertP T p)) _ ''
    {a | RingHom.ker (fontaineThetaInvertP T p) = Ideal.span {a}}

theorem genMonoid_le_comap (f : R →+* S) (g : S →+* R) (hgf : ∀ x, g (f x) = x)
    (hfg : ∀ y, f (g y) = y) :
    genMonoid p R ≤ (genMonoid p S).comap (bdrPlusMap p f) := by
  rw [genMonoid, Submonoid.closure_le]
  rintro _ ⟨a, ha, rfl⟩
  apply Submonoid.subset_closure
  refine ⟨locMap p f a, (ker_eq_span_locMap p f g hgf hfg a ha), ?_⟩
  exact (adicMap_of _ _ _ _ a).symm

/-- **The map on `B_dR`** induced by a ring isomorphism `f` (with inverse `g`). Mathlib's
`BDeRham R p` is by definition `Localization (genMonoid p R)`. -/
def bdrMap (f : R →+* S) (g : S →+* R) (hgf : ∀ x, g (f x) = x) (hfg : ∀ y, f (g y) = y) :
    Localization (genMonoid p R) →+* Localization (genMonoid p S) :=
  IsLocalization.map (M := genMonoid p R) (T := genMonoid p S) (Localization (genMonoid p S))
    (bdrPlusMap p f) (genMonoid_le_comap p f g hgf hfg)

end BdRMap

end PkgI4.DR

/-! ## Abelian varieties and Tate modules: copied from pkg-I3

Lines 26-335 of `scratch/pkg-I3/I3.lean` on `origin/wip/pkg-I3` (commit 7406c0ae), unchanged:
`PkgI4.I3.Tate.T`, `PkgI4.I3.AbVar`, `AbVar.Pt`, `AbVar.V`, `AbVar.galRep`. Used only by the statement
`DeRhamComparison` (§3). -/

/-! ## 1. The `ℓ`-adic Tate module of an abelian group -/

namespace PkgI4.I3.Tate

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (M : Type*) [AddCommGroup M]

/-- `T_ℓ(M) = lim_n M[ℓⁿ]` (transition maps: multiplication by `ℓ`), realized as the
sequences `(xₙ)` with `x₀ = 0` and `ℓ • xₙ₊₁ = xₙ`; then `xₙ ∈ M[ℓⁿ]`. -/
def T : AddSubgroup (ℕ → M) where
  carrier := {x | x 0 = 0 ∧ ∀ n, ℓ • x (n + 1) = x n}
  add_mem' := by
    rintro x y ⟨hx0, hx⟩ ⟨hy0, hy⟩
    refine ⟨by simp [hx0, hy0], fun n => ?_⟩
    simp [smul_add, hx n, hy n]
  zero_mem' := ⟨rfl, fun n => by simp⟩
  neg_mem' := by
    rintro x ⟨hx0, hx⟩
    refine ⟨by simp [hx0], fun n => ?_⟩
    simp [hx n]

variable {ℓ M}

omit hℓ in
lemma pow_smul_eq_zero {x : ℕ → M} (hx : x ∈ T ℓ M) (n : ℕ) : (ℓ ^ n) • x n = 0 := by
  induction n with
  | zero => simpa using hx.1
  | succ n ih => rw [pow_succ, mul_smul, hx.2 n, ih]

omit hℓ in
lemma nsmul_congr {y : M} {n : ℕ} (hy : (ℓ ^ n) • y = 0) {c d : ℕ}
    (h : (c : ZMod (ℓ ^ n)) = (d : ZMod (ℓ ^ n))) : c • y = d • y := by
  rw [ZMod.natCast_eq_natCast_iff'] at h
  rw [← Nat.mod_add_div' c (ℓ ^ n), ← Nat.mod_add_div' d (ℓ ^ n), add_smul, add_smul,
    mul_smul, mul_smul, hy, smul_zero, smul_zero, h]

instance (n : ℕ) : NeZero (ℓ ^ n) := ⟨pow_ne_zero n hℓ.out.ne_zero⟩

lemma val_cast (a : ℤ_[ℓ]) (n : ℕ) :
    (((PadicInt.toZModPow (n + 1) a).val : ℕ) : ZMod (ℓ ^ n)) = PadicInt.toZModPow n a := by
  rw [← PadicInt.cast_toZModPow n (n + 1) (Nat.le_succ n) a, ZMod.natCast_val]

/-- The `ℤ_ℓ`-action: `(a • x)ₙ = (a mod ℓⁿ) • xₙ`. -/
def smulSeq (a : ℤ_[ℓ]) (x : ℕ → M) : ℕ → M :=
  fun n => (PadicInt.toZModPow n a).val • x n

lemma smulSeq_mem (a : ℤ_[ℓ]) {x : ℕ → M} (hx : x ∈ T ℓ M) : smulSeq a x ∈ T ℓ M := by
  refine ⟨by simp [smulSeq, hx.1], fun n => ?_⟩
  simp only [smulSeq]
  rw [smul_comm, hx.2 n]
  apply nsmul_congr (pow_smul_eq_zero hx n)
  rw [val_cast, ZMod.natCast_zmod_val]

lemma smulSeq_congr {x : ℕ → M} (hx : x ∈ T ℓ M) (n : ℕ) {a : ℤ_[ℓ]} {c : ℕ}
    (h : (c : ZMod (ℓ ^ n)) = PadicInt.toZModPow n a) : smulSeq a x n = c • x n := by
  simp only [smulSeq]
  apply nsmul_congr (pow_smul_eq_zero hx n)
  rw [ZMod.natCast_zmod_val, h]

instance : Module ℤ_[ℓ] (T ℓ M) where
  smul a x := ⟨smulSeq a x.1, smulSeq_mem a x.2⟩
  one_smul x := Subtype.ext <| funext fun n => by
    change smulSeq 1 x.1 n = x.1 n
    rw [smulSeq_congr x.2 n (c := 1) (by simp), one_smul]
  mul_smul a b x := Subtype.ext <| funext fun n => by
    change smulSeq (a * b) x.1 n = smulSeq a (smulSeq b x.1) n
    rw [smulSeq_congr x.2 n (c := (PadicInt.toZModPow n a).val * (PadicInt.toZModPow n b).val)
      (by push_cast; simp), mul_smul]
    rfl
  smul_zero a := Subtype.ext <| funext fun n => by
    change smulSeq a 0 n = 0
    simp [smulSeq]
  smul_add a x y := Subtype.ext <| funext fun n => by
    change smulSeq a (x.1 + y.1) n = smulSeq a x.1 n + smulSeq a y.1 n
    simp [smulSeq, smul_add]
  add_smul a b x := Subtype.ext <| funext fun n => by
    change smulSeq (a + b) x.1 n = smulSeq a x.1 n + smulSeq b x.1 n
    rw [smulSeq_congr x.2 n (c := (PadicInt.toZModPow n a).val + (PadicInt.toZModPow n b).val)
      (by push_cast; simp), add_smul]
    rfl
  zero_smul x := Subtype.ext <| funext fun n => by
    change smulSeq 0 x.1 n = 0
    simp [smulSeq]

@[simp] lemma smul_apply (a : ℤ_[ℓ]) (x : T ℓ M) (n : ℕ) :
    (a • x).1 n = (PadicInt.toZModPow n a).val • x.1 n := rfl

variable {N : Type*} [AddCommGroup N]

/-- Functoriality: a group homomorphism `M → N` induces a `ℤ_ℓ`-linear map `T_ℓ M → T_ℓ N`. -/
def map (φ : M →+ N) : T ℓ M →ₗ[ℤ_[ℓ]] T ℓ N where
  toFun x := ⟨fun n => φ (x.1 n), by simp [x.2.1], fun n => by rw [← map_nsmul, x.2.2 n]⟩
  map_add' x y := Subtype.ext <| funext fun n => by simp
  map_smul' a x := Subtype.ext <| funext fun n => by simp [map_nsmul]

@[simp] lemma map_apply (φ : M →+ N) (x : T ℓ M) (n : ℕ) : (map φ x).1 n = φ (x.1 n) := rfl

end PkgI4.I3.Tate

/-! ## 2. Abelian varieties, their Hom groups, points, Tate modules -/

namespace PkgI4.I3

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

universe u

/-- An abelian variety over a field `K`: a group object in schemes over `Spec K` whose structure
morphism is proper, smooth and geometrically integral (Mumford §4, Milne 1986 §1). -/
structure AbVar (K : Type u) [Field K] where
  /-- the underlying `K`-scheme -/
  X : Over (Spec (CommRingCat.of K))
  [grp : GrpObj X]
  [proper : IsProper X.hom]
  [smooth : Smooth X.hom]
  [geomInt : GeometricallyIntegral X.hom]

attribute [instance] AbVar.grp AbVar.proper AbVar.smooth AbVar.geomInt

namespace AbVar

variable {K : Type u} [Field K]

/-- Commutativity is a Mathlib theorem (Stacks 0BFD), not an assumption. -/
instance (A : AbVar K) : IsCommMonObj A.X :=
  isCommMonObj_of_isProper_of_geometricallyIntegral A.X

/-- The dimension of `A` (Krull dimension of the underlying space). -/
def dim (A : AbVar K) : WithBot ℕ∞ := topologicalKrullDim A.X.left

/-- The homomorphisms `A → B` of group schemes over `K`, as a subgroup of the commutative group
of all `K`-morphisms `A → B` (pointwise product, `Hom.commGroup`). -/
def homGroup (A B : AbVar K) : Subgroup (A.X ⟶ B.X) where
  carrier := {f | IsMonHom f}
  one_mem' := by
    change IsMonHom (toUnit A.X ≫ η[B.X])
    infer_instance
  mul_mem' := by
    rintro f g (hf : IsMonHom f) (hg : IsMonHom g)
    change IsMonHom (lift f g ≫ μ[B.X])
    infer_instance
  inv_mem' := by
    rintro f (hf : IsMonHom f)
    change IsMonHom f⁻¹
    infer_instance

/-- `Hom_K(A, B)`, written additively (a `ℤ`-module). -/
abbrev Hom (A B : AbVar K) : Type u := Additive (homGroup A B)

/-- The underlying morphism of schemes. -/
def Hom.hom {A B : AbVar K} (f : Hom A B) : A.X ⟶ B.X := (Additive.toMul f).1

instance {A B : AbVar K} (f : Hom A B) : IsMonHom f.hom := (Additive.toMul f).2

lemma Hom.ext' {A B : AbVar K} {f g : Hom A B} (h : f.hom = g.hom) : f = g :=
  Additive.toMul.injective (Subtype.ext h)

/-- Package a homomorphism. -/
def Hom.mk' {A B : AbVar K} (f : A.X ⟶ B.X) [IsMonHom f] : Hom A B :=
  Additive.ofMul ⟨f, ‹_›⟩

@[simp] lemma Hom.hom_mk' {A B : AbVar K} (f : A.X ⟶ B.X) [IsMonHom f] :
    (Hom.mk' f).hom = f := rfl
@[simp] lemma Hom.hom_add {A B : AbVar K} (f g : Hom A B) : (f + g).hom = f.hom * g.hom := rfl
@[simp] lemma Hom.hom_zero {A B : AbVar K} : (0 : Hom A B).hom = 1 := rfl

/-- The endomorphism ring `End_K(A)`, with multiplication `f * g = f ∘ g`. -/
abbrev End (A : AbVar K) : Type u := Hom A A

instance (A : AbVar K) : Ring (End A) :=
  { (inferInstance : AddCommGroup (End A)) with
    mul := fun f g => Hom.mk' (g.hom ≫ f.hom)
    one := Hom.mk' (𝟙 _)
    mul_assoc := fun f g h => Hom.ext' (by simp [HMul.hMul, Mul.mul])
    one_mul := fun f => Hom.ext' (by simp [HMul.hMul, Mul.mul, OfNat.ofNat, One.one])
    mul_one := fun f => Hom.ext' (by simp [HMul.hMul, Mul.mul, OfNat.ofNat, One.one])
    left_distrib := fun f g h => Hom.ext' (by
      change (g + h).hom ≫ f.hom = g.hom ≫ f.hom * h.hom ≫ f.hom
      simp [MonObj.mul_comp])
    right_distrib := fun f g h => Hom.ext' (by
      change h.hom ≫ (f + g).hom = h.hom ≫ f.hom * h.hom ≫ g.hom
      simp [MonObj.comp_mul])
    zero_mul := fun f => Hom.ext' (by
      change f.hom ≫ (1 : A.X ⟶ A.X) = 1
      simp)
    mul_zero := fun f => Hom.ext' (by
      change (1 : A.X ⟶ A.X) ≫ f.hom = 1
      simp) }

/-- The endomorphism algebra `End⁰_K(A) = ℚ ⊗ End_K(A)`. -/
abbrev End0 (A : AbVar K) : Type u := TensorProduct ℤ ℚ (End A)

/-- A morphism of `K`-schemes is an isogeny-type map: finite and surjective. -/
def IsIsogenyMor {X Y : Over (Spec (CommRingCat.of K))} (f : X ⟶ Y) : Prop :=
  IsFinite f.left ∧ Surjective f.left

/-! ### Points over a field extension and the Galois action -/

variable (L : Type u) [Field L] [Algebra K L]

/-- `Spec L` as a `K`-scheme. -/
def ptObj : Over (Spec (CommRingCat.of K)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L)))

/-- The group `A(L)` of `L`-points: `K`-morphisms `Spec L → A`. -/
abbrev Pt (A : AbVar K) : Type u := ptObj (K := K) L ⟶ A.X

variable {L}

/-- `σ ∈ Aut_K(L)` acting on `Spec L` over `K`. -/
def galHom (σ : L ≃ₐ[K] L) : ptObj (K := K) L ⟶ ptObj L :=
  Over.homMk (Spec.map (CommRingCat.ofHom (σ : L →+* L))) (by
    simp only [ptObj, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp)

lemma galHom_one : galHom (1 : L ≃ₐ[K] L) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom ((1 : L ≃ₐ[K] L) : L →+* L)) = 𝟙 (Spec (CommRingCat.of L))
  rw [show CommRingCat.ofHom ((1 : L ≃ₐ[K] L) : L →+* L) = 𝟙 _ from by ext; rfl]
  exact Spec.map_id _

lemma galHom_mul (σ τ : L ≃ₐ[K] L) : galHom (σ * τ) = galHom σ ≫ galHom τ := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom ((σ * τ : L ≃ₐ[K] L) : L →+* L)) =
    Spec.map (CommRingCat.ofHom (σ : L →+* L)) ≫ Spec.map (CommRingCat.ofHom (τ : L →+* L))
  rw [← Spec.map_comp]
  congr 1

/-- The Galois action on `A(L)`: `σ • P = P ∘ Spec(σ)`, i.e. `σ` applied to coordinates. -/
def galAct (A : AbVar K) (σ : L ≃ₐ[K] L) : A.Pt L →* A.Pt L where
  toFun P := galHom σ ≫ P
  map_one' := MonObj.comp_one _
  map_mul' _ _ := MonObj.comp_mul _ _ _

/-- A homomorphism `f : A → B` acting on `L`-points. -/
def ptMap {A B : AbVar K} (f : Hom A B) : A.Pt L →* B.Pt L := IsMonHom.monoidHom f.hom _

/-! ### `T_ℓ(A)`, `V_ℓ(A)` and the Galois representation -/

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- `T_ℓ(A) = lim A(K̄)[ℓⁿ]`, a `ℤ_ℓ`-module. -/
abbrev T (A : AbVar K) : Type u := Tate.T ℓ (Additive (A.Pt (AlgebraicClosure K)))

/-- `V_ℓ(A) = ℚ_ℓ ⊗_{ℤ_ℓ} T_ℓ(A)`. -/
abbrev V (A : AbVar K) : Type u := TensorProduct ℤ_[ℓ] ℚ_[ℓ] (A.T ℓ)

variable {ℓ}

/-- Galois action on `T_ℓ(A)`. -/
def galT (A : AbVar K) (σ : Field.absoluteGaloisGroup K) : A.T ℓ →ₗ[ℤ_[ℓ]] A.T ℓ :=
  Tate.map (MonoidHom.toAdditive (A.galAct σ))

/-- A homomorphism acting on Tate modules. -/
def homT {A B : AbVar K} (f : Hom A B) : A.T ℓ →ₗ[ℤ_[ℓ]] B.T ℓ :=
  Tate.map (MonoidHom.toAdditive (ptMap f))

/-- Galois-equivariance of a `ℤ_ℓ`-linear map of Tate modules. -/
def IsGalEquivariant {A B : AbVar K} (φ : A.T ℓ →ₗ[ℤ_[ℓ]] B.T ℓ) : Prop :=
  ∀ (σ : Field.absoluteGaloisGroup K) (x : A.T ℓ), φ (A.galT σ x) = B.galT σ (φ x)

variable (ℓ)

/-- The Galois representation `ρ_ℓ : G_K → GL(V_ℓ(A))`. -/
def galRep (A : AbVar K) : Representation ℚ_[ℓ] (Field.absoluteGaloisGroup K) (A.V ℓ) where
  toFun σ := (A.galT (ℓ := ℓ) σ).baseChange ℚ_[ℓ]
  map_one' := by
    have : A.galT (ℓ := ℓ) 1 = LinearMap.id := by
      apply LinearMap.ext; intro x; apply Subtype.ext; funext n
      change Additive.ofMul (galHom (1 : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) ≫
        Additive.toMul (x.1 n)) = x.1 n
      rw [galHom_one, Category.id_comp]; rfl
    change (A.galT (ℓ := ℓ) 1).baseChange ℚ_[ℓ] = LinearMap.id
    rw [this, LinearMap.baseChange_id]
  map_mul' σ τ := by
    have : A.galT (ℓ := ℓ) (σ * τ) = A.galT σ ∘ₗ A.galT τ := by
      apply LinearMap.ext; intro x; apply Subtype.ext; funext n
      have h := galHom_mul (K := K) (L := AlgebraicClosure K) σ τ
      change Additive.ofMul (galHom (σ * τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) ≫
        Additive.toMul (x.1 n)) = Additive.ofMul (galHom σ ≫ galHom τ ≫ Additive.toMul (x.1 n))
      exact (congrArg (fun g => Additive.ofMul (g ≫ Additive.toMul (x.1 n))) h).trans
        (by rw [Category.assoc])
    change (A.galT (ℓ := ℓ) (σ * τ)).baseChange ℚ_[ℓ] =
      (A.galT σ).baseChange ℚ_[ℓ] ∘ₗ (A.galT τ).baseChange ℚ_[ℓ]
    rw [this, LinearMap.baseChange_comp]

/-- The action of `Hom(A, B)` on Tate modules, as a group homomorphism. -/
def tateHom (A B : AbVar K) : Hom A B →+ (A.T ℓ →ₗ[ℤ_[ℓ]] B.T ℓ) where
  toFun f := homT f
  map_zero' := by
    apply LinearMap.ext; intro x; apply Subtype.ext; funext n
    simp [homT, ptMap, IsMonHom.monoidHom]
  map_add' f g := by
    apply LinearMap.ext; intro x; apply Subtype.ext; funext n
    simp [homT, ptMap, IsMonHom.monoidHom, MonObj.comp_mul]

/-- The `ℤ_ℓ`-linear extension `ℤ_ℓ ⊗_ℤ Hom(A, B) → Hom_{ℤ_ℓ}(T_ℓ A, T_ℓ B)`, `a ⊗ f ↦ a · T_ℓ(f)`. -/
def tateHomZl (A B : AbVar K) :
    TensorProduct ℤ ℤ_[ℓ] (Hom A B) →ₗ[ℤ] (A.T ℓ →ₗ[ℤ_[ℓ]] B.T ℓ) :=
  TensorProduct.lift
    (LinearMap.mk₂ ℤ (fun (a : ℤ_[ℓ]) (f : Hom A B) => a • tateHom ℓ A B f)
      (fun a b f => add_smul a b _)
      (fun n a f => by rw [smul_assoc])
      (fun a f g => by rw [map_add, smul_add])
      (fun n a f => by rw [map_zsmul, smul_comm]))

end AbVar

end PkgI4.I3

namespace PkgI4

open scoped MatrixGroups ModularForm

/-! ## §0. Galois side over `ℚ̄` -/

variable {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ}

/-! ## §1. The local Galois group, `ℂ_p`, and Hodge–Tate multiplicities -/

section Local

variable (p : ℕ) [Fact p.Prime]

/-- Every `σ ∈ G_{ℚ_p}` is an isometry of `ℚ̄_p` (Mathlib: `spectralNorm_eq_of_equiv`). -/
theorem norm_gqp_apply (σ : GQp p) (x : PadicAlgCl p) : ‖σ x‖ = ‖x‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
  exact (spectralNorm_eq_of_equiv σ x).symm

theorem continuous_gqp (σ : GQp p) : Continuous σ :=
  (AddMonoidHomClass.isometry_of_norm σ (norm_gqp_apply p σ)).continuous

/-- `σ ∈ G_{ℚ_p}` as a continuous ring endomorphism of `ℚ̄_p`. -/
def gqpRingHom (σ : GQp p) : PadicAlgCl p →+* PadicAlgCl p := σ.toAlgHom.toRingHom

theorem continuous_gqpRingHom (σ : GQp p) : Continuous (gqpRingHom p σ) :=
  continuous_gqp p σ

/-- The action of `σ ∈ G_{ℚ_p}` on `ℂ_p = ℂ_[p]`: the extension of `σ` to the completion. -/
def cpAct (σ : GQp p) : ℂ_[p] →+* ℂ_[p] :=
  UniformSpace.Completion.mapRingHom (gqpRingHom p σ) (continuous_gqpRingHom p σ)

theorem cpAct_coe (σ : GQp p) (x : PadicAlgCl p) :
    cpAct p σ (x : ℂ_[p]) = ((σ x : PadicAlgCl p) : ℂ_[p]) :=
  UniformSpace.Completion.mapRingHom_coe _ x

theorem cpAct_algebraMap (σ : GQp p) (c : ℚ_[p]) :
    cpAct p σ (algebraMap ℚ_[p] ℂ_[p] c) = algebraMap ℚ_[p] ℂ_[p] c := by
  rw [IsScalarTower.algebraMap_apply ℚ_[p] (PadicAlgCl p) ℂ_[p], ← PadicComplex.coe_eq,
    cpAct_coe, AlgEquiv.commutes]

/-- The `p`-adic cyclotomic character `χ : G_{ℚ_p} → ℤ_p^×` (Mathlib's `cyclotomicCharacter`
on `ℚ̄_p`, which contains all `p`-power roots of unity). -/
def cyc (σ : GQp p) : ℤ_[p]ˣ :=
  cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv

/-- `χ(σ)^i ∈ ℚ_p` for `i ∈ ℤ`. -/
def cycPow (σ : GQp p) (i : ℤ) : ℚ_[p] :=
  ((((cyc p σ) ^ i : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p])

variable {E : Type*} [Field E] [Algebra ℚ_[p] E] [FiniteDimensional ℚ_[p] E]

/-- For an `E`-linear representation `ρ` of `G_{ℚ_p}` on `V = E^n` (`E/ℚ_p` finite), the space
`H_i(ρ) = { φ : V →ₗ[ℚ_p] ℂ_p | φ(ρ(σ)v) = χ(σ)^i · σ(φ(v)) }`. It is
`(ℂ_p(i) ⊗_{ℚ_p} V^∨)^{G_{ℚ_p}}` written as equivariant maps. -/
def htSpace (ρ : GQp p →* GL (Fin n) E) (i : ℤ) :
    Submodule ℚ_[p] ((Fin n → E) →ₗ[ℚ_[p]] ℂ_[p]) where
  carrier := {φ | ∀ (σ : GQp p) (v : Fin n → E),
    φ (Matrix.mulVec (ρ σ : Matrix (Fin n) (Fin n) E) v) = cycPow p σ i • cpAct p σ (φ v)}
  zero_mem' := by intro σ v; simp
  add_mem' := by
    intro φ ψ hφ hψ σ v
    simp only [Set.mem_ofPred_eq] at hφ hψ
    simp only [LinearMap.add_apply, hφ σ v, hψ σ v, map_add, smul_add]
  smul_mem' := by
    intro c φ hφ σ v
    simp only [Set.mem_ofPred_eq] at hφ
    simp only [LinearMap.smul_apply, hφ σ v]
    rw [Algebra.smul_def c (φ v), map_mul, cpAct_algebraMap, ← Algebra.smul_def, smul_comm]

/-- **Hodge–Tate multiplicity** of the weight `w`, in the convention of N5 and Pan: the
cyclotomic character has weight `−1`. It is `dim_E (ℂ_p(−w) ⊗ V^∨)^{G}` =
`dim_E (ℂ_p(w) ⊗ V)^{G}`·, computed as `dim_{ℚ_p} H_{−w}(ρ) / [E : ℚ_p]`. (Check: for `V = ℚ_p(1)`,
`H_i ≠ 0` iff `ℂ_p(1−i)^G ≠ 0` iff `i = 1`, i.e. weight `−1`, by Tate's theorem.) -/
def htMult (ρ : GQp p →* GL (Fin n) E) (w : ℤ) : ℕ :=
  Module.finrank ℚ_[p] (htSpace p ρ (-w)) / Module.finrank ℚ_[p] E

/-- `ρ` is Hodge–Tate with weight multiset `S` (`card S = n` makes it Hodge–Tate). -/
def HasHTWeights (ρ : GQp p →* GL (Fin n) E) (S : Multiset ℤ) : Prop :=
  ∀ w : ℤ, htMult p ρ w = S.count w

/-- A `ℚ̄_p`-valued representation of `G_{ℚ_p}` has Hodge–Tate weights `S`: it takes values in
`GL_n(E)` for a finite `E/ℚ_p` inside `ℚ̄_p`, and the `E`-representation has weights `S`. (The
multiplicities do not depend on `E`, by base change; STANDARD.) -/
def LocalHasHTWeights (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)) (S : Multiset ℤ) : Prop :=
  ∃ (E : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] E)
    (ρE : GQp p →* GL (Fin n) E),
    (∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (ρE σ) = ρ σ) ∧
    HasHTWeights p ρE S

/-- `ρ|_{G_{ℚ_p}}` has Hodge–Tate weights `S` (for `ρ` with `ℚ̄_p` coefficients). -/
def GaloisRep.HasHTWeightsAtSelf (ρ : GaloisRep p n) (S : Multiset ℤ) : Prop :=
  LocalHasHTWeights p (ρ.restrictLocal p) S

/-- `ρ|_{G_{ℚ_p}}` has distinct Hodge–Tate weights (2-dimensional case). -/
def GaloisRep.DistinctHTWeights (ρ : GaloisRep p 2) : Prop :=
  ∃ a b : ℤ, a ≠ b ∧ GaloisRep.HasHTWeightsAtSelf (ρ := ρ) p {a, b}


/-! ### Sanity check of the Hodge–Tate convention (given Tate's theorem as a hypothesis) -/

/-- `σ ↦ σ` as ring automorphisms, multiplicatively. -/
def toRingEquivHom : GQp p →* (PadicAlgCl p ≃+* PadicAlgCl p) where
  toFun σ := σ.toRingEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The cyclotomic character `ℚ_p(1)` as a one-dimensional representation over `ℚ_p`. -/
def cycRep : GQp p →* GL (Fin 1) ℚ_[p] :=
  (Units.map (algebraMap ℚ_[p] (Matrix (Fin 1) (Fin 1) ℚ_[p])).toMonoidHom).comp
    ((Units.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]).toMonoidHom).comp
      ((cyclotomicCharacter (PadicAlgCl p) p).comp (toRingEquivHom p)))

theorem cycPow_add_one (σ : GQp p) (j : ℤ) :
    cycPow p σ (j + 1) = cycPow p σ 1 * cycPow p σ j := by
  simp only [cycPow, zpow_add, zpow_one, Units.val_mul, PadicInt.coe_mul]
  ring

theorem cycPow_one_ne_zero (σ : GQp p) : cycPow p σ 1 ≠ 0 := by
  simp only [cycPow, zpow_one]
  intro h
  have := (cyc p σ).ne_zero
  exact this (PadicInt.ext (by simp at h))

set_option synthInstance.maxHeartbeats 200000 in
/-- **Convention check.** If `ℂ_p(j)^{G_{ℚ_p}} = 0` for `j ≠ 0` (Tate's theorem, here a
hypothesis), then `H_i(ℚ_p(1)) = 0` for `i ≠ 1`; so `htMult` of `ℚ_p(1)` vanishes outside the
weight `−1`, which is N5's and Pan's convention. -/
theorem htSpace_cycRep_eq_bot
    (tate : ∀ j : ℤ, j ≠ 0 → ∀ c : ℂ_[p], (∀ σ : GQp p, cycPow p σ j • cpAct p σ c = c) → c = 0)
    (i : ℤ) (hi : i ≠ 1) : htSpace p (cycRep p) i = ⊥ := by
  rw [eq_bot_iff]
  intro φ hφ
  rw [Submodule.mem_bot]
  set e : Fin 1 → ℚ_[p] := fun _ => 1
  have hc : φ e = 0 := by
    refine tate (i - 1) (by omega) (φ e) fun σ => ?_
    have h := hφ σ e
    have hmv : Matrix.mulVec ((cycRep p σ : GL (Fin 1) ℚ_[p]) : Matrix (Fin 1) (Fin 1) ℚ_[p]) e =
        cycPow p σ 1 • e := by
      ext k
      fin_cases k
      simp [cycRep, e, Matrix.mulVec, dotProduct, cycPow, toRingEquivHom, cyc,
        Algebra.algebraMap_eq_smul_one, PadicInt.Coe.ringHom_apply]
      rfl
    rw [hmv, map_smul] at h
    have h2 : cycPow p σ 1 • φ e = (cycPow p σ 1 * cycPow p σ (i - 1)) • cpAct p σ (φ e) := by
      rw [← cycPow_add_one]; simpa using h
    rw [mul_smul] at h2
    exact (smul_right_injective _ (cycPow_one_ne_zero p σ) h2).symm
  refine LinearMap.ext fun v => ?_
  have hv : v = v 0 • e := by
    ext k; fin_cases k; simp [e]
  rw [LinearMap.zero_apply, hv, map_smul, hc, smul_zero]

theorem htMult_cycRep_eq_zero
    (tate : ∀ j : ℤ, j ≠ 0 → ∀ c : ℂ_[p], (∀ σ : GQp p, cycPow p σ j • cpAct p σ c = c) → c = 0)
    (w : ℤ) (hw : w ≠ -1) : htMult p (cycRep p) w = 0 := by
  rw [htMult, htSpace_cycRep_eq_bot p tate (-w) (by omega), finrank_bot, Nat.zero_div]

end Local

/-! ## §1b. The action of `G_{ℚ_p}` on `B_dR` and the de Rham predicate -/

section DeRham

variable (p : ℕ) [Fact p.Prime]

theorem continuous_cpAct (σ : GQp p) : Continuous (cpAct p σ) :=
  UniformSpace.Completion.continuous_map

theorem norm_cpAct (σ : GQp p) (x : ℂ_[p]) : ‖cpAct p σ x‖ = ‖x‖ := by
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (continuous_norm.comp (continuous_cpAct p σ)) continuous_norm
  | ih a => rw [cpAct_coe, PadicComplex.norm_extends, PadicComplex.norm_extends, norm_gqp_apply]

theorem cpAct_inv_apply (σ : GQp p) (x : ℂ_[p]) : cpAct p σ⁻¹ (cpAct p σ x) = x := by
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq ((continuous_cpAct p _).comp (continuous_cpAct p σ)) continuous_id
  | ih a =>
    rw [cpAct_coe, cpAct_coe, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]

/-- `σ` acting on `𝓞_ℂ_[p]`. -/
def oAct (σ : GQp p) : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p] :=
  (cpAct p σ).restrict 𝓞_ℂ_[p] 𝓞_ℂ_[p] fun x hx => by
    rw [Cp.mem_O_iff, norm_cpAct]
    exact (Cp.mem_O_iff p x).mp hx

theorem oAct_inv_apply (σ : GQp p) (x : 𝓞_ℂ_[p]) : oAct p σ⁻¹ (oAct p σ x) = x :=
  Subtype.ext (cpAct_inv_apply p σ x)

theorem oAct_apply_inv (σ : GQp p) (x : 𝓞_ℂ_[p]) : oAct p σ (oAct p σ⁻¹ x) = x := by
  simpa using oAct_inv_apply p σ⁻¹ x

/-- `B_dR = B_dR(𝓞_ℂ_p)`: Mathlib's `BDeRham (𝓞_ℂ_[p]) p`, unfolded (see `bdR_eq`). -/
abbrev BdR := Localization (DR.genMonoid p 𝓞_ℂ_[p])

example : BdR p = BDeRham 𝓞_ℂ_[p] p := rfl

/-- **The action of `G_{ℚ_p}` on `B_dR`**, by functoriality of Mathlib's construction. -/
def bdrAct (σ : GQp p) : BdR p →+* BdR p :=
  DR.bdrMap p (oAct p σ) (oAct p σ⁻¹) (oAct_inv_apply p σ) (oAct_apply_inv p σ)

/-! ### `ℚ_p ⊆ B_dR`, fixed by `G_{ℚ_p}` -/

instance isLocalization_padic : IsLocalization (Submonoid.powers (p : ℤ_[p])) ℚ_[p] where
  map_units := by
    rintro ⟨_, k, rfl⟩
    exact IsUnit.mk0 _ (by simp [Fact.out (p := p.Prime) |>.ne_zero])
  surj z := by
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (by positivity : (0 : ℝ) < 1 / (‖z‖ + 1))
      (by simpa using (Padic.norm_p_lt_one (p := p)))
    refine ⟨⟨⟨(p : ℚ_[p]) ^ k * z, ?_⟩, ⟨(p : ℤ_[p]) ^ k, k, rfl⟩⟩, ?_⟩
    · change ‖(p : ℚ_[p]) ^ k * z‖ ≤ 1
      rw [norm_mul, norm_pow, Padic.norm_p]
      have h1 : (p : ℝ)⁻¹ ^ k * (‖z‖ + 1) < 1 := by
        rwa [lt_div_iff₀ (by positivity)] at hk
      nlinarith [norm_nonneg z, pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p : (0 : ℝ) ≤ p)) k]
    · change z * (((p : ℤ_[p]) ^ k : ℤ_[p]) : ℚ_[p]) = (p : ℚ_[p]) ^ k * z
      push_cast
      ring
  exists_of_eq {x y} h := ⟨1, by
    simp only [OneMemClass.coe_one, one_mul]
    exact PadicInt.ext h⟩

/-- `ℤ_p = W(𝔽_p) → W(𝓞_ℂ_p♭)`. -/
def zpToW : ℤ_[p] →+* WittVector p (PreTilt 𝓞_ℂ_[p] p) :=
  (WittVector.map (ZMod.castHom (dvd_refl p) (PreTilt 𝓞_ℂ_[p] p))).comp
    (WittVector.equiv p).symm.toRingHom

/-- `ℚ_p → W(𝓞_ℂ_p♭)[1/p]`. -/
def qpToLoc : ℚ_[p] →+* Localization.Away (p : WittVector p (PreTilt 𝓞_ℂ_[p] p)) :=
  IsLocalization.lift (M := Submonoid.powers (p : ℤ_[p]))
    (g := (algebraMap _ _).comp (zpToW p)) (by
      rintro ⟨_, k, rfl⟩
      have := (IsLocalization.Away.algebraMap_isUnit
        (S := Localization.Away (p : WittVector p (PreTilt 𝓞_ℂ_[p] p)))
        (p : WittVector p (PreTilt 𝓞_ℂ_[p] p))).pow k
      rw [map_natCast] at this
      simpa only [RingHom.comp_apply, map_pow, map_natCast] using this)

/-- `W(R♭)[1/p] → B_dR^+`. -/
def ofLoc : Localization.Away (p : WittVector p (PreTilt 𝓞_ℂ_[p] p)) →+*
    BDeRhamPlus 𝓞_ℂ_[p] p :=
  algebraMap _ (AdicCompletion (RingHom.ker (fontaineThetaInvertP 𝓞_ℂ_[p] p))
    (Localization.Away (p : WittVector p (PreTilt 𝓞_ℂ_[p] p))))

/-- `ℚ_p → B_dR`. -/
def qpToBdR : ℚ_[p] →+* BdR p :=
  (algebraMap (BDeRhamPlus 𝓞_ℂ_[p] p) (BdR p)).comp ((ofLoc p).comp (qpToLoc p))

theorem wittMap_zpToW (f : PreTilt 𝓞_ℂ_[p] p →+* PreTilt 𝓞_ℂ_[p] p) (z : ℤ_[p]) :
    WittVector.map f (zpToW p z) = zpToW p z := by
  ext n
  simp only [zpToW, RingHom.comp_apply, WittVector.map_coeff]
  exact RingHom.congr_fun (RingHom.ext_zmod (f.comp (ZMod.castHom (dvd_refl p) _))
    (ZMod.castHom (dvd_refl p) _)) _

theorem qpToLoc_algebraMap (z : ℤ_[p]) :
    qpToLoc p (algebraMap ℤ_[p] ℚ_[p] z) = algebraMap _ _ (zpToW p z) :=
  IsLocalization.lift_eq _ _

theorem locMap_algebraMap (f : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p]) (w : WittVector p (PreTilt 𝓞_ℂ_[p] p)) :
    DR.locMap p f (algebraMap _ (Localization.Away (p : WittVector p (PreTilt 𝓞_ℂ_[p] p))) w) =
      algebraMap _ _ (WittVector.map (DR.preTiltMap p f) w) := by
  unfold DR.locMap Localization.awayLift IsLocalization.Away.lift
  rw [IsLocalization.lift_eq]
  rfl

theorem bdrPlusMap_ofLoc (f : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p])
    (y : Localization.Away (p : WittVector p (PreTilt 𝓞_ℂ_[p] p))) :
    DR.bdrPlusMap p f (ofLoc p y) = ofLoc p (DR.locMap p f y) := by
  have e : ∀ y', ofLoc p y' = AdicCompletion.of _ _ y' := fun y' => by
    rw [ofLoc]
    erw [AdicCompletion.algebraMap_apply]
  rw [e, e]
  exact DR.adicMap_of _ _ _ _ y

/-- `G_{ℚ_p}` fixes `ℚ_p ⊆ B_dR`. -/
theorem bdrAct_qpToBdR (σ : GQp p) (c : ℚ_[p]) : bdrAct p σ (qpToBdR p c) = qpToBdR p c := by
  have h : (bdrAct p σ).comp (qpToBdR p) = qpToBdR p := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (p : ℤ_[p]))
    ext z
    simp only [RingHom.comp_apply, qpToBdR]
    rw [qpToLoc_algebraMap, bdrAct, DR.bdrMap, IsLocalization.map_eq, bdrPlusMap_ofLoc,
      locMap_algebraMap, wittMap_zpToW]
  exact congrArg (fun φ => φ c) h

/-- `B_dR` as a `ℚ_p`-algebra (through `qpToBdR`). -/
instance : Algebra ℚ_[p] (BdR p) := (qpToBdR p).toAlgebra

theorem bdrAct_smul (σ : GQp p) (c : ℚ_[p]) (x : BdR p) :
    bdrAct p σ (c • x) = c • bdrAct p σ x := by
  rw [Algebra.smul_def, map_mul, Algebra.smul_def]
  congr 1
  exact bdrAct_qpToBdR p σ c

variable {E : Type*} [Field E] [Algebra ℚ_[p] E] [FiniteDimensional ℚ_[p] E] {n : ℕ}

/-- `D_dR(V^∨) = (B_dR ⊗_{ℚ_p} V^∨)^{G_{ℚ_p}}`, written as `G_{ℚ_p}`-equivariant `ℚ_p`-linear maps
`V → B_dR`, for `V = E^n` with `E`-linear action `ρ`. -/
def ddrSpace (ρ : GQp p →* GL (Fin n) E) : Submodule ℚ_[p] ((Fin n → E) →ₗ[ℚ_[p]] BdR p) where
  carrier := {φ | ∀ (σ : GQp p) (v : Fin n → E),
    φ (Matrix.mulVec (ρ σ : Matrix (Fin n) (Fin n) E) v) = bdrAct p σ (φ v)}
  zero_mem' := by intro σ v; simp
  add_mem' := by
    intro φ ψ hφ hψ σ v
    simp only [Set.mem_ofPred_eq] at hφ hψ
    simp only [LinearMap.add_apply, hφ σ v, hψ σ v, map_add]
  smul_mem' := by
    intro c φ hφ σ v
    simp only [Set.mem_ofPred_eq] at hφ
    simp only [LinearMap.smul_apply, hφ σ v, bdrAct_smul]

/-- **`ρ` is de Rham** (Fontaine): `dim_{ℚ_p} D_dR = dim_{ℚ_p} V`. Stated for `V^∨` (equivalent:
`V` is de Rham iff `V^∨` is; Fontaine, Astérisque 223, Thm 3.8; STANDARD), with `K = ℚ_p`. -/
def IsDeRham (ρ : GQp p →* GL (Fin n) E) : Prop :=
  Module.finrank ℚ_[p] (ddrSpace p ρ) = n * Module.finrank ℚ_[p] E

/-- A `ℚ̄_p`-valued representation of `G_{ℚ_p}` is de Rham: it takes values in `GL_n(E)` for a
finite `E/ℚ_p` inside `ℚ̄_p`, and the `E`-representation is de Rham. -/
def LocalIsDeRham (n : ℕ) (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)) : Prop :=
  ∃ (E : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] E)
    (ρE : GQp p →* GL (Fin n) E),
    (∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (ρE σ) = ρ σ) ∧
    IsDeRham p ρE


/-! ### Sanity check of `IsDeRham` (given `B_dR^{G_{ℚ_p}} = ℚ_p` as a hypothesis) -/

/-- **Normalization check.** If every `G_{ℚ_p}`-invariant of `B_dR` lies in `ℚ_p` (Fontaine's
`B_dR^{G_{ℚ_p}} = ℚ_p`, here a hypothesis) and `ℚ_p → B_dR` is injective, then the trivial
one-dimensional representation is de Rham in the sense of `IsDeRham`. -/
theorem isDeRham_trivial
    (hfix : ∀ x : BdR p, (∀ σ : GQp p, bdrAct p σ x = x) → x ∈ Set.range (qpToBdR p))
    (hinj : Function.Injective (qpToBdR p)) :
    IsDeRham p (1 : GQp p →* GL (Fin 1) ℚ_[p]) := by
  set e : Fin 1 → ℚ_[p] := fun _ => 1
  -- the evaluation-at-`0` functional, followed by `ℚ_p → B_dR`
  set φ₀ : (Fin 1 → ℚ_[p]) →ₗ[ℚ_[p]] BdR p :=
    (LinearMap.proj (R := ℚ_[p]) (φ := fun _ : Fin 1 => ℚ_[p]) 0).smulRight (1 : BdR p)
  have hφ₀ : ∀ v, φ₀ v = qpToBdR p (v 0) := fun v => by
    simp [φ₀, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  have hmem : φ₀ ∈ ddrSpace p (1 : GQp p →* GL (Fin 1) ℚ_[p]) := by
    intro σ v
    simp only [MonoidHom.one_apply, Units.val_one, Matrix.one_mulVec, hφ₀, bdrAct_qpToBdR]
  have hne : φ₀ ≠ 0 := by
    intro h
    have h1 := congrArg (fun ψ => ψ e) h
    simp only [hφ₀, LinearMap.zero_apply, e] at h1
    exact one_ne_zero (hinj (h1.trans (map_zero _).symm))
  have hspan : ddrSpace p (1 : GQp p →* GL (Fin 1) ℚ_[p]) = ℚ_[p] ∙ φ₀ := by
    apply le_antisymm
    · intro φ hφ
      obtain ⟨c, hc⟩ := hfix (φ e) fun σ => by
        have := hφ σ e
        simp only [MonoidHom.one_apply, Units.val_one, Matrix.one_mulVec] at this
        exact this.symm
      rw [Submodule.mem_span_singleton]
      refine ⟨c, LinearMap.ext fun v => ?_⟩
      have hv : v = v 0 • e := by ext k; fin_cases k; simp [e]
      rw [LinearMap.smul_apply, hφ₀, hv, map_smul, ← hc]
      simp [e, Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_comm]
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact hmem
  rw [IsDeRham, hspan, finrank_span_singleton hne, Module.finrank_self]


/-! ### Over a finite extension `F/ℚ_p`, for any `ℚ_p`-linear representation

These forms take a Mathlib `Representation` of `G_F = Field.absoluteGaloisGroup F`, which is the
shape of pkg-I3's `AbVar.galRep` (the Galois action on `V_p(A)`); with them the comparison leaf of
C3 can be stated over genuine definitions (note §1.2). -/

section Over

variable (F : Type*) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]

/-- `G_F → G_{ℚ_p}` (restriction along an embedding `ℚ̄_p → F̄`; Mathlib's
`Field.absoluteGaloisGroup.map`). It is injective with image `G_{F'}`, `F'` the image of `F`. -/
def gfToGqp : Field.absoluteGaloisGroup F →* GQp p :=
  (Field.absoluteGaloisGroup.map (algebraMap ℚ_[p] F) :
    Field.absoluteGaloisGroup F →* Field.absoluteGaloisGroup ℚ_[p])

variable {F} {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]

/-- `D_dR,F(V^∨)` as `G_F`-equivariant `ℚ_p`-linear maps `V → B_dR`. -/
def ddrSpaceOver (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V) :
    Submodule ℚ_[p] (V →ₗ[ℚ_[p]] BdR p) where
  carrier := {φ | ∀ σ v, φ (ρ σ v) = bdrAct p (gfToGqp p F σ) (φ v)}
  zero_mem' := by intro σ v; simp
  add_mem' := by
    intro φ ψ hφ hψ σ v
    simp only [Set.mem_ofPred_eq] at hφ hψ
    simp only [LinearMap.add_apply, hφ σ v, hψ σ v, map_add]
  smul_mem' := by
    intro c φ hφ σ v
    simp only [Set.mem_ofPred_eq] at hφ
    simp only [LinearMap.smul_apply, hφ σ v, bdrAct_smul]

/-- `V` (finite-dimensional over `ℚ_p`) is de Rham as a `G_F`-representation:
`dim_F D_dR,F = dim_{ℚ_p} V`, i.e. `dim_{ℚ_p} D_dR,F = [F:ℚ_p] · dim_{ℚ_p} V`. -/
def IsDeRhamOver (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V) : Prop :=
  Module.finrank ℚ_[p] (ddrSpaceOver p ρ) = Module.finrank ℚ_[p] F * Module.finrank ℚ_[p] V

/-- `H_i` over `F`: `G_F`-equivariant maps `V → ℂ_p(i)`. -/
def htSpaceOver (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V) (i : ℤ) :
    Submodule ℚ_[p] (V →ₗ[ℚ_[p]] ℂ_[p]) where
  carrier := {φ | ∀ σ v,
    φ (ρ σ v) = cycPow p (gfToGqp p F σ) i • cpAct p (gfToGqp p F σ) (φ v)}
  zero_mem' := by intro σ v; simp
  add_mem' := by
    intro φ ψ hφ hψ σ v
    simp only [Set.mem_ofPred_eq] at hφ hψ
    simp only [LinearMap.add_apply, hφ σ v, hψ σ v, map_add, smul_add]
  smul_mem' := by
    intro c φ hφ σ v
    simp only [Set.mem_ofPred_eq] at hφ
    simp only [LinearMap.smul_apply, hφ σ v]
    rw [Algebra.smul_def c (φ v), map_mul, cpAct_algebraMap, ← Algebra.smul_def, smul_comm]

/-- Hodge–Tate multiplicity of `w` for a `G_F`-representation on a `ℚ_p`-space (cyclotomic
weight `−1`): `dim_F (ℂ_p(−w) ⊗ V^∨)^{G_F}`. For `V_p(A)`, `dim A = g`, the multiplicities are
`g` at `0` and `g` at `−1`. -/
def htMultOver (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V) (w : ℤ) : ℕ :=
  Module.finrank ℚ_[p] (htSpaceOver p ρ (-w)) / Module.finrank ℚ_[p] F

end Over

end DeRham

/-! ## §2. Modular side -/

/-! ## §3. Leaves of I4 statable now (statements only; none is proved) -/

/-- **I4-L0. de Rham comparison for abelian varieties, with Hodge–Tate weights** (C3; Fontaine,
LNM 1016 (1983) and Fontaine–Messing (1987) for abelian varieties; Faltings 1989; Tsuji 1999 with
de Jong; Scholze 2013 Cor. 1.8 with Thms 9.1, 9.3 and the 2016 corrigendum; with
`V_p(A) ≅ H¹_et(A_F̄, ℚ_p)^∨`, Mumford §§19-20 / Milne 1986 Thm 15.1(a); numbers UNVERIFIED except
Scholze's wording, VERIFIED by h-leaves §3.1). For an abelian variety `A` of dimension `g` over a
finite extension `F` of `ℚ_p`, `V_p(A)` (pkg-I3's `galRep`) is de Rham as a
`G_F`-representation, with Hodge–Tate weight `0` and `−1` each of multiplicity `g`. Consequence
form. Statable now over genuine definitions: pkg-I3's abelian varieties and Tate modules, and
§1b's `IsDeRhamOver`, `htMultOver`. -/
def DeRhamComparison : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : PkgI4.I3.AbVar F) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
    IsDeRhamOver p (A.galRep p) ∧ htMultOver p (A.galRep p) 0 = g ∧
      htMultOver p (A.galRep p) (-1) = g

/-- **I4-L2. Hodge–Tate weights of eigenform representations, every level** (Faltings, Math.
Ann. 278 (1987) for `k ≥ 2` (level `ℓ ∣ N` UNVERIFIED there); Saito, Invent. Math. 129 (1997)
(pst at `ℓ`, every level; UNVERIFIED); Kato, Astérisque 295 (2004) §§9.2-9.4, (9.2.2) pp. 187-188
(de Rham, every level, newforms; checked by the locator audit), with `NewformOfEigenform` and
Brauer–Nesbitt for general cuspidal eigenforms (hence `ρ.IsSemisimple`); Scholl 1990
with Scholze 2013 and Fontaine's closure). A semisimple `ρ` attached to a normalized eigenform of
weight `k ≥ 2` and any level `N` (including `ℓ ∣ N`) is Hodge–Tate at `ℓ` with weights
`{0, 1 − k}` in the Tate normalization (cyclotomic weight `−1`; h-trust C8). Consequence form
(the published theorems give de Rham or pst, which imply Hodge–Tate with the same weights). -/
def EigenformHT : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : CF N k) (ρ : GaloisRep ℓ 2),
    0 < N → 2 ≤ k → IsNormalizedEigenform g χ → ρ.IsSemisimple → ρ.AttachedTo ιC ιL g →
    GaloisRep.HasHTWeightsAtSelf (ρ := ρ) ℓ {0, 1 - k}

/-- **I4-L3. Deligne–Serre** (Ann. Sci. ÉNS 7 (1974), Thm 4.1, with Chebotarev and
Brauer–Nesbitt, their Lemma 3.2): a semisimple `ρ` attached to a weight-one eigenform has finite
image. Consequence form. Semisimplicity cannot be dropped (a non-split extension can have the same
traces; locator audit, R15). Same as hdec-faithful L27(b). -/
def DeligneSerreFinite : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (ρ : GaloisRep ℓ 2) (N : ℕ) (χ : DirichletCharacter ℂ N) (g : CF N 1),
    0 < N → IsNormalizedEigenform g χ → ρ.IsSemisimple → ρ.AttachedTo ιC ιL g →
    (Set.range ρ.toHom).Finite

/-- **I4-L6. Carayol at unramified primes** (Carayol, Ann. Sci. ÉNS 19 (1986), Théorème (A), pp. 409-411, the
case "conductor exponent 0"; coverage of every `ℓ ≠ p`, including `p ∣ N` and `ℓ = 2`, read by the
locator audit; newform conductor `a(π_p) = v_p(N)`, Casselman 1973, locator UNVERIFIED). For a newform `f` of weight 2 and level `N` and a semisimple `ρ` attached to it, a
prime `p ≠ ℓ` at which `ρ` is unramified does not divide `N`. Consequence form (Théorème (A)
gives `v_p(N) =` the conductor exponent, which is 0 exactly when `ρ` is unramified). -/
def CarayolUnramified : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2) (ρ : GaloisRep ℓ 2) (p : ℕ),
    0 < N → IsNewform f χ → ρ.IsSemisimple → ρ.AttachedTo ιC ιL f →
    p.Prime → p ≠ ℓ → ρ.UnramifiedAt p → ¬ p ∣ N

/-! ## §4. Templates (not leaves) and the statable Pan∘Berger leaf

`PanFor IsPst` is Pan's theorem once `IsPst` is the genuine "potentially semistable in the sense
of Fontaine" predicate on `ℚ̄_p`-representations of `G_{ℚ_p}`; for any other argument it means
nothing. Likewise for `BergerFor`, `CarayolFor`. -/

/-- A predicate on `ℚ̄_p`-valued representations of `G_{ℚ_p}`, for every `p` and `n`. -/
abbrev LocalPred := ∀ (p : ℕ) [Fact p.Prime] (n : ℕ), (GQp p →* GL (Fin n) (PadicAlgCl p)) → Prop

/-- **Template for I4-L7, Pan's theorem** (Pan, J. Amer. Math. Soc. 35 (2022), 1031-1169,
Thm 1.0.4 = arXiv:1901.07166v2 Thm 1.0.4 (statement VERIFIED in h-a011 §1.1 and by the locator
audit from the arXiv source; JAMS numbering UNVERIFIED)), for `p ≥ 5` only: at `p = 3` Pan excludes
`ρ̄|_{G_{ℚ₃}}^{ss} ≅ η ⊕ ηω`, and this leaf does not cover `p = 3`. Pan states the conclusion with
geometric Frobenius (`ρ ≅ ρ_g ⊗ ψ'`); the arithmetic-Frobenius trace form below follows with the
conjugate eigenform `g^ρ` (character `χ̄`) and `ψ = ψ'ε^{1−k}`, by `tr(M⁻¹) = tr M / det M`:
a continuous irreducible `ρ : G_ℚ → GL₂(ℚ̄_p)`, ramified at finitely many primes, potentially
semistable at `p`, odd, with distinct Hodge–Tate weights at `p`, comes from a cuspidal eigenform
up to twist. The conclusion is in trace form: some normalized eigenform `g`, continuous `ψ` and
embeddings with `tr ρ(Frob_q) = ψ(Frob_q) ι(a_q(g))` for almost all `q`. Every reading of
"comes from … up to twist" implies it, in either Frobenius normalization, since
`U^∨ ≅ U ⊗ det U⁻¹` in dimension 2 (h-trust C8; pkg-I4 note §2.1). -/
def PanFor (IsPst : LocalPred) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ ρ : GaloisRep p 2,
    ρ.IsIrreducible → ρ.FinitelyRamified → IsPst p 2 (ρ.restrictLocal p) → ρ.IsOdd →
    GaloisRep.DistinctHTWeights (ρ := ρ) p →
    ∃ (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : CF N k), 0 < N ∧ 1 ≤ k ∧
      IsNormalizedEigenform g χ ∧
      ∃ (ψ : GaloisChar p) (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl p) (S : Finset ℕ),
        ρ.AttachedUpToTwist ψ ιC ιL g S

/-- **I4-L7′. Pan∘Berger — statable now, over genuine definitions.** Pan's Theorem 1.0.4
(`PanFor`, `p ≥ 5`) with "de Rham at `p`" (`LocalIsDeRham`, built in §1b on Mathlib's `BDeRham`)
in place of "potentially semistable at `p`". It is a consequence of Pan 2022 Thm 1.0.4 together
with Berger 2002 Thm 0.7 (de Rham ⇒ pst), and it is the form N5 uses (N5 L734-741 proves de Rham
and then applies Berger). Needs no `B_st`. -/
def PanBerger : Prop :=
  PanFor fun (p : ℕ) [Fact p.Prime] (n : ℕ) (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)) =>
    LocalIsDeRham p n ρ

/-- **Template for I4-L8, Berger's theorem** (Invent. Math. 148 (2002), Théorème 0.7 in the
published numbering (ASTRA-READ), = Thm 0.6 = Thm 5.19 of arXiv:math/0102179v3 (VERIFIED by
rv-h-a011)): de Rham ⇒ potentially semistable. -/
def BergerFor (IsDR IsPst : LocalPred) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)),
    Continuous ρ → IsDR p n ρ → IsPst p n ρ

/-- **I4-L8′. Berger with the genuine de Rham predicate** (template only in `IsPst`). -/
def BergerDR (IsPst : LocalPred) : Prop :=
  BergerFor (fun (p : ℕ) [Fact p.Prime] (n : ℕ) (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)) =>
    LocalIsDeRham p n ρ) IsPst

/-- A conductor-exponent function: `a ℓ ρ p` is the Artin conductor exponent at `p ≠ ℓ` of the
`ℓ`-adic representation `ρ` (Weil–Deligne / Serre's definition). Missing in every library. -/
abbrev CondExp := ∀ (ℓ : ℕ) [Fact ℓ.Prime], GaloisRep ℓ 2 → ℕ → ℕ

/-- **Template for I4-L9, Carayol's Théorème (A)** at `F = ℚ`, weight 2 (the case N5 uses):
for a newform `f` of level `N` and a semisimple `ρ` attached to it, `v_p(N) = a(ρ, p)` for every
prime `p ≠ ℓ`. -/
def CarayolFor (a : CondExp) : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2) (ρ : GaloisRep ℓ 2) (p : ℕ),
    0 < N → IsNewform f χ → ρ.IsSemisimple → ρ.AttachedTo ιC ιL f →
    p.Prime → p ≠ ℓ → a ℓ ρ p = N.factorization p

/-! ## §5. Glue facts, proved -/

/-- **C8 weight comparison** (Tate normalization). If `ρ ≅ ρ_g ⊗ ψ` with `ψ` Hodge–Tate of
weight `n`, the weights of `ρ` are `{n, n + 1 − k}`; if they are `{0, −1}` and `k ≥ 1`, then
`n = 0` and `k = 2`. Stated on multisets. -/
theorem weight_match (n k : ℤ) (hk : 1 ≤ k)
    (h : ({n, n + 1 - k} : Multiset ℤ) = {0, -1}) : n = 0 ∧ k = 2 := by
  have h0 : (0 : ℤ) ∈ ({n, n + 1 - k} : Multiset ℤ) := by rw [h]; simp
  have h1 : (-1 : ℤ) ∈ ({n, n + 1 - k} : Multiset ℤ) := by rw [h]; simp
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at h0 h1
  omega

/-- The same comparison in Pan's cohomological normalization (weights of `ρ_g` are `{0, k−1}`):
`{n, n + k − 1} = {0, −1}` with `k ≥ 1` forces `k = 2`, `n = −1` (twist by `χ¹`; h-trust C8,
rv-h-c8 `weights.py`). -/
theorem weight_match_coh (n k : ℤ) (hk : 1 ≤ k)
    (h : ({n, n + k - 1} : Multiset ℤ) = {0, -1}) : n = -1 ∧ k = 2 := by
  have h0 : (0 : ℤ) ∈ ({n, n + k - 1} : Multiset ℤ) := by rw [h]; simp
  have h1 : (-1 : ℤ) ∈ ({n, n + k - 1} : Multiset ℤ) := by rw [h]; simp
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at h0 h1
  omega

-- hsyn-fold: copied from scratch/leaf-push/PushDR.lean.
/-! ## leaf-push: T23, Fontaine's closure properties of de Rham representations -/

section Fontaine

variable (p : ℕ) [Fact p.Prime]

/-- `σ ↦ ρ(σ)` is continuous for the Krull topology and the `p`-adic topology on matrices. -/
def ContRep {n : ℕ} (ρ : GQp p →* GL (Fin n) ℚ_[p]) : Prop :=
  Continuous fun σ => (ρ σ : Matrix (Fin n) (Fin n) ℚ_[p])

/-- **T23. Fontaine's closure properties.** Published statement: Fontaine, *Représentations
p-adiques des corps locaux I*, Astérisque 223 (1994), Exp. III, §1.5 (admissible representations
for a regular period ring form a Tannakian subcategory: stable under subobjects, quotients, direct
sums, tensor products, duals) applied to `B = B_dR` (regular, Exp. II §3 / Exp. III Thm 3.8;
numbering UNVERIFIED; also Brinon–Conrad, CMI notes, Thm 5.2.1, Prop. 6.3.3, 6.3.8). Lean form,
for continuous `ℚ_p`-linear representations of `G_{ℚ_p}` on `ℚ_pⁿ` and pkg-I4's predicate
`IsDeRham` (`dim_{ℚ_p} D_dR = n`, `D_dR` computed on `V^∨`, which is equivalent by the dual
clause): (i) invariance under change of basis; (ii) duals (`σ ↦ ρ(σ)⁻ᵀ`); (iii) subquotients:
if `ρ` is block upper triangular with diagonal blocks `ρ₁, ρ₂` (`ρ₁` the subrepresentation on
the first `a` coordinates, `ρ₂` the quotient), then `ρ` de Rham ⇒ `ρ₁, ρ₂` de Rham; (iv) direct
sums (block diagonal); (v) tensor products (Kronecker product, reindexed by `Fin a × Fin b ≃
Fin (a * b)`). Every clause is a special case of the published statement (matrix form of the
same representations); (i) is the basis independence of `dim D_dR`, a triviality included so
that the leaf is basis-free. Consequence (matrix form of the published statement). -/
def T23_FontaineClosure : Prop :=
  (∀ (n : ℕ) (ρ ρ' : GQp p →* GL (Fin n) ℚ_[p]) (P : GL (Fin n) ℚ_[p]),
    (∀ σ, ρ' σ = P * ρ σ * P⁻¹) → (IsDeRham p ρ ↔ IsDeRham p ρ')) ∧
  (∀ (n : ℕ) (ρ ρ' : GQp p →* GL (Fin n) ℚ_[p]), ContRep p ρ →
    (∀ σ, (ρ' σ : Matrix (Fin n) (Fin n) ℚ_[p]) =
      ((ρ σ)⁻¹ : GL (Fin n) ℚ_[p]).val.transpose) →
    IsDeRham p ρ → IsDeRham p ρ') ∧
  (∀ (a b : ℕ) (ρ : GQp p →* GL (Fin (a + b)) ℚ_[p]) (ρ₁ : GQp p →* GL (Fin a) ℚ_[p])
    (ρ₂ : GQp p →* GL (Fin b) ℚ_[p]) (X : GQp p → Matrix (Fin a) (Fin b) ℚ_[p]), ContRep p ρ →
    (∀ σ, (ρ σ : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[p]) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (ρ₁ σ : Matrix (Fin a) (Fin a) ℚ_[p]) (X σ) 0
          (ρ₂ σ : Matrix (Fin b) (Fin b) ℚ_[p]))) →
    IsDeRham p ρ → IsDeRham p ρ₁ ∧ IsDeRham p ρ₂) ∧
  (∀ (a b : ℕ) (ρ : GQp p →* GL (Fin (a + b)) ℚ_[p]) (ρ₁ : GQp p →* GL (Fin a) ℚ_[p])
    (ρ₂ : GQp p →* GL (Fin b) ℚ_[p]), ContRep p ρ₁ → ContRep p ρ₂ →
    (∀ σ, (ρ σ : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[p]) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (ρ₁ σ : Matrix (Fin a) (Fin a) ℚ_[p]) 0 0
          (ρ₂ σ : Matrix (Fin b) (Fin b) ℚ_[p]))) →
    IsDeRham p ρ₁ → IsDeRham p ρ₂ → IsDeRham p ρ) ∧
  (∀ (a b : ℕ) (ρ : GQp p →* GL (Fin (a * b)) ℚ_[p]) (ρ₁ : GQp p →* GL (Fin a) ℚ_[p])
    (ρ₂ : GQp p →* GL (Fin b) ℚ_[p]), ContRep p ρ₁ → ContRep p ρ₂ →
    (∀ σ, (ρ σ : Matrix (Fin (a * b)) (Fin (a * b)) ℚ_[p]) =
      Matrix.reindex finProdFinEquiv finProdFinEquiv
        (Matrix.kroneckerMap (· * ·) (ρ₁ σ : Matrix (Fin a) (Fin a) ℚ_[p])
          (ρ₂ σ : Matrix (Fin b) (Fin b) ℚ_[p]))) →
    IsDeRham p ρ₁ → IsDeRham p ρ₂ → IsDeRham p ρ)

end Fontaine

end PkgI4

end


end PkgI4Sec

section PkgI6Sec
/-! ### Copied from `scratch/pkg-I6/I6.lean` (compiled there). -/

/-!
# pkg-I6: arithmetic of `ℚ` and of local fields (steps B1, B2, C10, D1, D3, D4 of h-trust)

Leaves are `def … : Prop` over genuine Mathlib objects.  Each carries its published locator
(locators from memory are UNVERIFIED; see `docs/research/pkg-I6.md`).  Definitions that Mathlib
lacks (lower and upper ramification groups, Herbrand's function, the Artin conductor of a
representation of a finite group) are given concretely in Part II.

Part I  (global):  Skolem–Noether, the 2-torsion of the Brauer sequence of `ℚ` in Galois-cohomology
                   form, local Kronecker–Weber, Chebotarev, Brauer–Nesbitt.
Part II (local):   ramification groups, Serre's bound for the different, Hilbert's formula,
                   Herbrand's theorem, transitivity of `φ`, the Artin conductor, local class field
                   theory with the upper numbering theorem.
-/

open CategoryTheory

namespace PkgI6

/-! ## Part I. Global inputs -/

section SkolemNoether

end SkolemNoether

section Brauer

/-! ### The same three leaves at the level of continuous inhomogeneous cochains

Galois cohomology is classically *defined* by continuous inhomogeneous cochains (Serre,
*Cohomologie galoisienne*, I §2.2), and that is how N5 manipulates `ε` (a function
`G_ℚ × G_ℚ → {±1}`).  These forms need no comparison with Mathlib's resolution-defined
`continuousCohomology` (Mathlib describes only `H⁰` explicitly, `LowDegree.lean`). -/

end Brauer

section LocalKW

end LocalKW

section Chebotarev

open NumberField

end Chebotarev

section BrauerNesbitt

end BrauerNesbitt

/-! ## Part II. Local fields: ramification groups, the different, conductors, local CFT

Setting (Serre, *Corps locaux*, Ch. III–IV): `A → B` a finite extension of discrete valuation
rings, `A` complete with perfect residue field, fraction fields separable (and Galois where
stated).  Then `B` is the integral closure of `A` in `Frac B`, and `B ≃ₐ[A] B` is `Gal(L/K)`.
The definitions below are Serre's, written over Mathlib's `IsLocalRing.maximalIdeal`. -/

section Ramification

open IsLocalRing

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing B]

end Ramification

section LocalLeaves

open IsLocalRing

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

end LocalLeaves

section Conductor

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing B]

section Proof

open intervalIntegral

variable [Finite (B ≃ₐ[A] B)]

end Proof

end Conductor

section PrincipalUnits

open IsLocalRing

-- D3 (`PkgI6.sq_principalUnits`) is proved below, after glue-conductor's Hensel argument
-- (hsyn-fix; glue-I6-rest adopted the same proof).

end PrincipalUnits

end PkgI6


end PkgI6Sec

section CondBreaksSec
/-! ### Copied from `scratch/glue-conductor/Breaks.lean` (compiled there). -/

/-!
# glue-conductor: the elementary core of Glazer's uniform conductor bound (D1, D3, D4)

Manuscript `diophantine_zq.tex` L796-851 (h-trust steps D1-D4). Everything here is about
integers and rationals; the ramification data enter as the sequence `g i = |G_i|` of orders
of the lower ramification groups of a finite Galois extension of local fields at one prime
(`g 0 = e`, `g` antitone, `g i ≥ 1`, `g i = 1` for large `i`), as in Serre, *Corps locaux*,
IV §§1-3. The dictionary to the field-theoretic objects is:

* Hilbert's formula: `δ = v_P(𝔇) = ∑_{i ≥ 0} (|G_i| - 1)` (Serre IV §1 Prop. 4);
* Herbrand's function at an integer lower index `m ≥ 0`: `φ(m) = ∑_{i=1}^m |G_i|/|G_0|`
  (Serre IV §3), so the upper index of the lower break `b` is `φ b`;
* `G^u = G_i` for `φ(i-1) < u ≤ φ(i)`, so `∫ (1 - |G^u|⁻¹) du` is the sum of
  `(φ i - φ (i-1)) (1 - 1/|G_i|)`.

No `sorry`.
-/

namespace GlueConductor

open Finset

/-! ## D1's arithmetic: `δ ≤ e - 1 + e v_p(e)` and `e ≤ a!` give `2δ/e ≤ 4a²` -/

/-! ## D4: conductor exponents -/

/-! ## D2: odd `p`, the character `β` on wild inertia -/

/-! ## D2-D4: the constants -/

/-! ## D1 over genuine definitions (Mathlib's rings of integers, inertia and different)

For a Galois number field `L/ℚ` and a prime `P` of `𝓞 L`, the lower ramification groups are
`G_i = {σ ∈ Gal(L/ℚ) | ∀ x ∈ 𝓞 L, σ x - x ∈ P^(i+1)}`, i.e. Mathlib's `Ideal.inertia` of
`P^(i+1)`; `G_0` is Mathlib's inertia group. (Serre, *Corps locaux*, IV §1 defines them for the
completion; they agree with these, Serre I §7 and IV §1, UNVERIFIED locators.) The two leaves
below are published theorems (local statements transported to number fields by completion).
Citation needed for the transport (rv-leaves-b repair 4): the different localizes, and the global
`G_i` equals the local one by density of `𝓞_L` in `𝓞_{L_P}` (Serre, *Corps locaux*, III §4, I §7,
UNVERIFIED); pkg-I6's local forms `PkgI6.DifferentBound`, `PkgI6.HilbertDifferentFormula` (I6.6,
I6.7) state the same leaves without it. -/

open NumberField

end GlueConductor



end CondBreaksSec

section D1LocalSec
/-! ### Copied from `scratch/glue-d1-local/Local.lean` lines 401-635 (its copy of Breaks.lean dropped; hsyn-fold). -/


/-! # glue-d1-local: the local form of D1's degree bound `e ≤ a!`

Glazer bounds only the local degree `[F:ℚ_p] ≤ a` and uses the Galois closure `F̃` of `F/ℚ_p`.
For a finite Galois `L/ℚ` and a prime `P` of `𝓞 L` over `p`, the local Galois group
`Gal(L_P/ℚ_p)` is the decomposition group `D_P = Stab(P) ≤ Gal(L/ℚ)`, and for an intermediate
field `K` with `w = P ∩ 𝓞 K` the subgroup `Gal(L_P/K_w)` is `D_P ∩ Gal(L/K)`
(Serre, *Corps locaux*, II §3, UNVERIFIED locator). So "`L_P` is the Galois closure of
`K_w/ℚ_p`" is the group condition that `D_P ∩ Gal(L/K)` has trivial normal core in `D_P`, and
`[K_w:ℚ_p]` is the index `[D_P : D_P ∩ Gal(L/K)]`. Everything below is stated over Mathlib's
`Gal(L/ℚ)`, `MulAction.stabilizer`, `Ideal.inertia` and `Ideal.ramificationIdx`; no completion
is needed. -/

namespace GlueD1Local

open NumberField GlueConductor
open scoped Pointwise

variable (L : Type) [Field L] [NumberField L] [IsGalois ℚ L]

/-! ## The Krasner-type situation: `K` has a single prime over `p`

If `L` is the Galois closure of `K` over `ℚ` (`core_G(Gal(L/K)) = ⊥`) and `K` has only one prime
`w` over `p`, then the core hypothesis of `D1_local'` holds: `L_P` is then the Galois closure of
`K_w`. Krasner's lemma gives such a `K` for any finite `F/ℚ_p` (`K = ℚ(α)` with the minimal
polynomial of `α` close to that of a generator of `F`; then `K_w ≅ F` and `[K:ℚ] = [F:ℚ_p]`). -/

end GlueD1Local

end D1LocalSec

section CondDyadicSec
/-! ### Copied from `scratch/glue-conductor/Dyadic.lean` (compiled there). -/

/-!
# glue-conductor: the dyadic unit step of D3 (N5 L828-832)

N5: "the logarithm for `Ĝ_m` identifies `U_F^{e+1}` with `𝔪_F^{e+1}` since `e+1 > e`
[Silverman IV.6.4]. Multiplication by four gives `(U_F^{e+1})^4 = U_F^{3e+1}`."

The direction used is `U_F^{3e+1} ⊆ (U_F^{e+1})^4` (so that `β⁴ = 1` on `U_F` forces `β = 1` on
`U_F^{3e+1}`). We prove both directions for any complete discrete valuation ring `A` with
`v(2) = e`, i.e. `(2) = 𝔪^e`, with no logarithm: a square root of `1 + z`, `z ∈ 𝔪^{2e+s}`,
`s ≥ 1`, is `1 + 2u` with `u² + u = z/4`, a simple root by Hensel's lemma (Mathlib's
`IsAdicComplete.henselianRing`). The ring of integers of a finite extension `F/ℚ₂` with
absolute ramification index `e` satisfies the hypotheses. No `sorry`.
-/

namespace GlueConductor

open IsLocalRing Polynomial

variable {A : Type*} [CommRing A] [IsLocalRing A]

end GlueConductor


end CondDyadicSec

section CondLevelSec
/-! ### Copied from `scratch/glue-conductor/Level.lean` (compiled there). -/

/-!
# glue-conductor: the level product `N ≤ Q_R M²` (h-trust D4-D5, N5 L846-857)

Over the repository's own definitions (`ZInQ.heightE0`, `ZInQ.heightQ`,
`ZInQ.contactSupport`). The conductor exponents `a_p = v_p(N)` (Carayol's Théorème A turns the
conductor exponents of `r₅` (and of `r₃` at `p = 5`) into the exponents of the level `N`) enter
through `N.factorization`. Hypotheses, as in N5:

* `a_p ≤ E₀` at primes `p ≤ R` (D4, first case);
* at primes `p > R`, `a_p ≤ 2` (D4, tame case), and `a_p = 0` unless `p ∈ T = S ∪ supp M_S(u)`
  (D4, third case: outside `T`, `L` is unramified, `A` has good reduction and `β` is unramified).

Since `max S ≤ R`, a prime `p > R` with `a_p > 0` divides `M = M_S(u)`, a product of distinct
primes, so the large part of `N` is at most `M²`; the small part is at most
`(∏_{p ≤ R} p)^{E₀} ≤ R^{R E₀} = Q_R`. No `sorry`.
-/

namespace GlueConductor

open _root_.ZInQ

end GlueConductor


end CondLevelSec

section AssemblySec
/-! ### Copied from `scratch/glue-assembly/GlueAssembly.lean` (compiled there). -/


/-!
# Step F2 of h-trust: `h(Φ(z)) ≤ 40 h(z) + 22` over Mathlib's Weil heights

`Φ(z) = 3779136 (∏ z_m)⁴ / (∑ z_m⁸)⁵` (N5 L920-932). The statement is about Mathlib's genuine
Weil height `Height.logHeight` on a field with admissible absolute values (number fields).
-/

namespace GlueAssembly

open MvPolynomial Height Real

variable {K : Type*} [Field K] [AdmissibleAbsValues K]

end GlueAssembly


/-!
# Height of a rational number in a number field

`h_K(q) = [K:ℚ] · log max(|num q|, den q)` for `q ∈ ℚ` and a number field `K` (Mathlib's relative
height `Height.logHeight₁`). This is the invariance of the absolute height under finite
extension, for rational numbers.
-/

namespace GlueAssembly

open Height NumberField Real

variable {K : Type*} [Field K] [NumberField K]

end GlueAssembly


/-!
# E2-E4 and F3 arithmetic of N5 (h-trust steps E2, E3, E4, F3), and the CM-branch arithmetic

Real-number lemmas. Their hypotheses are the numerical outputs of the literature theorems
(Javanpeykar, Gaudron–Rémond Thm 1.4, Faltings' Lemma 5 with additivity, Bost, Pazuki); their
conclusions are N5's displayed bounds.
-/

namespace GlueAssembly

open Real _root_.ZInQ -- op-compact: root ZInQ, as before HDec.ZInQ was a namespace

/-! ### E3-E4: the non-CM transfer (N5 L868-905) -/

/-! ### CM branch (N5 L581-631): `h_F(A) ≤ C_cm` -/

/-! ### F3: Pazuki's bound in N5's normalization (N5 L934-947) -/

/-- **F3 arithmetic (hardened, rv-leaves-a §3.3).** From Pazuki's Cor. 1.3(2) for `g = 2`, `r = 2`,
`h_Θ ≤ X_D/2 + C₂ log(X_D + 2)` with `X_D = max(1, h_F(A) + 3)` (covering every normalization
shift `≤ 3`, in particular Deligne's `log π`) and `C₂ = 1000·2⁴·(log 2⁴)⁵`, conclude
`h ≤ 10⁴·2²⁴·max(1, h_F(A))`: the final constant is unchanged. -/
theorem pazuki_numerics {hz hA : ℝ}
    (hP : hz ≤ max 1 (hA + 3) / 2 +
      1000 * 2 ^ 4 * (log (2 ^ 4)) ^ 5 * log (max 1 (hA + 3) + 2)) :
    hz ≤ 10000 * 2 ^ 24 * max 1 hA := by
  set X := max 1 hA with hX
  set XD := max 1 (hA + 3) with hXD
  have hX1 : 1 ≤ X := le_max_left _ _
  have hXD1 : 1 ≤ XD := le_max_left _ _
  have hXD4 : XD ≤ 4 * X := by
    refine max_le (by linarith) ?_
    have : hA ≤ X := le_max_right _ _
    linarith
  have hlogXD : log (XD + 2) ≤ 2 * XD := by
    have := log_le_sub_one_of_pos (by linarith : (0 : ℝ) < XD + 2)
    linarith
  have hC0 : 0 ≤ log (2 ^ 4 : ℝ) := log_nonneg (by norm_num)
  have hC : (log (2 ^ 4 : ℝ)) ^ 5 ≤ 243 := by
    calc (log (2 ^ 4 : ℝ)) ^ 5 ≤ 3 ^ 5 := pow_le_pow_left₀ hC0 log_sixteen_le 5
      _ = 243 := by norm_num
  have hlog0 : 0 ≤ log (XD + 2) := log_nonneg (by linarith)
  have h1 : 1000 * 2 ^ 4 * (log (2 ^ 4)) ^ 5 * log (XD + 2) ≤ 1000 * 2 ^ 4 * 243 * (8 * X) := by
    have : log (XD + 2) ≤ 8 * X := by linarith
    gcongr
  have h2 : XD / 2 ≤ 4 * X / 2 := by linarith
  have h3 := hP.trans (add_le_add h2 h1)
  have h4 : 4 * X / 2 + 1000 * 2 ^ 4 * 243 * (8 * X) ≤ 10000 * 2 ^ 24 * X := by nlinarith
  exact h3.trans h4

end GlueAssembly


/-!
# Copy of `ZInQKernel/Hypotheses/JHeight.lean` (F4), for scratch use

Scratch files cannot import `ZInQKernel.Hypotheses.JHeight` in this worktree (its import chain
reaches the unbuilt upstream package `lean/`). The F4 part of that file is copied verbatim
(namespace changed); `SixContactMinAt S` is `SixContactMin` at `S = Mult.S_mul` by `rfl`.
-/

namespace GlueAssembly

open _root_.ZInQ

/-- The binary sextic `F_h(a,b) = a(a+15b)(a+20b)(a+24b)(a+30b)(a+60b)`. -/
def Fh (a b : ℤ) : ℤ := a * (a + 15 * b) * (a + 20 * b) * (a + 24 * b) * (a + 30 * b) * (a + 60 * b)

/-- The binary quadratic `G_h(a,b) = 7a² + 300ab + 3600b²` (discriminant `−10800 < 0`). -/
def Gh (a b : ℤ) : ℤ := 7 * a ^ 2 + 300 * a * b + 3600 * b ^ 2

/-- The Hauptmodul value `J(u) = −57600 F(u)² / G(u)⁶` (h-b1 M7). -/
def Jmap (u : ℚ) : ℚ :=
  -57600 * (u * (u + 15) * (u + 20) * (u + 24) * (u + 30) * (u + 60)) ^ 2 /
    (7 * u ^ 2 + 300 * u + 3600) ^ 6

/-- Nullstellensatz certificate for `x⁷` (`scratch/wk-h/f4_cert.py`). -/
theorem cert_x (a b : ℤ) :
    3 * a ^ 7 = (-200 * a - 4800 * b) * Fh a b +
      (29 * a ^ 5 + 3700 * a ^ 4 * b + 164400 * a ^ 3 * b ^ 2 + 2880000 * a ^ 2 * b ^ 3 +
        17280000 * a * b ^ 4) * Gh a b := by
  unfold Fh Gh; ring

/-- Nullstellensatz certificate for `y⁷` (`scratch/wk-h/f4_cert.py`). -/
theorem cert_y (a b : ℤ) :
    104976000000 * b ^ 7 = (-1001 * a - 37650 * b) * Fh a b +
      (143 * a ^ 5 + 20557 * a ^ 4 * b + 1026600 * a ^ 3 * b ^ 2 + 20691900 * a ^ 2 * b ^ 3 +
        133110000 * a * b ^ 4 + 29160000 * b ^ 5) * Gh a b := by
  unfold Fh Gh; ring

/-- `G` has no rational zero (negative discriminant). -/
theorem G_ne_zero (u : ℚ) : 7 * u ^ 2 + 300 * u + 3600 ≠ 0 := by
  nlinarith [sq_nonneg (7 * u + 150)]

/-- `C₀ = 57600²·3⁷·(2¹⁰3⁸5⁶)⁷`, the bound for the cancellation in `J(u)`. -/
def C0 : ℤ := (57600 * 3 ^ 7) * (57600 * 104976000000 ^ 7)

/-- **Cancellation bound.** For coprime `a, b`, a common divisor of `57600F_h²` and `G_h⁶` divides
`C₀` (from `cert_x`, `cert_y` raised to the 7th power). -/
theorem dvd_C0 {a b c : ℤ} (hab : IsCoprime a b) (hP : c ∣ 57600 * Fh a b ^ 2)
    (hQ : c ∣ Gh a b ^ 6) : c ∣ C0 := by
  have key : ∀ x y : ℤ, 57600 * (x + y) ^ 7 =
      57600 * x ^ 2 * (x ^ 5 + 7 * x ^ 4 * y + 21 * x ^ 3 * y ^ 2 + 35 * x ^ 2 * y ^ 3 +
        35 * x * y ^ 4 + 21 * y ^ 5) + y ^ 6 * (57600 * (7 * x + y)) := by intros; ring
  have hsplit : ∀ (A B : ℤ), c ∣ 57600 * (A * Fh a b + B * Gh a b) ^ 7 := by
    intro A B
    rw [key]
    refine dvd_add ?_ ?_
    · have : 57600 * (A * Fh a b) ^ 2 = (57600 * Fh a b ^ 2) * A ^ 2 := by ring
      rw [this, mul_assoc]; exact dvd_mul_of_dvd_left hP _
    · have : (B * Gh a b) ^ 6 = Gh a b ^ 6 * B ^ 6 := by ring
      rw [this, mul_assoc]; exact dvd_mul_of_dvd_left hQ _
  have hx : c ∣ 57600 * 3 ^ 7 * a ^ 49 := by
    have e : 57600 * 3 ^ 7 * a ^ 49 = 57600 * (3 * a ^ 7) ^ 7 := by ring
    rw [e, cert_x]; exact hsplit _ _
  have hy : c ∣ 57600 * 104976000000 ^ 7 * b ^ 49 := by
    have e : 57600 * 104976000000 ^ 7 * b ^ 49 = 57600 * (104976000000 * b ^ 7) ^ 7 := by ring
    rw [e, cert_y]; exact hsplit _ _
  obtain ⟨s, t, hst⟩ := hab.pow (m := 49) (n := 49)
  have e : C0 = (57600 * 104976000000 ^ 7 * s) * (57600 * 3 ^ 7 * a ^ 49) +
      (57600 * 3 ^ 7 * t) * (57600 * 104976000000 ^ 7 * b ^ 49) := by
    have : C0 = C0 * (s * a ^ 49 + t * b ^ 49) := by rw [hst, mul_one]
    rw [this, C0]; ring
  rw [e]
  exact dvd_add (dvd_mul_of_dvd_right hx _) (dvd_mul_of_dvd_right hy _)

theorem abs_monomial_le {a b m : ℤ} (ha : |a| ≤ m) (hb : |b| ≤ m) (i j : ℕ) :
    |a ^ i * b ^ j| ≤ m ^ (i + j) := by
  have hm : 0 ≤ m := (abs_nonneg a).trans ha
  rw [abs_mul, abs_pow, abs_pow, pow_add]
  exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) ha _) (pow_le_pow_left₀ (abs_nonneg _) hb _)
    (by positivity) (by positivity)

/-- **Lower bound.** With `m = max(|a|, |b|) > 0`: `m¹² ≤ 10⁴⁸ max(57600F_h², G_h⁶)`. -/
theorem lower_bound {a b m : ℤ} (ha : |a| ≤ m) (hb : |b| ≤ m) (hm : 0 < m)
    (hmax : m = |a| ∨ m = |b|) :
    m ^ 12 ≤ 10 ^ 48 * max (57600 * Fh a b ^ 2) (Gh a b ^ 6) := by
  by_contra hlt
  push Not at hlt
  have hP := le_max_left (57600 * Fh a b ^ 2) (Gh a b ^ 6)
  have hQ := le_max_right (57600 * Fh a b ^ 2) (Gh a b ^ 6)
  have hF : 240 * 10 ^ 24 * |Fh a b| < m ^ 6 := by
    have h2 : (240 * 10 ^ 24 * |Fh a b|) ^ 2 < (m ^ 6) ^ 2 := by
      rw [mul_pow, sq_abs]; nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h2
  have hG : 10 ^ 8 * |Gh a b| < m ^ 2 := by
    have h6 : (10 ^ 8 * |Gh a b|) ^ 6 < (m ^ 2) ^ 6 := by
      rw [mul_pow, pow_abs, abs_of_nonneg (by positivity : (0:ℤ) ≤ Gh a b ^ 6)]
      nlinarith
    exact lt_of_pow_lt_pow_left₀ 6 (by positivity) h6
  have hX : 240 * 10 ^ 24 * (m * |Fh a b|) < m ^ 7 := by nlinarith
  have hY : 10 ^ 8 * (m ^ 5 * |Gh a b|) < m ^ 7 := by
    have : (0 : ℤ) < m ^ 5 := by positivity
    nlinarith
  have m10 : -m ≤ a ∧ a ≤ m := abs_le.mp ha
  have m01 : -m ≤ b ∧ b ≤ m := abs_le.mp hb
  have mono : ∀ i j : ℕ, i + j = 5 → -m ^ 5 ≤ a ^ i * b ^ j ∧ a ^ i * b ^ j ≤ m ^ 5 := by
    intro i j hij
    have := abs_monomial_le ha hb i j
    rw [hij] at this
    exact abs_le.mp this
  have m50 := mono 5 0 rfl
  have m41 := mono 4 1 rfl
  have m32 := mono 3 2 rfl
  have m23 := mono 2 3 rfl
  have m14 := mono 1 4 rfl
  have m05 := mono 0 5 rfl
  simp only [pow_one, pow_zero, mul_one, one_mul] at m50 m41 m32 m23 m14 m05
  have hm7 : (0 : ℤ) < m ^ 7 := by positivity
  have tri : ∀ A B : ℤ, |A * Fh a b + B * Gh a b| ≤ |A| * |Fh a b| + |B| * |Gh a b| := by
    intro A B; rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
  rcases hmax with h | h
  · have hA : |-200 * a - 4800 * b| ≤ 5000 * m := by
      rw [abs_le]; constructor <;> linarith
    have hB : |29 * a ^ 5 + 3700 * a ^ 4 * b + 164400 * a ^ 3 * b ^ 2 + 2880000 * a ^ 2 * b ^ 3 +
        17280000 * a * b ^ 4| ≤ 20328129 * m ^ 5 := by
      rw [abs_le]; constructor <;> linarith
    have e := tri (-200 * a - 4800 * b) (29 * a ^ 5 + 3700 * a ^ 4 * b + 164400 * a ^ 3 * b ^ 2 +
      2880000 * a ^ 2 * b ^ 3 + 17280000 * a * b ^ 4)
    rw [← cert_x, abs_mul, abs_pow, ← h, show |(3 : ℤ)| = 3 by norm_num] at e
    have e1 := mul_le_mul_of_nonneg_right hA (abs_nonneg (Fh a b))
    have e2 := mul_le_mul_of_nonneg_right hB (abs_nonneg (Gh a b))
    linarith
  · have hA : |-1001 * a - 37650 * b| ≤ 38651 * m := by
      rw [abs_le]; constructor <;> linarith
    have hB : |143 * a ^ 5 + 20557 * a ^ 4 * b + 1026600 * a ^ 3 * b ^ 2 +
        20691900 * a ^ 2 * b ^ 3 + 133110000 * a * b ^ 4 + 29160000 * b ^ 5| ≤
        184009200 * m ^ 5 := by
      rw [abs_le]; constructor <;> linarith
    have e := tri (-1001 * a - 37650 * b) (143 * a ^ 5 + 20557 * a ^ 4 * b +
      1026600 * a ^ 3 * b ^ 2 + 20691900 * a ^ 2 * b ^ 3 + 133110000 * a * b ^ 4 + 29160000 * b ^ 5)
    rw [← cert_y, abs_mul, abs_pow, ← h, show |(104976000000 : ℤ)| = 104976000000 by norm_num] at e
    have e1 := mul_le_mul_of_nonneg_right hA (abs_nonneg (Fh a b))
    have e2 := mul_le_mul_of_nonneg_right hB (abs_nonneg (Gh a b))
    linarith

/-- **F4, strengthened.** `12 h(u) ≤ h(J(u)) + 450` for `u ∉ 𝒞` (N5: `h(u) < h(J(u)) + 74`). -/
theorem twelve_mul_ratHeight_le (u : ℚ) (_hu : u ∉ contactSet) :
    12 * ratHeight u ≤ ratHeight (Jmap u) + 450 := by
  set a : ℤ := u.num with ha_def
  set b : ℤ := (u.den : ℤ) with hb_def
  have hb : 0 < b := by rw [hb_def]; exact_mod_cast u.den_pos
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  have hcop : IsCoprime a b := by
    rw [Int.isCoprime_iff_gcd_eq_one]; exact u.reduced
  have hu_eq : u = (a : ℚ) / (b : ℚ) := by
    rw [ha_def, hb_def]; push_cast; exact (Rat.num_div_den u).symm
  have hFq : u * (u + 15) * (u + 20) * (u + 24) * (u + 30) * (u + 60) =
      (Fh a b : ℚ) / (b : ℚ) ^ 6 := by
    rw [hu_eq]; unfold Fh; push_cast; field_simp
  have hGq : 7 * u ^ 2 + 300 * u + 3600 = (Gh a b : ℚ) / (b : ℚ) ^ 2 := by
    rw [hu_eq]; unfold Gh; push_cast; field_simp
  have hG0 : 0 < Gh a b := by unfold Gh; nlinarith [sq_nonneg (7 * a + 150 * b), mul_pos hb hb]
  set n : ℤ := -(57600 * Fh a b ^ 2) with hn_def
  set d : ℤ := Gh a b ^ 6 with hd_def
  have hdpos : 0 < d := by positivity
  have hJ : Jmap u = (n : ℚ) / (d : ℚ) := by
    have hGq0 : (Gh a b : ℚ) ≠ 0 := by exact_mod_cast hG0.ne'
    unfold Jmap; rw [hFq, hGq, hn_def, hd_def]; push_cast; field_simp
  obtain ⟨c, hn, hd⟩ := Rat.exists_eq_mul_div_num_and_eq_mul_div_den n hdpos.ne'
  rw [← hJ] at hn hd
  set J := Jmap u with hJdef
  have hden : (0 : ℤ) < (J.den : ℤ) := by exact_mod_cast J.den_pos
  have hcpos : 0 < c := by
    by_contra h; push Not at h; rw [hd] at hdpos; nlinarith
  have hcdvd : c ∣ C0 := dvd_C0 hcop (dvd_neg.mp (Dvd.intro _ hn.symm)) (Dvd.intro _ hd.symm)
  have hcle : c ≤ C0 := Int.le_of_dvd (by norm_num [C0]) hcdvd
  have hmaxeq : max (57600 * Fh a b ^ 2) d = c * max |J.num| (J.den : ℤ) := by
    have h1 : 57600 * Fh a b ^ 2 = |n| := by
      rw [hn_def, abs_neg, abs_of_nonneg (by positivity)]
    rw [h1, hn, hd, abs_mul, abs_of_pos hcpos, mul_max_of_nonneg _ _ hcpos.le]
  set m := max |a| b with hm_def
  have hm : 0 < m := lt_of_lt_of_le hb (le_max_right _ _)
  have hlow := lower_bound (a := a) (b := b) (le_max_left |a| b)
    (by rw [abs_of_pos hb]; exact le_max_right _ _) hm
    (by rcases max_choice |a| b with h | h
        · left; exact h
        · right; rw [abs_of_pos hb]; exact h)
  rw [hmaxeq] at hlow
  set H := max |J.num| (J.den : ℤ) with hH_def
  have hH : 1 ≤ H := le_max_of_le_right (by exact_mod_cast J.den_pos)
  have hlow2 : m ^ 12 ≤ 10 ^ 139 * H := by
    have hC : 10 ^ 48 * C0 ≤ 10 ^ 139 := by norm_num [C0]
    calc m ^ 12 ≤ 10 ^ 48 * (c * H) := hlow
      _ ≤ 10 ^ 48 * (C0 * H) := by gcongr
      _ = (10 ^ 48 * C0) * H := by ring
      _ ≤ 10 ^ 139 * H := by gcongr
  have hu_h : ratHeight u = Real.log (m : ℝ) := by
    unfold ratHeight; rw [hm_def]; push_cast [ha_def, hb_def]; rfl
  have hJ_h : ratHeight J = Real.log (H : ℝ) := by
    unfold ratHeight; rw [hH_def]; push_cast; rfl
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hlowR : (m : ℝ) ^ 12 ≤ 10 ^ 139 * (H : ℝ) := by exact_mod_cast hlow2
  have hlog10 : Real.log 10 < 3 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have h1 := Real.exp_one_gt_d9
    have : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    have h2 : (2.7 : ℝ) ^ 3 < Real.exp 1 ^ 3 :=
      pow_lt_pow_left₀ (by linarith) (by norm_num) (by norm_num)
    rw [this]; norm_num at h2 ⊢; linarith
  have key : 12 * Real.log (m : ℝ) ≤ 139 * Real.log 10 + Real.log (H : ℝ) := by
    have := Real.log_le_log (by positivity) hlowR
    rw [Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_pow] at this
    push_cast at this
    linarith
  rw [hu_h, hJ_h]
  linarith

/-- `M_S(u) > 0` (copied from `Hypotheses/HeightMin.lean`). -/
theorem contactSupport_pos (S : Finset ℕ) (u : ℚ) : 0 < contactSupport S u := by
  unfold contactSupport
  exact Finset.prod_pos fun p hp =>
    (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos

/-- The constant `X(R) = max(1, C_cm, Q_R¹⁷)` of N5's final display (as in `JHeight.lean`). -/
noncomputable def heightX (R : ℝ) : ℝ := max 1 (max (heightCcm : ℝ) (heightQ R ^ 17))

/-- `JHeightBound S` (as in `JHeight.lean`). -/
def JHeightBound (S : Finset ℕ) : Prop :=
  ∀ u : ℚ, u ∉ contactSet →
    ratHeight (Jmap u) ≤
      (40 * 10000 * 2 ^ 24 + 22 : ℝ) * heightX heightD * (contactSupport S u : ℝ) ^ 24

theorem heightH6_eq (R : ℝ) : heightH6 R = 2 * 10 ^ 13 * heightX R := rfl

end GlueAssembly

/-!
# The assembly: from the numerical outputs of E2-E4, F1, F3 to `SixContactMinAt S`

`GlueOutputs S` is a conjunction, for every `u ∉ 𝒞`, of the numerical outputs that steps
A1-E1 (modularity half), E2-E4 (Javanpeykar, Gaudron–Rémond, Faltings, Bost), F1 (the theta
expression of `j`) and F3 (Pazuki) give. Lean checks the assembly: F2 (`logHeight_Phi_le`, over
Mathlib's Weil height), the invariance of the height of a rational number in a number field
(`logHeight₁_algebraMap_rat`), the E-arithmetic (`transfer_of_level`, `cm_numerics`), the
F3-arithmetic (`pazuki_numerics`), F4 (`twelve_mul_ratHeight_le`) and the final constant.

`GlueOutputs S` is NOT a faithful statement of the literature theorems: the abelian varieties and
their Faltings heights do not exist in Mathlib, so they appear only as real numbers with the
inequalities the theorems give. As a Lean Prop it is a height bound in disguise (wk-h §4.3).
What is faithful is the theta point: a genuine point of `K¹⁰` with its genuine Weil height.
-/

namespace GlueAssembly

open Real _root_.ZInQ Height -- op-compact: root ZInQ, as before HDec.ZInQ was a namespace

attribute [instance] NF.fld NF.nf

/-- **Output of F3 (Pazuki, Cor. 1.3(2), `g = r = 2`), hardened to `h_F + 3` (rv-leaves-a §3.3; covers Deligne's `log π`)** for the absolute
sup-norm height `hz` of the even theta nulls. -/
def PazukiOutput (hz hA : ℝ) : Prop :=
  hz ≤ max 1 (hA + 3) / 2 +
    1000 * 2 ^ 4 * (log (2 ^ 4)) ^ 5 * log (max 1 (hA + 3) + 2)

/-- **The glue interface.** For every `u ∉ 𝒞`: a number field `K`, the ten even theta nulls
`z ∈ K¹⁰` of the QM surface `A` over `J(u)` (F1: `Φ(z) = J(u)`), the Faltings height `hA` of
`A`, Pazuki's bound for the absolute Weil height `h(z) = h_K(z)/[K:ℚ]` (F3), and the outputs of
either the non-CM transfer (at `Q = Q_D`, `M = M_S(u)`) or the CM branch. -/
def GlueOutputs (S : Finset ℕ) : Prop :=
  ∀ u : ℚ, u ∉ contactSet → ∃ (K : NF) (z : Fin 10 → K.K) (hA : ℝ),
    3779136 * (∏ i, z i) ^ 4 / (∑ i, z i ^ 8) ^ 5 = algebraMap ℚ K.K (Jmap u) ∧
    PazukiOutput (logHeight z / Module.finrank ℚ K.K) hA ∧
    (NonCMOutput (heightQ heightD) (contactSupport S u) hA ∨ CMOutput hA)

/-- **The assembly.** `GlueOutputs S → JHeightBound S`. -/
theorem jHeightBound_of_glueOutputs {S : Finset ℕ} (h : GlueOutputs S) : JHeightBound S := by
  intro u hu
  obtain ⟨K, z, hA, hF1, hPaz, hE⟩ := h u hu
  have hM : (1 : ℝ) ≤ contactSupport S u := by exact_mod_cast contactSupport_pos S u
  set Y := heightX heightD * (contactSupport S u : ℝ) ^ 24 with hY
  have hXM : max 1 hA ≤ Y := max_one_hA_le hM hE
  have hz := pazuki_numerics hPaz
  have hj := ratHeight_le_of_theta z (Jmap u) hF1
  have hY1 : 1 ≤ Y := (le_max_left 1 hA).trans hXM
  have hlog := log_3779136_le
  have : ratHeight (Jmap u) ≤ (40 * 10000 * 2 ^ 24 + 22 : ℝ) * Y := by nlinarith
  rw [hY] at this
  linarith

/-- **H from the glue interface.** `GlueOutputs S → SixContactMinAt S`; at `S = Mult.S_mul`
the conclusion is `ZInQ.SixContactMin`. -/
theorem sixContactMinAt_of_glueOutputs {S : Finset ℕ} (h : GlueOutputs S) :
    SixContactMinAt S :=
  sixContactMinAt_of_jHeightBound (jHeightBound_of_glueOutputs h)

end GlueAssembly


end AssemblySec

section AsmC8Sec
/-! ### Copied from `scratch/glue-assembly/C8.lean` (compiled there). -/

/-!
# Elementary glue of step C8 (twist and weight) and of E1, over genuine Mathlib objects

* `weight_match`: the Hodge–Tate weight comparison `{n, n+1−k} = {0, −1}`, `k ≥ 1` ⇒ `k = 2`,
  `n = 0` (Tate normalization), and its cohomological variant.
* The determinant argument for the finiteness of the twisting character `ψ` (h-trust C8 items
  1-3), as group theory: (a) a character trivial-on-squares on a finite-index subgroup has finite
  image; (b) a character into the units of a field whose square has finite image has finite image.
  These are stated for an arbitrary group `G` (for C8, `G = G_ℚ` and `H = G_F`), with values in
  `Eˣ` for a field `E` (for C8, `E = \bar ℚ₅`).
-/

namespace GlueAssembly

end GlueAssembly

end AsmC8Sec

section AsmE1Sec
/-! ### Copied from `scratch/glue-assembly/E1Lin.lean` (compiled there). -/

/-!
# E1 glue: invariants commute with extension of the coefficient field

N5 L862-864: "Invariants in their finite-dimensional Hom space commute with extension of the
coefficient field." The direction used: if `(E ⊗_F W)^G ≠ 0` then `W^G ≠ 0`, for a
representation `W` of a group `G` over a field `F` and a field extension `E/F` (for E1:
`W = Hom_{ℚ₅}(V₅A, V₅J)`, `G = G_{L'}`, `E` a finite extension of `ℚ₅`). Proved for any
`F`-module `W` (no finiteness needed) by expanding in an `F`-basis of `E`.
-/

namespace GlueAssembly

open TensorProduct

variable {F E W G : Type*} [Field F] [Field E] [Algebra F E] [AddCommGroup W] [Module F W]
  [Group G]

end GlueAssembly

end AsmE1Sec

section AsmE2Sec
/-! ### Copied from `scratch/glue-assembly/E2Index.lean` (compiled there). -/

/-!
# E2 glue: `[SL₂(ℤ) : Γ₁(N)] ≤ N²` (N5 L871: "The index of `Γ₁(N)` is at most `N²`")

The first column modulo `N` separates the left cosets of `Γ₁(N)`.
-/

namespace GlueAssembly

open Matrix CongruenceSubgroup
open scoped MatrixGroups

end GlueAssembly

end AsmE2Sec

section AsmF3Sec
/-! ### Copied from `scratch/glue-assembly/F3Glue.lean` (compiled there). -/

/-!
# Elementary glue of step F3: normalizations of the theta height (N5 L934-947)

* `mulHeight_le_mulHeightL2`: the projective height with the Euclidean (`L²`) norm at the
  archimedean places dominates Mathlib's sup-norm height (N5: "His Euclidean projective height
  dominates our supremum projective height").
* `logHeight_sixteen_eq`: adjoining the six vanishing odd theta constants does not change the
  height (N5 L932-933), Mathlib's `logHeight_sumElim_zero_eq`.
* `logHeight_rootsOfUnity_smul`: multiplying coordinates by roots of unity does not change the
  height (N5 L937: the permitted changes of theta structure permute coordinates and multiply them
  by roots of unity).
-/

namespace GlueAssembly

open Height Real

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {ι : Type*} [Fintype ι]

end GlueAssembly

end AsmF3Sec

section DescProjRepSec
/-! ### Copied from `scratch/glue-descent/ProjRep.lean` (compiled there). -/

/-!
# glue-descent: the algebraic core of B1 and C1 (N5 L632-664, L719-731)

All statements are over arbitrary groups, fields, vector spaces and algebras (genuine Mathlib
definitions). They are the steps of Glazer's scalar descent after the abelian surface has been
replaced by its Tate realization:

* `G` stands for `G_ℚ`, `E` for a finite extension of `ℚ_ℓ` containing the image of the
  coefficient field `C`, and `V` for `V_ℓ(A) ⊗ E`;
* `T σ = μ_σ ∘ σ ∈ GL(V)` (the Tate action of `σ` followed by the `B`-linear isogeny
  `μ_σ : ^σA → A`), so that `T σ * T τ = c(σ,τ) • T (σ τ)` with `c(σ,τ) ∈ ℚ^×` (N5 L640-644);
* `a σ = (deg μ_σ)^{-1/4}` and `ε = sign c` (N5 L645-664);
* `β` the cochain of B2-B3 with `β σ β τ = ε(σ,τ) β(στ)`.

The instantiation (Tate modules, the Galois action, `End⁰(A) = B`, Skolem–Noether) is not in
Mathlib; see `docs/research/glue-descent.md`.
-/

namespace GlueDescent

open scoped BigOperators

section Cocycle

variable {G : Type*} [Group G] {E : Type*} [Field E] {A : Type*} [Ring A] [Algebra E A]
  [Nontrivial A]

end Cocycle

section Sign

end Sign

section Rho

variable {G : Type*} [Group G] {E : Type*} [Field E] {V : Type*} [AddCommGroup V] [Module E V]

end Rho

section Split

variable {E : Type*} [Field E] {V : Type*} [AddCommGroup V] [Module E V]

namespace MatrixUnits2

variable (u : MatrixUnits2 E V)

end MatrixUnits2

end Split

section Span

variable {E : Type*} [Field E] {V : Type*} [AddCommGroup V] [Module E V]

end Span

end GlueDescent


end DescProjRepSec

section DescB1QuatSec
/-! ### Copied from `scratch/glue-descent/B1Quat.lean` (compiled there). -/

/-!
# glue-descent: the quaternion algebra of B1 (N5 L637-644)

N5's `B = (2, -3)` is Mathlib's `ℍ[ℚ, 2, -3] = QuaternionAlgebra ℚ 2 0 (-3)` (`i² = 2`,
`j² = -3`, `ij = -ji = k`).

* `B6_commute_i_j`: an element commuting with `i` and `j` is a rational scalar. This is the step
  "`c(σ,τ)` commutes with `B`, hence belongs to `ℚ^×`" (N5 L640-644), given `End⁰(A_ℚ̄) = B`.
* `B6_isCentral`: `Algebra.IsCentral ℚ B6`.
* `LeafSkolemNoether`: the Skolem–Noether theorem (automorphism case) over Mathlib's central
  simple algebras, the literature input of B1 (Reiner, *Maximal orders*, Thm 7.21; formalized in
  Tau Ceti, not in Mathlib v4.35).
-/

namespace GlueDescent

open Quaternion

/-! ### `B` is a division algebra, hence simple (so `LeafSkolemNoether` applies to it) -/

end GlueDescent


end DescB1QuatSec

section DescCochainSec
/-! ### Copied from `scratch/glue-descent/Cochain.lean` (compiled there). -/

/-!
# glue-descent: the group theory of B2-B3 (N5 L693-716)

`G` stands for `G_ℚ` (or the finite quotient `Gal(L'/ℚ)` through which everything factors),
`H` for `G_L` (normal, of index `d = [L:ℚ]`), `ε` for the sign cocycle inflated from
`Gal(L/ℚ) = G/H` and normalized, `U` for the coefficient group (`E^×` for a field `E`), and
`β : G → U` for the cochain with `β σ β τ = ε(σ,τ) β(στ)`.

Proved here, over arbitrary groups (genuine Mathlib definitions):

* `β|_H` is a homomorphism and is invariant under conjugation by `G` (N5 L701);
* `K' = ker β|_H` is normal in `G`, and `β` is constant on its cosets, so `β` factors
  through `G/K' = Gal(L'/ℚ)` (implicit in N5);
* if `β^{2m} = 1` on `H` with values in a field, `[H : K'] ≤ 2m`, hence
  `[G : K'] ≤ 2m [G : H]` (N5 L711-714: `[L':ℚ] ≤ 2md`);
* twisting by a character `η` with `η² = 1` changes neither `β² = χ` nor `dβ = ε`
  (N5 L707-709);
* the cohomological core of B2: if `ε · (dβ₀)⁻¹ = dγ` with `β₀² = χ` and `γ` valued in `±1`,
  then `β = β₀ γ⁻¹` has `β² = χ` and `dβ = ε` (N5 L694-700).
-/

namespace GlueDescent

section Basic

variable {G : Type*} [Group G] {U : Type*} [CommGroup U]

variable {H : Subgroup G} {ε : G → G → U} {β : G → U}

end Basic

section Index

variable {G : Type*} [Group G] {E : Type*} [Field E]
variable {H : Subgroup G} {ε : G → G → Eˣ} {β : G → Eˣ}

end Index

section Inertia

variable {G : Type*} [Group G] {U : Type*} [CommGroup U]

end Inertia

end GlueDescent

end DescCochainSec

section DescConstantsSec
/-! ### Copied from `scratch/glue-descent/Constants.lean` (compiled there). -/

/-!
# glue-descent: the constants of B2-B3 (N5 L674-677, L711-716)

Against the repository's own definitions (`ZInQKernel/Hypotheses/Height.lean`): `heightD = D`,
`heightE0 = E₀`, `heightQ R = Q_R = R^{R E₀}`, `contactSupport S u = M_S(u)`.

* `prod_odd_le`: `∏_{p ∈ T, p ≠ 2} (p - 1) ≤ R^R · M` for `T = S ∪ supp M`
  (N5 L676: `m ≤ 2 ∏_{p∈T, p≠2}(p-1) ≤ 2R^R M`);
* `degree_le_QM`: if `d ≤ D` and `m ≤ 2 ∏_{p ∈ T, p ≠ 2}(p-1)` then `2md ≤ Q_R · M`
  (N5 L713-716: `[L':ℚ] ≤ 2md ≤ 4DR^RM ≤ QM`).

The huge constants are never evaluated: only `1 ≤ D ≤ R`, `10¹² ≤ R` and `10 ≤ E₀` are used.
-/

namespace GlueDescent

open _root_.ZInQ

end GlueDescent

end DescConstantsSec

section DescChiSec
/-! ### Copied from `scratch/glue-descent/Chi.lean` (compiled there). -/

/-!
# glue-descent: the Dirichlet character `χ` of B2 (N5 L671-677)

N5 takes `T₋` to be the finite primes where the invariant of `[ε]` is `1/2`, picks an odd
character of `(ℤ/p)^×` at each odd `p ∈ T₋` and the nontrivial character mod `4` if `2 ∈ T₋`,
multiplies them to `χ`, and bounds the order `m ≤ 2 ∏_{p∈T, p≠2}(p-1)` (paraphrase).

Proved here over Mathlib's `DirichletCharacter` (genuine definitions), for any finite set `T`
of primes and any subset `T₋ ⊆ T`:

* `exists_odd_char`: for `n > 2` there is a Dirichlet character mod `n` with `χ(-1) = -1`
  (at `n = 4` it is the nontrivial character mod four);
* `exists_chi`: the product `χ = ∏_{p ∈ T₋} χ_p` (each `χ_p` odd of level `p`, or `4` at `p = 2`,
  raised to the level `N = ∏_{p ∈ T₋} lev p`) has level supported in `T` and
  `orderOf χ ≤ 2 ∏_{p ∈ T, p ≠ 2} (p - 1)`.

Not here: that the local invariant of `δχ` at `p` is `1/2` exactly when `χ_p(-1) = -1` (local
class field theory; leaf L-B2c of `docs/research/glue-descent.md`).
-/

namespace GlueDescent

open scoped Nat

end GlueDescent


end DescChiSec

section DescB2GlueSec
/-! ### Copied from `scratch/glue-descent/B2Glue.lean` (compiled there). -/

/-!
# glue-descent: the deduction of B2 from its literature inputs (N5 L665-700)

An abstract but universally quantified form: `G` is any topological group (for the application,
`G_ℚ` with the Krull topology), `ι` any index type (the finite primes), `Gv v` any topological
groups with continuous homomorphisms `r v : Gv v →* G` (the decomposition groups
`G_{ℚ_p} → G_ℚ` along a chosen embedding `ℚ̄ → ℚ̄_p`), and `U` any commutative group (`ℂ^×`).
"Continuous with values in a discrete group" is `IsLocallyConstant`.

A sign 2-cocycle `η` is *trivial* (`SignCob`) if `η = dγ` for a locally constant sign cochain
`γ`. The hypotheses are exactly the inputs of N5's argument:

* `hasse` (leaf L-B2a): a locally constant sign 2-cocycle on `G` that is trivial at every finite
  place is trivial (injectivity of `H²(G_ℚ, ±1) → ∏_{p<∞} H²(G_{ℚ_p}, ±1)`: Kummer theory
  with Hilbert 90, Albert–Brauer–Hasse–Noether and reciprocity, with `Br(ℝ)[2] = ℤ/2`);
* `local_two` (leaf L-B2b): `H²(G_{ℚ_p}, ±1)` has at most two elements (`Br(ℚ_p)[2] = ℤ/2`);
* `agree` (the local analysis of B2, leaves L-B2c, L-B2d): at every finite place, `[ε]` and
  `δχ = [dβ₀]` are both trivial or both nontrivial.

Conclusion: a locally constant `β` with `β² = χ` and `β σ β τ = ε(σ,τ) β(στ)`.
-/

namespace GlueDescent.B2

variable {U : Type*} [CommGroup U]

section Pullback

variable {Γ Δ : Type*} [Group Γ] [Group Δ] [TopologicalSpace Γ] [TopologicalSpace Δ]

end Pullback

section Algebra

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ]

end Algebra

end GlueDescent.B2

/-!
## The leaves of B2 over genuine Mathlib objects

`G_ℚ = Field.absoluteGaloisGroup ℚ` and `G_{ℚ_p} = Field.absoluteGaloisGroup ℚ_[p]` with their
Krull topologies; `resp p : G_{ℚ_p} →* G_ℚ` is Mathlib's `absoluteGaloisGroup.map` along
`ℚ → ℚ_p` (it depends on a choice of embedding `ℚ̄ → ℚ̄_p`; the vanishing of a class does not).
Sign-valued cochains are `ℂ^×`-valued with square `1`. `cyc N : G_ℚ →* (ℤ/N)^×` is Mathlib's
`modularCyclotomicCharacter` on `ℚ̄`.
-/

namespace GlueDescent.B2Q

open GlueDescent.B2 NumberField

local instance (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

end GlueDescent.B2Q

/-!
## Toward the assembly of B2 over `G_ℚ`: continuity of the cyclotomic character
-/

namespace GlueDescent.B2Q

open GlueDescent.B2 NumberField

end GlueDescent.B2Q

end DescB2GlueSec

section DescB2AssemblySec
/-! ### Copied from `scratch/glue-descent/B2Assembly.lean` (compiled there). -/

/-!
# glue-descent: B2 over `G_ℚ` from the four leaves L-B2a..d (N5 L665-700)

`b2_of_leaves`: for a finite Galois `L ⊂ ℚ̄` unramified outside a finite set `T` of primes, and
a continuous sign 2-cocycle `ε` of `G_ℚ` inflated from `Gal(L/ℚ)`, the four leaves give a set
`T₋ ⊆ T`, the Dirichlet character `χ = ∏_{p ∈ T₋} χ_p` of `Chi.lean` (level supported in `T`,
order `≤ 2 ∏_{p∈T, p≠2}(p-1)`), and a continuous `β : G_ℚ → ℂ^×` with `β² = χ` and
`dβ = ε`. Everything is over Mathlib's genuine objects (`Field.absoluteGaloisGroup`, `ℚ_[p]`,
`modularCyclotomicCharacter`, `DirichletCharacter`, `𝓞 L`).

Compile (out of tree, one file at a time; `OUT = scratch/glue-descent/.lake/out`):
`lake env bash -c "LEAN_PATH=$OUT:\$LEAN_PATH lean -o $OUT/GlueDescent/Chi.olean scratch/glue-descent/Chi.lean"`,
the same for `B2Glue`, then `lake env bash -c "LEAN_PATH=$OUT:\$LEAN_PATH lean scratch/glue-descent/B2Assembly.lean"`.
-/

namespace GlueDescent.B2Q

open GlueDescent GlueDescent.B2 NumberField

local instance (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

end GlueDescent.B2Q


end DescB2AssemblySec

section DescB3AssemblySec
/-! ### Copied from `scratch/glue-descent/B3Assembly.lean` (compiled there). -/

/-!
# glue-descent: B3 over `G_ℚ` (N5 L701-716), from the leaves of B2

`b3_of_leaves`: with the hypotheses of `b2_of_leaves` and `ε` normalized (`ε(1,1) = 1`), there
are `χ`, `β` as in B2 and an intermediate field `L' ⊇ L` of `ℚ̄/ℚ` (the kernel field of
`β|_{G_L}`), Galois over `ℚ`, with `G_{L'} = ker(β|_{G_L})`, `β` constant on the cosets of
`G_{L'}`, and `[L' : ℚ] ≤ 2 · ord(χ) · [L : ℚ]`.

`b3_degree_le_QM`: if moreover `[L:ℚ] ≤ D` and `T = S ∪ supp M_S(u)` for an admissible `(S, R)`,
then `[L' : ℚ] ≤ Q_R · M_S(u)` (the repository's `heightQ`, `contactSupport`).

Not here: that `L'` is unramified outside `T` after the twist of N5 L702-709. Its group theory is
`twist_kills_inertia` and `inertia_le_kernel` (Cochain.lean); it needs inertia subgroups of
`G_ℚ` (absent from Mathlib) and leaves L-B3a, L-B3b.

Compile out of tree as in B2Assembly.lean (oleans for Cochain, Constants, Chi, B2Glue,
B2Assembly in `scratch/glue-descent/.lake/out/GlueDescent/`).
-/

namespace GlueDescent.B3Q

open GlueDescent GlueDescent.B2 GlueDescent.B2Q

instance : IsGalois ℚ (AlgebraicClosure ℚ) := {}

end GlueDescent.B3Q


end DescB3AssemblySec

section RepoA1QuaternionSec
/-! ### Copied from `scratch/glue-repo/A1Quaternion.lean` (compiled there). -/

/-!
# glue-repo, step A1: the quaternion datum and the Riemann form (N5 L405-418)

`B = (2,-3)` is Mathlib's `ℍ[ℚ, 2, 0, -3]` (`i² = 2`, `j² = -3`, `k = ij`).
`𝒪 = ℤ⟨1, i, (1+j)/2, (i+ij)/2⟩` is a genuine `Subring B`, and `μ = 2j + ij`.
Proved here (no `sorry`): `μ² = -6`; `𝒪` is a subring (an order) with reduced discriminant 6
(`det Trd(eₐ e_b) = -36`); the Gram matrix of `E(x,y) = Trd(μ⁻¹ x ȳ)` in N5's basis is N5's
matrix, with determinant 1; `E` is alternating and `E(ax, y) = E(x, a† y)` with
`a† = μ⁻¹ ā μ`; `†` is an anti-involution; `†` is positive: `Trd(a a†) > 0` for `a ≠ 0`.
-/

open Quaternion

attribute [local simp] QuaternionAlgebra.re_ofNat QuaternionAlgebra.imI_ofNat QuaternionAlgebra.imJ_ofNat QuaternionAlgebra.imK_ofNat

namespace GlueRepo.A1

/-! ### Elliptic elements (h-b1 M9, Lemma NV step 2; rv-h-cm (Emb)) -/

/-! ### `𝒪/3𝒪` and its unit group (A3: `|(𝒪/3𝒪)^*| = 72`)

`𝒪/3𝒪` is `(ZMod 3)⁴` (coordinates in N5's basis) with the reduction `mul3` of the structure
constants `combMul`; `red3_mul` says reduction mod 3 of coordinates is multiplicative. -/

/-! ### `B` is a division algebra; the toric part of PR(ii) step 2 vanishes -/

end GlueRepo.A1


end RepoA1QuaternionSec

section RepoTorsionFreeSec
/-! ### Copied from `scratch/glue-repo/TorsionFree.lean` (compiled there). -/

/-!
# glue-repo, steps A6 and A8: `1 + 3 M_r(R)` is torsion-free; Minkowski's bound

* `CommCore.eq_one_of_pow_eq_one`: in a commutative ring in which `3` is a non-zero-divisor
  and `⋂ₙ 3ⁿ C = 0`, an element `A ≡ 1 (mod 3)` of finite order is `1`.
* `eq_one_of_pow_eq_one`: the same in any ring (applied in the commutative subalgebra `ℤ[y]`).
* `matrix_int_eq_one`, `matrix_padic_eq_one`: the same for `M_r(ℤ)` and `M_r(ℤ₃)` (N5 L468-470;
  h-b1 Lemma PR(ii) step 3: `ρ(I_v)` finite inside `1 + 3M₄(ℤ₃)` is trivial; A4's neatness).
* `injective_mod_three`, `card_le_three_pow`: a finite subgroup of `GL_r(ℤ)` injects into
  `GL_r(𝔽₃)`, so has order `≤ 3^(r²)` (N5 L551-553, step A8: `[E:ℚ] ≤ 3^{r²}`).
-/

namespace GlueRepo.TorsionFree

namespace CommCore

variable {C : Type*} [CommRing C]
variable (h3 : ∀ x : C, (3 : C) * x = 0 → x = 0)
variable (hsep : ∀ x : C, (∀ n : ℕ, ∃ y, x = (3 : C) ^ n * y) → x = 0)

include h3

end CommCore

section General

variable {S : Type*} [Ring S]

end General

section Matrices

variable {r : ℕ} {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]

end Matrices

end GlueRepo.TorsionFree


end RepoTorsionFreeSec

section RepoPRArithSec
/-! ### Copied from `scratch/glue-repo/PRArith.lean` (compiled there). -/

/-!
# glue-repo, steps A5 and A7: the arithmetic of Lemma PR(i) (h-b1 §4) and of the fibre point

For `u ∈ ℚ ∖ 𝒞`, `j₀ = J(u) = −57600 F(u)²/G(u)⁶`. Prop. TS (h-b1 §1.2, a published theorem)
says: at a prime `p` where the cover `Y₃ → P¹_j` is tame with no vertical ramification
(Lemma NV, `p ≥ 5`), the inertia of the fibre field at `p` has order `e_b / gcd(e_b, m_b)`, where
`m_b` is the intersection multiplicity of `j₀` with the branch point `b ∈ {0, ∞, −16/27}`,
`(e₀, e_∞, e_{−16/27}) = (4, 6, 2)`: the orbifold orders of `Γ*` (Baba–Granath §3.1, p. 740),
which are the indices of `Y₃ → P¹_j` because the level-3 group is torsion-free
(`GlueRepo.TorsionFree`); they are not indices of the degree-4 map `X₆ → X₆/W` (index 2). Here we prove the elementary half of Lemma PR(i):

* `inertia_trivial_iff` : for every prime `p ≥ 17` and `u ∈ ℚ ∖ 𝒞`,
  `4 ∣ m₀ ∧ 6 ∣ m_∞ ∧ 2 ∣ m_{−16/27}` (i.e. all three predicted inertia orders are 1)
  iff no `v_p(u − c)`, `c ∈ 𝒞`, is positive and odd; with `m₀ = v_p(j₀)⁺`,
  `m_∞ = (−v_p(j₀))⁺`, `m_{−16/27} = v_p(j₀ + 16/27)⁺`.
* `inertia_trivial_of_not_dvd` : the same in terms of `M_S(u) = ZInQ.contactSupport S u`.
* `Hq_ne_zero`, `J_ne_zero`, `J_ne_branch` : `j₀` is finite, nonzero and `≠ −16/27`
  (h-b1 M7; A7 "j = J(u) is rational, finite and nonzero").
* `G6_sub_F2`, `J_add`, `t_eq`, `t_sub_one` : N5 L510-516 and rv-h-cm §1.4.
-/

open _root_.ZInQ

namespace GlueRepo.PR

/-! ### Nonvanishing -/

/-! ### The valuation case analysis of Lemma PR(i) -/

section Valuation

variable {p : ℕ} [hp : Fact p.Prime]

end Valuation

/-! ### NoCM: the fibre of `X⁶ → X*` over `t(u)` (A10; rv-h-cm §2.4, §7.2 step 3)

In Elkies' model `ℚ(X⁶) = ℚ(t)(y₁, y₂)`, `y₁² = −t`, `y₂² = 3(t − 1)` (rv-h-cm §2.3; `w₂`, `w₆`,
`w₃` negate `y₂`, `y₁`, both). Over `t(u)` the four points are `(±i h₁, ±i h₂)` with
`h₁ = H/G³`, `h₂ = 540F/G³`, both nonzero: a free `W`-orbit, with coordinates in `ℚ(i)`, no
coordinate real (so the residue field is not `ℚ`), and complex conjugation acting as `w₃`. -/

end GlueRepo.PR


end RepoPRArithSec

section RepoNumericsSec
/-! ### Copied from `scratch/glue-repo/Numerics.lean` (compiled there). -/

/-!
# glue-repo, steps A3, A5 and A8: the numerical bookkeeping

* `a3_numerals`: `4·|(𝒪/3𝒪)^*| = 4·72 ≤ 4·81 = 324`, and `|Γ'| = 4·72/2 = 144 = 2⁴3²`
  (N5 L436-441; h-b1 M3). The count `|(𝒪/3𝒪)^*| = 72` is `GlueRepo.A1.card_units_mod3`.
* `splitting_degree_le`: a separable polynomial over `ℚ` of degree `≤ 324` has splitting field of
  degree `≤ 324! = F₀` (N5 L524-526: `[K:ℚ] ≤ F₀`).
* `a8_rank`, `a8_degree`, `a8_field`: `r ≤ 16F₀²` and `[EK:ℚ] ≤ [K:ℚ]·[E:ℚ] ≤ F₀·3^{r²} ≤ D`
  (N5 L544-555), for variables `F₀`, `D = F₀·3^{256F₀⁴}` (the bodies of `ZInQ.heightF0`,
  `ZInQ.heightD`; the kernel cannot unfold those constants, see `HeightConstant.lean`).
-/

open _root_.ZInQ Module Polynomial

namespace GlueRepo.Numerics

end GlueRepo.Numerics


end RepoNumericsSec

section ObjBridgeSec
/-! ### Copied from `scratch/obj-bridge/Objects.lean` §C-§F (lines 1129-1795; its copies of pkg-I3 and pkg-I2, §A-§B, dropped in favour of this file's `PkgI3`, `PkgI2`; hsyn-fold). -/

noncomputable section

/-! # §C. The shared object layer -/

namespace ObjBridge

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
-- op-dedupe was: open PkgI2 (IsAbelianVariety)
open _root_.PkgI2 (IsAbelianVariety) -- op-dedupe
open scoped Quaternion TensorProduct

variable {K : Type} [Field K]

section Derived

variable (A B : Grp (Over (Spec (.of K)))) [IsAbelianVariety A] [IsAbelianVariety B]

variable (ℓ : ℕ) [Fact ℓ.Prime]

end Derived

/-! ## The bridge on morphisms is a bijection -/

section Bridge

variable {A B C : Grp (Over (Spec (.of K)))} [IsAbelianVariety A] [IsAbelianVariety B]
  [IsAbelianVariety C]

end Bridge

/-! ## Objects: quantifying over `AbVar K` is quantifying over the shared objects -/

/-! ## Points: one definition (I2's `Pts`, over any `K`-algebra), which is I3's `Pt` for fields -/

section Points

variable (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A] (L : Type) [Field L] [Algebra K L]

end Points

end ObjBridge

/-! # §D. The I2 and I3 leaves restated over the shared layer, with equivalences -/

namespace ObjBridge

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
-- op-dedupe was: open PkgI2 (IsAbelianVariety IsAbelianScheme Pts torsion galAct IsInertia HasGoodReduction InertiaTrivialOn UnipSq baseChange IsReductionOf)
open _root_.PkgI2 (IsAbelianVariety IsAbelianScheme Pts torsion galAct IsInertia HasGoodReduction InertiaTrivialOn UnipSq baseChange IsReductionOf) -- op-dedupe
open Polynomial
open scoped Quaternion TensorProduct

/-! ## I2 leaves

Universe fixed to `Type`. Points, torsion, Galois action, inertia, good reduction and base change
are the shared ones (I2's single definitions; for a field `L`, `Pts A L` is I3's `Pt` by `rfl`,
`pts_eq`). The leaves that do not involve `Hom`/`End` are I2's text at `Type` with
`topologicalKrullDim A.X.left` written `dim A`; each is `Iff.rfl` to the original. I2-Char and
I2-Rank are restated with the shared `End`/`Hom` (I3's ring and ℤ-module through the bridge). -/

/-! ## I3 leaves

Each is I3's text with `A : AbVar k` replaced by `A : Grp (Over (Spec k))` with
`[IsAbelianVariety A]`, and `End`, `End0`, `T`, `V`, `galRep`, `dim`, `tateHomZl` the shared ones.
Equivalence with the original: `forall_abVar_iff`-style round trips (`ofGrp (toGrp A) = A` is
`rfl`). -/

/-! ## I3 glue over the shared layer (proved) -/

end ObjBridge

/-! # §E. Base change and functoriality on the shared layer -/

namespace ObjBridge

open CategoryTheory AlgebraicGeometry Limits MonObj
-- op-dedupe was: open PkgI2 (IsAbelianVariety)
open _root_.PkgI2 (IsAbelianVariety) -- op-dedupe

section BaseChange

variable {K : Type} [Field K] (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A]
  (L : Type) [Field L] [Algebra K L]

end BaseChange

section Functoriality

variable {K : Type} [Field K] {A B C : Grp (Over (Spec (.of K)))} [IsAbelianVariety A]
  [IsAbelianVariety B] [IsAbelianVariety C]

variable (ℓ : ℕ) [Fact ℓ.Prime]

end Functoriality

end ObjBridge

/-! # §F (obj-bridge): NOT adopted here (hsyn-fold). In this file the proof of
`ObjBridge.homRankBound_of_homFreeFinite` fails: instance search does not find
`AddCommMonoid (ObjBridge.Hom A B)` at `LinearIndependent ℤ f` (also with raised heartbeats),
although it compiles in `scratch/obj-bridge/Objects.lean`. The consolidation "I2-Rank follows from
I3.M1" (`pkgI2_homRankBound_of_pkgI3_homFreeFinite`) is therefore only in obj-bridge's file. -/

end

end ObjBridgeSec

section GlueC10Sec
/-! ### Copied from `scratch/glue-c10/C10.lean` (compiled there; hsyn-fold). -/
open NumberField

namespace GlueC10

/-! ## Leaves (copied from pkg-I6) -/

/-! ## Part A. Finite level (the form recommended by glue-I6-rest)

A representation that factors through a finite Galois group `Gal(M/ℚ)`: traces that agree at
every unramified Frobenius outside `S` agree everywhere, hence the representations are
isomorphic. -/

/-! ## Part B. The absolute Galois group `G_ℚ` -/

example : GQ = Field.absoluteGaloisGroup ℚ := rfl

/-! ### Proof of `FrobLift` (merged from `Lift.lean`) -/

/-- **Step (c) of `FrobLift` (GLUE, proved).** -/
theorem restrictNormal_eq_of_frob (E : IntermediateField ℚ Qbar) [FiniteDimensional ℚ E]
    [IsGalois ℚ E] (τ : E ≃ₐ[ℚ] E) (p : ℕ) [Fact p.Prime] (Q : Ideal (𝓞 E)) [Q.IsPrime]
    (hQp : Q.under ℤ = Ideal.span {(p : ℤ)}) [Algebra.IsUnramifiedAt ℤ Q]
    (hτ : IsArithFrobAt ℤ τ Q) (h : GQ) (P : Ideal Zbar) (hPQ : P.comap (toZbar E) = Q)
    (hh : ∀ x y : Zbar, (y : Qbar) = h (x : Qbar) - (x : Qbar) ^ p → y ∈ P) :
    AlgEquiv.restrictNormal h E = τ := by
  have : NumberField E := ⟨⟩
  set σ := AlgEquiv.restrictNormal h E
  have hσ : IsArithFrobAt ℤ σ Q := by
    intro x
    rw [hQp, card_quot, ← hPQ, Ideal.mem_comap]
    apply hh (toZbar E x)
    rw [map_sub, map_pow, AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, toZbar_coe,
      toZbar_coe]
    congr 1
    exact AlgEquiv.restrictNormal_commutes h E (x : E)
  have hQ : Q.primeCompl ≤ nonZeroDivisors (𝓞 E) := by
    intro x hx
    apply mem_nonZeroDivisors_of_ne_zero
    rintro rfl
    exact hx Q.zero_mem
  have heq := AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt hσ hτ hQ
  ext y
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) y
  have ha := congrArg (fun f => ((f a : 𝓞 E) : E)) heq
  have hb := congrArg (fun f => ((f b : 𝓞 E) : E)) heq
  simp only [MulSemiringAction.toAlgHom_apply] at ha hb
  have key : ∀ (g : E ≃ₐ[ℚ] E) (c : 𝓞 E), g (algebraMap (𝓞 E) E c) = ((g • c : 𝓞 E) : E) :=
    fun g c => rfl
  have e1 := (key σ a).trans (ha.trans (key τ a).symm)
  have e2 := (key σ b).trans (hb.trans (key τ b).symm)
  rw [map_div₀, map_div₀, e1, e2]

/-! ## Part C. N5's transport from five to three -/

end GlueC10

end GlueC10Sec

section LeafPushSec
/-! ### Copied from `scratch/leaf-push/Push.lean` (compiled there; hsyn-fold), over PkgI2. -/
universe u

open CategoryTheory AlgebraicGeometry Limits
open scoped CategoryTheory.MonObj Quaternion

namespace LeafPush

/-! ## 1. Abelian varieties, points, Galois action, inertia (copied from pkg-I2) -/

-- hsyn-fold: pkg-I2 copy (Push.lean §1) replaced by PkgI2's definitions.
open PkgI2

/-! ## 2. R8: Grothendieck's semistable reduction theorem, monodromy form -/

/-- **R8 (consequence form). Grothendieck's semistable reduction theorem.**
Published statement: SGA 7 I, Exp. IX, Thm 3.6 (UNVERIFIED numbering): an abelian variety `A`
over the fraction field `K` of a discrete valuation ring acquires semistable reduction over a
finite separable extension; Prop. 3.5 of the same exposé (UNVERIFIED): semistable reduction at
`w` is equivalent to "every inertia element `σ` acts on `T_ℓ A` with `(σ - 1)² = 0`" (`ℓ`
invertible in the residue field). Lean form: there is a finite `K' ⊆ K̄` such that every inertia
element of `w` fixing `K'` satisfies `(σ - 1)² = 0` on every `A(K̄)[ℓⁿ]`. This is the image of
Thm 3.6 under the direction "semistable ⇒ unipotent of echelon 2" of Prop. 3.5, applied over
`K'` (whose inertia at `w` is `I_w ∩ G_{K'}`); the finite-level form is equivalent to the
Tate-module form because `T_ℓ A → A[ℓⁿ]` is onto. It is therefore a consequence, never stronger.
Identical to `PkgI2.GrothendieckMonodromy` (pkg-I2), restated here so that R8 is counted as a
concrete leaf. Used only on h-b1's route for A6 (Raynaud's route R6 avoids it). -/
def R08_GrothendieckMonodromy : Prop :=
  ∀ (K : Type u) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K)),
    w.comap (algebraMap K (AlgebraicClosure K)) = O →
    ∀ (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A],
      ∃ K' : IntermediateField K (AlgebraicClosure K), FiniteDimensional K K' ∧
        ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, IsInertia w σ →
          (∀ x ∈ K', σ x = x) →
          ∀ ℓ : ℕ, ℓ.Prime → IsUnit (ℓ : O) →
            ∀ n : ℕ, ∀ x ∈ torsion A (AlgebraicClosure K) (ℓ ^ n), UnipSq A σ x

/-! ## 3. T9: the Weil pairing, finite-level Galois form -/

/-- **T9 (consequence form). Weil pairing of a polarization.**
Published statements (Mumford, *Abelian varieties*, §20: the Weil pairing
`e_n : A[n] × Â[n] → μ_n` is bilinear, perfect, Galois-equivariant, with `e_{mn}(x, y) = e_n(mx, y)`;
§23: for `λ = φ_L`, `e^L_n(x, y) := e_n(x, λ y)` is skew-symmetric with `e^L_n(x, x) = 1`;
Milne, *Abelian varieties* (in Cornell–Silverman 1986), §§13, 16; numbering UNVERIFIED), with the
existence over `K` of an ample line bundle `L` (Mumford §6), whose polarization `λ = φ_L` has
kernel killed by some `d ≥ 1`. Lean form: for an abelian variety `A/K` there are `d ≥ 1` and a
family `e n : A(K̄) × A(K̄) → K̄` such that for every `n ≥ 1` invertible in `K`, on `A[n]`:
values in `μ_n`, bimultiplicative, alternating, Galois-equivariant (`e(σx, σy) = σ(e(x, y))`),
compatible (`e_n(x^m, y^m) = e_{mn}(x, y)^m`), and nondegenerate up to `d` (if `e_n(x, y) = 1`
for all `y ∈ A[n]` then `x^d = 1`). Take `e n x y := e_n(x, λ y)`. The last clause: there is
`ψ : Â → A` with `λ ∘ ψ = [d]`, so `d·Â[n] ⊆ λ(A[n])`, and perfectness of `e_n` gives `d x = 0`.
Equivariance holds since `λ` is defined over `K`. Hence a consequence, never stronger.
The form used at C8 step 1 (h-trust; `ℓ = 5`): passing to the limit over `n = ℓᵏ` gives a
`G_K`-equivariant alternating pairing on `T_ℓ A` with values in `ℤ_ℓ(1)` whose kernel is killed by
`d`, hence perfect on `V_ℓ A`: `G_K` acts through `GSp` with cyclotomic multiplier, for every `ℓ`
invertible in `K` (glue). The group of points is written multiplicatively, as in pkg-I2. -/
def T09_WeilPairing : Prop :=
  ∀ (K : Type u) [Field K] (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A],
    ∃ d : ℕ, 0 < d ∧ ∃ e : ℕ → Pts A (AlgebraicClosure K) → Pts A (AlgebraicClosure K) →
        AlgebraicClosure K,
      ∀ n : ℕ, 0 < n → (n : K) ≠ 0 →
        (∀ x ∈ torsion A (AlgebraicClosure K) n, ∀ y ∈ torsion A (AlgebraicClosure K) n,
          e n x y ^ n = 1) ∧
        (∀ x ∈ torsion A (AlgebraicClosure K) n, ∀ x' ∈ torsion A (AlgebraicClosure K) n,
          ∀ y ∈ torsion A (AlgebraicClosure K) n,
            e n (x * x') y = e n x y * e n x' y ∧ e n y (x * x') = e n y x * e n y x') ∧
        (∀ x ∈ torsion A (AlgebraicClosure K) n, e n x x = 1) ∧
        (∀ x ∈ torsion A (AlgebraicClosure K) n,
          (∀ y ∈ torsion A (AlgebraicClosure K) n, e n x y = 1) → x ^ d = 1) ∧
        (∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
          ∀ x ∈ torsion A (AlgebraicClosure K) n, ∀ y ∈ torsion A (AlgebraicClosure K) n,
            e n (galAct A σ x) (galAct A σ y) = σ (e n x y)) ∧
        (∀ m : ℕ, 0 < m → (m : K) ≠ 0 →
          ∀ x ∈ torsion A (AlgebraicClosure K) (m * n),
          ∀ y ∈ torsion A (AlgebraicClosure K) (m * n),
            e n (x ^ m) (y ^ m) = e (m * n) x y ^ m)

/-! ## 4. T29: local normalizers of maximal quaternion orders -/

section T29

variable (p : ℕ) [Fact p.Prime]

/-- `x ∈ ℚ_p` lies in `ℤ_p`. -/
def IsPadicInt (x : ℚ_[p]) : Prop := ‖x‖ ≤ 1

/-- An element of `ℍ[ℚ_p, a, b] = (a, b)_{ℚ_p}` is integral: its reduced trace `x + x̄` and
reduced norm `x x̄` (scalars) lie in `ℤ_p`. -/
def QIntegral {a b : ℚ_[p]} (x : ℍ[ℚ_[p], a, b]) : Prop :=
  (∃ t : ℚ_[p], IsPadicInt p t ∧ x + star x = (t : ℍ[ℚ_[p], a, b])) ∧
  (∃ n : ℚ_[p], IsPadicInt p n ∧ x * star x = (n : ℍ[ℚ_[p], a, b]))

/-- `u` is a unit of the ring of integral elements: `u` and some integral `v` with `u v = 1`. -/
def IsOUnit {a b : ℚ_[p]} (u : ℍ[ℚ_[p], a, b]) : Prop :=
  QIntegral p u ∧ ∃ v : ℍ[ℚ_[p], a, b], QIntegral p v ∧ u * v = 1 ∧ v * u = 1

/-- **T29(a) (division case). Vignéras, LNM 800, Ch. II, §1 (UNVERIFIED numbering: Lemme 1.5,
Thm 1.6 / Cor. 1.7).** Published statement: if `H` is the quaternion division algebra over
`ℚ_p`, the integral elements form a ring `𝒪`, the unique maximal order; there is `π` with
`v(nrd π) = 1`, every `x ∈ H^×` is `π^k u` with `u ∈ 𝒪^×`, and hence (with `ℚ_p^× = p^ℤ ℤ_p^×`,
`p = π²·unit`) `H^× / ℚ_p^× 𝒪^×` has order 2, generated by `π`; and `N(𝒪) = H^×` since `𝒪` is
defined by `nrd`, `trd`, which are conjugation-invariant. Lean form, for `(a, b)_{ℚ_p}` whose
norm form is anisotropic (`x x̄ = 0 → x = 0`, i.e. a division algebra): the integral elements
are closed under `+` and `*`; there is an integral `π` that is not a scalar multiple of a unit of
`𝒪`; and every nonzero `x` is `c·u` or `c·π·u` with `c ∈ ℚ_p^×`, `u ∈ 𝒪^×`. This is the
statement "index exactly 2" written out; it is a restatement of the published one. -/
def T29a_DivisionNormalizer : Prop :=
  ∀ a b : ℚ_[p], (∀ x : ℍ[ℚ_[p], a, b], x * star x = 0 → x = 0) →
    (∀ x y : ℍ[ℚ_[p], a, b], QIntegral p x → QIntegral p y →
      QIntegral p (x + y) ∧ QIntegral p (x * y)) ∧
    ∃ π : ℍ[ℚ_[p], a, b], QIntegral p π ∧
      (¬ ∃ c : ℚ_[p], ∃ u : ℍ[ℚ_[p], a, b], IsOUnit p u ∧
          π = (c : ℍ[ℚ_[p], a, b]) * u) ∧
      ∀ x : ℍ[ℚ_[p], a, b], x ≠ 0 →
        ∃ c : ℚ_[p], c ≠ 0 ∧ ∃ u : ℍ[ℚ_[p], a, b], IsOUnit p u ∧
          (x = (c : ℍ[ℚ_[p], a, b]) * u ∨ x = (c : ℍ[ℚ_[p], a, b]) * π * u)

/-- A `2 × 2` matrix over `ℚ_p` with entries in `ℤ_p`. -/
def IsIntMat (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) : Prop := ∀ i j, IsPadicInt p (g i j)

/-- **T29(b) (split case). Vignéras, LNM 800, Ch. II, §2 (UNVERIFIED numbering).** Published
statement: the normalizer of `M₂(ℤ_p)` in `GL₂(ℚ_p)` is `ℚ_p^× GL₂(ℤ_p)`. Lean form, exactly
that: if `g` is invertible and `g M₂(ℤ_p) g⁻¹ = M₂(ℤ_p)`, then `g = c·k` with `c ∈ ℚ_p^×` and
`k ∈ GL₂(ℤ_p)` (entries in `ℤ_p`, determinant a unit of `ℤ_p`). -/
def T29b_SplitNormalizer : Prop :=
  ∀ g : Matrix (Fin 2) (Fin 2) ℚ_[p], IsUnit g.det →
    (∀ m, IsIntMat p m ↔ IsIntMat p (g * m * g⁻¹)) →
    ∃ c : ℚ_[p], c ≠ 0 ∧ ∃ k : Matrix (Fin 2) (Fin 2) ℚ_[p], IsIntMat p k ∧ ‖k.det‖ = 1 ∧
      g = c • k

end T29

/-! ## 5. T32: tame inertia and quadratic characters, over inertia subgroups of `G_ℚ` -/

end LeafPush

end LeafPushSec

section GlueT32aSec
/-! ### leaf-adopt (2026-11-12): copied from `scratch/glue-t32a/T32a.lean` (compiled there).
Only changes: imports and `#print axioms` lines dropped, and the two `namespace LeafPush` blocks
(T32a.lean L1473-1506, L1612-1632) dropped: they re-declare `LeafPush.GQ`, `IsAtPrime`,
`inertiaQ`, `T32b_QuadraticRamification`, `T32a_TameQuadratic`, whose bodies are identical to
section `LeafPushSec` above (checked by leaf-adopt), so `GlueB3Unram.t32a`, `t32b` below prove
this file's leaf-push statements. -/


/-!
# glue-b3-unram: the kernel field `L'` of B3 is unramified outside `T` (N5 L702-712)

glue-conj copy: `scratch/glue-b3-unram/Unram.lean` verbatim, plus the section `Conj` (proof of
`LeafConj` as glue, `leafConj`), and `unramified_outside_final` now takes only `LeafB3a`,
`LeafB3b`.

Self-contained (scratch files cannot import each other). The definitions `GQ`, `act`,
`toRingAut`, `cyc`, `galChar`, `isLocallyConstant_of_openSubgroup`, `cyc_eq_of_agree`,
`cyc_isLocallyConstant` are copied verbatim from `scratch/glue-descent/B2Glue.lean`.

Inertia subgroups of `G_ℚ` are taken through valuation subrings `w` of `ℚ̄`, as in pkg-I2:
`inertiaGQ w` is the image in `G_ℚ` of Mathlib's `ValuationSubring.inertiaSubgroup` (the
elements of the decomposition group of `w` acting trivially on the residue field of `w`).
`w` lies over `p` when `v_w(p) < 1`.

Unramifiedness of an intermediate field `L' ⊆ ℚ̄` at `p` is stated Galois-theoretically
(`GalUnramifiedOutside`): every inertia subgroup over `p` fixes `L'` pointwise.

Leaves (`def … : Prop`, over Mathlib objects only):
* `LeafB3a` (L-B3a): at an odd prime, inertia has at most one nontrivial locally constant
  quadratic character;
* `LeafB3b` (L-B3b): the Legendre character mod an odd prime `p` (as a character of `G_ℚ`
  through the cyclotomic character) is nontrivial on every inertia subgroup over `p`;
* `LeafConj`: places of `ℚ̄` over the same `p` are `G_ℚ`-conjugate, with conjugate inertia;
* `LeafFinRam`: an open subgroup of `G_ℚ` contains the inertia groups over all but finitely
  many primes. PROVED below as glue (`finRam`).
Glue proved here: `cycUnram` (the cyclotomic character mod `N` is trivial on inertia over
`p ∤ N`); the bridge `inertia_le_of_unramifiedAt` (glue-descent's `UnramifiedAt L p` gives
`I_w ≤ G_L`); `finRam`. The final theorem `unramified_outside_final` uses three leaves:
`LeafB3a`, `LeafB3b`, `LeafConj`.
-/

namespace GlueB3Unram

open NumberField

/-- `G_ℚ`. -/
abbrev GQ := Field.absoluteGaloisGroup ℚ

/-- `ℚ̄`. -/
abbrev Qbar := AlgebraicClosure ℚ

instance : IsTopologicalGroup GQ :=
  inferInstanceAs (IsTopologicalGroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))

instance : IsGalois ℚ (AlgebraicClosure ℚ) := {}

def act (σ : GQ) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ := σ

/-- The forgetful map `Gal(ℚ̄/ℚ) → Aut(ℚ̄)` as a monoid homomorphism. -/
noncomputable def toRingAut : GQ →* (AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) where
  toFun σ := σ.toRingEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The cyclotomic character `G_ℚ → (ℤ/N)^×`. -/
noncomputable def cyc (N : ℕ) [NeZero N] : GQ →* (ZMod N)ˣ :=
  haveI : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast NeZero.ne N⟩
  (modularCyclotomicCharacter (AlgebraicClosure ℚ)
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) N)).comp toRingAut

/-- A Dirichlet character as a character of `G_ℚ`. -/
noncomputable def galChar {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : GQ →* ℂˣ :=
  χ.toUnitHom.comp (cyc N)

theorem isLocallyConstant_of_openSubgroup {G X : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (U : Subgroup G) (hU : IsOpen (U : Set G)) (f : G → X)
    (hf : ∀ g, ∀ k ∈ U, f (g * k) = f g) : IsLocallyConstant f := by
  refine IsLocallyConstant.iff_isOpen_fiber.2 fun y => isOpen_iff_forall_mem_open.2 fun x hx =>
    ⟨(x * ·) '' U, ?_, isOpenMap_mul_left x _ hU, ⟨1, U.one_mem, mul_one x⟩⟩
  rintro _ ⟨k, hk, rfl⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx ⊢
  rw [hf x k hk, hx]

theorem cyc_eq_of_agree (N : ℕ) [NeZero N] (σ τ : GQ)
    (h : ∀ t ∈ rootsOfUnity N (AlgebraicClosure ℚ),
      act σ (t : AlgebraicClosure ℚ) = act τ (t : AlgebraicClosure ℚ)) :
    cyc N σ = cyc N τ := by
  haveI : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast NeZero.ne N⟩
  have hn := HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) N
  apply Units.ext
  show ((modularCyclotomicCharacter (AlgebraicClosure ℚ) hn (toRingAut σ) : (ZMod N)ˣ) : ZMod N) =
    ((modularCyclotomicCharacter (AlgebraicClosure ℚ) hn (toRingAut τ) : (ZMod N)ˣ) : ZMod N)
  apply modularCyclotomicCharacter.unique _ hn
  intro t ht
  rw [← modularCyclotomicCharacter.spec (AlgebraicClosure ℚ) hn (toRingAut σ) ht]
  exact (h t ht).symm

theorem cyc_isLocallyConstant (N : ℕ) [NeZero N] : IsLocallyConstant (cyc N) := by
  let S : Set (AlgebraicClosure ℚ) :=
    (fun t : (AlgebraicClosure ℚ)ˣ => (t : AlgebraicClosure ℚ)) ''
      (rootsOfUnity N (AlgebraicClosure ℚ) : Set (AlgebraicClosure ℚ)ˣ)
  have hfin : Finite (rootsOfUnity N (AlgebraicClosure ℚ) : Set (AlgebraicClosure ℚ)ˣ) :=
    (inferInstance : Finite (rootsOfUnity N (AlgebraicClosure ℚ)))
  haveI : Finite S := ((Set.toFinite _).image _).to_subtype
  let K : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.adjoin ℚ S
  haveI : FiniteDimensional ℚ K :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  refine isLocallyConstant_of_openSubgroup (G := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    K.fixingSubgroup K.fixingSubgroup_isOpen (fun g => cyc N g) ?_
  intro g k hk
  apply cyc_eq_of_agree
  intro t ht
  have hfix : act k (t : AlgebraicClosure ℚ) = t :=
    (IntermediateField.mem_fixingSubgroup_iff K k).mp hk _
      (IntermediateField.subset_adjoin ℚ S ⟨t, ht, rfl⟩)
  show g (k (t : AlgebraicClosure ℚ)) = g (t : AlgebraicClosure ℚ)
  exact congrArg g hfix

theorem galChar_isLocallyConstant {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    IsLocallyConstant (galChar χ) :=
  show IsLocallyConstant (χ.toUnitHom ∘ cyc N) from (cyc_isLocallyConstant N).comp _

/-! ## Places and inertia subgroups of `G_ℚ` -/

/-! ## The Legendre character mod `p` -/

/-! ## Leaves -/

/-! ## Elementary facts -/

/-! ## The kernel subgroup `{σ ∈ G_L : β σ = 1}` -/

section Kernel

variable (H : Subgroup GQ) (ε : GQ → GQ → ℂˣ) (β : GQ → ℂˣ)
  (hεN : ∀ σ τ, σ ∈ H ∨ τ ∈ H → ε σ τ = 1) (hβe : ∀ x y, β x * β y = ε x y * β (x * y))

end Kernel

/-! ## The main theorem -/

/-! ## Proof of `CycUnram` -/

/-! ## Bridge: ideal-theoretic unramifiedness gives trivial inertia -/

section Bridge

open NumberField

/-- glue-descent's `UnramifiedAt` (copied from `scratch/glue-descent/B2Glue.lean`). -/
def UnramifiedAt (L : IntermediateField ℚ Qbar) (p : ℕ) : Prop :=
  ∀ P : Ideal (𝓞 L), P.IsPrime → ((p : ℤ) : 𝓞 L) ∈ P → P.ramificationIdx ℤ = 1

variable (L : IntermediateField ℚ Qbar)

end Bridge

/-! ## `LeafFinRam` from the bridge and Mathlib's discriminant theorem -/

section FinRam

open NumberField

end FinRam

section Conj

/-! ## Proof of `LeafConj` (from glue-conj, `scratch/glue-conj/Conj.lean`) -/

open scoped Pointwise

/-! ## 1. The center lemma -/

/-! ## 2. Profinite transitivity on primes of the algebraic integers -/

/-! ## 3. Transport and inertia conjugation -/

/-! ## 4. Assembly -/

end Conj

/-! ## glue-b3b: `LeafB3b` is glue

`ℚ(√p*)` is ramified at `p`, proved without discriminants: with `α` the quadratic Gauss sum
(`α² = ±p`), `H` the stabilizer of `α` and `A = B^H` (the algebraic integers fixed by `H`),
Mathlib's profinite transitivity over `A` and its surjectivity of the stabilizer of a prime onto
the automorphisms of the residue extension (`Ideal.Quotient.stabilizerHom_surjective_of_profinite`)
produce an element of the inertia group of `w` with `s α = -α`. The input "the residue extension
of `A` is trivial" is replaced by valuation arithmetic: `v(α)² = v(p)`. -/

section B3b

open scoped Pointwise

variable {w : ValuationSubring Qbar} {p : ℕ}

end B3b

section B3bMain

open scoped Pointwise

end B3bMain

section B3bGauss

end B3bGauss


end GlueB3Unram


namespace GlueB3Unram

open scoped Pointwise

end GlueB3Unram


namespace GlueB3Unram

end GlueB3Unram



/-!
# glue-t32a: proof of T32(a) (`LeafPush.T32a_TameQuadratic`)

For an odd prime `p` and `w` over `p`, every continuous `χ : I_w → ℤˣ` is `1` or `η_g`, the
character `τ ↦ τ(g)/g` of `g = √p`. Proof: a Kummer generator `β` of `χ`; `v(β)` is a rational
power of `v(p)`; glue-b3b's `exists_inertia_neg` (an inertia element negating `√p`) forces the
exponent of `v(β)` to have odd denominator over `v(g)`; then `β^n / g^k` is a unit and inertia acts
trivially on it modulo `w`, which pins `χ = η_g^k`.
-/

namespace GlueB3Unram

open scoped Pointwise

section T32a

variable {w : ValuationSubring Qbar} {p : ℕ}

end T32a

end GlueB3Unram

end GlueT32aSec

section LeafQMSec
/-! ### leaf-adopt (2026-11-12): copied from `scratch/leaf-qm-fp/QMLeaves.lean` (compiled there).
Only changes: imports and `#print axioms` lines dropped, and one renaming: the kernel's
`GlueA6Alg.goodReduction_of_QM_rational3'` (ZInQKernel/HDecomp/A6/A6.lean) is this file's
`PkgI2.goodReduction_of_QM_rational3'` (same statement; the kernel module cannot be imported
here because its namespaces `PkgI2`, `PkgI3`, `ObjBridge` are also defined in this file).
`PkgI3.AbVar`, `ObjBridge.TorsionStructure`, `ObjBridge.dim` resolve to this file's copies,
which are those of ZInQKernel/HDecomp/Objects.lean. -/


/-!
# leaf-qm-fp: the field-point leaves R1fp, R1hecke, R2fp, R1rec, R5fp of the H decomposition

See `docs/research/leaf-qm-fp.md`. Blueprint: `docs/research/bp-qmmoduli.md` §2.3.
Over the kernel's `PkgI3.AbVar` (`ZInQKernel/HDecomp/Objects.lean`); the order `𝒪` and the QM
structures are copied from `scratch/bp-qmmoduli/QMAbVar.lean` (scratch files cannot import each
other). No `sorry`, no `axiom`.
-/

noncomputable section

namespace LeafQM

/-! ## §0 The order `𝒪` (copied from `scratch/bp-qmmoduli/QMAbVar.lean` §0) -/

namespace AV

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3

variable {K : Type} [Field K]

/-! ## §1 QM structures (copied from `QMAbVar.lean` §§1-2) -/

section EndPt

variable (A : AbVar K) (L : Type) [Field L] [Algebra K L]

end EndPt

/-! ## §2 Level-3 structures on `K`-rational points

**Change from bp-qmmoduli.** `QMAbVar.lean` puts `η` in `A(K̄)` with a Galois-invariance and an
ontoness clause; that form does not base-change without the counting leaf `TorsionStructure`.
Here `η : 𝒪 → A(K)` is `𝒪`-linear with kernel exactly `3𝒪`. For an abelian surface over a field
of characteristic `0` this is the same datum as an `𝒪`-linear isomorphism of group schemes
`(𝒪/3𝒪)_K ≅ A[3]`: `η` embeds `𝒪/3𝒪` (81 elements) into `A(K)[3] ⊆ A(K̄)[3]`, which has
`3^{2·2} = 81` elements (Mumford, *Abelian varieties*, §4 (iv), the kernel's leaf
`TorsionStructure`), so `η` is onto `A(K̄)[3]`, all of `A[3]` is `K`-rational, and the étale group
scheme `A[3]` is the constant one. Conversely an isomorphism `(𝒪/3𝒪)_K ≅ A[3]` gives such an `η`
on `K`-points. (STANDARD.) -/

namespace Level3

variable {A : AbVar K} {q : QMStr A}

end Level3

/-! ## §3 The objects `(A, ι, η)`, their isomorphisms and classes, and the action of `Γ'` -/

section Classes

variable {P Q R : QML3 K}

/-! ### Glue for A3: composition laws of `Γ'` on classes, and the level-structure torsor -/

end Classes

/-! ### Glue for A3 and A6: a level structure is onto `A(K̄)[3]` (from `TorsionStructure`) -/

section Onto

open ObjBridge

end Onto

/-! ### Glue A6 on the objects of the leaves (good reduction away from 3) -/

section A6

open ObjBridge

variable (P : QML3 K)

local notation "Kb" => AlgebraicClosure K

/-- **Glue A6 on the objects of the leaves**: every `QML3` object over a field of characteristic
0 has good reduction at every DVR in which 3 is a unit, from the kernel's leaves
`NeronOggShafarevich`, `RaynaudCriterion`, `TorsionStructure` (via
`PkgI2.goodReduction_of_QM_rational3'`). With R1fp, this applies to the fibre object over
`J(u)` (A4 + A6). -/
theorem QML3.goodReduction [CharZero K] (hNOS : PkgI2.NeronOggShafarevich.{0})
    (hRay : PkgI2.RaynaudCriterion.{0}) (hTors : PkgI2.TorsionStructure.{0})
    (Ov : ValuationSubring K) [IsDiscreteValuationRing Ov] (h3 : IsUnit (3 : Ov)) :
    PkgI2.HasGoodReduction (toGrp P.A) Ov := by
  have hdim : topologicalKrullDim (toGrp P.A).X.left = ((2 : ℕ) : WithBot ℕ∞) := P.surface
  exact PkgI2.goodReduction_of_QM_rational3' hNOS hRay hTors Ov (toGrp P.A) hdim
    (grpOfHom (P.q.iota oi)) (grpOfHom (P.q.iota oj)) (hI P) (hJ P) (hIJ P) h3
    (hrat P hTors)

end A6

/-! ## §4 QM pairs `(A, ι)` (the objects of `X₆ = X₀(6,1)`), the centralizer and CM -/

section CM

variable {A : AbVar K}

end CM

/-! ## §5 Base change as a relation, and fields of moduli

`IsBaseChangeOf f P Q` says that `Q/L` is `P/K` base-changed along `f : K → L`: a morphism of
schemes `g : Q.A → P.A` over `Spec f` that makes the square a pullback (so `Q.A ≅ P.A ×_K L` as
`L`-schemes), commutes with `ι`, and carries `η_Q` to `η_P` (in particular, at `a = 0`, the
identity section to the identity section; a morphism of abelian varieties preserving the identity
is a homomorphism, Mumford §4 Cor. 1, so the group laws correspond). Stated as a relation, it
needs neither the object `P.A ×_K L` nor `dim (A_L) = dim A` (not in Mathlib). -/

/-! ## §6 Maps to `P¹`, by charts

Mathlib v4.35 has no `P¹` with its point bijection. A morphism `π : X → P¹_ℤ` is the same as two
opens `U = π⁻¹(t ≠ ∞)`, `V = π⁻¹(t ≠ 0)` covering `X` with `f = π^*t ∈ Γ(U)`,
`g = π^*(1/t) ∈ Γ(V)`, `fg = 1` on `U ∩ V`, and `U ∩ V` the non-vanishing locus of `f` in `U` and
of `g` in `V` (glue the two charts `U → 𝔸¹`, `V → 𝔸¹` along `t ↦ 1/t`; STANDARD, e.g.
Hartshorne II.7.1). A scheme over `ℚ` maps to `P¹_ℚ` over `ℚ` exactly when it maps to `P¹_ℤ`. -/

/-! ## §7 Field points of a `ℚ`-scheme -/

/-! ## §8 The leaves -/

namespace Pin

/-! ## §3 The relabeling attack, re-run

`relabel Φ τ` and `IsNaturalRelabel` are rv-g0pieces' definitions (copied). Candidate content of
a new kernel module `ZInQKernel/HDecomp/QM/Pin.lean` (task qm-pin), after the full patch. -/

/-! ## §4 Optional strengthening for provability: the universal property on families

`PinUnique` needs R1(a)'s universal property, which the leaf does not carry. The clause
`R1univProps` carries it on families over proper smooth curves (all the comparison needs). With
it, the `Φ`-half of the comparison is compiled (`phi_part`), and what remains is
`MobiusGlue` (a morphism of curves `Y' → P¹` with the fibres and the three values of `π ∘ g` is
`π ∘ g`): algebraic geometry of curves, glue, not a leaf. -/

end Pin

end AV

end LeafQM
end

end LeafQMSec

section LeafModCurvesSec
/-! ### leaf-adopt (2026-11-12): copied from `scratch/leaf-modcurves/ModCurveLeaves.lean` (compiled there).
Only changes: imports and `#print axioms` lines dropped; two docstrings (of `R16_EichlerShimuraJ1'`
and `DimJ1Genus`) say that MC9 is a citation-chain fact, not a leaf (rv-blueprints M1); no
statement changed. `PkgI3.AbVar` and `GlueC10.IsFrobAt`, `GlueC10.Zbar` resolve to this file's
copies (those of ZInQKernel/HDecomp/Objects.lean and C10/C10.lean). -/


/-!
# leaf-modcurves: `X₁(N)`, `J₁(N)` over `ℚ` and the leaf R16 (Eichler–Shimura in `J₁(N)`)

Task leaf-modcurves (2026-11-12), following `docs/research/bp-modcurves.md`. Replaces the opaque
placeholder `R16_EichlerShimuraJ1` of `scratch/h-decomposition/Leaves.lean` by a concrete
statement over genuine definitions, and states the genus input of R18/E2.

Layout.
* §A (copied from `scratch/bp-modcurves/Gamma1Genus.lean`, lines 25-270): the Belyi degree and
  the genus formula of `Γ₁(N)`; `genus_Gamma1_le : genus (Γ₁ N) ≤ N²` (proved there and here).
* §B (copied from `scratch/h-decomposition/Leaves.lean`, namespace `PkgI4`): `ℚ̄`, `G_ℚ`;
  arithmetic Frobenius is the kernel's `GlueC10.IsFrobAt`; Mathlib cusp forms on `Γ₁(N)`, `q`-coefficients, nebentypus, normalized
  eigenforms, newforms. New: the coefficient field `K_f`.
* §C (copied from `scratch/bp-modcurves/ModularCurveDefs.lean`): the `j`-line, `E_j`,
  `K_N = ℚ(j)(x(P))`, and the affine chart `Y1j` (relative normalization of `Spec ℚ[j]` in `K_N`).
* §D (new): `IsX1Model N X`: `X` is a smooth proper geometrically connected integral curve over
  `ℚ` whose function field is isomorphic to `K_N` (function-field definition of `X₁(N)/ℚ`).
* §E (adapted from `scratch/bp-modcurves/Jacobian.lean`, now over the kernel's `PkgI3.AbVar`):
  `IsJacobian` (Albanese property), the leaf `JacobianExists` (Weil/Milne), `IsJacobian.unique`,
  `IsJ1 N J` (`J` is a Jacobian of some model of `X₁(N)`).
* §F (new): the leaf **R16** in existential form, `R16_EichlerShimuraJ1'`.
* §G (new): the genus leaf `DimJ1Genus`, the glue `dim_J1_le` (`dim J₁(N) ≤ N²`), Belyi functions
  (`IsBelyiFunction`) and the glue target `BelyiX1`.
* §H: the bundle `ModCurveLeaves`, and the glue `exists_J1`, `exists_J1_dim_le`.

No `sorry`, no `axiom`. Leaves and glue targets are `def … : Prop`.
-/

noncomputable section

/-! ## §A. Belyi degree and genus formula of `Γ₁(N)` (copied from bp-modcurves) -/

namespace LeafModCurves

section Genus

open Matrix CongruenceSubgroup ModularGroup MulAction
open scoped MatrixGroups


/-! ### Fixed points are conjugates in `±Γ` -/

/-! ### The bounds used in step E2 (N5 L868-871) -/

/-! ### `[SL₂(ℤ) : Γ₁(N)] ≤ N²`

Copied verbatim from `scratch/glue-assembly/E2Index.lean` (`GlueAssembly.index_Gamma1_le`),
since scratch files cannot import each other. The first column modulo `N` separates the left
cosets of `Γ₁(N)`. -/



/-- The first column of `γ ∈ SL₂(ℤ)` modulo `N`. -/
def firstColMod (N : ℕ) (γ : SL(2, ℤ)) : ZMod N × ZMod N :=
  (((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ), ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ))

/-- The algebra of `firstColMod_eq_iff`, over variables. -/
theorem firstCol_algebra {N : ℕ} (A B C : Matrix (Fin 2) (Fin 2) ℤ)
    (hda : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1) (hdet : C 0 0 * C 1 1 - C 0 1 * C 1 0 = 1)
    (c00 : C 0 0 = A 1 1 * B 0 0 - A 0 1 * B 1 0) (c10 : C 1 0 = -A 1 0 * B 0 0 + A 0 0 * B 1 0)
    (b00 : B 0 0 = A 0 0 * C 0 0 + A 0 1 * C 1 0) (b10 : B 1 0 = A 1 0 * C 0 0 + A 1 1 * C 1 0) :
    ((A 0 0 : ZMod N), (A 1 0 : ZMod N)) = ((B 0 0 : ZMod N), (B 1 0 : ZMod N)) ↔
      (C 0 0 : ZMod N) = 1 ∧ (C 1 1 : ZMod N) = 1 ∧ (C 1 0 : ZMod N) = 0 := by
  rw [Prod.mk.injEq]
  have hdaN := congrArg (fun x : ℤ => (x : ZMod N)) hda
  have hdetN := congrArg (fun x : ℤ => (x : ZMod N)) hdet
  push_cast at hdaN hdetN
  constructor
  · rintro ⟨h0, h1⟩
    have e00 : (C 0 0 : ZMod N) = 1 := by
      rw [c00]; push_cast; rw [← h0, ← h1]; linear_combination hdaN
    have e10 : (C 1 0 : ZMod N) = 0 := by
      rw [c10]; push_cast; rw [← h0, ← h1]; ring
    refine ⟨e00, ?_, e10⟩
    rw [e00, e10] at hdetN
    linear_combination hdetN
  · rintro ⟨e00, _, e10⟩
    constructor
    · rw [b00]; push_cast; rw [e00, e10]; ring
    · rw [b10]; push_cast; rw [e00, e10]; ring

theorem firstColMod_eq_iff (N : ℕ) (a b : SL(2, ℤ)) :
    firstColMod N a = firstColMod N b ↔ a⁻¹ * b ∈ Gamma1 N := by
  have hCe : ((a⁻¹ * b : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![(a : Matrix (Fin 2) (Fin 2) ℤ) 1 1, -(a : Matrix (Fin 2) (Fin 2) ℤ) 0 1;
        -(a : Matrix (Fin 2) (Fin 2) ℤ) 1 0, (a : Matrix (Fin 2) (Fin 2) ℤ) 0 0] *
        (b : Matrix (Fin 2) (Fin 2) ℤ) := by
    have e1 : ((a⁻¹ * b : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
        Matrix.adjugate (a : Matrix (Fin 2) (Fin 2) ℤ) * (b : Matrix (Fin 2) (Fin 2) ℤ) := rfl
    rw [e1, Matrix.adjugate_fin_two]
  have hBe : (b : Matrix (Fin 2) (Fin 2) ℤ) =
      (a : Matrix (Fin 2) (Fin 2) ℤ) * ((a⁻¹ * b : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
    have e2 : ((a * (a⁻¹ * b) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
        (a : Matrix (Fin 2) (Fin 2) ℤ) * ((a⁻¹ * b : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := rfl
    rw [← e2, mul_inv_cancel_left]
  have hdet := (a⁻¹ * b).det_coe
  have hda := a.det_coe
  rw [Matrix.det_fin_two] at hdet hda
  rw [Gamma1_mem]
  refine firstCol_algebra _ _ _ hda hdet ?_ ?_ ?_ ?_
  · rw [hCe]; simp [Matrix.mul_apply, Fin.sum_univ_two]; ring
  · rw [hCe]; simp [Matrix.mul_apply, Fin.sum_univ_two]
  · conv_lhs => rw [hBe]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  · conv_lhs => rw [hBe]
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **`[SL₂(ℤ) : Γ₁(N)] ≤ N²`.** -/
theorem index_Gamma1_le (N : ℕ) [NeZero N] : (Gamma1 N).index ≤ N ^ 2 := by
  classical
  let g : SL(2, ℤ) ⧸ Gamma1 N → ZMod N × ZMod N :=
    Quotient.lift (firstColMod N) fun a b hab =>
      (firstColMod_eq_iff N a b).2 (QuotientGroup.leftRel_apply.mp hab)
  have hg : Function.Injective g := by
    intro x y hxy
    induction x using QuotientGroup.induction_on
    induction y using QuotientGroup.induction_on
    exact QuotientGroup.eq.mpr ((firstColMod_eq_iff N _ _).1 hxy)
  rw [Subgroup.index_eq_card]
  calc Nat.card (SL(2, ℤ) ⧸ Gamma1 N) ≤ Nat.card (ZMod N × ZMod N) :=
        Nat.card_le_card_of_injective g hg
    _ = N ^ 2 := by rw [Nat.card_prod, Nat.card_zmod]; ring


end Genus

end LeafModCurves

/-! ## §B. Galois side and modular forms (copied from `Leaves.lean`, namespace `PkgI4`) -/

namespace LeafModCurves

open scoped MatrixGroups ModularForm

/-- `ℚ̄`. -/
abbrev Qbar := AlgebraicClosure ℚ

/-- `G_ℚ = Gal(ℚ̄/ℚ)` (definitionally `Field.absoluteGaloisGroup ℚ`). -/
abbrev GQ := Qbar ≃ₐ[ℚ] Qbar

/-- (`Leaves.lean`, `PkgI4`) `v` is a place of `ℚ̄` above the prime `p`. -/
def LiesOver (v : ValuationSubring Qbar) (p : ℕ) : Prop := (p : Qbar) ∈ v.nonunits

/-- (`Leaves.lean`, `PkgI4`) `σ` is an arithmetic Frobenius at the place `v` above `p`. -/
def IsArithFrob (σ : GQ) (v : ValuationSubring Qbar) (p : ℕ) : Prop :=
  σ ∈ v.decompositionSubgroup ℚ ∧ ∀ x ∈ v, σ x - x ^ p ∈ v.nonunits

/-- Cusp forms of weight `k` on `Γ₁(N)` (Mathlib). -/
abbrev CF (N : ℕ) (k : ℤ) := CuspForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k

/-- The `m`-th q-expansion coefficient `a_m(f)` (period 1). -/
def coeff {N : ℕ} {k : ℤ} (f : CF N k) (m : ℕ) : ℂ :=
  (UpperHalfPlane.qExpansion 1 f).coeff m

/-- `f` has nebentypus `χ`: `f|_k γ = χ(d) f` for `γ = (a b; c d) ∈ Γ₀(N)`. -/
def HasNebentypus {N : ℕ} {k : ℤ} (f : CF N k) (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ γ ∈ CongruenceSubgroup.Gamma0 N, (⇑f ∣[k] γ) = χ (((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod N) • ⇑f

/-- `f` is a normalized eigenform of all `T_n` with nebentypus `χ`, through its coefficients
(as in `Leaves.lean`). -/
def IsNormalizedEigenform {N : ℕ} {k : ℤ} (f : CF N k) (χ : DirichletCharacter ℂ N) : Prop :=
  HasNebentypus f χ ∧ coeff f 1 = 1 ∧
    ∀ m n : ℕ, 0 < m → 0 < n →
      coeff f m * coeff f n =
        ∑ d ∈ (Nat.gcd m n).divisors, χ (d : ZMod N) * (d : ℂ) ^ (k - 1) * coeff f (m * n / d ^ 2)

/-- `τ ↦ dτ` on `ℍ`, for `d ≥ 1`. -/
def scaleH (d : ℕ+) (τ : UpperHalfPlane) : UpperHalfPlane :=
  ⟨(d : ℂ) * (τ : ℂ), by
    have h := τ.coe_im_pos
    simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
    exact mul_pos (by exact_mod_cast d.pos) h⟩

/-- The old space of level `N`, weight `k` (as in `Leaves.lean`). -/
def oldSpace (N : ℕ) (k : ℤ) : Submodule ℂ (UpperHalfPlane → ℂ) :=
  Submodule.span ℂ {F | ∃ (M : ℕ) (d : ℕ+) (f : CF M k), 0 < M ∧ M ∣ N ∧ M < N ∧
    (d : ℕ) * M ∣ N ∧ F = fun τ => f (scaleH d τ)}

/-- `f` is a newform of level `N` with nebentypus `χ` (as in `Leaves.lean`). -/
def IsNewform {N : ℕ} {k : ℤ} (f : CF N k) (χ : DirichletCharacter ℂ N) : Prop :=
  IsNormalizedEigenform f χ ∧ (⇑f : UpperHalfPlane → ℂ) ∉ oldSpace N k

/-! ## §C. The `j`-line and `K_N = ℚ(j)(x(P))` (copied from bp-modcurves) -/

open WeierstrassCurve AlgebraicGeometry

/-! ## §D. Curves over a field and the function-field definition of `X₁(N)/ℚ` -/

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-! ## §E. The Jacobian as an Albanese predicate over `PkgI3.AbVar` -/

open PkgI3 PkgI3.AbVar

/-! ## §F. The leaf R16 (existential form) -/

section R16

variable (ℓ : ℕ) [Fact ℓ.Prime]

end R16

/-! ## §G. The genus and Belyi inputs of E2 / R18 -/

/-! ## §H. Existence, the bundle, and the glue that C9, E1, E2 will consume -/

/-! ## §I. G13: `ρ_{f,ι}` is a constituent of `V_ℓ(J₁(N)) ⊗ ℚ̄_ℓ` -/

section G13

variable (ℓ : ℕ) [Fact ℓ.Prime]

end G13

/-! ## §J. C9 bridge: R16's `ρ_{f,ι}` satisfies the `AttachedTo` trace clause of `Leaves.lean`

`Leaves.lean` (`PkgI4.GaloisRep.AttachedTo`, used by R14 `EigenformRepExists`) normalizes
coefficients through `ιC : ℚ̄ → ℂ` and `ιL : ℚ̄ → ℚ̄_ℓ`: at `p ∤ Nℓ` there is `α ∈ ℚ̄` with
`ιC α = a_p` and every arithmetic Frobenius has trace `ιL α`. R16 uses `ι : K_f → ℚ̄_ℓ`. The bridge
is `ι := ιL ∘ ιC⁻¹` on `K_f ⊆ ιC(ℚ̄)`. -/

section C9Bridge

variable (ℓ : ℕ) [Fact ℓ.Prime]

end C9Bridge

end LeafModCurves
end

end LeafModCurvesSec

section DefFaltingsSec
/-! ### leaf-adopt (2026-11-12): copied from `scratch/def-faltings/Faltings.lean` (compiled there).
Only changes: imports and `#print axioms` lines dropped. Note: its `ZInQ.DefFaltings.AbVar` is a
second copy of the kernel's abelian-variety structure (same five fields as `PkgI3.AbVar`: `X`
and four instances; fact-check w34b), so
R19-R21 and H5 are over that copy; `LeafAdopt.abVarEquiv` (proved) identifies the two, and
unifying the declarations is WP1 work. -/


/-!
# def-faltings: the stable Faltings height as an infimum of model heights

Task def-faltings (2026-11-12). Mathlib-only, self-contained (scratch files cannot import each
other). Sections 1-14 are copied from `scratch/bp-faltings/Hodge.lean` (namespace renamed); they
build the Arakelov degree of a Hermitian line on `Spec 𝓞_K`, the torus metric and `HodgeData`.
Sections 15-22 are new:

* 15. `AbVar`, `GroupModel` (copied from `scratch/bp-faltings/Models.lean`).
* 16. The Hodge line of a smooth group model `𝒢/𝓞_L` (nodes AV3, M2, M3), built from the local
  ring `𝒪_{𝒢,ξ}` at the identity `ξ` of the generic fibre: `cotangent = 𝔪_ξ/𝔪_ξ²`,
  `omega = ω_𝒢 = ⋂_s (image of I_{e(s)})`, `hodgeSpace g = L ⊗_{𝓞_L} ⋀^g cotangent`,
  `detLattice g = ⋀^g ω_𝒢`.
* 17. Complex points `𝒢(ℂ)_τ` with their group law (Mathlib), evaluation of regular functions,
  and **`IsAnalyticUniformization`**: the concrete Prop saying that `Φ : ℂ^g → 𝒢(ℂ)_τ` is a
  holomorphic surjective homomorphism with kernel `Λ`. This is where node AN3 enters: the
  *definition* constrains the archimedean data by this Prop; the *missing theorem* is
  `AnalyticUniformizationExists` (stated, unproved).
* 18. `MetrizedModel A L g`, `stableFaltingsHeight A : EReal` (node H3), Deligne's normalization.
* 19-20. Acceptance tests AT1 (elliptic curves) and AT2 (genus 2), statements and conditional
  forms (proved).
* 21. Leaves R19-R21 stated over `stableFaltingsHeight`; R18, R22: what is missing.
-/

namespace ZInQ.DefFaltings

open NumberField MeasureTheory

/-! ## 1. Norms and complex embeddings -/

section Embeddings

variable {K : Type*} [Field K] [NumberField K]

end Embeddings

/-! ## 2. Hermitian line bundles on `Spec 𝓞_K` and the Arakelov degree -/

section Arakelov

variable {K : Type*} [Field K] [NumberField K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

namespace HermitianLattice

variable (L : HermitianLattice K V)

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem _root_.HDec.ZInQ.DefFaltings.exists_smul_eq (hV : Module.finrank K V = 1)
    {s t : V} (hs : s ≠ 0) :
    ∃ b d : 𝓞 K, d ≠ 0 ∧ (d : K) • t = (b : K) • s := by
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' s hs).mp hV t
  obtain ⟨b, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) c
  refine ⟨b, d, nonZeroDivisors.ne_zero hd, ?_⟩
  have hd' : (algebraMap (𝓞 K) K d) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
  rw [← hc, smul_smul, mul_div_cancel₀ _ hd']

end HermitianLattice

end Arakelov

/-! ## 3. The archimedean term: a translation-invariant top form on a complex torus

For an abelian variety `A` over `ℂ` of dimension `g`, `A(ℂ) ≅ ℂ^g / Λ` with `Λ` the period lattice
(the analytic uniformization; not in Mathlib, see the blueprint node `AN3`). In these linear
coordinates every invariant top form is `η = c · dz₁ ∧ ⋯ ∧ dz_g`, and `(i/2) dz ∧ dz̄ = dx ∧ dy` is
Lebesgue measure on `ℂ = ℝ²` (Mathlib's `volume` on `ℂ`), so the Faltings metric
`‖η‖² = (i/2)^g ∫_{A(ℂ)} η ∧ η̄` (sign convention: the positive value, i.e. with the factor
`(-1)^{g(g-1)/2}` that reorders `η ∧ η̄` into `∏ (dz_k ∧ dz̄_k)`) is `|c|²` times the volume of a
fundamental domain. -/

section Torus

variable {g : ℕ}

variable (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

end Torus

/-! ## 4. The metrized Hodge bundle of an abelian variety given with a model

`HodgeData K g V` is what an abelian variety `A/K` of dimension `g`, *given with* a smooth
group-scheme model `𝒢/𝓞_K` and complex uniformizations, contributes to Faltings' definition:

* `V = ∧^g H⁰(A, Ω¹) = ∧^g Lie(A)^∨`, a `K`-line (blueprint node `AV4`);
* `lattice = ∧^g ω_𝒢 = ∧^g e*Ω¹_{𝒢/𝓞_K}` inside `V` (node `M3`);
* `periods σ`: the period lattice `H₁(A_σ(ℂ), ℤ)` in linear coordinates `z₁, …, z_g` of
  `Lie(A_σ(ℂ))` (node `AN3`);
* `coeff σ`: the `σ`-semilinear map `V → ℂ`, `η ↦ c` where `η ⊗_σ 1 = c · dz₁ ∧ ⋯ ∧ dz_g`.

These fields are **data produced by the missing nodes**, not hypotheses about an abstract
structure: in the full formalization `HodgeData.ofModel 𝒢 (uniformization)` constructs them, and
the theorems below then apply. -/

section Hodge

variable {K : Type*} [Field K] [NumberField K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

namespace HodgeData

variable {g : ℕ} (D : HodgeData K g V)

end HodgeData

end Hodge

/-! ## 5. Acceptance-test interface: elliptic curves

The definitions `hypGram`, `hypVol`, `finiteHeightPart`, `faltingsHeightEC` are copied verbatim
from `scratch/pkg-I5/I5.lean` (task pkg-I5), so that the acceptance test can be stated here. -/

section Acceptance

open Polynomial

variable {K : Type*} [Field K] [NumberField K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

/-- The period lattice of a `PeriodPair` as a lattice in `ℂ¹ = Fin 1 → ℂ`. -/
noncomputable def _root_.HDec.PeriodPair.lattice1 (L : PeriodPair) : Submodule ℤ (Fin 1 → ℂ) :=
  ZLattice.comap ℝ L.lattice (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℂ).toLinearMap

instance (L : PeriodPair) : DiscreteTopology (PeriodPair.lattice1 L) := by
  unfold PeriodPair.lattice1; infer_instance

instance (L : PeriodPair) : IsZLattice ℝ (PeriodPair.lattice1 L) := by
  unfold PeriodPair.lattice1; infer_instance

theorem _root_.HDec.PeriodPair.covolume_lattice1 (L : PeriodPair) :
    ZLattice.covolume (PeriodPair.lattice1 L) = ZLattice.covolume L.lattice :=
  ZLattice.covolume_comap L.lattice volume volume
    (e := ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℂ) (volume_preserving_funUnique (Fin 1) ℂ)

/-- **Acceptance test AT1, conditional form.** Let `D` be Hodge data of dimension 1 whose lattice
is free on `η₀`, whose period lattices are those of period pairs `L σ` with `η₀ ↦ dz`
(i.e. `η₀ = dx/(2y + a₁x + a₃)` and `L σ` the period lattice of `W^σ`: node AT1b), where the
Weierstrass polynomial of `W^σ` is `4x³ − g₂(L σ) x − g₃(L σ)` and the finite part of
`faltingsHeightEC` vanishes (`W` semistable and minimal at every prime, which is when `𝓞_K η₀` is
the Néron lattice: node AT1a). Then, given the area formula AT1c, `modelHeight D` equals pkg-I5's
`faltingsHeightEC W`. Proved. -/
theorem modelHeight_eq_faltingsHeightEC (hA : PeriodAreaFormula)
    (W : WeierstrassCurve K) [W.IsElliptic] (D : HodgeData K 1 V) {η₀ : V}
    (hspan : D.lattice = Submodule.span (𝓞 K) {η₀}) (hη₀ : η₀ ≠ 0)
    (L : (K →+* ℂ) → PeriodPair) (hper : ∀ σ, D.periods σ = (PeriodPair.lattice1 (L σ)))
    (hco : ∀ σ, D.coeff σ η₀ = 1)
    (hP : ∀ σ, (4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆ : K[X]).map σ =
      4 * X ^ 3 - C (L σ).g₂ * X - C (L σ).g₃)
    (hfin : finiteHeightPart W.j = ∑ σ : K →+* ℂ, Real.log ‖σ W.Δ‖) :
    D.modelHeight = faltingsHeightEC W := by
  rw [D.modelHeight_of_span hspan hη₀, faltingsHeightEC]
  rw [hfin, sub_self, zero_div, zero_sub]
  have hterm : ∀ σ : K →+* ℂ, torusMetricSq (D.periods σ) (D.coeff σ η₀) =
      hypVol 1 ((4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆ : K[X]).map σ) := by
    intro σ
    rw [hco, hper, hP, torusMetricSq, PeriodPair.covolume_lattice1, hA]
    simp
  simp only [hterm]
  have hd : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  field_simp

end Acceptance

/-! ## 6. Rescaling, and a sanity check that `HodgeData` is inhabited -/

section Sanity

variable {K : Type*} [Field K] [NumberField K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

/-- **Sanity check: `HodgeData` is inhabited** (the elliptic curve `ℂ/(ℤ + ℤi)` over `ℚ`, with
the lattice `ℤ · 1`; this is a consistency check of the structure, not a claim about a curve over
`ℚ`). -/
noncomputable def exampleHodge : HodgeData ℚ 1 ℚ where
  lattice := Submodule.span (𝓞 ℚ) {1}
  finrank_eq_one := Module.finrank_self ℚ
  isLattice := ⟨1, Submodule.mem_span_singleton_self 1, one_ne_zero, by
    unfold secIndex; rw [AddSubgroup.relIndex_self]; exact one_ne_zero⟩
  periods _ := (PeriodPair.lattice1 gaussianPair)
  periods_discrete _ := inferInstance
  periods_isZLattice _ := inferInstance
  coeff σ := ratCoeff σ
  coeff_ne_zero σ h := by
    have := congr_arg (fun f => f 1) h
    simp [ratCoeff] at this

theorem exampleHodge_modelHeight :
    exampleHodge.modelHeight = -(1 / 2) * Real.log (ZLattice.covolume gaussianPair.lattice) := by
  rw [HodgeData.modelHeight_of_span exampleHodge (η₀ := (1 : ℚ)) rfl one_ne_zero]
  have hu : (Finset.univ : Finset (ℚ →+* ℂ)) = {Rat.castHom ℂ} := by
    ext σ; simp [Subsingleton.elim σ (Rat.castHom ℂ)]
  rw [hu, Finset.sum_singleton]
  simp [exampleHodge, torusMetricSq, ratCoeff, PeriodPair.covolume_lattice1]

end Sanity

/-! ## 7. Hermitian lines given by fractional ideals: the closed formula (part of node AR3)

Every invertible `𝓞_K`-module with a trivialization of its generic fibre is a fractional ideal
`I ⊆ K`. For such lines `#(I / 𝓞_K x) · N(I) = |N_{K/ℚ}(x)|` (`secIndex_mul_absNorm`), so
`deg(I, ρ·|σ(·)|) = −log N(I) − ∑_σ log ρ_σ` (`arakelovDegree_ofFractionalIdeal`). This is the form
in which AT1a meets a Néron lattice `𝔞 · dx/(2y + a₁x + a₃)` that is not free (class number > 1). -/

section FractionalIdeal

open Pointwise
open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

end FractionalIdeal

/-! ## 8. Acceptance test AT1 for a non-free Hodge lattice

For an elliptic curve with semistable reduction everywhere, the Néron lattice of invariant
differentials is `𝔞 · ω` with `ω = dx/(2y + a₁x + a₃)` and `𝔞` the fractional ideal with
`ord_𝔭 𝔞 = (ord_𝔭 Δ − ord_𝔭 Δ_min)/12` (`Δ_min` the minimal discriminant at `𝔭`). With
`ord_𝔭 Δ_min = max(0, −ord_𝔭 j)` (semistable) and the product formula,
`−12 log N(𝔞) = ∑_{v∤∞} log⁺|j|_v − ∑_σ log|σΔ|`. That identity is node AT1a (literature: Néron
models of elliptic curves); here it is the hypothesis `hNeron`. -/

section AcceptanceIdeal

open Polynomial
open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

/-- The Hodge data `(𝔞 ⊆ K, Λ_σ)` of dimension 1: `V = K` (`ω ↦ 1`), lattice `𝔞`, period lattices
`(PeriodPair.lattice1 (L σ))`, `ω ↦ dz`. -/
noncomputable def HodgeData.ofIdeal (𝔞 : FractionalIdeal (𝓞 K)⁰ K) (h𝔞 : 𝔞 ≠ 0)
    (L : (K →+* ℂ) → PeriodPair) : HodgeData K 1 K where
  lattice := 𝔞
  finrank_eq_one := Module.finrank_self K
  isLattice := (HermitianLattice.ofFractionalIdeal 𝔞 h𝔞 (fun _ => 1) (fun _ => one_pos)).isLattice
  periods σ := (PeriodPair.lattice1 (L σ))
  periods_discrete _ := inferInstance
  periods_isZLattice _ := inferInstance
  coeff σ := embCoeff σ
  coeff_ne_zero σ h := by
    have := congr_arg (fun f => f 1) h
    simp [embCoeff] at this

end AcceptanceIdeal

/-! ## 9. Base change: the archimedean count (part of nodes AR3, H4)

Each complex embedding `σ` of `K` has exactly `[L:K]` extensions to `L`, so sums over the
embeddings of `L` of functions of the restriction are `[L:K]` times the sums over `K`. -/

section BaseChange

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

end BaseChange

/-! ## 10. AT1 for every Weierstrass model: translation invariance

`ω ↦ dz` forces `g₂ = c₄/12`, `g₃ = c₆/216` but `P_W = 4x³ + b₂x² + 2b₄x + b₆` equals
`4x³ − g₂x − g₃` only after the translation `x ↦ x − b₂/12`. The archimedean term is translation
invariant (Lebesgue measure on `ℂ`), so AT1 holds with a translation at each `σ`. -/

section Translate

open Polynomial
open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

end Translate

/-! ## 11. Base change of fractional-ideal Hermitian lines (node AR3, finite half)

`N_L(I𝓞_L) = N_K(I)^{[L:K]}` for fractional ideals (from Mathlib's `Ideal.absNorm_algebraMap` for
integral ideals), hence `deg_L((I, ρ)_{𝓞_L}) = [L:K] · deg_K(I, ρ)`: the Arakelov degree divided
by the absolute degree, i.e. the height, is invariant under base change. -/

section BaseChangeNorm

open scoped nonZeroDivisors

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

end BaseChangeNorm

/-! ## 12. Base-change invariance of the model height (node H4, dimension-1 Hodge data) -/

section BaseChangeHeight

open scoped nonZeroDivisors

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

end BaseChangeHeight

/-! ## 13. A numerical normalization check: `covol(ℤ + ℤi) = 1`, so `exampleHodge` has height 0 -/

section Gaussian

theorem exampleHodge_modelHeight_eq_zero : exampleHodge.modelHeight = 0 := by
  rw [exampleHodge_modelHeight, covolume_gaussianPair, Real.log_one, mul_zero]

end Gaussian

/-! ## 14. Tensor products of fractional-ideal Hermitian lines (node AR3)

For invertible `𝓞_K`-modules inside `K`, `I ⊗ J ≅ IJ`, and the tensor-product metric is the
product metric; the degree is additive. -/

section Tensor

open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

end Tensor

/-! ## 15. Abelian varieties and smooth group models (copied from `bp-faltings/Models.lean`) -/

section ModelsSec

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ExteriorAlgebra

/-! op-dedupe: the copies `AbVar`, `AbVar.baseChange`, `AbVar.dim` of `ZInQKernel/HDecomp/Objects.lean` are
removed: `AbVar` is the kernel's alias `ZInQ.DefFaltings.AbVar := PkgI3.AbVar`
(`ZInQKernel/Contrib/HeightBC/G0StableBC.lean`). -/

attribute [instance] GroupModel.grp GroupModel.smooth GroupModel.separated GroupModel.qc

/-! ## 16. The Hodge line of a smooth group model (nodes AV3, M2, M3)

Let `e : S = Spec 𝓞_L → 𝒢` be the unit section and `ξ = e(η_S)` the image of the generic point
(the identity of the generic fibre `𝒢_L ≅ A_L`). The local ring `𝒪_{𝒢,ξ}` is the local ring of
`A_L` at its origin, so `cotangent = 𝔪_ξ/𝔪_ξ²` is `ω_{A_L} = e*Ω¹_{A_L/L}` (an `L`-space of
dimension `g`; STANDARD, not proved here). For a point `s ∈ S`, `x = e(s)` specializes from `ξ`,
and `I_x = ker(𝒪_{𝒢,x} → 𝒪_{S,s})` is the ideal of the section at `x`; the image of `I_x` in
`𝔪_ξ/𝔪_ξ²` is the stalk at `s` of the conormal sheaf `e*(I/I²) = e*Ω¹_{𝒢/S}` (`𝒢/S` smooth;
EGA IV 17.2.5, UNVERIFIED locator). A locally free sheaf on the integral scheme `S` has global
sections the intersection of its stalks inside the generic stalk, hence

`ω_𝒢 = Γ(S, e*Ω¹_{𝒢/S}) = ⋂_s image(I_{e(s)})`   (`GroupModel.omega`).

Every module structure below is definitional (no proof obligations): the `𝓞_L`-module structure
on `cotangent` is restriction of scalars along the structure map `𝓞_L → 𝒪_{𝒢,ξ}`, and the
`L`-line is `hodgeSpace g = L ⊗_{𝓞_L} ⋀^g_{𝓞_L} cotangent` (`≅ ⋀^g_L ω_{A_L}` since `cotangent`
is an `L`-space; STANDARD). -/

namespace GroupModel

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

/-! ## 17. Complex points and the analytic uniformization (node AN3: the gap)

For `τ : L → ℂ`, the `ℂ`-points of `A_L` at `τ` are the `𝓞_L`-morphisms `Spec ℂ → 𝒢` with
`Spec ℂ → Spec 𝓞_L` given by `τ|_{𝓞_L}` (they factor through the generic fibre since `τ` is
injective). Mathlib gives them a group structure (`MonObj.Hom.group`). A regular function
`s ∈ Γ(U, 𝒪_𝒢)` has a value `evalAt p U s ∈ ℂ` at a point `p ∈ U(ℂ)`.

**`IsAnalyticUniformization 𝒢 τ Λ Φ`** says: `Φ : ℂ^g → 𝒢(ℂ)_τ` is a group homomorphism, onto,
with kernel exactly `Λ`; each `Φ⁻¹(U(ℂ))` is open and each regular function is holomorphic along
`Φ` there. With `Λ` a full lattice, `Φ` is then continuous for the analytic topology, so it
induces a continuous bijection of the compact `ℂ^g/Λ` onto the Hausdorff `A_τ(ℂ)`, a
homeomorphism, holomorphic, hence biholomorphic. Any two such `(Λ, Φ)` differ by a `ℂ`-linear
automorphism of `ℂ^g` (a holomorphic homomorphism of complex tori lifts to a linear map). These
are STANDARD facts of complex analysis, not proved here.

**The gap (AN3).** That such `(Λ, Φ)` *exists* is `AnalyticUniformizationExists` below: a
precisely stated Prop over Mathlib's objects, unproved (it is the uniformization theorem
`A(ℂ) ≅ ℂ^g/Λ`, Mumford, *Abelian varieties* §1, with GAGA-type input; locator UNVERIFIED). The
definition of the height does **not** assume it: the infimum ranges over models *together with*
a uniformization satisfying the Prop. Without the theorem one cannot prove the index set
nonempty, i.e. that the height is `< ⊤`. -/

end GroupModel

/-! ## 18. Metrized models and the stable Faltings height (node H3) -/

attribute [instance] FinExt.field FinExt.numberField FinExt.algebra

section HeightLemmas

variable {K : Type} [Field K] (A : AbVar K)

end HeightLemmas

/-! ### Independence of the uniformization (node H2, archimedean part)

Under the uniqueness half of AN3, the height of a metrized model depends only on the group model:
the coefficient map is determined by its values on the wedges `1 ⊗ df₁ ∧ ⋯ ∧ df_g`
(`GroupModel.semilinear_ext_wedge`), which change by `det T` under `Φ ↦ Φ ∘ T`
(`GroupModel.jacDet_comp`, the chain rule), and `HodgeData.modelHeight_recoord` absorbs `T`. -/

section UnifIndep

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

namespace GroupModel

variable (𝒢 : GroupModel A L)

end GroupModel

end UnifIndep

/-! ### The theorems that tie the definition to the literature (node H5), stated

`IsNeronModel` is the Néron mapping property (BLR 1.2/1, UNVERIFIED locator), stated with
Mathlib's objects: every morphism from the generic fibre of a smooth `𝓞_L`-scheme to `A_L`
extends uniquely. H5 is unproved; it needs Néron models (existence: BLR 1.4/3), semistable
reduction (SGA 7 IX 3.6) and the base change of semistable Néron models (SGA 7 IX 3.3), all
absent from Mathlib (locators UNVERIFIED). -/

section NeronSec

variable {K : Type} [Field K]

end NeronSec

/-! ## 19. Acceptance test AT1: elliptic curves

`IsEllipticCurveOf A W` identifies an abelian variety with the elliptic curve of a Weierstrass
equation using only Mathlib objects: the complement of the origin is an affine open whose ring of
functions is `K`-isomorphic to the affine coordinate ring `K[x, y]/(W)`. (Then `A` is the smooth
projective model of the function field of `W` with origin `O`, so `A ≅ E_W` as pointed curves,
and the group law with a given origin is unique by rigidity: STANDARD.) Mathlib v4.35 cannot yet
construct such an `A` from `W` (node AV7), so `AcceptanceEC` is a statement, not a theorem. -/

section AT1

open Polynomial

variable {K : Type} [Field K]

/-- The structure map `K → Γ(U, 𝒪_A)`. -/
noncomputable def AbVar.structMapOn (A : AbVar K) (U : A.X.left.Opens) : K →+* Γ(A.X.left, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ A.X.hom.appTop ≫
    A.X.left.presheaf.map (homOfLE le_top).op).hom

/-- The origin of `A` (image of the unit section). -/
noncomputable def AbVar.origin (A : AbVar K) : A.X.left :=
  (η[A.X] : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X).left
    ((⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K) : Spec (CommRingCat.of K))

/-- `A` is the elliptic curve `y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆`: `A ∖ {O}` is affine with
ring of functions `K[x, y]/(W)`, compatibly with `K`. -/
def IsEllipticCurveOf (A : AbVar K) (W : WeierstrassCurve K) : Prop :=
  ∃ U : A.X.left.Opens, (U : Set A.X.left) = {A.origin}ᶜ ∧ IsAffineOpen U ∧
    ∃ e : W.toAffine.CoordinateRing ≃+* Γ(A.X.left, U),
      ∀ c : K, e (algebraMap K W.toAffine.CoordinateRing c) = A.structMapOn U c

/-- **Acceptance test AT1 (statement).** For an elliptic curve over a number field, the general
definition agrees with pkg-I5's closed formula. Unproved: needs AV7 (an `A` with
`IsEllipticCurveOf A W` exists), AN3 for `g = 1` (AN4: `℘`), AN5 (`PeriodAreaFormula`), M2 for
the minimal Weierstrass model, AT1a (the Néron lattice) and H5 (the infimum is attained at the
Néron model over a semistable field). -/
def AcceptanceEC : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (W : WeierstrassCurve K) [W.IsElliptic] (A : AbVar K),
    IsEllipticCurveOf A W → stableFaltingsHeight A = (faltingsHeightEC W : EReal)

/-- **AT1, conditional form over the general definition (proved).** Let `M` be a metrized model
of `A` over `K` itself whose Hodge lattice is free on `η₀` with `η₀ ↦ dz` for period pairs
`Lp σ` (outputs of AN4 and M2 for a minimal semistable Weierstrass model: `η₀ = dx/(2y+a₁x+a₃)`),
with the Weierstrass polynomial equal to `4x³ − g₂x − g₃` after a translation `x ↦ x + c_σ`
(so any `b₂` is allowed: `g₂ = σ(c₄)/12`, `g₃ = σ(c₆)/216`) and the finite part of
`faltingsHeightEC` vanishing (AT1a: the model is semistable and minimal everywhere). Then, given
the area formula AN5, `M.hodge.modelHeight = faltingsHeightEC W` (the content of the theorem),
and with `hmin` the stable height equals it.

Caveat: `hmin` ("no metrized model of `A` has smaller height") is literally the `≥` half of the
conclusion. It is the output H5 must supply for this `A`: the Néron mapping property
(`GroupModel.IsNeronModel`, `NeronModelMinimal`) plus semistable base change (SGA 7 IX), none of
which is proved. The theorem ties `M` to `W` only through the hypotheses on `M`; it does not
assume `IsEllipticCurveOf A W`. -/
theorem stableFaltingsHeight_eq_faltingsHeightEC [NumberField K] (hA : PeriodAreaFormula)
    (W : WeierstrassCurve K) [W.IsElliptic] (A : AbVar K) (M : MetrizedModel A K 1)
    {η₀ : M.model.hodgeSpace 1}
    (hspan : M.hodge.lattice = Submodule.span (𝓞 K) {η₀}) (hη₀ : η₀ ≠ 0)
    (Lp : (K →+* ℂ) → PeriodPair) (hper : ∀ σ, M.hodge.periods σ = (PeriodPair.lattice1 (Lp σ)))
    (hco : ∀ σ, M.hodge.coeff σ η₀ = 1) (c : (K →+* ℂ) → ℂ)
    (hP : ∀ σ, (4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆ : K[X]).map σ =
      (4 * X ^ 3 - C (Lp σ).g₂ * X - C (Lp σ).g₃).comp (X + C (c σ)))
    (hfin : finiteHeightPart W.j = ∑ σ : K →+* ℂ, Real.log ‖σ W.Δ‖)
    (hmin : ∀ (E : FinExt K) (g : ℕ) (M' : MetrizedModel A E.L g),
      faltingsHeightEC W ≤ M'.hodge.modelHeight) :
    stableFaltingsHeight A = (faltingsHeightEC W : EReal) := by
  have hM : M.hodge.modelHeight = faltingsHeightEC W := by
    rw [M.hodge.modelHeight_of_span hspan hη₀, faltingsHeightEC, hfin, sub_self, zero_div,
      zero_sub]
    have hterm : ∀ σ : K →+* ℂ, torusMetricSq (M.hodge.periods σ) (M.hodge.coeff σ η₀) =
        hypVol 1 ((4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆ : K[X]).map σ) := by
      intro σ
      rw [hco, hper, hP, hypVol_one_comp_add, torusMetricSq, PeriodPair.covolume_lattice1, hA]
      simp
    simp only [hterm]
    have hd : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
    field_simp
  refine le_antisymm ?_ ?_
  · exact (stableFaltingsHeight_le A M).trans_eq (by rw [hM])
  · exact le_stableFaltingsHeight A fun E g M' => EReal.coe_le_coe_iff.mpr (hmin E g M')

end AT1

/-! ## 20. Acceptance test AT2: genus-2 curves with a smooth model

`Genus2Eq`, `Genus2Eq.P`, `Genus2Eq.binDisc`, `Genus2Eq.Good` and `faltingsHeightGood` are copied
from `scratch/pkg-I5/I5.lean`. A statement "`stableFaltingsHeight (Jac C) = faltingsHeightGood E`"
cannot be written: Mathlib v4.35 has no Jacobians (node AV7) and no way to say that an `AbVar` is
the Jacobian of a curve. What is proved is the conditional form: a metrized model whose Hodge
lattice is free on `η₀` (M8: for a smooth Weierstrass model `𝒞/𝓞_K`, the Néron lattice is
`∧² H⁰(𝒞, ω) = 𝓞_K · (dx/(2y+h)) ∧ (x dx/(2y+h))`, BLR 9.5 Thm 4, Liu, UNVERIFIED locators) and
whose archimedean metric of `η₀` is the Gram determinant `hypVol 2` (AN6: Riemann's bilinear
relations), with `hmin` (H5), has `stableFaltingsHeight = faltingsHeightGood E`. -/

section AT2

open Polynomial

namespace Genus2Eq

variable {R : Type*} [CommRing R]

end Genus2Eq

end AT2

/-! ## 21. The leaves R19-R21 over `stableFaltingsHeight`

Normalizations (docs/research/locators.md): Gaudron-Rémond (R19) and Faltings (R20) use the
stable height in Faltings' original normalization, which is `stableFaltingsHeight`; Bost's bound
(R21) is used in the form `h_F ≥ −(3/2) dim A` printed by Gaudron-Rémond §9; Pazuki (R22) uses
Deligne's metric, `stableFaltingsHeightDeligne = stableFaltingsHeight + (g/2) log π`
(`stableFaltingsHeightDeligne_eq`).

Where the height is an input of an upper bound (R19, R20), it is taken through a real `x` with
`stableFaltingsHeight A = x`, never through `EReal.toReal` (whose junk value `0` at `⊤` would
make the statement stronger than the published one). Isogenies: homomorphisms of group schemes
that are finite and surjective (project's `IsIsogenyMor`); the degree is the order of the kernel
on `K̄`-points, which equals the degree in characteristic `0` (STANDARD). -/

section Leaves

open MonObj

variable {K : Type} [Field K]

end Leaves

/-! ## 22. R18 and R22: not stated

* **R22 (Pazuki, Bull. SMF 140 (2012), Cor. 1.3(2)).** The height side is available:
  `stableFaltingsHeightDeligne` and `stableFaltingsHeightDeligne_eq` give
  `h_D = h_F + log π` for surfaces, so the condition `X_D ≥ max(1, h_D(A))` of the consequence
  form is expressible. Missing: principal polarizations, level-2 theta structures and the theta
  (Fubini-Study) height `h_Θ(A)` of a principally polarized abelian surface (the theta constants
  need the period matrix, i.e. AN3 together with the Riemann form). The genus-2 special case over
  `faltingsHeightGood` is `PkgI5.PazukiGoodGenus2Literal` (scratch/rv-loc-leaves).
* **R18 (Javanpeykar, ANT 8 (2014), Thm 1.1.1).** Missing: the genus of a smooth projective
  curve over `ℚ̄` (differentials or `H¹`), Belyi maps (finite morphisms to `ℙ¹` unramified outside
  `{0, 1, ∞}`, with their degree) and the Jacobian as an `AbVar` (node AV7). -/

end ModelsSec

end ZInQ.DefFaltings

end DefFaltingsSec

section LeafAdoptSec
/-! ### leaf-adopt (2026-11-12): repairs of rv-blueprints to the leaf statements, and H5

New in this file (not copied). Over the definitions of the sections above:
* **Q4** (`π₀(X₆) = 1`): `R1pi0Props X`, Mathlib's `GeometricallyConnected` for `X₆ → Spec ℚ`.
* **Q5** (biconditional CM clauses of R2fp): `R2X6PropsIff`; it follows from leaf-qm-fp's one-way
  clauses together with `CMExists` (`r2X6PropsIff_of`, proved from `LeafQM.AV.cm_of_val`), and
  it gives `CMExists` back with `X6Surj` (`cmExists_of_iff`).
* The repaired bundle `R1R2fpRep` (R1(a), R1(c), R1(d) on points, R1 at level one, R2 with
  biconditional CM clauses, R5 on points, and `π₀ = 1`, on one `Y₃` and one `X₆`), with
  `R1R2fp_of_rep : R1R2fpRep → LeafQM.AV.R1R2fp` (the source bundle is a consequence).
* **Q2** (R5fpStrong): `R5fpStrong` is rv-blueprints' statement transcribed over leaf-qm-fp's
  definitions (`QMPair`, `fieldOfModuliPair`); `R5fp_iff_R5fpStrong` proves it equivalent to
  leaf-qm-fp's `R5fp`, which already carries `k ↪ ℚ(x)`.
* **F2** (H5 as an explicit leaf): `H5 = StableHeightFinite ∧ NeronModelMinimal` of def-faltings.
-/

namespace LeafAdopt

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-- **R1pi0 (rv-blueprints Q4): `X₆` is geometrically connected over `ℚ`.** For the level-one
curve `X₆ = X₀(6,1)` of the bundle, `X₆ ×_ℚ ℚ̄` is connected (`π₀(X₆_ℚ̄) = 1`), the input of
h-b1 M10 (Lemma NV step 4) and of the shape `ℚ(t)(√(at), √(b(t−1)))` in A10 step 2.
*Published*: Deligne, Sém. Bourbaki 389 (1971), §2: `π₀(Sh_{K₀}) = ℚ^×_{>0}\𝔸_f^×/nrd(K₀)`,
trivial for `K₀ = 𝒪̂^×` since `nrd(𝒪̂^×) = ℤ̂^×` (locator UNVERIFIED; rv-blueprints re-derived the
computation, and `π₀(Y₃) = 2` from `nrd(1 + 3𝒪₃) = 1 + 3ℤ₃`). *Alternative*: rv-blueprints Q4
sketches a glue proof from `R5fpCount` and the CM clauses (Kummer parity of branch points;
SPECULATIVE, not checked in detail). Counted inside leaf R1 (same publications), not as a new
leaf. -/
def R1pi0Props (X : Over (Spec (CommRingCat.of ℚ))) : Prop :=
  GeometricallyConnected X.hom

/-- **R2 on `X₆` with biconditional CM clauses (rv-blueprints Q5).** As `R2X6Props`, with
"CM by `ℤ[i]` (resp. `ℤ[ζ₃]`, `ℤ[√−6]`) `↔` `π₆ = 0` (resp. `∞`, `−16/27`)". *Published*:
Baba–Granath 2008, Thm 2.1 and the §3.1 elliptic-order table (each of `CM(−4)`, `CM(−3)`,
`CM(−24)` is one `W`-orbit, the fibre over the corresponding value); a consequence, as
`R2X6Props` is. In the bundle it is not an extra assumption: `r2X6PropsIff_of` derives it from
`R2X6Props` and `CMExists`. -/
def R2X6PropsIff (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (π₆ : ToP1 X.left) : Prop :=
  ∀ (x x' : fieldPt Qbar ⟶ X) (P Q : QMPair Qbar),
    Ψ x = Quotient.mk _ P → Ψ x' = Quotient.mk _ Q →
      (π₆.val (K := Qbar) x.left = π₆.val (K := Qbar) x'.left ↔
          ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q)) ∧
      (HasCM4 P.q ↔ π₆.val (K := Qbar) x.left = OnePoint.some 0) ∧
      (HasCM3 P.q ↔ π₆.val (K := Qbar) x.left = OnePoint.infty) ∧
      (HasCM24 P.q ↔ π₆.val (K := Qbar) x.left = OnePoint.some (-16 / 27))

variable {X : Over (Spec (CommRingCat.of ℚ))} {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)}
  {π₆ : ToP1 X.left}

/-- **Glue (proved): Q5 from leaf-qm-fp's clauses.** The one-way clauses with `CMExists` give
the biconditionals (through `cm_of_val`). -/
theorem r2X6PropsIff_of (h2 : R2X6Props X Ψ π₆) (hE : CMExists X Ψ) : R2X6PropsIff X Ψ π₆ := by
  intro x x' P Q hP hQ
  obtain ⟨hf, h4, h3, h24⟩ := h2 x x' P Q hP hQ
  obtain ⟨c4, c3, c24⟩ := cm_of_val h2 hE x P hP
  exact ⟨hf, ⟨h4, c4⟩, ⟨h3, c3⟩, ⟨h24, c24⟩⟩

/-- The biconditional form gives back the one-way form. -/
theorem r2X6Props_of_iff (h : R2X6PropsIff X Ψ π₆) : R2X6Props X Ψ π₆ := by
  intro x x' P Q hP hQ
  obtain ⟨hf, h4, h3, h24⟩ := h x x' P Q hP hQ
  exact ⟨hf, h4.1, h3.1, h24.1⟩

/-- **Glue (proved): existence of the three CM points** from the biconditionals and the
surjectivity of `π₆` on `ℚ̄`-points (the first half of `X6Surj`). -/
theorem cmExists_of_iff (h : R2X6PropsIff X Ψ π₆)
    (hs : ∀ t : OnePoint Qbar, ∃ x : fieldPt Qbar ⟶ X, π₆.val (K := Qbar) x.left = t) :
    CMExists X Ψ := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hs (OnePoint.some 0)
    exact ⟨x, (Ψ x).out, (Quotient.out_eq _).symm,
      ((h x x _ _ (Quotient.out_eq _).symm (Quotient.out_eq _).symm).2.1).2 hx⟩
  · obtain ⟨x, hx⟩ := hs OnePoint.infty
    exact ⟨x, (Ψ x).out, (Quotient.out_eq _).symm,
      ((h x x _ _ (Quotient.out_eq _).symm (Quotient.out_eq _).symm).2.2.1).2 hx⟩
  · obtain ⟨x, hx⟩ := hs (OnePoint.some (-16 / 27))
    exact ⟨x, (Ψ x).out, (Quotient.out_eq _).symm,
      ((h x x _ _ (Quotient.out_eq _).symm (Quotient.out_eq _).symm).2.2.2).2 hx⟩

/-- **The Shimura-curve leaves R1 (a), (c), (d) on points, R1 at level one, R2, R5 on points,
with the repairs Q4 (`π₀(X₆) = 1`) and Q5 (biconditional CM clauses), on one `Y₃` and one `X₆`.**
This is `LeafQM.AV.R1R2fp` with `R2X6Props ∧ CMExists` replaced by `R2X6PropsIff` (equivalent
given `X6Surj`: `r2X6PropsIff_of`, `cmExists_of_iff`) and the clause `R1pi0Props X` added.

**Premise: Lemma QP (rv-qm-polar §0; leaf-adopt2).** `QML3` and `QMPair` omit the polarization
`λ`. Every clause is the published statement for the type-`μ` PEL problem (Shimura 1967 Main
Thms I-II; Deligne 1971 Thm 4.21, Cor. 5.7, Ex. 5.8, §§2, 4.8-4.17; Baba–Granath 2008 Thm 2.1,
Lemma 3.1, §3.1; González–Rotger 2006 Prop. 5.6, Thm 5.12) or a consequence of it **together
with** Lemma QP: for a fixed `μ` (N5's `2j+ij`), a QM pair `(A, ι)` over a field of characteristic
0 (`𝒪` maximal) has exactly one principal polarization with Rosati involution `x ↦ μ⁻¹x̄μ` on
`ι(𝒪)`, also at CM points (rv-qm-polar §2: no statement needs correcting, and the λ-free
clauses do not depend on the choice of `μ`). Lemma QP is VERIFIED as an argument (rv-qm-polar
§1.2; lattice core and sign step compiled for N5's `μ` on `Λ = 𝒪` only: `eq_pm_E0_of_principal`,
`type_eq_mu_mul`, `lemmaP_lattice` (Lemma QP; Lean name unchanged in rv-qm-polar and the kernel); the `E0R`/`E0` identification, `Λ = 𝒪v`, Riemann forms ↔
polarizations, class number one and the descent from `ℂ` not in Lean; fact-check w34b item 3);
its published locators
(Buzzard 1997 p. 592; Rotger 2003, 2004) are UNVERIFIED, and if they print only uniqueness its
existence half becomes glue. Without fixing `μ` the polarization is not unique (one per type
`c`, `c² = −6`, up to sign; `two_principal_types`). Polarizations cannot be stated in Lean today,
so Lemma QP is folded into the leaf rather than a separate hypothesis. Buzzard's
polarization-free moduli problem would remove it (UNVERIFIED for full level 3). Also: the audit's verdict on R1 is "qualified consequence" (the specialization of Deligne's
PEL model to this functor needs a human check). -/
def R1R2fpRep : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
    (fY : Y ⟶ X) (π₆ : ToP1 X.left),
    R1fpProps Y Φ ∧ R1heckeProps Y Φ ∧ X6Props Y Φ X Ψ fY ∧ R2X6PropsIff X Ψ π₆ ∧
      R1recProps Y Φ ∧ X6Surj Y X fY π₆ ∧ R5ptProps X Ψ ∧ R1pi0Props X

/-- **Glue (proved)**: the repaired bundle implies leaf-qm-fp's `R1R2fp`, so every glue theorem
of leaf-qm-fp (`conj_iso_of_rational`, `cm_of_val`, `residue_unramified_over_branch`,
`exists_fibre_object`, `leaves_on_one_witness`, ...) applies to it. -/
theorem R1R2fp_of_rep (h : R1R2fpRep) : R1R2fp := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, h1, hh, h6, h2, hr, hs, h5, -⟩ := h
  exact ⟨Y, Φ, X, Ψ, fY, π₆, h1, hh, h6, r2X6Props_of_iff h2, cmExists_of_iff h2 hs.1, hr, hs, h5⟩

/-- **R5fpStrong (rv-blueprints Q2)**, transcribed from `scratch/rv-blueprints/R5Repair.lean`
(there over bp-qmmoduli's `(A, q)` with `A.dim = 2`; here over leaf-qm-fp's `QMPair`, which
carries `A.dim = 2`, and `fieldOfModuliPair`). González–Rotger 2006 Thm 5.12 with
`[H_R : k] = #Pic R`: for `b = #{p ∣ 6 inert in k} ≥ 1`, `[ℚ(x):ℚ] = 2·#Pic R` and `k ↪ ℚ(x)`;
for `b = 0`, `[ℚ(x):ℚ] = #Pic R`. Premise Lemma QP (rv-qm-polar) as for `R1R2fpRep`. -/
def R5fpStrong : Prop :=
  ∀ (k : Type) [Field k] [NumberField k] [NumberField.IsTotallyComplex k],
    Module.finrank ℚ k = 2 →
    ∀ R : Subring k, R ≤ (integralClosure ℤ k).toSubring → Nat.Coprime (conductor R) 6 →
      ∀ P : QMPair Qbar, Nonempty (com P.q ≃+* R) →
        (1 ≤ inertCount6 k →
            Module.finrank ℚ (fieldOfModuliPair P) = 2 * Nat.card (CommRing.Pic R) ∧
              Nonempty (k →ₐ[ℚ] fieldOfModuliPair P)) ∧
        (inertCount6 k = 0 →
            Module.finrank ℚ (fieldOfModuliPair P) = Nat.card (CommRing.Pic R))

/-- **Proved**: leaf-qm-fp's `R5fp` is rv-blueprints' `R5fpStrong` (Q2 is already satisfied by
the adopted leaf). -/
theorem R5fp_iff_R5fpStrong : R5fp ↔ R5fpStrong := by
  constructor
  · intro h k _ _ _ hk R hR hc P hP
    obtain ⟨h1, h2⟩ := h k hk R hR hc P hP
    refine ⟨fun hb => ?_, fun hb => ?_⟩
    · have hb' : inertCount6 k ≠ 0 := by omega
      rw [if_neg hb'] at h1
      exact ⟨h1, h2 hb'⟩
    · rw [if_pos hb] at h1
      simpa using h1
  · intro h k _ _ _ hk R hR hc P hP
    obtain ⟨h1, h0⟩ := h k hk R hR hc P hP
    by_cases hb : inertCount6 k = 0
    · rw [if_pos hb]
      exact ⟨by simpa using h0 hb, fun h' => absurd hb h'⟩
    · rw [if_neg hb]
      exact ⟨(h1 (by omega)).1, fun _ => (h1 (by omega)).2⟩

/-- **H5 (rv-blueprints F2): the stable Faltings height is the published one, as an explicit
leaf.** `StableHeightFinite` (over a number field, `stableFaltingsHeight A ∈ ℝ`) and
`NeronModelMinimal` (over each `L`, a group model with the Néron mapping property has the least
height). Each of R18-R22 is a consequence of its publication only together with H5
(rv-blueprints §1.2), and the direction `h(A) + h(Z) ≤ h(A × Z)` of additivity that E4 uses needs
Néron models and H5 (F1). *Published*: Faltings 1983 §1; Deligne, Sém. Bourbaki 616 (1983);
Bosch–Lütkebohmert–Raynaud, *Néron models* (1990) 1.2/1, 1.4/3; SGA 7 I, Exp. IX 3.3, 3.6
(locators UNVERIFIED). **Caveat**: `StableHeightFinite` holds for def-faltings' infimum only if
its index set is nonempty, which is what the open Props `AnalyticUniformizationExists` and
`HodgeLatticeTheorem` (with `AnalyticUniformizationUnique` for independence of the
uniformization) assert; they are true theorems (Mumford §1 with GAGA; smoothness of `𝒢`) but
unproved in Lean. So H5 as stated is "published theorem + correctness of the definition". -/
def H5 : Prop :=
  ZInQ.DefFaltings.StableHeightFinite ∧ ZInQ.DefFaltings.NeronModelMinimal

/-- **Bridge (proved)**: def-faltings' copy of the abelian-variety structure and this file's
`PkgI3.AbVar` (= the kernel's) are the same data (for `K : Type`), so R19-R21 and H5 transfer to
`PkgI3.AbVar` along this equivalence; unifying the two declarations is WP1 work. -/
def abVarEquiv (K : Type) [Field K] : ZInQ.DefFaltings.AbVar K ≃ PkgI3.AbVar K where
  toFun A := { X := A.X }
  invFun A := { X := A.X }
  left_inv _ := rfl
  right_inv _ := rfl

theorem abVarEquiv_dim (K : Type) [Field K] (A : ZInQ.DefFaltings.AbVar K) :
    (abVarEquiv K A).dim = A.dim := rfl

end LeafAdopt

end LeafAdoptSec

section LeafPush2Sec

/-!
# leaf-push2: concrete statements of R18, R22, R3 over the new definitions

(leaf-adopt2, 2026-11-12: this section is `scratch/leaf-push2/LeafPush2.lean` copied verbatim,
without its imports and `#print axioms`; only the R3 docstring now cites Lemma QP of
rv-qm-polar. `PkgI3.AbVar` and `PkgI4.IsComplexConj` resolve to this file's copies of the
kernel's `ZInQKernel/HDecomp/Objects.lean` definitions. Part I duplicates `DefFaltingsSec` with
`PkgI3.AbVar` in place of the local `ZInQ.DefFaltings.AbVar`, see `LeafAdopt.abVarEquiv`.)

Task leaf-push2 (2026-11-12). One file. Contents:

* Part I (copied from `scratch/def-faltings/Faltings.lean` §§1-18 and the H5 section, namespace
  renamed to `ZInQ.LeafPush2`; the local copy of `AbVar` is **replaced by the kernel's
  `PkgI3.AbVar`** (`ZInQKernel/HDecomp/Objects.lean`), so the stable Faltings height is defined on
  the same abelian varieties as the Jacobians of leaf-modcurves). Nothing in Part I is new.
* Part II (copied from `scratch/leaf-modcurves/ModCurveLeaves.lean` §D, §E, §G): curves, the
  Albanese predicate `IsJacobian`, the leaf `JacobianExists`, `IsBelyiFunction`.
* Part III (new): R18 (Javanpeykar), R22 (Pazuki), R3 (Lin–Yang), sanity theorems.
-/


namespace ZInQ.LeafPush2

open NumberField MeasureTheory

/-! ## 1. Norms and complex embeddings -/

section Embeddings

variable {K : Type*} [Field K] [NumberField K]

/-- `∑_{σ : K → ℂ} log |σ x| = log |N_{K/ℚ}(x)|` (the archimedean half of the product formula). -/
theorem sum_log_norm_embeddings (x : K) (hx : x ≠ 0) :
    ∑ σ : K →+* ℂ, Real.log ‖σ x‖ = Real.log |(Algebra.norm ℚ x : ℝ)| := by
  rw [← Real.log_prod (fun σ _ => by simpa using hx)]
  congr 1
  have h := congr_arg (‖·‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ x)
  simp only [norm_prod] at h
  rw [Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun f => ‖f x‖) (fun φ => ‖φ x‖)
    (fun _ => by simp [RingHom.equivRatAlgHom_apply]), ← h]
  simp

/-- The same for an algebraic integer, with the integer norm. -/
theorem sum_log_norm_embeddings_int (a : 𝓞 K) (ha : a ≠ 0) :
    ∑ σ : K →+* ℂ, Real.log ‖σ (a : K)‖ = Real.log ((Algebra.norm ℤ a).natAbs : ℝ) := by
  rw [sum_log_norm_embeddings _ (by simpa using ha), ← Algebra.coe_norm_int]
  simp [Nat.cast_natAbs]

end Embeddings

/-! ## 2. Hermitian line bundles on `Spec 𝓞_K` and the Arakelov degree -/

section Arakelov

variable {K : Type*} [Field K] [NumberField K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

/-- The index `#(M / 𝓞_K s)` (as a natural number; `0` if infinite). -/
noncomputable def secIndex (M : Submodule (𝓞 K) V) (s : V) : ℕ :=
  (Submodule.span (𝓞 K) {s}).toAddSubgroup.relIndex M.toAddSubgroup

/-- **Change of section.** For `a ∈ 𝓞_K` and `0 ≠ s ∈ M`:
`#(M / 𝓞_K·as) = |N(a)| · #(M / 𝓞_K·s)`. -/
theorem secIndex_smul (M : Submodule (𝓞 K) V) {s : V} (hsM : s ∈ M) (hs : s ≠ 0) (a : 𝓞 K) :
    secIndex M (a • s) = (Algebra.norm ℤ a).natAbs * secIndex M s := by
  classical
  let φ : 𝓞 K →ₗ[𝓞 K] V := LinearMap.toSpanSingleton (𝓞 K) V s
  have hφ : Function.Injective φ := by
    intro x y hxy
    simp only [φ, LinearMap.toSpanSingleton_apply] at hxy
    have h1 : algebraMap (𝓞 K) K (x - y) • s = 0 := by
      rw [algebraMap_smul, sub_smul, hxy, sub_self]
    rcases smul_eq_zero.mp h1 with h | h
    · exact sub_eq_zero.mp (IsFractionRing.injective (𝓞 K) K (by simpa using h))
    · exact absurd h hs
  have h1 : Submodule.span (𝓞 K) {a • s} = Submodule.map φ (Ideal.span {a}) := by
    rw [Submodule.map_span, Set.image_singleton]
    simp [φ]
  have h2 : Submodule.span (𝓞 K) {s} = Submodule.map φ (⊤ : Ideal (𝓞 K)) := by
    rw [Submodule.map_top, LinearMap.span_singleton_eq_range]
  have hle1 : Submodule.span (𝓞 K) {a • s} ≤ Submodule.span (𝓞 K) {s} :=
    Submodule.span_le.mpr (by
      simpa using Submodule.smul_mem _ a (Submodule.mem_span_singleton_self s))
  have hle2 : Submodule.span (𝓞 K) {s} ≤ M := Submodule.span_le.mpr (by simpa using hsM)
  unfold secIndex
  rw [← AddSubgroup.relIndex_mul_relIndex _ _ _ (Submodule.toAddSubgroup_mono hle1)
    (Submodule.toAddSubgroup_mono hle2)]
  congr 1
  rw [h1, h2, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup,
    AddSubgroup.relIndex_map_map_of_injective _ _ hφ, Submodule.top_toAddSubgroup,
    AddSubgroup.relIndex_top_right, ← Ideal.absNorm_span_singleton, Ideal.absNorm_apply,
    Submodule.cardQuot_apply]
  rfl

/-- **A Hermitian line bundle on `Spec 𝓞_K`**, in generic-fibre form. `V` is a one-dimensional
`K`-vector space (the generic fibre), `lattice` is the `𝓞_K`-module of global sections (an
invertible `𝓞_K`-module, i.e. a rank-one lattice in `V`), and `norm σ` is a norm on the complex
line `V ⊗_{K,σ} ℂ`, recorded through its values on `V`. Conjugation symmetry
(`‖v‖_σ̄ = ‖v‖_σ`) is not needed for the degree and is not imposed. -/
structure HermitianLattice (K : Type*) [Field K] [NumberField K] (V : Type*) [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] where
  /-- The `𝓞_K`-module of sections. -/
  lattice : Submodule (𝓞 K) V
  /-- `V` is a line. -/
  finrank_eq_one : Module.finrank K V = 1
  /-- `lattice` is a full lattice: some nonzero section generates a subgroup of finite index
  (then every nonzero section does, `secIndex_ne_zero`). -/
  isLattice : ∃ s ∈ lattice, s ≠ 0 ∧ secIndex lattice s ≠ 0
  /-- The norm on `V ⊗_{K,σ} ℂ`. -/
  norm : (K →+* ℂ) → V → ℝ
  norm_smul : ∀ σ (a : K) (v : V), norm σ (a • v) = ‖σ a‖ * norm σ v
  norm_pos : ∀ σ (v : V), v ≠ 0 → 0 < norm σ v

namespace HermitianLattice

variable (L : HermitianLattice K V)

/-- The Arakelov degree computed with the section `s`:
`log #(M / 𝓞_K s) − ∑_{σ : K → ℂ} log ‖s‖_σ`. -/
noncomputable def degreeAt (s : V) : ℝ :=
  Real.log (secIndex L.lattice s) - ∑ σ : K →+* ℂ, Real.log (L.norm σ s)

theorem degreeAt_smul {s : V} (hsM : s ∈ L.lattice) (hs : s ≠ 0)
    (hi : secIndex L.lattice s ≠ 0) {a : 𝓞 K} (ha : a ≠ 0) :
    L.degreeAt (a • s) = L.degreeAt s := by
  have hN : (Algebra.norm ℤ a).natAbs ≠ 0 := by
    simpa [Int.natAbs_eq_zero] using (Algebra.norm_ne_zero_iff (R := ℤ)).mpr ha
  have has : a • s = (a : K) • s := (algebraMap_smul K a s).symm
  have hσ : ∀ σ : K →+* ℂ, Real.log (L.norm σ ((a : K) • s)) =
      Real.log ‖σ (a : K)‖ + Real.log (L.norm σ s) := by
    intro σ
    rw [L.norm_smul, Real.log_mul]
    · simpa using ha
    · exact (L.norm_pos σ s hs).ne'
  unfold degreeAt
  rw [secIndex_smul _ hsM hs, has, Finset.sum_congr rfl (fun σ _ => hσ σ), Finset.sum_add_distrib,
    sum_log_norm_embeddings_int a ha]
  push_cast
  rw [Real.log_mul (by exact_mod_cast hN) (by exact_mod_cast hi)]
  ring

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem _root_.HDec.ZInQ.LeafPush2.exists_smul_eq (hV : Module.finrank K V = 1)
    {s t : V} (hs : s ≠ 0) :
    ∃ b d : 𝓞 K, d ≠ 0 ∧ (d : K) • t = (b : K) • s := by
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' s hs).mp hV t
  obtain ⟨b, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) c
  refine ⟨b, d, nonZeroDivisors.ne_zero hd, ?_⟩
  have hd' : (algebraMap (𝓞 K) K d) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
  rw [← hc, smul_smul, mul_div_cancel₀ _ hd']

/-- Every nonzero section has finite index. -/
theorem secIndex_ne_zero {t : V} (htM : t ∈ L.lattice) (ht : t ≠ 0) :
    secIndex L.lattice t ≠ 0 := by
  obtain ⟨s, hsM, hs, hi⟩ := L.isLattice
  obtain ⟨b, d, hd, h⟩ := exists_smul_eq L.finrank_eq_one (t := t) hs
  have hb : b ≠ 0 := by
    rintro rfl
    simp only [map_zero, zero_smul, smul_eq_zero] at h
    rcases h with h | h
    · exact hd (by exact_mod_cast h)
    · exact ht h
  have e1 := secIndex_smul L.lattice htM ht d
  have e2 := secIndex_smul L.lattice hsM hs b
  have h' : d • t = b • s := by
    rw [← algebraMap_smul K d t, ← algebraMap_smul K b s]; exact h
  have : (Algebra.norm ℤ d).natAbs * secIndex L.lattice t =
      (Algebra.norm ℤ b).natAbs * secIndex L.lattice s := by
    rw [← e1, ← e2, h']
  intro h0
  rw [h0, mul_zero] at this
  have hN : (Algebra.norm ℤ b).natAbs ≠ 0 := by
    simpa [Int.natAbs_eq_zero] using (Algebra.norm_ne_zero_iff (R := ℤ)).mpr hb
  exact hi (by simpa [hN] using this.symm)

/-- **Independence of the section.** -/
theorem degreeAt_eq {s t : V} (hsM : s ∈ L.lattice) (hs : s ≠ 0) (htM : t ∈ L.lattice)
    (ht : t ≠ 0) : L.degreeAt s = L.degreeAt t := by
  obtain ⟨b, d, hd, h⟩ := exists_smul_eq L.finrank_eq_one (t := t) hs
  have hb : b ≠ 0 := by
    rintro rfl
    simp only [map_zero, zero_smul, smul_eq_zero] at h
    rcases h with h | h
    · exact hd (by exact_mod_cast h)
    · exact ht h
  have e1 := L.degreeAt_smul htM ht (L.secIndex_ne_zero htM ht) hd
  have e2 := L.degreeAt_smul hsM hs (L.secIndex_ne_zero hsM hs) hb
  have h' : d • t = b • s := by
    rw [← algebraMap_smul K d t, ← algebraMap_smul K b s]; exact h
  rw [← e1, ← e2, h']

/-- **The Arakelov degree** `deg(M̄) = log #(M / 𝓞_K s) − ∑_σ log ‖s‖_σ` for any `0 ≠ s ∈ M`. -/
noncomputable def arakelovDegree : ℝ := L.degreeAt L.isLattice.choose

theorem degreeAt_eq_arakelovDegree {s : V} (hsM : s ∈ L.lattice) (hs : s ≠ 0) :
    L.degreeAt s = L.arakelovDegree :=
  L.degreeAt_eq hsM hs L.isLattice.choose_spec.1 L.isLattice.choose_spec.2.1

end HermitianLattice

end Arakelov

/-! ## 3. The archimedean term: a translation-invariant top form on a complex torus

For an abelian variety `A` over `ℂ` of dimension `g`, `A(ℂ) ≅ ℂ^g / Λ` with `Λ` the period lattice
(the analytic uniformization; not in Mathlib, see the blueprint node `AN3`). In these linear
coordinates every invariant top form is `η = c · dz₁ ∧ ⋯ ∧ dz_g`, and `(i/2) dz ∧ dz̄ = dx ∧ dy` is
Lebesgue measure on `ℂ = ℝ²` (Mathlib's `volume` on `ℂ`), so the Faltings metric
`‖η‖² = (i/2)^g ∫_{A(ℂ)} η ∧ η̄` (sign convention: the positive value, i.e. with the factor
`(-1)^{g(g-1)/2}` that reorders `η ∧ η̄` into `∏ (dz_k ∧ dz̄_k)`) is `|c|²` times the volume of a
fundamental domain. -/

section Torus

/-- Real-linear change of variables and covolume: `covol(e⁻¹ Λ) · |det e| = covol Λ`. -/
theorem covolume_comap_mul_det {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (μ : Measure E) [μ.IsAddHaarMeasure] (e : E ≃L[ℝ] E) :
    ZLattice.covolume (ZLattice.comap ℝ L e.toLinearMap) μ *
      |LinearMap.det (e.toLinearMap : E →ₗ[ℝ] E)| = ZLattice.covolume L μ := by
  set ν : Measure E := Measure.map e.symm μ with hνdef
  have hmp : MeasurePreserving e ν μ := by
    refine ⟨e.continuous.measurable, ?_⟩
    rw [hνdef, Measure.map_map e.continuous.measurable e.symm.continuous.measurable]
    simp
  have h1 := ZLattice.covolume_comap L μ ν hmp
  have hdet : LinearMap.det (e.symm.toLinearMap : E →ₗ[ℝ] E) ≠ 0 := by
    rw [show (e.symm.toLinearMap : E →ₗ[ℝ] E) = (e.toLinearEquiv.symm : E →ₗ[ℝ] E) from rfl,
      LinearEquiv.det_coe_symm]
    exact inv_ne_zero (LinearEquiv.isUnit_det' e.toLinearEquiv).ne_zero
  have hν : ν = ENNReal.ofReal |LinearMap.det (e.toLinearMap : E →ₗ[ℝ] E)| • μ := by
    rw [hνdef, show (⇑e.symm : E → E) = ⇑(e.symm.toLinearMap : E →ₗ[ℝ] E) from rfl,
      Measure.map_linearMap_addHaar_eq_smul_addHaar μ hdet,
      show (e.symm.toLinearMap : E →ₗ[ℝ] E) = (e.toLinearEquiv.symm : E →ₗ[ℝ] E) from rfl,
      LinearEquiv.det_coe_symm, inv_inv]
  rw [← h1]
  have hF := ZLattice.isAddFundamentalDomain
    (Module.Free.chooseBasis ℤ (ZLattice.comap ℝ L e.toLinearMap)) μ
  have hFν := ZLattice.isAddFundamentalDomain
    (Module.Free.chooseBasis ℤ (ZLattice.comap ℝ L e.toLinearMap)) ν
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ μ hF,
    ZLattice.covolume_eq_measure_fundamentalDomain _ ν hFν, hν]
  simp only [Measure.real, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _)]
  ring

/-- The real determinant of a complex-linear map is `|det_ℂ|²`. -/
theorem det_restrictScalars_complex {g : ℕ} (T : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) :
    LinearMap.det (T.restrictScalars ℝ) = Complex.normSq (LinearMap.det T) := by
  rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply]

variable {g : ℕ}

/-- **The archimedean Faltings metric** of `η = c · dz₁ ∧ ⋯ ∧ dz_g` on `ℂ^g / Λ`:
`‖η‖² = (i/2)^g ∫_{ℂ^g/Λ} η ∧ η̄ = |c|² · covol(Λ)`. -/
noncomputable def torusMetricSq (Λ : Submodule ℤ (Fin g → ℂ)) (c : ℂ) : ℝ :=
  ‖c‖ ^ 2 * ZLattice.covolume Λ

variable (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

/-- The metric as an integral over a fundamental domain of `Λ` (i.e. over `A(ℂ)`). -/
theorem torusMetricSq_eq_setIntegral {F : Set (Fin g → ℂ)} (hF : IsAddFundamentalDomain Λ F)
    (c : ℂ) : torusMetricSq Λ c = ∫ _ in F, ‖c‖ ^ 2 := by
  rw [torusMetricSq, ZLattice.covolume_eq_measure_fundamentalDomain Λ volume hF,
    setIntegral_const, smul_eq_mul, mul_comm]

/-- Integrals over `A(ℂ) = ℂ^g/Λ` of `Λ`-periodic densities do not depend on the fundamental
domain (Mathlib's `IsAddFundamentalDomain.setIntegral_eq`). -/
theorem torus_setIntegral_indep {F F' : Set (Fin g → ℂ)} (hF : IsAddFundamentalDomain Λ F)
    (hF' : IsAddFundamentalDomain Λ F') (f : (Fin g → ℂ) → ℝ)
    (hf : ∀ (l : Λ) (x : Fin g → ℂ), f (l +ᵥ x) = f x) :
    ∫ x in F, f x = ∫ x in F', f x := by
  have : MeasurableVAdd Λ (Fin g → ℂ) := (inferInstance : MeasurableVAdd Λ.toAddSubgroup _)
  have : VAddInvariantMeasure Λ (Fin g → ℂ) volume :=
    (inferInstance : VAddInvariantMeasure Λ.toAddSubgroup _ volume)
  exact hF.setIntegral_eq hF' hf

theorem torusMetricSq_pos {c : ℂ} (hc : c ≠ 0) : 0 < torusMetricSq Λ c :=
  mul_pos (by positivity) (ZLattice.covolume_pos Λ volume)

omit [DiscreteTopology Λ] [IsZLattice ℝ Λ] in
theorem torusMetricSq_smul (a c : ℂ) : torusMetricSq Λ (a * c) = ‖a‖ ^ 2 * torusMetricSq Λ c := by
  simp only [torusMetricSq, norm_mul]; ring

/-- The real-linear equivalence underlying a complex coordinate change. -/
noncomputable def realify (T : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) : (Fin g → ℂ) ≃L[ℝ] (Fin g → ℂ) :=
  (T.restrictScalars ℝ).toContinuousLinearEquiv

/-- **Independence of the linear coordinates.** In coordinates `z'` with `z = T z'`, the lattice
becomes `T⁻¹ Λ` and `c · dz₁∧⋯∧dz_g = (c · det T) · dz'₁∧⋯∧dz'_g`; the metric is unchanged. -/
theorem torusMetricSq_comap (T : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (c : ℂ) :
    torusMetricSq (ZLattice.comap ℝ Λ (realify T).toLinearMap)
      (c * LinearMap.det (T : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))) = torusMetricSq Λ c := by
  have h := covolume_comap_mul_det Λ volume (realify T)
  have hd : LinearMap.det ((realify T).toLinearMap : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)) =
      Complex.normSq (LinearMap.det (T : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))) :=
    det_restrictScalars_complex (T : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
  rw [hd, abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq] at h
  simp only [torusMetricSq, norm_mul]
  rw [← h]
  ring

end Torus

/-! ## 4. The metrized Hodge bundle of an abelian variety given with a model

`HodgeData K g V` is what an abelian variety `A/K` of dimension `g`, *given with* a smooth
group-scheme model `𝒢/𝓞_K` and complex uniformizations, contributes to Faltings' definition:

* `V = ∧^g H⁰(A, Ω¹) = ∧^g Lie(A)^∨`, a `K`-line (blueprint node `AV4`);
* `lattice = ∧^g ω_𝒢 = ∧^g e*Ω¹_{𝒢/𝓞_K}` inside `V` (node `M3`);
* `periods σ`: the period lattice `H₁(A_σ(ℂ), ℤ)` in linear coordinates `z₁, …, z_g` of
  `Lie(A_σ(ℂ))` (node `AN3`);
* `coeff σ`: the `σ`-semilinear map `V → ℂ`, `η ↦ c` where `η ⊗_σ 1 = c · dz₁ ∧ ⋯ ∧ dz_g`.

These fields are **data produced by the missing nodes**, not hypotheses about an abstract
structure: in the full formalization `HodgeData.ofModel 𝒢 (uniformization)` constructs them, and
the theorems below then apply. -/

section Hodge

variable {K : Type*} [Field K] [NumberField K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

/-- The Hodge data of an abelian variety of dimension `g` over `K` with a model. -/
structure HodgeData (K : Type*) [Field K] [NumberField K] (g : ℕ) (V : Type*) [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] where
  /-- `∧^g ω_𝒢 ⊆ ∧^g H⁰(A, Ω¹)`. -/
  lattice : Submodule (𝓞 K) V
  finrank_eq_one : Module.finrank K V = 1
  isLattice : ∃ s ∈ lattice, s ≠ 0 ∧ secIndex lattice s ≠ 0
  /-- The period lattice of `A_σ(ℂ)` in linear coordinates. -/
  periods : (K →+* ℂ) → Submodule ℤ (Fin g → ℂ)
  periods_discrete : ∀ σ, DiscreteTopology (periods σ)
  periods_isZLattice : ∀ σ, IsZLattice ℝ (periods σ)
  /-- `η ↦ c` with `η ⊗_σ 1 = c · dz₁ ∧ ⋯ ∧ dz_g`. -/
  coeff : ∀ σ : K →+* ℂ, V →ₛₗ[σ] ℂ
  coeff_ne_zero : ∀ σ, coeff σ ≠ 0

namespace HodgeData

variable {g : ℕ} (D : HodgeData K g V)

omit [IsScalarTower (𝓞 K) K V] in
theorem coeff_apply_ne_zero (σ : K →+* ℂ) {v : V} (hv : v ≠ 0) : D.coeff σ v ≠ 0 := by
  intro h0
  apply D.coeff_ne_zero σ
  ext w
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' v hv).mp D.finrank_eq_one w
  simp [h0]

/-- `‖η‖_σ = (‖η‖²_σ)^{1/2}`, `‖η‖²_σ = (i/2)^g ∫_{A_σ(ℂ)} η ∧ η̄`. -/
noncomputable def norm (σ : K →+* ℂ) (v : V) : ℝ :=
  ‖D.coeff σ v‖ * Real.sqrt (ZLattice.covolume (D.periods σ))

omit [IsScalarTower (𝓞 K) K V] in
theorem norm_sq (σ : K →+* ℂ) (v : V) :
    D.norm σ v ^ 2 = torusMetricSq (D.periods σ) (D.coeff σ v) := by
  have := D.periods_discrete σ
  have := D.periods_isZLattice σ
  rw [norm, torusMetricSq, mul_pow,
    Real.sq_sqrt (ZLattice.covolume_pos (D.periods σ) volume).le]

/-- **The metrized Hodge bundle** `ω̄_𝒢 = (det ω_𝒢, ‖·‖_Faltings)`. -/
noncomputable def hodgeBundle : HermitianLattice K V where
  lattice := D.lattice
  finrank_eq_one := D.finrank_eq_one
  isLattice := D.isLattice
  norm := D.norm
  norm_smul σ a v := by
    simp only [norm, map_smulₛₗ, smul_eq_mul, norm_mul]; ring
  norm_pos σ v hv := by
    have := D.periods_discrete σ
    have := D.periods_isZLattice σ
    exact mul_pos (norm_pos_iff.mpr (D.coeff_apply_ne_zero σ hv))
      (Real.sqrt_pos.mpr (ZLattice.covolume_pos (D.periods σ) volume))

/-- **Faltings' height of `A` relative to the model**: `deg(ω̄_𝒢) / [K:ℚ]`. -/
noncomputable def modelHeight : ℝ := D.hodgeBundle.arakelovDegree / Module.finrank ℚ K

/-- **Faltings' formula** (pkg-I5 §2.1), for every nonzero `η ∈ ∧^g ω_𝒢`:
`h(A, 𝒢) = [K:ℚ]⁻¹ (log #(∧^g ω_𝒢 / 𝓞_K η) − ½ ∑_σ log ((i/2)^g ∫_{A_σ(ℂ)} η ∧ η̄))`. -/
theorem modelHeight_eq {η : V} (hηM : η ∈ D.lattice) (hη : η ≠ 0) :
    D.modelHeight = (Real.log (secIndex D.lattice η) -
      (1 / 2) * ∑ σ : K →+* ℂ, Real.log (torusMetricSq (D.periods σ) (D.coeff σ η))) /
        Module.finrank ℚ K := by
  rw [modelHeight, ← D.hodgeBundle.degreeAt_eq_arakelovDegree hηM hη]
  unfold HermitianLattice.degreeAt
  congr 2
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← D.norm_sq, Real.log_pow]
  simp only [hodgeBundle]
  push_cast; ring

/-- Change of the linear coordinates at every `σ`: `z = T_σ z'`. -/
noncomputable def recoord (T : (K →+* ℂ) → ((Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))) : HodgeData K g V where
  lattice := D.lattice
  finrank_eq_one := D.finrank_eq_one
  isLattice := D.isLattice
  periods σ := ZLattice.comap ℝ (D.periods σ) (realify (T σ)).toLinearMap
  periods_discrete σ := by
    have := D.periods_discrete σ
    infer_instance
  periods_isZLattice σ := by
    have := D.periods_discrete σ
    have := D.periods_isZLattice σ
    infer_instance
  coeff σ := LinearMap.det (T σ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) • D.coeff σ
  coeff_ne_zero σ := by
    intro h
    obtain ⟨v, hvM, hv, -⟩ := D.isLattice
    have := congr_arg (fun f => f v) h
    simp only [LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply, mul_eq_zero] at this
    rcases this with h1 | h1
    · exact (LinearEquiv.isUnit_det' (T σ)).ne_zero h1
    · exact D.coeff_apply_ne_zero σ hv h1

omit [IsScalarTower (𝓞 K) K V] in
/-- **Independence of the coordinates on `Lie(A_σ)`.** -/
theorem modelHeight_recoord (T : (K →+* ℂ) → ((Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))) :
    (D.recoord T).modelHeight = D.modelHeight := by
  have hn : ∀ σ v, (D.recoord T).norm σ v = D.norm σ v := by
    intro σ v
    have := D.periods_discrete σ
    have := D.periods_isZLattice σ
    have h2 : (D.recoord T).norm σ v ^ 2 = D.norm σ v ^ 2 := by
      rw [norm_sq, norm_sq]
      simp only [recoord, LinearMap.smul_apply, smul_eq_mul]
      rw [mul_comm]
      exact torusMetricSq_comap (D.periods σ) (T σ) _
    have h0 : 0 ≤ (D.recoord T).norm σ v := mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
    have h0' : 0 ≤ D.norm σ v := mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
    exact (pow_left_inj₀ h0 h0' two_ne_zero).mp h2
  unfold modelHeight HermitianLattice.arakelovDegree HermitianLattice.degreeAt
  simp only [hodgeBundle, hn]
  rfl

/-- **Change of model.** If `D'` has the same generic fibre and uniformizations and a smaller
lattice (`ω_𝒢' ⊆ ω_𝒢`, e.g. `𝒢'` the Néron model, which receives a map from every smooth model),
then `h(A, 𝒢) = h(A, 𝒢') + [K:ℚ]⁻¹ log [ω_𝒢 : ω_𝒢']`. -/
theorem modelHeight_eq_add_of_le (D' : HodgeData K g V) (hp : D'.periods = D.periods)
    (hc : D'.coeff = D.coeff) (hle : D'.lattice ≤ D.lattice) :
    D.modelHeight = D'.modelHeight +
      Real.log (D'.lattice.toAddSubgroup.relIndex D.lattice.toAddSubgroup) /
        Module.finrank ℚ K := by
  obtain ⟨η, hηM', hη, -⟩ := D'.isLattice
  have hηM : η ∈ D.lattice := hle hηM'
  rw [D.modelHeight_eq hηM hη, D'.modelHeight_eq hηM' hη, hp, hc, ← add_div]
  congr 1
  have hle1 : Submodule.span (𝓞 K) {η} ≤ D'.lattice := Submodule.span_le.mpr (by simpa using hηM')
  have hmul : secIndex D'.lattice η *
      D'.lattice.toAddSubgroup.relIndex D.lattice.toAddSubgroup = secIndex D.lattice η :=
    AddSubgroup.relIndex_mul_relIndex _ _ _ (Submodule.toAddSubgroup_mono hle1)
      (Submodule.toAddSubgroup_mono hle)
  have hne : secIndex D.lattice η ≠ 0 := D.hodgeBundle.secIndex_ne_zero hηM hη
  rw [← hmul] at hne ⊢
  have h1 : secIndex D'.lattice η ≠ 0 := left_ne_zero_of_mul hne
  have h2 : D'.lattice.toAddSubgroup.relIndex D.lattice.toAddSubgroup ≠ 0 :=
    right_ne_zero_of_mul hne
  push_cast
  rw [Real.log_mul (by exact_mod_cast h1) (by exact_mod_cast h2)]
  ring

/-- Hence a smaller lattice gives a smaller height; the Néron lattice gives the infimum. -/
theorem modelHeight_le_of_le (D' : HodgeData K g V) (hp : D'.periods = D.periods)
    (hc : D'.coeff = D.coeff) (hle : D'.lattice ≤ D.lattice) :
    D'.modelHeight ≤ D.modelHeight := by
  rw [D.modelHeight_eq_add_of_le D' hp hc hle]
  have : 0 ≤ Real.log (D'.lattice.toAddSubgroup.relIndex D.lattice.toAddSubgroup) /
      Module.finrank ℚ K :=
    div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)
  linarith

end HodgeData

end Hodge

/-! ## 5. Acceptance-test interface: elliptic curves

The definitions `hypGram`, `hypVol`, `finiteHeightPart`, `faltingsHeightEC` are copied verbatim
from `scratch/pkg-I5/I5.lean` (task pkg-I5), so that the acceptance test can be stated here. -/

section Acceptance

open Polynomial

/-- (copied from pkg-I5) `2 ∫_ℂ xⁱ x̄ʲ / |P(x)| dλ`. -/
noncomputable def hypGram (P : ℂ[X]) (i j : ℕ) : ℂ :=
  2 * ∫ x : ℂ, x ^ i * (starRingEnd ℂ x) ^ j / ((‖P.eval x‖ : ℝ) : ℂ)

/-- (copied from pkg-I5) `det` of the Gram matrix. -/
noncomputable def hypVol (g : ℕ) (P : ℂ[X]) : ℝ :=
  (Matrix.of fun i j : Fin g => hypGram P i j).det.re

/-- (copied from pkg-I5) `∑_{v finite} log max(1, |x|_v)`. -/
noncomputable def finiteHeightPart {K : Type*} [Field K] [NumberField K] (x : K) : ℝ :=
  Height.logHeight₁ x - ∑ σ : K →+* ℂ, Real.log (max 1 ‖σ x‖)

/-- (copied from pkg-I5) The closed formula for the stable Faltings height of an elliptic curve. -/
noncomputable def faltingsHeightEC {K : Type*} [Field K] [NumberField K]
    (W : WeierstrassCurve K) [W.IsElliptic] : ℝ :=
  let d : ℝ := Module.finrank ℚ K
  let P : K[X] := 4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆
  (finiteHeightPart W.j - ∑ σ : K →+* ℂ, Real.log ‖σ W.Δ‖) / (12 * d) -
    (∑ σ : K →+* ℂ, Real.log (hypVol 1 (P.map σ))) / (2 * d)

variable {K : Type*} [Field K] [NumberField K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

/-- A free Hodge lattice `𝓞_K · η₀`: `h(A, 𝒢) = −(2[K:ℚ])⁻¹ ∑_σ log ‖η₀‖²_σ`. -/
theorem HodgeData.modelHeight_of_span {g : ℕ} (D : HodgeData K g V) {η₀ : V}
    (h : D.lattice = Submodule.span (𝓞 K) {η₀}) (hη₀ : η₀ ≠ 0) :
    D.modelHeight = -((1 / 2) * ∑ σ : K →+* ℂ,
      Real.log (torusMetricSq (D.periods σ) (D.coeff σ η₀))) / Module.finrank ℚ K := by
  have hm : η₀ ∈ D.lattice := h ▸ Submodule.mem_span_singleton_self η₀
  rw [D.modelHeight_eq hm hη₀]
  have h1 : secIndex D.lattice η₀ = 1 := by
    unfold secIndex; rw [h, AddSubgroup.relIndex_self]
  rw [h1]
  simp

/-! leaf-adopt2: `_root_.PeriodPair.lattice1` (the period lattice of a `PeriodPair` in
`ℂ¹ = Fin 1 → ℂ`) is declared in `DefFaltingsSec` with this exact text; not re-declared. -/

instance (L : PeriodPair) : DiscreteTopology (PeriodPair.lattice1 L) := by
  unfold PeriodPair.lattice1; infer_instance

instance (L : PeriodPair) : IsZLattice ℝ (PeriodPair.lattice1 L) := by
  unfold PeriodPair.lattice1; infer_instance

/-! leaf-adopt2: `_root_.PeriodPair.covolume_lattice1` is proved in `DefFaltingsSec` with this
exact text; not re-declared. -/

/-- **Node AT1c (the area formula).** For the lattice `Λ` of a period pair and
`P = 4x³ − g₂(Λ)x − g₃(Λ)`: `covol(Λ) = 2 ∫_ℂ dλ(x)/|P(x)|`. A classical theorem (the map
`z ↦ ℘(z)` is a degree-2 cover `ℂ/Λ → ℙ¹` with `d℘ = ℘' dz` and `℘'² = P(℘)`; Mathlib has `℘` and
`PeriodPair.derivWeierstrassP_sq`); numerically checked in pkg-I5 (`area_check.py`). Stated as a
Prop here, unproved. -/
def PeriodAreaFormula : Prop :=
  ∀ L : PeriodPair, ZLattice.covolume L.lattice =
    hypVol 1 (4 * X ^ 3 - C L.g₂ * X - C L.g₃)

/-- **Acceptance test AT1, conditional form.** Let `D` be Hodge data of dimension 1 whose lattice
is free on `η₀`, whose period lattices are those of period pairs `L σ` with `η₀ ↦ dz`
(i.e. `η₀ = dx/(2y + a₁x + a₃)` and `L σ` the period lattice of `W^σ`: node AT1b), where the
Weierstrass polynomial of `W^σ` is `4x³ − g₂(L σ) x − g₃(L σ)` and the finite part of
`faltingsHeightEC` vanishes (`W` semistable and minimal at every prime, which is when `𝓞_K η₀` is
the Néron lattice: node AT1a). Then, given the area formula AT1c, `modelHeight D` equals pkg-I5's
`faltingsHeightEC W`. Proved. -/
theorem modelHeight_eq_faltingsHeightEC (hA : PeriodAreaFormula)
    (W : WeierstrassCurve K) [W.IsElliptic] (D : HodgeData K 1 V) {η₀ : V}
    (hspan : D.lattice = Submodule.span (𝓞 K) {η₀}) (hη₀ : η₀ ≠ 0)
    (L : (K →+* ℂ) → PeriodPair) (hper : ∀ σ, D.periods σ = (PeriodPair.lattice1 (L σ)))
    (hco : ∀ σ, D.coeff σ η₀ = 1)
    (hP : ∀ σ, (4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆ : K[X]).map σ =
      4 * X ^ 3 - C (L σ).g₂ * X - C (L σ).g₃)
    (hfin : finiteHeightPart W.j = ∑ σ : K →+* ℂ, Real.log ‖σ W.Δ‖) :
    D.modelHeight = faltingsHeightEC W := by
  rw [D.modelHeight_of_span hspan hη₀, faltingsHeightEC]
  rw [hfin, sub_self, zero_div, zero_sub]
  have hterm : ∀ σ : K →+* ℂ, torusMetricSq (D.periods σ) (D.coeff σ η₀) =
      hypVol 1 ((4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆ : K[X]).map σ) := by
    intro σ
    rw [hco, hper, hP, torusMetricSq, PeriodPair.covolume_lattice1, hA]
    simp
  simp only [hterm]
  have hd : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  field_simp

end Acceptance

/-! ## 6. Rescaling, and a sanity check that `HodgeData` is inhabited -/

section Sanity

variable {K : Type*} [Field K] [NumberField K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

/-- Rescale the metrics by `c σ > 0`. -/
noncomputable def HermitianLattice.rescale (L : HermitianLattice K V) (c : (K →+* ℂ) → ℝ)
    (hc : ∀ σ, 0 < c σ) : HermitianLattice K V where
  lattice := L.lattice
  finrank_eq_one := L.finrank_eq_one
  isLattice := L.isLattice
  norm σ v := c σ * L.norm σ v
  norm_smul σ a v := by rw [L.norm_smul]; ring
  norm_pos σ v hv := mul_pos (hc σ) (L.norm_pos σ v hv)

omit [IsScalarTower (𝓞 K) K V] in
/-- **Rescaling (part of node AR3):** `deg(M, c·‖·‖) = deg(M, ‖·‖) − ∑_σ log c_σ`. -/
theorem HermitianLattice.arakelovDegree_rescale (L : HermitianLattice K V)
    (c : (K →+* ℂ) → ℝ) (hc : ∀ σ, 0 < c σ) :
    (L.rescale c hc).arakelovDegree = L.arakelovDegree - ∑ σ : K →+* ℂ, Real.log (c σ) := by
  obtain ⟨hsM, hs, -⟩ := L.isLattice.choose_spec
  unfold HermitianLattice.arakelovDegree HermitianLattice.degreeAt
  simp only [HermitianLattice.rescale]
  rw [Finset.sum_congr rfl fun σ _ => Real.log_mul (hc σ).ne' (L.norm_pos σ _ hs).ne',
    Finset.sum_add_distrib]
  ring

/-- The square lattice `ℤ + ℤi`. -/
noncomputable def gaussianPair : PeriodPair where
  ω₁ := 1
  ω₂ := Complex.I
  indep := by simpa [Complex.coe_basisOneI] using Complex.basisOneI.linearIndependent

/-- `σ : ℚ → ℂ` as a `σ`-semilinear map. -/
def ratCoeff (σ : ℚ →+* ℂ) : ℚ →ₛₗ[σ] ℂ where
  toFun := σ
  map_add' := map_add σ
  map_smul' a v := by simp

/-- **Sanity check: `HodgeData` is inhabited** (the elliptic curve `ℂ/(ℤ + ℤi)` over `ℚ`, with
the lattice `ℤ · 1`; this is a consistency check of the structure, not a claim about a curve over
`ℚ`). -/
noncomputable def exampleHodge : HodgeData ℚ 1 ℚ where
  lattice := Submodule.span (𝓞 ℚ) {1}
  finrank_eq_one := Module.finrank_self ℚ
  isLattice := ⟨1, Submodule.mem_span_singleton_self 1, one_ne_zero, by
    unfold secIndex; rw [AddSubgroup.relIndex_self]; exact one_ne_zero⟩
  periods _ := (PeriodPair.lattice1 gaussianPair)
  periods_discrete _ := inferInstance
  periods_isZLattice _ := inferInstance
  coeff σ := ratCoeff σ
  coeff_ne_zero σ h := by
    have := congr_arg (fun f => f 1) h
    simp [ratCoeff] at this

theorem exampleHodge_modelHeight :
    exampleHodge.modelHeight = -(1 / 2) * Real.log (ZLattice.covolume gaussianPair.lattice) := by
  rw [HodgeData.modelHeight_of_span exampleHodge (η₀ := (1 : ℚ)) rfl one_ne_zero]
  have hu : (Finset.univ : Finset (ℚ →+* ℂ)) = {Rat.castHom ℂ} := by
    ext σ; simp [Subsingleton.elim σ (Rat.castHom ℂ)]
  rw [hu, Finset.sum_singleton]
  simp [exampleHodge, torusMetricSq, ratCoeff, PeriodPair.covolume_lattice1]

end Sanity

/-! ## 7. Hermitian lines given by fractional ideals: the closed formula (part of node AR3)

Every invertible `𝓞_K`-module with a trivialization of its generic fibre is a fractional ideal
`I ⊆ K`. For such lines `#(I / 𝓞_K x) · N(I) = |N_{K/ℚ}(x)|` (`secIndex_mul_absNorm`), so
`deg(I, ρ·|σ(·)|) = −log N(I) − ∑_σ log ρ_σ` (`arakelovDegree_ofFractionalIdeal`). This is the form
in which AT1a meets a Néron lattice `𝔞 · dx/(2y + a₁x + a₃)` that is not free (class number > 1). -/

section FractionalIdeal

open Pointwise
open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

/-- **Index formula.** For a fractional ideal `I` and `0 ≠ x ∈ I`:
`#(I / 𝓞_K x) · N(I) = |N_{K/ℚ}(x)|`. -/
theorem secIndex_mul_absNorm (I : FractionalIdeal (𝓞 K)⁰ K) {x : K} (hx : x ∈ I) (hx0 : x ≠ 0) :
    (secIndex (I : Submodule (𝓞 K) K) x : ℚ) * FractionalIdeal.absNorm I =
      |Algebra.norm ℚ x| := by
  classical
  set d : 𝓞 K := (I.den : 𝓞 K) with hd
  have hd0' : d ≠ 0 := nonZeroDivisors.ne_zero I.den.2
  have hd0 : (d : K) ≠ 0 := by exact_mod_cast hd0'
  let f : K →ₗ[𝓞 K] K := DistribSMul.toLinearMap (𝓞 K) K I.den
  have hf_apply : ∀ z, f z = (d : K) * z := by
    intro z
    show I.den • z = (d : K) * z
    rw [Submonoid.smul_def, ← algebraMap_smul K, smul_eq_mul]
  have hf : Function.Injective f := fun a b h => by
    rw [hf_apply, hf_apply] at h
    exact mul_left_cancel₀ hd0 h
  have hfI : Submodule.map f (I : Submodule (𝓞 K) K) =
      Submodule.map (Algebra.linearMap (𝓞 K) K) I.num :=
    FractionalIdeal.den_mul_self_eq_num I
  -- `d x = y` with `y ∈ I.num`
  have hdx : f x ∈ Submodule.map (Algebra.linearMap (𝓞 K) K) I.num :=
    hfI ▸ Submodule.mem_map_of_mem hx
  obtain ⟨y, hy, hyx⟩ := hdx
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp only [map_zero] at hyx
    exact hx0 (hf (by rw [← hyx, map_zero]))
  let ι : 𝓞 K →ₗ[𝓞 K] K := Algebra.linearMap (𝓞 K) K
  have hι : Function.Injective ι := IsFractionRing.injective (𝓞 K) K
  have hspan : Submodule.map f (Submodule.span (𝓞 K) {x}) =
      Submodule.map ι (Ideal.span {y}) := by
    rw [Submodule.map_span, Submodule.map_span, Set.image_singleton, Set.image_singleton]
    simp only [ι] at hyx ⊢
    rw [hyx]
  -- transport the index
  have h1 : secIndex (I : Submodule (𝓞 K) K) x =
      (Ideal.span {y}).toAddSubgroup.relIndex I.num.toAddSubgroup := by
    unfold secIndex
    have e1 := AddSubgroup.relIndex_map_map_of_injective
      (Submodule.span (𝓞 K) {x}).toAddSubgroup (I : Submodule (𝓞 K) K).toAddSubgroup
      (f := (f : K →+ K)) hf
    rw [← Submodule.map_toAddSubgroup, ← Submodule.map_toAddSubgroup, hspan, hfI,
      Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup,
      AddSubgroup.relIndex_map_map_of_injective _ _ hι] at e1
    exact e1.symm
  have hle : Ideal.span {y} ≤ I.num := (Ideal.span_singleton_le_iff_mem _).mpr hy
  have h2 : (Ideal.span {y}).toAddSubgroup.relIndex I.num.toAddSubgroup *
      Ideal.absNorm I.num = (Algebra.norm ℤ y).natAbs := by
    rw [← Ideal.absNorm_span_singleton, Ideal.absNorm_apply, Ideal.absNorm_apply,
      Submodule.cardQuot_apply, Submodule.cardQuot_apply]
    exact AddSubgroup.relIndex_mul_index (Submodule.toAddSubgroup_mono hle)
  have hnum0 : Ideal.absNorm I.num ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h2
    have : Algebra.norm ℤ y ≠ 0 := (Algebra.norm_ne_zero_iff (R := ℤ)).mpr hy0
    omega
  -- norms
  have hNy : (Algebra.norm ℚ (y : K)) = Algebra.norm ℚ (d : K) * Algebra.norm ℚ x := by
    have : (y : K) = (d : K) * x := by rw [← hf_apply]; exact hyx
    rw [this, map_mul]
  rw [FractionalIdeal.absNorm_eq, h1]
  have hNyz : ((Algebra.norm ℤ y).natAbs : ℚ) = |Algebra.norm ℚ (y : K)| := by
    rw [← Algebra.coe_norm_int]; simp [Nat.cast_natAbs]
  have hNdz : ((Algebra.norm ℤ d : ℤ) : ℚ) = Algebra.norm ℚ (d : K) := Algebra.coe_norm_int d
  have hNd0 : Algebra.norm ℚ (d : K) ≠ 0 := by
    rw [← hNdz]; exact_mod_cast (Algebra.norm_ne_zero_iff (R := ℤ)).mpr hd0'
  have key : ((Ideal.span {y}).toAddSubgroup.relIndex I.num.toAddSubgroup : ℚ) *
      (Ideal.absNorm I.num : ℚ) = |Algebra.norm ℚ (d : K)| * |Algebra.norm ℚ x| := by
    rw [← abs_mul, ← hNy, ← hNyz]; exact_mod_cast h2
  have hden : ((|Algebra.norm ℤ (I.den : 𝓞 K)| : ℤ) : ℚ) = |Algebra.norm ℚ (d : K)| := by
    rw [Int.cast_abs]; exact congr_arg _ hNdz
  rw [hden, ← mul_div_assoc, key]
  field_simp

/-- The Hermitian line `(I, ρ_σ · |σ(·)|)` on `Spec 𝓞_K`. -/
noncomputable def HermitianLattice.ofFractionalIdeal (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    (ρ : (K →+* ℂ) → ℝ) (hρ : ∀ σ, 0 < ρ σ) : HermitianLattice K K where
  lattice := I
  finrank_eq_one := Module.finrank_self K
  isLattice := by
    obtain ⟨x, hxI, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (FractionalIdeal.coeToSubmodule_ne_bot.mpr hI)
    refine ⟨x, hxI, hx0, fun h0 => ?_⟩
    have := secIndex_mul_absNorm I hxI hx0
    rw [h0, Nat.cast_zero, zero_mul] at this
    exact (Algebra.norm_ne_zero_iff.mpr hx0) (abs_eq_zero.mp this.symm)
  norm σ x := ρ σ * ‖σ x‖
  norm_smul σ a x := by rw [smul_eq_mul, map_mul, norm_mul]; ring
  norm_pos σ x hx := mul_pos (hρ σ) (by simpa using hx)

/-- **Closed formula:** `deg(I, ρ·|σ(·)|) = −log N(I) − ∑_σ log ρ_σ`. -/
theorem HermitianLattice.arakelovDegree_ofFractionalIdeal (I : FractionalIdeal (𝓞 K)⁰ K)
    (hI : I ≠ 0) (ρ : (K →+* ℂ) → ℝ) (hρ : ∀ σ, 0 < ρ σ) :
    (HermitianLattice.ofFractionalIdeal I hI ρ hρ).arakelovDegree =
      -Real.log (FractionalIdeal.absNorm I : ℝ) - ∑ σ : K →+* ℂ, Real.log (ρ σ) := by
  set L := HermitianLattice.ofFractionalIdeal I hI ρ hρ
  obtain ⟨hxI, hx0, hi⟩ := L.isLattice.choose_spec
  set x := L.isLattice.choose
  have hidx := secIndex_mul_absNorm I hxI hx0
  have hN0 : FractionalIdeal.absNorm I ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hidx
    exact (Algebra.norm_ne_zero_iff.mpr hx0) (abs_eq_zero.mp hidx.symm)
  unfold HermitianLattice.arakelovDegree HermitianLattice.degreeAt
  have hsum : ∑ σ : K →+* ℂ, Real.log (L.norm σ x) =
      ∑ σ : K →+* ℂ, Real.log (ρ σ) + Real.log |(Algebra.norm ℚ x : ℝ)| := by
    rw [← sum_log_norm_embeddings x hx0, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    exact Real.log_mul (hρ σ).ne' (by simpa using hx0)
  rw [hsum]
  have hidxR : (secIndex L.lattice x : ℝ) * (FractionalIdeal.absNorm I : ℝ) =
      |(Algebra.norm ℚ x : ℝ)| := by exact_mod_cast hidx
  have hlog : Real.log (secIndex L.lattice x : ℝ) + Real.log (FractionalIdeal.absNorm I : ℝ) =
      Real.log |(Algebra.norm ℚ x : ℝ)| := by
    rw [← Real.log_mul (by exact_mod_cast hi) (by exact_mod_cast hN0), hidxR]
  linarith

end FractionalIdeal

/-! ## 8. Acceptance test AT1 for a non-free Hodge lattice

For an elliptic curve with semistable reduction everywhere, the Néron lattice of invariant
differentials is `𝔞 · ω` with `ω = dx/(2y + a₁x + a₃)` and `𝔞` the fractional ideal with
`ord_𝔭 𝔞 = (ord_𝔭 Δ − ord_𝔭 Δ_min)/12` (`Δ_min` the minimal discriminant at `𝔭`). With
`ord_𝔭 Δ_min = max(0, −ord_𝔭 j)` (semistable) and the product formula,
`−12 log N(𝔞) = ∑_{v∤∞} log⁺|j|_v − ∑_σ log|σΔ|`. That identity is node AT1a (literature: Néron
models of elliptic curves); here it is the hypothesis `hNeron`. -/

section AcceptanceIdeal

open Polynomial
open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

/-- `σ : K → ℂ` as a `σ`-semilinear map. -/
def embCoeff (σ : K →+* ℂ) : K →ₛₗ[σ] ℂ where
  toFun := σ
  map_add' := map_add σ
  map_smul' a v := by simp

/-- The Hodge data `(𝔞 ⊆ K, Λ_σ)` of dimension 1: `V = K` (`ω ↦ 1`), lattice `𝔞`, period lattices
`(PeriodPair.lattice1 (L σ))`, `ω ↦ dz`. -/
noncomputable def HodgeData.ofIdeal (𝔞 : FractionalIdeal (𝓞 K)⁰ K) (h𝔞 : 𝔞 ≠ 0)
    (L : (K →+* ℂ) → PeriodPair) : HodgeData K 1 K where
  lattice := 𝔞
  finrank_eq_one := Module.finrank_self K
  isLattice := (HermitianLattice.ofFractionalIdeal 𝔞 h𝔞 (fun _ => 1) (fun _ => one_pos)).isLattice
  periods σ := (PeriodPair.lattice1 (L σ))
  periods_discrete _ := inferInstance
  periods_isZLattice _ := inferInstance
  coeff σ := embCoeff σ
  coeff_ne_zero σ h := by
    have := congr_arg (fun f => f 1) h
    simp [embCoeff] at this

theorem HodgeData.modelHeight_ofIdeal (𝔞 : FractionalIdeal (𝓞 K)⁰ K) (h𝔞 : 𝔞 ≠ 0)
    (L : (K →+* ℂ) → PeriodPair) :
    (HodgeData.ofIdeal 𝔞 h𝔞 L).modelHeight =
      (-Real.log (FractionalIdeal.absNorm 𝔞 : ℝ) -
        (1 / 2) * ∑ σ : K →+* ℂ, Real.log (ZLattice.covolume (L σ).lattice)) /
          Module.finrank ℚ K := by
  set ρ : (K →+* ℂ) → ℝ := fun σ => Real.sqrt (ZLattice.covolume (L σ).lattice)
  have hρ : ∀ σ, 0 < ρ σ := fun σ => Real.sqrt_pos.mpr (ZLattice.covolume_pos _ volume)
  have hdeg := HermitianLattice.arakelovDegree_ofFractionalIdeal 𝔞 h𝔞 ρ hρ
  have heq : (HodgeData.ofIdeal 𝔞 h𝔞 L).hodgeBundle.arakelovDegree =
      (HermitianLattice.ofFractionalIdeal 𝔞 h𝔞 ρ hρ).arakelovDegree := by
    unfold HermitianLattice.arakelovDegree HermitianLattice.degreeAt
    congr 1
    refine Finset.sum_congr rfl fun σ _ => ?_
    congr 1
    simp only [HodgeData.hodgeBundle, HodgeData.norm, HermitianLattice.ofFractionalIdeal,
      HodgeData.ofIdeal, embCoeff, LinearMap.coe_mk, AddHom.coe_mk, ρ,
      PeriodPair.covolume_lattice1]
    ring
  rw [HodgeData.modelHeight, heq, hdeg]
  congr 1
  have hs : ∀ σ : K →+* ℂ, Real.log (ρ σ) = (1 / 2) * Real.log (ZLattice.covolume (L σ).lattice) := by
    intro σ
    simp only [ρ]
    rw [Real.log_sqrt (ZLattice.covolume_pos _ volume).le]
    ring
  rw [Finset.sum_congr rfl fun σ _ => hs σ, ← Finset.mul_sum]

/-- **Acceptance test AT1 (semistable elliptic curves, any class number), conditional form.**
Given the area formula AT1c (`PeriodAreaFormula`), period pairs `L σ` with Weierstrass polynomial
`4x³ − g₂(L σ)x − g₃(L σ)` equal to that of `W^σ` (AT1b), and a Hodge lattice `𝔞 · ω` satisfying the
Néron identity AT1a (`hNeron`), the model height equals pkg-I5's `faltingsHeightEC W`. Proved. -/
theorem modelHeight_ofIdeal_eq_faltingsHeightEC (hA : PeriodAreaFormula)
    (W : WeierstrassCurve K) [W.IsElliptic] (𝔞 : FractionalIdeal (𝓞 K)⁰ K) (h𝔞 : 𝔞 ≠ 0)
    (L : (K →+* ℂ) → PeriodPair)
    (hP : ∀ σ, (4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆ : K[X]).map σ =
      4 * X ^ 3 - C (L σ).g₂ * X - C (L σ).g₃)
    (hNeron : -12 * Real.log (FractionalIdeal.absNorm 𝔞 : ℝ) =
      finiteHeightPart W.j - ∑ σ : K →+* ℂ, Real.log ‖σ W.Δ‖) :
    (HodgeData.ofIdeal 𝔞 h𝔞 L).modelHeight = faltingsHeightEC W := by
  rw [HodgeData.modelHeight_ofIdeal, faltingsHeightEC, ← hNeron]
  have hterm : ∀ σ : K →+* ℂ, ZLattice.covolume (L σ).lattice =
      hypVol 1 ((4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆ : K[X]).map σ) := by
    intro σ; rw [hP, hA]
  simp only [hterm]
  have hd : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  field_simp

end AcceptanceIdeal

/-! ## 9. Base change: the archimedean count (part of nodes AR3, H4)

Each complex embedding `σ` of `K` has exactly `[L:K]` extensions to `L`, so sums over the
embeddings of `L` of functions of the restriction are `[L:K]` times the sums over `K`. -/

section BaseChange

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

open Classical in
theorem card_embeddings_over (σ : K →+* ℂ) :
    (Finset.univ.filter (fun τ : L →+* ℂ => τ.comp (algebraMap K L) = σ)).card =
      Module.finrank K L := by
  let _ : Algebra K ℂ := σ.toAlgebra
  have hc : ∀ τ : {τ : L →+* ℂ // τ.comp (algebraMap K L) = σ}, ∀ k : K,
      τ.1 (algebraMap K L k) = algebraMap K ℂ k := fun τ k => by
    have := congr_arg (fun f : K →+* ℂ => f k) τ.2
    simpa [RingHom.algebraMap_toAlgebra] using this
  have hc' : ∀ φ : L →ₐ[K] ℂ, (φ : L →+* ℂ).comp (algebraMap K L) = σ := fun φ => by
    ext k
    simp [RingHom.algebraMap_toAlgebra]
  rw [← AlgHom.card K L ℂ, ← Fintype.card_subtype]
  exact Fintype.card_congr
    { toFun := fun τ => ⟨τ.1, hc τ⟩
      invFun := fun φ => ⟨(φ : L →+* ℂ), hc' φ⟩
      left_inv := fun τ => by ext; rfl
      right_inv := fun φ => by ext; rfl }

open Classical in
/-- `∑_{τ : L → ℂ} f(τ|_K) = [L:K] · ∑_{σ : K → ℂ} f(σ)`. -/
theorem sum_embeddings_comp (f : (K →+* ℂ) → ℝ) :
    ∑ τ : L →+* ℂ, f (τ.comp (algebraMap K L)) =
      Module.finrank K L * ∑ σ : K →+* ℂ, f σ := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (fun τ : L →+* ℂ => τ.comp (algebraMap K L))
    (fun τ => f (τ.comp (algebraMap K L))), Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_congr rfl (fun τ hτ => by rw [(Finset.mem_filter.mp hτ).2]),
    Finset.sum_const, card_embeddings_over, nsmul_eq_mul]

end BaseChange

/-! ## 10. AT1 for every Weierstrass model: translation invariance

`ω ↦ dz` forces `g₂ = c₄/12`, `g₃ = c₆/216` but `P_W = 4x³ + b₂x² + 2b₄x + b₆` equals
`4x³ − g₂x − g₃` only after the translation `x ↦ x − b₂/12`. The archimedean term is translation
invariant (Lebesgue measure on `ℂ`), so AT1 holds with a translation at each `σ`. -/

section Translate

open Polynomial
open scoped nonZeroDivisors

theorem hypGram_comp_add (P : ℂ[X]) (c : ℂ) :
    hypGram (P.comp (X + C c)) 0 0 = hypGram P 0 0 := by
  simp only [hypGram, pow_zero, one_mul, eval_comp, eval_add, eval_X, eval_C]
  congr 1
  exact integral_add_right_eq_self (fun x => 1 / ((‖P.eval x‖ : ℝ) : ℂ)) c

theorem hypVol_one_comp_add (P : ℂ[X]) (c : ℂ) : hypVol 1 (P.comp (X + C c)) = hypVol 1 P := by
  simp only [hypVol, Matrix.det_fin_one, Matrix.of_apply, Fin.val_zero, hypGram_comp_add]

variable {K : Type*} [Field K] [NumberField K]

/-- **Acceptance test AT1, conditional form, any Weierstrass model with semistable reduction.**
As `modelHeight_ofIdeal_eq_faltingsHeightEC`, with the Weierstrass polynomial of `W^σ` equal to
`4x³ − g₂(L σ)x − g₃(L σ)` after a translation `x ↦ x + c σ`. -/
theorem modelHeight_ofIdeal_eq_faltingsHeightEC' (hA : PeriodAreaFormula)
    (W : WeierstrassCurve K) [W.IsElliptic] (𝔞 : FractionalIdeal (𝓞 K)⁰ K) (h𝔞 : 𝔞 ≠ 0)
    (L : (K →+* ℂ) → PeriodPair) (c : (K →+* ℂ) → ℂ)
    (hP : ∀ σ, (4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆ : K[X]).map σ =
      (4 * X ^ 3 - C (L σ).g₂ * X - C (L σ).g₃).comp (X + C (c σ)))
    (hNeron : -12 * Real.log (FractionalIdeal.absNorm 𝔞 : ℝ) =
      finiteHeightPart W.j - ∑ σ : K →+* ℂ, Real.log ‖σ W.Δ‖) :
    (HodgeData.ofIdeal 𝔞 h𝔞 L).modelHeight = faltingsHeightEC W := by
  rw [HodgeData.modelHeight_ofIdeal, faltingsHeightEC, ← hNeron]
  have hterm : ∀ σ : K →+* ℂ, ZLattice.covolume (L σ).lattice =
      hypVol 1 ((4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆ : K[X]).map σ) := by
    intro σ; rw [hP, hypVol_one_comp_add, hA]
  simp only [hterm]
  have hd : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  field_simp

end Translate

/-! ## 11. Base change of fractional-ideal Hermitian lines (node AR3, finite half)

`N_L(I𝓞_L) = N_K(I)^{[L:K]}` for fractional ideals (from Mathlib's `Ideal.absNorm_algebraMap` for
integral ideals), hence `deg_L((I, ρ)_{𝓞_L}) = [L:K] · deg_K(I, ρ)`: the Arakelov degree divided
by the absolute degree, i.e. the height, is invariant under base change. -/

section BaseChangeNorm

open scoped nonZeroDivisors

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem finrank_ringOfIntegers : Module.finrank (𝓞 K) (𝓞 L) = Module.finrank K L :=
  (IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L).symm

theorem absNorm_map_ringOfIntegers (I : Ideal (𝓞 K)) :
    Ideal.absNorm (I.map (algebraMap (𝓞 K) (𝓞 L))) = Ideal.absNorm I ^ Module.finrank K L := by
  rw [Ideal.absNorm_algebraMap, finrank_ringOfIntegers]

theorem norm_algebraMap_tower (x : K) :
    Algebra.norm ℚ (algebraMap K L x) = Algebra.norm ℚ x ^ Module.finrank K L := by
  rw [← Algebra.norm_norm (S := K), Algebra.norm_algebraMap, map_pow]

/-- **Norm of an extended fractional ideal.** -/
theorem absNorm_extendedHom (I : FractionalIdeal (𝓞 K)⁰ K) :
    FractionalIdeal.absNorm (FractionalIdeal.extendedHom L (𝓞 L) I) =
      FractionalIdeal.absNorm I ^ Module.finrank K L := by
  have hnum := FractionalIdeal.den_mul_self_eq_num' (𝓞 K)⁰ K I
  set d : 𝓞 K := (I.den : 𝓞 K) with hd
  have hd0 : algebraMap (𝓞 K) K d ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors I.den.2
  have hK := congr_arg FractionalIdeal.absNorm hnum
  rw [map_mul, FractionalIdeal.absNorm_span_singleton, FractionalIdeal.coeIdeal_absNorm] at hK
  have hL := congr_arg (fun J => FractionalIdeal.absNorm (FractionalIdeal.extendedHom L (𝓞 L) J))
    hnum
  simp only [map_mul, FractionalIdeal.extendedHom_spanSingleton,
    FractionalIdeal.extendedHom_coeIdeal_eq_map, FractionalIdeal.absNorm_span_singleton,
    FractionalIdeal.coeIdeal_absNorm, absNorm_map_ringOfIntegers] at hL
  have hmap : IsFractionRing.map (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L))
      (algebraMap (𝓞 K) K d) = algebraMap K L (algebraMap (𝓞 K) K d) := by
    simp only [IsFractionRing.map]
    rw [IsLocalization.map_eq, ← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L,
      ← IsScalarTower.algebraMap_apply (𝓞 K) K L]
  rw [hmap, norm_algebraMap_tower, Nat.cast_pow, ← hK, abs_pow, mul_pow] at hL
  have hN0 : |Algebra.norm ℚ (algebraMap (𝓞 K) K d)| ^ Module.finrank K L ≠ 0 :=
    pow_ne_zero _ (abs_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr hd0))
  exact mul_left_cancel₀ hN0 hL

/-- **Base change of the Arakelov degree** for Hermitian lines given by fractional ideals:
`deg_L(I𝓞_L, ρ∘res) = [L:K] · deg_K(I, ρ)`. -/
theorem arakelovDegree_ofFractionalIdeal_baseChange (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    (ρ : (K →+* ℂ) → ℝ) (hρ : ∀ σ, 0 < ρ σ) :
    (HermitianLattice.ofFractionalIdeal (FractionalIdeal.extendedHom L (𝓞 L) I)
      ((FractionalIdeal.extendedHom_eq_zero_iff L (𝓞 L)).not.mpr hI)
      (fun τ => ρ (τ.comp (algebraMap K L))) (fun _ => hρ _)).arakelovDegree =
      Module.finrank K L * (HermitianLattice.ofFractionalIdeal I hI ρ hρ).arakelovDegree := by
  rw [HermitianLattice.arakelovDegree_ofFractionalIdeal,
    HermitianLattice.arakelovDegree_ofFractionalIdeal, absNorm_extendedHom,
    sum_embeddings_comp (fun σ => Real.log (ρ σ))]
  push_cast
  rw [Real.log_pow]
  ring

end BaseChangeNorm

/-! ## 12. Base-change invariance of the model height (node H4, dimension-1 Hodge data) -/

section BaseChangeHeight

open scoped nonZeroDivisors

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- **The model height does not change under base change** (Hodge data of the form
`HodgeData.ofIdeal`): extending the lattice to `𝓞_L` and restricting the period lattices,
`h_L = h_K`. This is the Arakelov-theoretic content of "the Faltings height of a model with good
(or semistable) base change is invariant", node H4. -/
theorem HodgeData.modelHeight_ofIdeal_baseChange (𝔞 : FractionalIdeal (𝓞 K)⁰ K) (h𝔞 : 𝔞 ≠ 0)
    (P : (K →+* ℂ) → PeriodPair) :
    (HodgeData.ofIdeal (FractionalIdeal.extendedHom L (𝓞 L) 𝔞)
      ((FractionalIdeal.extendedHom_eq_zero_iff L (𝓞 L)).not.mpr h𝔞)
      (fun τ => P (τ.comp (algebraMap K L)))).modelHeight =
      (HodgeData.ofIdeal 𝔞 h𝔞 P).modelHeight := by
  rw [HodgeData.modelHeight_ofIdeal, HodgeData.modelHeight_ofIdeal, absNorm_extendedHom,
    sum_embeddings_comp (L := L) (fun σ => Real.log (ZLattice.covolume (P σ).lattice volume)),
    ← Module.finrank_mul_finrank ℚ K L]
  have hK : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hL : (0 : ℝ) < Module.finrank K L := by exact_mod_cast Module.finrank_pos
  push_cast
  rw [Real.log_pow]
  field_simp

end BaseChangeHeight

/-! ## 13. A numerical normalization check: `covol(ℤ + ℤi) = 1`, so `exampleHodge` has height 0 -/

section Gaussian

theorem covolume_gaussianPair : ZLattice.covolume gaussianPair.lattice = 1 := by
  have hspan : gaussianPair.lattice = Submodule.span ℤ (Set.range Complex.basisOneI) := by
    rw [Complex.coe_basisOneI, Matrix.range_cons, Matrix.range_cons, Matrix.range_empty,
      Set.union_empty, Set.singleton_union]
    rfl
  have hF : IsAddFundamentalDomain gaussianPair.lattice
      (ZSpan.fundamentalDomain Complex.basisOneI) volume := by
    rw [hspan]; exact ZSpan.isAddFundamentalDomain _ volume
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume hF]
  have himg : Complex.measurableEquivPi ⁻¹'
      ZSpan.fundamentalDomain (Complex.basisOneI.map Complex.basisOneI.equivFun) =
      ZSpan.fundamentalDomain Complex.basisOneI := by
    rw [← ZSpan.map_fundamentalDomain]
    ext z
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨w, hw, hwz⟩
      have : w = z := Complex.basisOneI.equivFun.injective (by
        rw [hwz]; rfl)
      exact this ▸ hw
    · intro hz
      exact ⟨z, hz, rfl⟩
  rw [Measure.real, ← himg, Complex.volume_preserving_equiv_pi.measure_preimage
    (ZSpan.fundamentalDomain_measurableSet _).nullMeasurableSet, ZSpan.volume_fundamentalDomain]
  have : Matrix.of (Complex.basisOneI.map Complex.basisOneI.equivFun) = 1 := by
    ext i j
    simp [Matrix.one_apply]
    fin_cases i <;> fin_cases j <;> simp
  rw [this, Matrix.det_one, abs_one, ENNReal.ofReal_one, ENNReal.toReal_one]

theorem exampleHodge_modelHeight_eq_zero : exampleHodge.modelHeight = 0 := by
  rw [exampleHodge_modelHeight, covolume_gaussianPair, Real.log_one, mul_zero]

end Gaussian

/-! ## 14. Tensor products of fractional-ideal Hermitian lines (node AR3)

For invertible `𝓞_K`-modules inside `K`, `I ⊗ J ≅ IJ`, and the tensor-product metric is the
product metric; the degree is additive. -/

section Tensor

open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

theorem arakelovDegree_ofFractionalIdeal_mul (I J : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    (hJ : J ≠ 0) (ρ ρ' : (K →+* ℂ) → ℝ) (hρ : ∀ σ, 0 < ρ σ) (hρ' : ∀ σ, 0 < ρ' σ) :
    (HermitianLattice.ofFractionalIdeal (I * J) (mul_ne_zero hI hJ) (fun σ => ρ σ * ρ' σ)
      (fun σ => mul_pos (hρ σ) (hρ' σ))).arakelovDegree =
      (HermitianLattice.ofFractionalIdeal I hI ρ hρ).arakelovDegree +
        (HermitianLattice.ofFractionalIdeal J hJ ρ' hρ').arakelovDegree := by
  simp only [HermitianLattice.arakelovDegree_ofFractionalIdeal, map_mul, Rat.cast_mul]
  have hI0 : (FractionalIdeal.absNorm I : ℝ) ≠ 0 := by
    exact_mod_cast (FractionalIdeal.absNorm_eq_zero_iff.not.mpr hI)
  have hJ0 : (FractionalIdeal.absNorm J : ℝ) ≠ 0 := by
    exact_mod_cast (FractionalIdeal.absNorm_eq_zero_iff.not.mpr hJ)
  rw [Real.log_mul hI0 hJ0, Finset.sum_congr rfl fun σ _ =>
    Real.log_mul (hρ σ).ne' (hρ' σ).ne', Finset.sum_add_distrib]
  ring

end Tensor

/-! ## 15. Abelian varieties and smooth group models (copied from `bp-faltings/Models.lean`) -/

section ModelsSec

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ExteriorAlgebra
open PkgI3

/-! `AbVar`, `AbVar.baseChange`, `AbVar.dim` are the kernel's `PkgI3.AbVar`,
`PkgI3.AbVar.baseChange`, `PkgI3.AbVar.dim` (identical definitions to the copies in
`scratch/def-faltings/Faltings.lean` §15). -/

/-- The generic fibre `𝒢_L` of a scheme `𝒢` over `𝓞_L`. -/
noncomputable def genericFibre (L : Type) [Field L] [NumberField L]
    (G : Over (Spec (CommRingCat.of (𝓞 L)))) : Over (Spec (CommRingCat.of L)) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L)))).obj G

/-- **Node M1** (copied from `bp-faltings/Models.lean`). A smooth, separated, quasi-compact group
scheme over `𝓞_L` with an isomorphism of group schemes from its generic fibre to `A_L`. -/
structure GroupModel {K : Type} [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L]
    [Algebra K L] where
  /-- the model -/
  G : Over (Spec (CommRingCat.of (𝓞 L)))
  [grp : GrpObj G]
  [smooth : Smooth G.hom]
  [separated : IsSeparated G.hom]
  [qc : QuasiCompact G.hom]
  /-- the identification of the generic fibre with `A_L` -/
  gen : genericFibre L G ≅ (A.baseChange L).X
  /-- ... as group schemes -/
  gen_hom : letI : GrpObj (genericFibre L G) := Functor.grpObjObj
    IsMonHom gen.hom

attribute [instance] GroupModel.grp GroupModel.smooth GroupModel.separated GroupModel.qc

/-- The generic point of `Spec 𝓞_L`. -/
def genericPt (L : Type) [Field L] [NumberField L] : Spec (CommRingCat.of (𝓞 L)) :=
  (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (𝓞 L))

/-! ## 16. The Hodge line of a smooth group model (nodes AV3, M2, M3)

Let `e : S = Spec 𝓞_L → 𝒢` be the unit section and `ξ = e(η_S)` the image of the generic point
(the identity of the generic fibre `𝒢_L ≅ A_L`). The local ring `𝒪_{𝒢,ξ}` is the local ring of
`A_L` at its origin, so `cotangent = 𝔪_ξ/𝔪_ξ²` is `ω_{A_L} = e*Ω¹_{A_L/L}` (an `L`-space of
dimension `g`; STANDARD, not proved here). For a point `s ∈ S`, `x = e(s)` specializes from `ξ`,
and `I_x = ker(𝒪_{𝒢,x} → 𝒪_{S,s})` is the ideal of the section at `x`; the image of `I_x` in
`𝔪_ξ/𝔪_ξ²` is the stalk at `s` of the conormal sheaf `e*(I/I²) = e*Ω¹_{𝒢/S}` (`𝒢/S` smooth;
EGA IV 17.2.5, UNVERIFIED locator). A locally free sheaf on the integral scheme `S` has global
sections the intersection of its stalks inside the generic stalk, hence

`ω_𝒢 = Γ(S, e*Ω¹_{𝒢/S}) = ⋂_s image(I_{e(s)})`   (`GroupModel.omega`).

Every module structure below is definitional (no proof obligations): the `𝓞_L`-module structure
on `cotangent` is restriction of scalars along the structure map `𝓞_L → 𝒪_{𝒢,ξ}`, and the
`L`-line is `hodgeSpace g = L ⊗_{𝓞_L} ⋀^g_{𝓞_L} cotangent` (`≅ ⋀^g_L ω_{A_L}` since `cotangent`
is an `L`-space; STANDARD). -/

namespace GroupModel

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

/-- The unit section `e : Spec 𝓞_L → 𝒢`. -/
noncomputable def unitSection : Spec (CommRingCat.of (𝓞 L)) ⟶ 𝒢.G.left :=
  (η[𝒢.G] : 𝟙_ (Over (Spec (CommRingCat.of (𝓞 L)))) ⟶ 𝒢.G).left

/-- `ξ = e(generic point)`: the identity of the generic fibre. -/
noncomputable def genericUnit : 𝒢.G.left := 𝒢.unitSection (genericPt L)

/-- The local ring `𝒪_{𝒢,ξ} = 𝒪_{A_L,0}`. -/
noncomputable abbrev genStalk : CommRingCat := 𝒢.G.left.presheaf.stalk 𝒢.genericUnit

/-- The structure map `𝓞_L = Γ(S) → Γ(𝒢) → 𝒪_{𝒢,ξ}`. -/
noncomputable def structMap : 𝓞 L →+* 𝒢.genStalk :=
  ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv ≫ 𝒢.G.hom.appTop ≫
    𝒢.G.left.presheaf.germ ⊤ 𝒢.genericUnit trivial).hom

/-- **Node AV3.** `ω_{A_L} = 𝔪_ξ/𝔪_ξ²`, the invariant differentials of the generic fibre. -/
def cotangent : Type := IsLocalRing.CotangentSpace 𝒢.genStalk

noncomputable instance : AddCommGroup 𝒢.cotangent :=
  inferInstanceAs (AddCommGroup (IsLocalRing.CotangentSpace 𝒢.genStalk))

noncomputable instance : Module 𝒢.genStalk 𝒢.cotangent :=
  inferInstanceAs (Module 𝒢.genStalk (IsLocalRing.CotangentSpace 𝒢.genStalk))

noncomputable instance : Module (𝓞 L) 𝒢.cotangent := Module.compHom _ 𝒢.structMap

/-- `df ∈ 𝔪_ξ/𝔪_ξ²` for a germ `f ∈ 𝔪_ξ`. -/
noncomputable def dCls (f : IsLocalRing.maximalIdeal 𝒢.genStalk) : 𝒢.cotangent :=
  (IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent f

/-- `ξ ⤳ e(s)` for every `s ∈ Spec 𝓞_L`. -/
theorem specializes_genericUnit (s : Spec (CommRingCat.of (𝓞 L))) :
    𝒢.genericUnit ⤳ 𝒢.unitSection s :=
  ((PrimeSpectrum.le_iff_specializes (genericPt L) s).mp bot_le).map
    𝒢.unitSection.continuous

/-- The stalk at `s` of `e*Ω¹_{𝒢/S}` inside `ω_{A_L}`: the `𝓞_L`-span of the image of
`I_{e(s)} = ker(𝒪_{𝒢,e(s)} → 𝒪_{S,s})` under specialization `𝒪_{𝒢,e(s)} → 𝒪_{𝒢,ξ}`. (The
condition that the image lies in `𝔪_ξ` always holds; it is imposed so that no proof is needed in
the definition. The image is already an `𝒪_{S,s}`-module, so the span adds nothing.) -/
noncomputable def omegaAt (s : Spec (CommRingCat.of (𝓞 L))) : Submodule (𝓞 L) 𝒢.cotangent :=
  Submodule.span (𝓞 L) {m | ∃ f ∈ RingHom.ker (𝒢.unitSection.stalkMap s).hom,
    ∃ h : 𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s) f ∈
      IsLocalRing.maximalIdeal 𝒢.genStalk, m = 𝒢.dCls ⟨_, h⟩}

/-- Sanity check of `omegaAt`: at the generic point of `Spec 𝓞_L` the local lattice is all of
`ω_{A_L}` (the stalk of `e*Ω¹` at the generic point is the generic stalk), so `omega` is the
intersection of genuine local lattices at the closed points. Proved. -/
theorem omegaAt_genericPt : 𝒢.omegaAt (genericPt L) = ⊤ := by
  rw [eq_top_iff]
  rintro m -
  obtain ⟨f, rfl⟩ := (IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent_surjective m
  have hspec : ∀ x, (𝒢.G.left.presheaf.stalkSpecializes
      (𝒢.specializes_genericUnit (genericPt L))).hom x = x := by
    intro x
    rw [show 𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit (genericPt L)) =
      𝟙 _ from TopCat.Presheaf.stalkSpecializes_refl _ _]
    rfl
  have hfield : IsField ((Spec (CommRingCat.of (𝓞 L))).presheaf.stalk (genericPt L)) := by
    have : genericPt L = genericPoint (Spec (CommRingCat.of (𝓞 L))) :=
      (genericPoint_eq_bot_of_affine (CommRingCat.of (𝓞 L))).symm
    rw [this]
    exact Field.toIsField _
  apply Submodule.subset_span
  refine ⟨(f : 𝒢.genStalk), ?_, ?_, ?_⟩
  · show (𝒢.unitSection.stalkMap (genericPt L)).hom (f : 𝒢.genStalk) = 0
    have hloc : (𝒢.unitSection.stalkMap (genericPt L)).hom (f : 𝒢.genStalk) ∈
        IsLocalRing.maximalIdeal _ :=
      map_nonunit _ _ ((IsLocalRing.mem_maximalIdeal _).mp f.2)
    rw [IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield] at hloc
    exact hloc
  · convert f.2 using 1
    exact hspec _
  · unfold dCls
    congr 1
    exact Subtype.ext (hspec _).symm

/-- **Node M2.** `ω_𝒢 = Γ(Spec 𝓞_L, e*Ω¹_{𝒢/𝓞_L}) = ⋂_s (ω_𝒢)_s ⊆ ω_{A_L}`. -/
noncomputable def omega : Submodule (𝓞 L) 𝒢.cotangent := ⨅ s, 𝒢.omegaAt s

/-- **Node AV4.** The Hodge line `⋀^g ω_{A_L}`, as `L ⊗_{𝓞_L} ⋀^g_{𝓞_L} (𝔪_ξ/𝔪_ξ²)`. -/
abbrev hodgeSpace (g : ℕ) : Type :=
  TensorProduct (𝓞 L) L (exteriorPower (𝓞 L) g 𝒢.cotangent)

/-- **Node M3.** The Hodge lattice `⋀^g ω_𝒢 ⊆ ⋀^g ω_{A_L}`: the `𝓞_L`-span of the wedges of
elements of `ω_𝒢`. -/
noncomputable def detLattice (g : ℕ) : Submodule (𝓞 L) (𝒢.hodgeSpace g) :=
  Submodule.span (𝓞 L) (Set.range fun v : Fin g → 𝒢.omega =>
    (1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g (fun i => (v i : 𝒢.cotangent)))

/-- The wedge `1 ⊗ df₁ ∧ ⋯ ∧ df_g ∈ hodgeSpace g` of germs `f_i ∈ 𝔪_ξ`. -/
noncomputable def wedge {g : ℕ} (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) :
    𝒢.hodgeSpace g :=
  (1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g (fun i => 𝒢.dCls (f i))

/-! ## 17. Complex points and the analytic uniformization (node AN3: the gap)

For `τ : L → ℂ`, the `ℂ`-points of `A_L` at `τ` are the `𝓞_L`-morphisms `Spec ℂ → 𝒢` with
`Spec ℂ → Spec 𝓞_L` given by `τ|_{𝓞_L}` (they factor through the generic fibre since `τ` is
injective). Mathlib gives them a group structure (`MonObj.Hom.group`). A regular function
`s ∈ Γ(U, 𝒪_𝒢)` has a value `evalAt p U s ∈ ℂ` at a point `p ∈ U(ℂ)`.

**`IsAnalyticUniformization 𝒢 τ Λ Φ`** says: `Φ : ℂ^g → 𝒢(ℂ)_τ` is a group homomorphism, onto,
with kernel exactly `Λ`; each `Φ⁻¹(U(ℂ))` is open and each regular function is holomorphic along
`Φ` there. With `Λ` a full lattice, `Φ` is then continuous for the analytic topology, so it
induces a continuous bijection of the compact `ℂ^g/Λ` onto the Hausdorff `A_τ(ℂ)`, a
homeomorphism, holomorphic, hence biholomorphic. Any two such `(Λ, Φ)` differ by a `ℂ`-linear
automorphism of `ℂ^g` (a holomorphic homomorphism of complex tori lifts to a linear map). These
are STANDARD facts of complex analysis, not proved here.

**The gap (AN3).** That such `(Λ, Φ)` *exists* is `AnalyticUniformizationExists` below: a
precisely stated Prop over Mathlib's objects, unproved (it is the uniformization theorem
`A(ℂ) ≅ ℂ^g/Λ`, Mumford, *Abelian varieties* §1, with GAGA-type input; locator UNVERIFIED). The
definition of the height does **not** assume it: the infimum ranges over models *together with*
a uniformization satisfying the Prop. Without the theorem one cannot prove the index set
nonempty, i.e. that the height is `< ⊤`. -/

/-- `Spec ℂ` over `Spec 𝓞_L` via `τ`. -/
noncomputable def ptC (τ : L →+* ℂ) : Over (Spec (CommRingCat.of (𝓞 L))) :=
  Over.mk (Spec.map (CommRingCat.ofHom (τ.comp (algebraMap (𝓞 L) L))))

/-- The complex points `𝒢(ℂ)_τ = A_L(ℂ)_τ`, a group (`MonObj.Hom.group`). -/
noncomputable abbrev Pts (τ : L →+* ℂ) : Type := ptC τ ⟶ 𝒢.G

noncomputable example (τ : L →+* ℂ) : Group (𝒢.Pts τ) := inferInstance

/-- The value `s(p) ∈ ℂ` of a regular function `s ∈ Γ(U, 𝒪_𝒢)` at a complex point `p ∈ U(ℂ)`
(and `0` if `p ∉ U(ℂ)`). -/
noncomputable def evalAt {τ : L →+* ℂ} (p : 𝒢.Pts τ) (U : 𝒢.G.left.Opens)
    (s : Γ(𝒢.G.left, U)) : ℂ := by
  classical
  exact if h : ⊤ ≤ p.left ⁻¹ᵁ U then
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.left.appLE U ⊤ h s) else 0

/-- `Φ⁻¹(U(ℂ)) ⊆ ℂ^g`. -/
def dom {τ : L →+* ℂ} {g : ℕ} (Φ : (Fin g → ℂ) → 𝒢.Pts τ) (U : 𝒢.G.left.Opens) :
    Set (Fin g → ℂ) := {z | ⊤ ≤ (Φ z).left ⁻¹ᵁ U}

/-- **The analytic uniformization at `τ`** (the Prop that pins down the archimedean data). -/
def IsAnalyticUniformization (τ : L →+* ℂ) {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → 𝒢.Pts τ) : Prop :=
  (∀ z w, Φ (z + w) = Φ z * Φ w) ∧
  (∀ z, Φ z = 1 ↔ z ∈ Λ) ∧
  Function.Surjective Φ ∧
  (∀ U, IsOpen (𝒢.dom Φ U)) ∧
  (∀ U (s : Γ(𝒢.G.left, U)), DifferentiableOn ℂ (fun z => 𝒢.evalAt (Φ z) U s) (𝒢.dom Φ U))

theorem exists_rep (t : 𝒢.genStalk) : ∃ (U : 𝒢.G.left.Opens) (m : 𝒢.genericUnit ∈ U)
    (s : Γ(𝒢.G.left, U)), 𝒢.G.left.presheaf.germ U 𝒢.genericUnit m s = t :=
  TopCat.Presheaf.exists_germ_eq _ t

/-- A germ `t ∈ 𝒪_{𝒢,ξ}` composed with `Φ`, through a chosen representative `(U, s)`. Since
`Φ(0) = 1` lies over `ξ` and `Φ⁻¹(U(ℂ))` is open, the germ at `0` of this function, hence its
derivative at `0`, does not depend on the representative (for an analytic uniformization). -/
noncomputable def germAlong {τ : L →+* ℂ} {g : ℕ} (Φ : (Fin g → ℂ) → 𝒢.Pts τ)
    (t : 𝒢.genStalk) : (Fin g → ℂ) → ℂ := fun z =>
  𝒢.evalAt (Φ z) (𝒢.exists_rep t).choose (𝒢.exists_rep t).choose_spec.choose_spec.choose

/-- `det(∂(f_i ∘ Φ)/∂z_j (0))`: the coefficient of `Φ*(df₁ ∧ ⋯ ∧ df_g)` on `dz₁ ∧ ⋯ ∧ dz_g`
(an invariant form is determined by its value at `0`). -/
noncomputable def jacDet {τ : L →+* ℂ} {g : ℕ} (Φ : (Fin g → ℂ) → 𝒢.Pts τ)
    (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) : ℂ :=
  (Matrix.of fun i j : Fin g =>
    fderiv ℂ (𝒢.germAlong Φ (f i : 𝒢.genStalk)) 0 (Pi.single j 1)).det

end GroupModel

/-- **The gap AN3, stated.** For every smooth group model `𝒢` of `A_L` and every `τ : L → ℂ` there
are `g`, a full lattice `Λ ⊂ ℂ^g` and an analytic uniformization `Φ : ℂ^g → 𝒢(ℂ)_τ` with kernel
`Λ`. (The uniformization theorem for complex abelian varieties; unproved, absent from Mathlib:
it needs the analytification of `A_τ` as a compact complex Lie group.) -/
def AnalyticUniformizationExists : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ), ∃ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ))
      (Φ : (Fin g → ℂ) → 𝒢.Pts τ),
      ∃ _ : DiscreteTopology Λ, IsZLattice ℝ Λ ∧ 𝒢.IsAnalyticUniformization τ Λ Φ

/-- **The uniqueness half of AN3, stated.** Two analytic uniformizations differ by a `ℂ`-linear
automorphism `T` of `ℂ^g`: `Φ' = Φ ∘ T`, `Λ' = T⁻¹Λ`. (A holomorphic homomorphism of complex
tori lifts to a linear map; unproved.) With `HodgeData.modelHeight_recoord` this is what makes the
model height independent of the uniformization. -/
def AnalyticUniformizationUnique : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ) (g : ℕ) (Λ Λ' : Submodule ℤ (Fin g → ℂ))
    (Φ Φ' : (Fin g → ℂ) → 𝒢.Pts τ),
    𝒢.IsAnalyticUniformization τ Λ Φ → 𝒢.IsAnalyticUniformization τ Λ' Φ' →
    ∃ T : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), (∀ z, Φ' z = Φ (T z)) ∧ (∀ z, z ∈ Λ' ↔ T z ∈ Λ)

/-- **The algebraic half (AV2-AV4, M2-M3), stated.** For a model of relative dimension `g`
(`g` = the dimension of `A`), `hodgeSpace g` is an `L`-line and `detLattice g` is a full
`𝓞_L`-lattice in it. (Smoothness: `ω_𝒢` is projective of rank `g`; unproved.) -/
def HodgeLatticeTheorem : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (g : ℕ), A.dim = g →
    Module.finrank L (𝒢.hodgeSpace g) = 1 ∧
      ∃ s ∈ 𝒢.detLattice g, s ≠ 0 ∧ secIndex (𝒢.detLattice g) s ≠ 0

/-! ## 18. Metrized models and the stable Faltings height (node H3) -/

/-- **A metrized model of `A_L` of dimension `g`**: a smooth group model `𝒢` (node M1) with its
metrized Hodge line. The lattice is the genuine `⋀^g ω_𝒢` (`lattice_eq`), and at every `τ` the
period lattice and the coefficient map come from an analytic uniformization of `𝒢(ℂ)_τ`
(`arch`): `coeff_τ(1 ⊗ df₁ ∧ ⋯ ∧ df_g) = det(∂(f_i ∘ Φ)/∂z_j(0))`. Since the wedges `wedge f`
span `hodgeSpace g` over `L`, `arch` determines `coeff`; by `AnalyticUniformizationUnique` and
`HodgeData.modelHeight_recoord`, `hodge.modelHeight` depends only on `𝒢`. A wrong `g` makes the
structure empty: for `0 < g ≠ dim A`, `hodge.finrank_eq_one` fails (and for `g > dim A` also
`periods_discrete`); `g = 0` passes `finrank_eq_one` (`hodgeSpace 0 ≅ L`) but is excluded for
`dim A ≥ 1` by surjectivity of `Φ : ℂ⁰ → A_τ(ℂ)` (STANDARD reasoning, not proved). -/
structure MetrizedModel {K : Type} [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L]
    [Algebra K L] (g : ℕ) where
  /-- the smooth group model -/
  model : GroupModel A L
  /-- its Hodge data: lattice, period lattices, coefficient maps -/
  hodge : HodgeData L g (model.hodgeSpace g)
  /-- the lattice is `⋀^g ω_𝒢` -/
  lattice_eq : hodge.lattice = model.detLattice g
  /-- the archimedean data come from analytic uniformizations -/
  arch : ∀ τ : L →+* ℂ, ∃ Φ : (Fin g → ℂ) → model.Pts τ,
    model.IsAnalyticUniformization τ (hodge.periods τ) Φ ∧
    ∀ f : Fin g → IsLocalRing.maximalIdeal model.genStalk,
      hodge.coeff τ (model.wedge f) = model.jacDet Φ f

/-- A number field `L` with a `K`-algebra structure (the index type of the infimum). -/
structure FinExt (K : Type) [Field K] where
  /-- the field -/
  L : Type
  [field : Field L]
  [numberField : NumberField L]
  [algebra : Algebra K L]

attribute [instance] FinExt.field FinExt.numberField FinExt.algebra

/-- **Node H3. The stable Faltings height** (Faltings' original normalization `(i/2)^g`):
`h_F^st(A) = inf_{L, 𝒢} h(A_L, 𝒢) ∈ EReal`, over all number fields `L ⊇ K` and all smooth
separated finite-type group models `𝒢/𝓞_L` of `A_L`, each with its metrized Hodge line.
(pkg-I5 §2.1; equal to the Néron-model value over a semistable `L` by the Néron mapping property
and SGA 7 IX: node H5, not proved. `⊤` if there is no metrized model, which
`AnalyticUniformizationExists` and `HodgeLatticeTheorem` exclude once proved.) -/
noncomputable def stableFaltingsHeight {K : Type} [Field K] (A : AbVar K) : EReal :=
  ⨅ (E : FinExt K) (g : ℕ) (M : MetrizedModel A E.L g), (M.hodge.modelHeight : EReal)

/-- **Node H6. Deligne's normalization** `(i/2π)^g`: each model height shifts by `(g/2) log π`. -/
noncomputable def stableFaltingsHeightDeligne {K : Type} [Field K] (A : AbVar K) : EReal :=
  ⨅ (E : FinExt K) (g : ℕ) (M : MetrizedModel A E.L g),
    ((M.hodge.modelHeight + g / 2 * Real.log Real.pi : ℝ) : EReal)

section HeightLemmas

variable {K : Type} [Field K] (A : AbVar K)

theorem stableFaltingsHeight_le {L : Type} [Field L] [NumberField L] [Algebra K L] {g : ℕ}
    (M : MetrizedModel A L g) : stableFaltingsHeight A ≤ (M.hodge.modelHeight : EReal) :=
  iInf_le_of_le (FinExt.mk L) (iInf_le_of_le g (iInf_le_of_le M le_rfl))

theorem le_stableFaltingsHeight {x : EReal}
    (h : ∀ (E : FinExt K) (g : ℕ) (M : MetrizedModel A E.L g), x ≤ (M.hodge.modelHeight : EReal)) :
    x ≤ stableFaltingsHeight A :=
  le_iInf fun E => le_iInf fun g => le_iInf fun M => h E g M

theorem EReal.add_coe_add_neg_coe (x : EReal) (c : ℝ) : x + (c : EReal) + ((-c : ℝ) : EReal) = x := by
  induction x using EReal.rec with
  | bot => simp
  | top => simp
  | coe a => rw [← EReal.coe_add, ← EReal.coe_add]; congr 1; ring

/-- **H6 for the infimum**: if every metrized model of `A` has dimension `g` (true for
`g = dim A`), `h_D^st(A) = h_F^st(A) + (g/2) log π`. Proved. -/
theorem stableFaltingsHeightDeligne_eq (g : ℕ)
    (hg : ∀ (E : FinExt K) (g' : ℕ), Nonempty (MetrizedModel A E.L g') → g' = g) :
    stableFaltingsHeightDeligne A =
      stableFaltingsHeight A + ((g / 2 * Real.log Real.pi : ℝ) : EReal) := by
  set c : ℝ := g / 2 * Real.log Real.pi
  apply le_antisymm
  · -- `hD + (-c) ≤ hF`
    have key : stableFaltingsHeightDeligne A + ((-c : ℝ) : EReal) ≤ stableFaltingsHeight A := by
      refine le_stableFaltingsHeight A fun E g' M => ?_
      obtain rfl := hg E g' ⟨M⟩
      have h1 : stableFaltingsHeightDeligne A ≤
          ((M.hodge.modelHeight + g' / 2 * Real.log Real.pi : ℝ) : EReal) :=
        iInf_le_of_le E (iInf_le_of_le g' (iInf_le_of_le M le_rfl))
      calc stableFaltingsHeightDeligne A + ((-c : ℝ) : EReal)
          ≤ ((M.hodge.modelHeight + c : ℝ) : EReal) + ((-c : ℝ) : EReal) := by gcongr
        _ = (M.hodge.modelHeight : EReal) := by
          rw [← EReal.coe_add]; congr 1; ring
    calc stableFaltingsHeightDeligne A
        = stableFaltingsHeightDeligne A + ((-c : ℝ) : EReal) + ((c : ℝ) : EReal) := by
          have := EReal.add_coe_add_neg_coe (stableFaltingsHeightDeligne A) (-c)
          rw [neg_neg] at this; exact this.symm
      _ ≤ stableFaltingsHeight A + (c : EReal) := by gcongr
  · refine le_iInf fun E => le_iInf fun g' => le_iInf fun M => ?_
    obtain rfl := hg E g' ⟨M⟩
    rw [EReal.coe_add]
    gcongr
    exact stableFaltingsHeight_le A M

end HeightLemmas

/-! ### Independence of the uniformization (node H2, archimedean part)

Under the uniqueness half of AN3, the height of a metrized model depends only on the group model:
the coefficient map is determined by its values on the wedges `1 ⊗ df₁ ∧ ⋯ ∧ df_g`
(`GroupModel.semilinear_ext_wedge`), which change by `det T` under `Φ ↦ Φ ∘ T`
(`GroupModel.jacDet_comp`, the chain rule), and `HodgeData.modelHeight_recoord` absorbs `T`. -/

section UnifIndep

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

namespace GroupModel

variable (𝒢 : GroupModel A L)

/-- A `τ`-semilinear functional on the Hodge line is determined by its values on the wedges
`1 ⊗ df₁ ∧ ⋯ ∧ df_g` of germs `f_i ∈ 𝔪_ξ`. -/
theorem semilinear_ext_wedge {g : ℕ} {τ : L →+* ℂ} (φ ψ : 𝒢.hodgeSpace g →ₛₗ[τ] ℂ)
    (h : ∀ f, φ (𝒢.wedge f) = ψ (𝒢.wedge f)) : φ = ψ := by
  have h1 : ∀ n : exteriorPower (𝓞 L) g 𝒢.cotangent,
      φ ((1 : L) ⊗ₜ[𝓞 L] n) = ψ ((1 : L) ⊗ₜ[𝓞 L] n) := by
    intro n
    have hn : n ∈ Submodule.span (𝓞 L) (Set.range (exteriorPower.ιMulti (𝓞 L) g)) := by
      rw [exteriorPower.ιMulti_span]; trivial
    induction hn using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, rfl⟩ := hx
      have hm : ∀ i, ∃ f, 𝒢.dCls f = m i := fun i =>
        (IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent_surjective (m i)
      choose f hf using hm
      have := h f
      simp only [wedge, hf] at this
      exact this
    | zero => simp
    | add x y _ _ hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | smul c x _ hx =>
      rw [TensorProduct.tmul_smul, ← algebraMap_smul L c, map_smulₛₗ, map_smulₛₗ, hx]
  ext v
  induction v using TensorProduct.inductionOn with
  | tmul l n =>
    have : l ⊗ₜ[𝓞 L] n = l • ((1 : L) ⊗ₜ[𝓞 L] n) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [this, map_smulₛₗ, map_smulₛₗ, h1]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- **Chain rule**: `jacDet (Φ ∘ T) f = jacDet Φ f · det T`. -/
theorem jacDet_comp {τ : L →+* ℂ} {g : ℕ} (Φ : (Fin g → ℂ) → 𝒢.Pts τ)
    (T : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) :
    𝒢.jacDet (fun z => Φ (T z)) f =
      𝒢.jacDet Φ f * LinearMap.det (T : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) := by
  set Tc := T.toContinuousLinearEquiv
  have hd : ∀ t, fderiv ℂ (𝒢.germAlong (fun z => Φ (T z)) t) 0 =
      (fderiv ℂ (𝒢.germAlong Φ t) 0).comp (Tc : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) := by
    intro t
    have : 𝒢.germAlong (fun z => Φ (T z)) t = 𝒢.germAlong Φ t ∘ Tc := rfl
    rw [this, Tc.comp_right_fderiv, map_zero]
  unfold jacDet
  simp only [hd]
  rw [← LinearMap.det_toMatrix', ← Matrix.det_mul]
  congr 1
  ext i j
  simp only [Matrix.of_apply, Matrix.mul_apply, LinearMap.toMatrix'_apply,
    ContinuousLinearMap.comp_apply]
  show (fderiv ℂ (𝒢.germAlong Φ ↑(f i)) 0) (T (Pi.single j 1)) = _
  conv_lhs => rw [← Finset.univ_sum_single (T (Pi.single j 1))]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hs : (Pi.single k ((T (Pi.single j 1)) k) : Fin g → ℂ) =
      ((T (Pi.single j 1)) k) • (Pi.single k (1 : ℂ) : Fin g → ℂ) := by
    ext m; by_cases hm : m = k
    · subst hm; simp
    · simp [hm]
  rw [hs, map_smul, smul_eq_mul, mul_comm]
  rfl

end GroupModel

/-- **The model height does not depend on the uniformization** (given the uniqueness half of
AN3): two metrized models with the same group model have the same height. Proved. -/
theorem MetrizedModel.modelHeight_eq_of_model_eq (hU : AnalyticUniformizationUnique) {g : ℕ}
    (M M' : MetrizedModel A L g) (h : M.model = M'.model) :
    M.hodge.modelHeight = M'.hodge.modelHeight := by
  obtain ⟨𝒢, D, hl, ha⟩ := M
  obtain ⟨𝒢', D', hl', ha'⟩ := M'
  dsimp only at h ⊢
  subst h
  have key : ∀ τ, ∃ T : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ),
      (∀ z, z ∈ D'.periods τ ↔ T z ∈ D.periods τ) ∧
      D'.coeff τ = LinearMap.det (T : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) • D.coeff τ := by
    intro τ
    obtain ⟨Φ, hΦ, hc⟩ := ha τ
    obtain ⟨Φ', hΦ', hc'⟩ := ha' τ
    obtain ⟨T, hT, hΛ⟩ := hU K A L 𝒢 τ g _ _ Φ Φ' hΦ hΦ'
    refine ⟨T, hΛ, ?_⟩
    apply GroupModel.semilinear_ext_wedge
    intro f
    have hΦ'T : Φ' = fun z => Φ (T z) := funext hT
    rw [hc', LinearMap.smul_apply, hc, smul_eq_mul, hΦ'T, GroupModel.jacDet_comp, mul_comm]
  choose T hTp hTc using key
  have hD' : D' = D.recoord T := by
    obtain ⟨l', f1', il', p', pd', pz', c', cn'⟩ := D'
    obtain ⟨l, f1, il, p, pd, pz, c, cn⟩ := D
    simp only [HodgeData.recoord, HodgeData.mk.injEq]
    refine ⟨hl'.trans hl.symm, ?_, ?_⟩
    · funext τ
      ext z
      rw [hTp τ z]
      rfl
    · funext τ
      exact hTc τ
  show D.modelHeight = D'.modelHeight
  rw [hD', HodgeData.modelHeight_recoord]

/-- **The height of a group model** `h(A_L, 𝒢)`: the infimum over its metrizations (all of which
have the same height, `MetrizedModel.modelHeight_eq_of_model_eq`, given the uniqueness half of
AN3). -/
noncomputable def GroupModel.height (𝒢 : GroupModel A L) : EReal :=
  ⨅ (g : ℕ) (M : MetrizedModel A L g) (_ : M.model = 𝒢), (M.hodge.modelHeight : EReal)

/-- Given the uniqueness half of AN3, a metrized model computes the height of its group model
(among metrizations of the same dimension; the dimension is unique by `hodge.finrank_eq_one` and
the surjectivity in `IsAnalyticUniformization`). -/
theorem GroupModel.height_eq (hU : AnalyticUniformizationUnique) {g : ℕ} (M : MetrizedModel A L g)
    (hg : ∀ (g' : ℕ), Nonempty (MetrizedModel A L g') → g' = g) :
    M.model.height = (M.hodge.modelHeight : EReal) := by
  refine le_antisymm (iInf_le_of_le g (iInf_le_of_le M (iInf_le_of_le rfl le_rfl))) ?_
  refine le_iInf fun g' => le_iInf fun M' => le_iInf fun hM' => ?_
  obtain rfl := hg g' ⟨M'⟩
  rw [MetrizedModel.modelHeight_eq_of_model_eq hU M M' hM'.symm]

/-- `stableFaltingsHeight A = inf_{L, 𝒢} h(A_L, 𝒢)`. -/
theorem stableFaltingsHeight_eq_iInf_height (A : AbVar K) :
    stableFaltingsHeight A = ⨅ (E : FinExt K) (𝒢 : GroupModel A E.L), 𝒢.height := by
  unfold stableFaltingsHeight GroupModel.height
  refine le_antisymm ?_ ?_
  · refine le_iInf fun E => le_iInf fun 𝒢 => le_iInf fun g => le_iInf fun M => le_iInf fun _ => ?_
    exact iInf_le_of_le E (iInf_le_of_le g (iInf_le_of_le M le_rfl))
  · refine le_iInf fun E => le_iInf fun g => le_iInf fun M => ?_
    exact iInf_le_of_le E (iInf_le_of_le M.model (iInf_le_of_le g (iInf_le_of_le M
      (iInf_le_of_le rfl le_rfl))))

end UnifIndep

/-! ### The theorems that tie the definition to the literature (node H5), stated

`IsNeronModel` is the Néron mapping property (BLR 1.2/1, UNVERIFIED locator), stated with
Mathlib's objects: every morphism from the generic fibre of a smooth `𝓞_L`-scheme to `A_L`
extends uniquely. H5 is unproved; it needs Néron models (existence: BLR 1.4/3), semistable
reduction (SGA 7 IX 3.6) and the base change of semistable Néron models (SGA 7 IX 3.3), all
absent from Mathlib (locators UNVERIFIED). -/

section NeronSec

variable {K : Type} [Field K]

/-- **The Néron mapping property** for a group model `𝒩` of `A_L`. -/
def GroupModel.IsNeronModel {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
    (𝒩 : GroupModel A L) : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of (𝓞 L)))) [Smooth Y.hom],
    Function.Bijective fun f : Y ⟶ 𝒩.G =>
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L)))).map f ≫ 𝒩.gen.hom

/-- **H5, finiteness (statement).** Over a number field, the stable height is a real number. -/
def StableHeightFinite : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : AbVar K),
    stableFaltingsHeight A ≠ ⊤ ∧ stableFaltingsHeight A ≠ ⊥

/-- **H5, minimality of the Néron model (statement).** Over any `L`, the Néron model has the
least height among group models (from the mapping property, `ω_𝒩 ⊆ ω_𝒢`, and
`HodgeData.modelHeight_le_of_le`). -/
def NeronModelMinimal : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒩 𝒢 : GroupModel A L), 𝒩.IsNeronModel → 𝒩.height ≤ 𝒢.height

/-- The real-valued stable Faltings height. Meaningful only together with `StableHeightFinite`
(`EReal.toReal` sends `⊤` and `⊥` to `0`); the leaves above therefore never use it. -/
noncomputable def faltingsHeight (A : AbVar K) : ℝ := (stableFaltingsHeight A).toReal

theorem faltingsHeight_coe (hfin : StableHeightFinite) [NumberField K] (A : AbVar K) :
    (faltingsHeight A : EReal) = stableFaltingsHeight A :=
  EReal.coe_toReal (hfin K A).1 (hfin K A).2

end NeronSec

end ModelsSec

/-! # Part II. Curves, Jacobians, Belyi functions (copied from
`scratch/leaf-modcurves/ModCurveLeaves.lean` §D, §E, §G; definitions unchanged) -/

section CurvesSec

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3

/-- (copied) A smooth proper geometrically connected curve over `K` (proper curves are
projective). -/
class IsCurve {K : Type} [Field K] (X : Over (Spec (CommRingCat.of K))) : Prop where
  proper : IsProper X.hom
  smooth : SmoothOfRelativeDimension 1 X.hom
  geomConnected : GeometricallyConnected X.hom

/-- (copied) **`J` is the Jacobian of the pointed curve `(X, P₀)`, with Abel–Jacobi map `aj`**
(the Albanese property; Milne, *Jacobian varieties*, in Arithmetic Geometry (1986), Prop. 6.1,
UNVERIFIED number). Every pointed `K`-morphism to an abelian variety factors uniquely through a
homomorphism `J → A`. -/
structure IsJacobian {K : Type} [Field K] (X : Over (Spec (CommRingCat.of K)))
    (P₀ : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ X) (J : AbVar K) (aj : X ⟶ J.X) : Prop where
  base : P₀ ≫ aj = η[J.X]
  univ : ∀ (A : AbVar K) (f : X ⟶ A.X), P₀ ≫ f = η[A.X] →
    ∃! φ : J.X ⟶ A.X, IsMonHom φ ∧ aj ≫ φ = f

/-- (copied) **Leaf MC6' (existence of the Jacobian)** of leaf-modcurves: Weil 1948; Milne 1986,
Thm 1.1 with Prop. 6.1 (UNVERIFIED numbers). -/
def JacobianExists (K : Type) [Field K] : Prop :=
  ∀ (X : Over (Spec (CommRingCat.of K))) (_ : IsCurve X)
    (P₀ : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ X),
    ∃ (J : AbVar K) (aj : X ⟶ J.X), IsJacobian X P₀ J aj

/-- (copied) **Belyi function over `k`** (function-field form): `t` transcendental over `k`, and
`k(t) ⊆ F` unramified (ramification index 1) at every place `w ⊇ k` of `F` over a finite place of
`k(t)` other than `t = 0`, `t = 1`. -/
def IsBelyiFunction (k F : Type) [Field k] [Field F] [Algebra k F] (t : F) : Prop :=
  Transcendental k t ∧
  ∀ w : ValuationSubring F, (∀ c : k, algebraMap k F c ∈ w) → t ∈ w →
    ∀ q : Polynomial k, q.Monic → Irreducible q → q ≠ Polynomial.X → q ≠ Polynomial.X - 1 →
      Polynomial.aeval t q ∈ w.nonunits →
      ∀ x ∈ w.nonunits, ∃ y ∈ w, x = Polynomial.aeval t q * y

/-! ### New: the function field of a curve as a `K`-algebra -/

variable {K : Type} [Field K]

end CurvesSec

/-! # Part III. The leaves R18, R22, R3 -/

section R18Sec

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3

/-- **R18. Javanpeykar** (Algebra Number Theory 8 (2014), Thm 1.1.1, p. 90; arXiv:1403.6404v1
p. 1; height identification p. 98 / arXiv §2.3 p. 9; read by the locator audit,
docs/research/locators.md). Printed: for a smooth projective connected curve `X/ℚ̄` of genus
`g ≥ 1`, `h_Fal(X) ≤ 13·10⁶ · g · deg_B(X)⁵`, where `h_Fal(X)` is the stable Faltings height of
`Jac X` and `deg_B(X)` the least degree of a Belyi map `X → ℙ¹_ℚ̄`.

**Stated form (a consequence).** `X` is a smooth proper geometrically connected integral curve over
a number field `K` with a `K`-point `P₀`; `J` is its Jacobian (Albanese predicate, over the
kernel's `PkgI3.AbVar`); `g = dim J` (= genus `X`, Milne 1986 Prop. 2.1/Thm 1.1, UNVERIFIED
numbers; rv-blueprints §2 recommendation 5: state with `g := dim J`); `t ∈ K(X)` is a Belyi
function over `K` with `d = [K(X) : K(t)]`. Then `h_F^st(J) ≤ 13·10⁶ · g · d⁵`.

Why it is a consequence of the printed theorem:
* `X_ℚ̄` (any embedding `K ↪ ℚ̄`) is smooth projective connected of genus `g`; `J_ℚ̄ = Jac(X_ℚ̄)`
  (the Albanese property is stable under field extension; STANDARD, Milne 1986).
* A Belyi function over `K` is one over `ℚ̄` of the same degree (characteristic 0, `K`
  algebraically closed in `K(X)`), so `deg_B(X_ℚ̄) ≤ d`, and the bound is monotone in `d`.
* The stable height does not depend on the field of definition, and in either of the two
  normalizations in question (Faltings' `(i/2)^g`, Deligne's `(i/2π)^g`) the bound holds for
  `h_F`, since `h_D = h_F + (g/2) log π ≥ h_F` (rv-blueprints §1.2). A normalization without the
  `2^{-g}` factor would give `h = h_F − (g/2) log 2` and make this form stronger; the locator audit
  read Javanpeykar's height as the stable Faltings height (leaf-push2 review: RISK, low).
* **H5** (rv-blueprints F2): `stableFaltingsHeight` (an infimum over metrized smooth group
  models, `EReal`) equals the published height. Only the half "the Néron model over a semistable
  field is a metrized model with the published height" is used here (an upper bound on an
  infimum). The statement asserts in particular `stableFaltingsHeight J < ⊤`, which is part of
  that half (the published height is a real number). -/
def R18_Javanpeykar : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (X : Over (Spec (CommRingCat.of K))) [IsCurve X]
    [IsIntegral X.left] (P₀ : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ X) (J : AbVar K)
    (aj : X ⟶ J.X), IsJacobian X P₀ J aj →
    ∀ g : ℕ, J.dim = (g : WithBot ℕ∞) → 1 ≤ g →
    ∀ t : X.left.functionField,
      letI := ffAlgebra X
      IsBelyiFunction K X.left.functionField t →
      ∀ d : ℕ, Module.finrank (IntermediateField.adjoin K {t}) X.left.functionField = d → 0 < d →
        stableFaltingsHeight J ≤ ((javanpeykarBound g d : ℝ) : EReal)

/-- The real-valued form: if the stable height is a real number `x`, then `x ≤ 13·10⁶ g d⁵`. -/
theorem R18_real (h : R18_Javanpeykar) (K : Type) [Field K] [NumberField K]
    (X : Over (Spec (CommRingCat.of K))) [IsCurve X] [IsIntegral X.left]
    (P₀ : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ X) (J : AbVar K) (aj : X ⟶ J.X)
    (hJ : IsJacobian X P₀ J aj) (g : ℕ) (hg : J.dim = (g : WithBot ℕ∞)) (hg1 : 1 ≤ g)
    (t : X.left.functionField)
    (ht : letI := ffAlgebra X; IsBelyiFunction K X.left.functionField t) (d : ℕ)
    (hd : letI := ffAlgebra X
      Module.finrank (IntermediateField.adjoin K {t}) X.left.functionField = d) (hd0 : 0 < d)
    (x : ℝ) (hx : stableFaltingsHeight J = x) : x ≤ javanpeykarBound g d := by
  have := h K X P₀ J aj hJ g hg hg1 t ht d hd hd0
  rw [hx] at this
  exact_mod_cast this

end R18Sec

/-! ## R22 (Pazuki): complex points, analytic uniformization, Siegel space, theta constants -/

section R22Sec

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3 Complex

variable {K : Type} [Field K]

/-- **R22. Pazuki** (Bull. SMF 140 (2012), Cor. 1.3(2), pp. 21-22 (`g = r = 2`), metric p. 26,
theta height p. 30; arXiv:0907.1458v2 Cor. 1.3(2) p. 3, Def. 2.1 pp. 6-7, Def. 2.6 p. 9; read by
the locator audit, docs/research/locators.md item 5). Printed (literal): for a principally
polarized abelian surface over `ℚ̄`, `|max(1,h_Θ) − max(1,h_D)/2| ≤ C₂ log(min(max(1,h_Θ),
max(1,h_D)) + 2)`, `h_D` in Deligne's metric, `h_Θ` the theta height with Euclidean norms at the
infinite places.

**Stated form (a consequence; the audit's upper half, rv-loc-leaves (c)).** For an abelian
surface `A` over a number field `K` whose stable Faltings height (Faltings' normalization) is the
real number `x`, and any `X ≥ max(1, x + log π)`; for every complex embedding `σ`, every analytic
uniformization `Φ` of `A(ℂ)_σ` with kernel `Λ`, every `Ω ∈ 𝔥₂` that is a period matrix of `Λ`
(= every principal polarization of `A(ℂ)_σ` with a symplectic basis), and every algebraic
representative `z ∈ L¹⁶` (`L` a number field, `emb : L → ℂ`) of the theta-null point
`[θ_m(0, Ω)]_m`: `h(z) ≤ X/2 + C₂ log(X + 2)`.

Why it is a consequence (each step is a citation-chain fact, not a Lean leaf):
* `h_D = h_F + log π` for surfaces (audit; `stableFaltingsHeightDeligne_eq`), so the hypothesis
  on `X` gives `X ≥ max(1, h_D)`; the three algebraic steps from the literal corollary are proved
  (`pazuki_upper_of_literal` in scratch/rv-loc-leaves, recompiled in §R22-glue below).
* The sup-norm height `absLogHeight` is `≤` the Euclidean-norm height of the paper (each
  archimedean factor `max |z_m| ≤ (∑|z_m|²)^{1/2}`); so an upper bound on Pazuki's `h_Θ` bounds it.
* Every analytic principal polarization of `A(ℂ)_σ` is algebraic and defined over `ℚ̄` (Riemann's
  theorem / GAGA, Mumford §§1-3 (T11-type input); rigidity of `NS`); its theta-null point is
  Pazuki's (Def. 2.6, level `r = 2`; the identification of his coordinates with the classical
  `θ[a;b](0, Ω)`, `a, b ∈ {0,½}²`, follows the project's reading (h-decomposition R22, pkg-I5),
  UNVERIFIED here). A change of symplectic basis permutes the `θ_m` up to eighth roots of unity
  and one common factor (theta transformation formula), so the height does not depend on it.
* **H5** identifies `stableFaltingsHeight` with the published height (rv-blueprints F2); taking
  the height through a real `x` (not `EReal.toReal`) keeps the statement no stronger.

Non-vacuity rests on standard facts not proved here: uniformizations exist (the `AbVar` analogue
of def-faltings' `AnalyticUniformizationExists`), principally polarizable abelian surfaces exist
over number fields (Jacobians of genus-2 curves), the theta-null point is algebraic up to a
common factor; and `𝔥₂ ≠ ∅` (`isSiegel_I`, proved below). -/
def R22_Pazuki : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : AbVar K), A.dim = (2 : WithBot ℕ∞) →
    ∀ x : ℝ, stableFaltingsHeight A = x →
    ∀ X : ℝ, max 1 (x + Real.log Real.pi) ≤ X →
    ∀ (σ : K →+* ℂ) (Λ : Submodule ℤ (Fin 2 → ℂ)) (Φ : (Fin 2 → ℂ) → CPts A σ),
      IsUniformization σ Λ Φ →
    ∀ Ω : Matrix (Fin 2) (Fin 2) ℂ, IsSiegel Ω → IsPeriodMatrix Λ Ω →
    ∀ (L : Type) [Field L] [NumberField L] (emb : L →+* ℂ) (z : Char2 → L) (c : ℂ), c ≠ 0 →
      (∀ m, emb (z m) = c * thetaConst Ω m) →
      absLogHeight z ≤ X / 2 + pazukiC2 * Real.log (X + 2)

/-- The hardened form used by the glue (`X = max(1, h_F + 3)`, rv-leaves-a §3.3). -/
theorem R22_plus3 (h : R22_Pazuki) (K : Type) [Field K] [NumberField K] (A : AbVar K)
    (hA : A.dim = (2 : WithBot ℕ∞)) (x : ℝ) (hx : stableFaltingsHeight A = x)
    (σ : K →+* ℂ) (Λ : Submodule ℤ (Fin 2 → ℂ)) (Φ : (Fin 2 → ℂ) → CPts A σ)
    (hΦ : IsUniformization σ Λ Φ) (Ω : Matrix (Fin 2) (Fin 2) ℂ) (hΩ : IsSiegel Ω)
    (hP : IsPeriodMatrix Λ Ω) (L : Type) [Field L] [NumberField L] (emb : L →+* ℂ)
    (z : Char2 → L) (c : ℂ) (hc : c ≠ 0) (hz : ∀ m, emb (z m) = c * thetaConst Ω m) :
    absLogHeight z ≤ max 1 (x + 3) / 2 + pazukiC2 * Real.log (max 1 (x + 3) + 2) := by
  have hpi : Real.log Real.pi ≤ 3 := by
    have h4 : Real.log Real.pi ≤ Real.log 4 :=
      Real.log_le_log Real.pi_pos (by linarith [Real.pi_lt_four])
    have h42 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith [Real.log_two_lt_d9]
  exact h K A hA x hx (max 1 (x + 3)) (max_le_max le_rfl (by linarith)) σ Λ Φ hΦ Ω hΩ hP
    L emb z c hc hz

end R22Sec

/-! ## R3 (Lin–Yang): the QM surfaces of discriminant 6 are Jacobians on the Lin–Yang family -/

section R3Sec

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3

/-! ### The order `𝒪` and QM structures (copied from `scratch/leaf-qm-fp/QMLeaves.lean` §0-§1) -/

/-- (copied) `B = (2, −3)_ℚ` (`i² = 2`, `j² = −3`). -/
abbrev B := QuaternionAlgebra ℚ 2 0 (-3)

/-- (copied) -/
def ofInt (n : Fin 4 → ℤ) : B :=
  ⟨n 0 + (n 2 : ℚ) / 2, n 1 + (n 3 : ℚ) / 2, (n 2 : ℚ) / 2, (n 3 : ℚ) / 2⟩

/-- (copied) -/
def InO (x : B) : Prop := ∃ n : Fin 4 → ℤ, x = ofInt n

/-- (copied) -/
def mulCoord (n m : Fin 4 → ℤ) : Fin 4 → ℤ :=
  ![m 0 * n 0 + 2 * m 1 * n 1 + 2 * m 1 * n 3 - m 2 * n 2 + 2 * m 3 * n 3,
    m 0 * n 1 + m 1 * n 0 + m 1 * n 2 - m 2 * n 3 + m 3 * n 2,
    m 0 * n 2 - 2 * m 1 * n 3 + m 2 * n 0 + m 2 * n 2 + 2 * m 3 * n 1,
    m 0 * n 3 - m 1 * n 2 + m 2 * n 1 + m 2 * n 3 + m 3 * n 0]

theorem ofInt_mul (n m : Fin 4 → ℤ) : ofInt n * ofInt m = ofInt (mulCoord n m) := by
  ext <;> simp [ofInt, mulCoord] <;> ring

theorem ofInt_add (n m : Fin 4 → ℤ) : ofInt n + ofInt m = ofInt (n + m) := by
  ext <;> simp [ofInt] <;> ring

theorem ofInt_neg (n : Fin 4 → ℤ) : -ofInt n = ofInt (-n) := by
  ext <;> simp [ofInt] <;> ring

theorem ofInt_zero : ofInt 0 = 0 := by ext <;> simp [ofInt]

theorem ofInt_one : ofInt ![1, 0, 0, 0] = 1 := by ext <;> simp [ofInt]

/-- (copied) The maximal order `𝒪 = ℤ⟨1, i, (1+j)/2, (i+k)/2⟩` of `B = (2,−3)`. -/
def O : Subring B where
  carrier := {x | InO x}
  mul_mem' := by
    rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
    exact ⟨mulCoord n m, ofInt_mul n m⟩
  one_mem' := ⟨![1, 0, 0, 0], ofInt_one.symm⟩
  add_mem' := by
    rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
    exact ⟨n + m, ofInt_add n m⟩
  zero_mem' := ⟨0, ofInt_zero.symm⟩
  neg_mem' := by
    rintro _ ⟨n, rfl⟩
    exact ⟨-n, ofInt_neg n⟩

/-- (copied) **A QM structure by `𝒪` on `A`**: an injective unital ring homomorphism
`ι : 𝒪 → End_K(A)`. No polarization (see the R3 docstring). -/
structure QMStr {K : Type} [Field K] (A : AbVar K) where
  iota : O →+* AbVar.End A
  injective : Function.Injective iota

/-! ### Igusa–Clebsch and Igusa invariants of a sextic (copied from
`scratch/hdec-elementary/Leaves.lean` §1; Igusa's `J`'s new here) -/

variable {k : Type*} [Field k]

/-! ### The curve `y² = a ∏ (X − rᵢ)` as a scheme -/

/-- **R3. Lin–Yang** (Math. Z. 295 (2020), 775-819; arXiv:1807.00466v1 **Example 29**, pp. 20-21,
discriminant 6, eqs. (13)-(14); read in arXiv v1 by the locator audit, journal numbering
UNVERIFIED; alternative supplier of the tuple and of the finite-nonzero-`j` Jacobian assertion:
Baba–Granath, Canad. J. Math. 60 (2008), Prop. 3.6, p. 742, read by the audit). Printed: on the
finite nonzero `j`-locus, the principally polarized QM surface of discriminant 6 over `j` is the
Jacobian of a genus-2 curve with `[J₂:J₄:J₆:J₁₀] = [12(j+1) : 6(j²+j+1) : 4(j³−2j²+1) : j³]`.

**Stated form (a consequence; polarization-free and coordinate-free).** Every abelian surface `A`
over `ℂ` with an embedding `𝒪 ↪ End(A)` is either `≅ Jac(C)` (as group schemes) for a curve `C`
with an affine model `y² = a ∏ (x − rᵢ)` (six distinct roots) on the Lin–Yang family at some
`j ≠ 0`, or `≅ E₁ × E₂` for elliptic curves `E₁, E₂`.

Why it is a consequence (citation chain, not Lean leaves):
* `(A, ι)` carries a principal polarization of the fixed type, so it is a point of `X₆` with a
  value `j ∈ ℙ¹` of the Hauptmodul of `X₆/W` (leaf-adopt2: Lemma QP, rv-qm-polar §0: for the
  fixed `μ` (N5's `2j+ij`) the type-`μ` principal polarization of `(A, ι)` exists and is unique
  in characteristic 0, also at CM points; its conditions (type fixed, characteristic 0, `𝒪`
  maximal) all hold here; VERIFIED as an argument, lattice cores compiled
  (`eq_pm_E0_of_principal`, `type_eq_mu_mul`), published locators (Buzzard 1997 p. 592; Rotger
  2003, 2004) UNVERIFIED; Baba–Granath Thm 2.1 for `X₆/W`).
* `j ≠ 0, ∞`: Lin–Yang's assertion, forgetting the polarization (`≅` of group schemes).
* `j ∈ {0, ∞}`: the tuple has `J₁₀ = 0` there (in weighted-projective coordinates), so the
  principally polarized surface is not the Jacobian of a smooth curve, hence a product of elliptic
  curves (Weil's dichotomy for principally polarized abelian surfaces; Weil 1957, UNVERIFIED).
  The second disjunct is weaker than "product with its product polarization".

**Polarization (rv-qm-polar).** The statement is existential in `C` and does not mention a
polarization, so it stays a consequence although a QM surface carries several principal
polarizations (rv-qm-polar §1.3: one of each type `c ∈ 𝒪`, `c² = −6`, up to sign; only the
type-`μ` one of Lemma QP is used, and it gives Lin–Yang's curve).
What would change: a form "for **every** genus-2
`C` with `Jac C ≅ A`, `C` lies on the family" (not stated here; false in general if `A` carries a
principal polarization whose Rosati involution is not of the fixed type), and the
coordinate-linked form "`j` = the value `π₆(x)` of the moduli point" (needs leaf-qm-fp's `X₆`
package and the polarization type; not stated here).

**Over `ℂ`** (Lin–Yang's setting). The `ℚ̄`-form used at A7/F1 follows by the Lefschetz principle
(the Shimura curve, the family and the Igusa invariants are defined over `ℚ`): glue target
`R03_LinYang_algClosed` below, not a leaf. -/
def R03_LinYang : Prop :=
  ∀ (A : AbVar ℂ) (_ : QMStr A), A.dim = (2 : WithBot ℕ∞) →
    (∃ (j a : ℂ) (r : Fin 6 → ℂ), j ≠ 0 ∧ IsGenus2 a r ∧ LinYangTuple a r j ∧
      ∃ (C : Over (Spec (CommRingCat.of ℂ))) (_ : IsCurve C) (_ : IsIntegral C.left),
        HasSexticModel C a r ∧
        ∃ (P₀ : 𝟙_ (Over (Spec (CommRingCat.of ℂ))) ⟶ C) (J : AbVar ℂ) (aj : C ⟶ J.X),
          IsJacobian C P₀ J aj ∧ ∃ e : J.X ≅ A.X, IsMonHom e.hom) ∨
    (∃ E₁ E₂ : AbVar ℂ, E₁.dim = (1 : WithBot ℕ∞) ∧ E₂.dim = (1 : WithBot ℕ∞) ∧
      Nonempty (A.X ≅ E₁.X ⊗ E₂.X))

/-- **Glue target (Lefschetz principle), not a leaf**: `R03_LinYang` over every algebraically
closed field of characteristic 0 (the case `k = ℚ̄` is the one A7/F1 use). -/
def R03_LinYang_algClosed : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (A : AbVar k) (_ : QMStr A),
    A.dim = (2 : WithBot ℕ∞) →
    (∃ (j a : k) (r : Fin 6 → k), j ≠ 0 ∧ IsGenus2 a r ∧ LinYangTuple a r j ∧
      ∃ (C : Over (Spec (CommRingCat.of k))) (_ : IsCurve C) (_ : IsIntegral C.left),
        HasSexticModel C a r ∧
        ∃ (P₀ : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ C) (J : AbVar k) (aj : C ⟶ J.X),
          IsJacobian C P₀ J aj ∧ ∃ e : J.X ≅ A.X, IsMonHom e.hom) ∨
    (∃ E₁ E₂ : AbVar k, E₁.dim = (1 : WithBot ℕ∞) ∧ E₂.dim = (1 : WithBot ℕ∞) ∧
      Nonempty (A.X ≅ E₁.X ⊗ E₂.X))

/-- The algebraically closed form contains the leaf (`k = ℂ`). -/
theorem R03_of_algClosed (h : R03_LinYang_algClosed) : R03_LinYang :=
  fun A q hA => h ℂ A q hA

end R3Sec

/-! ## T10-T12: what a concrete statement needs (only the parts statable over the definitions
above; no étale cohomology is built). See docs/research/leaf-push2.md §5. -/

section TSec

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3

/-- Complex conjugation in `G_ℚ`: `c` restricts complex conjugation along some embedding
`ℚ̄ ↪ ℂ`. (Duplicates `PkgI4.IsComplexConj` of Leaves.lean; to be identified at integration.) -/
def IsComplexConj (c : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : Prop :=
  ∃ emb : AlgebraicClosure ℚ →ₐ[ℚ] ℂ, ∀ x, emb (c x) = starRingEnd ℂ (emb x)

end TSec

end ZInQ.LeafPush2

end LeafPush2Sec
section GlueSSBCSec
/-! ### Copied from `scratch/glue-ssbc/SSBC.lean` (compiled there; imports covered by Mathlib). Inserted by leaf-adopt3 following g0-split's recipe. -/
noncomputable section

namespace GlueSSBC

open Module Representation

section General

variable {F W : Type*} [Field F] [AddCommGroup W] [Module F W] [FiniteDimensional F W]

/-- The trace form `(x, y) ↦ tr_W (x y)` on a subalgebra `B ⊆ End_F W` is nondegenerate. -/
def TraceNondeg (B : Subalgebra F (Module.End F W)) : Prop :=
  ∀ x ∈ B, (∀ y ∈ B, LinearMap.trace F W (x * y) = 0) → x = 0

/-- A finite-dimensional subalgebra of `End W` with nondegenerate trace form is a semisimple
ring. -/
theorem isSemisimpleRing_of_traceNondeg (B : Subalgebra F (Module.End F W))
    (h : TraceNondeg B) : IsSemisimpleRing B := by
  have : IsArtinianRing B := IsArtinianRing.of_finite F B
  rw [IsArtinianRing.isSemisimpleRing_iff_jacobson, eq_bot_iff]
  intro x hx
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := B)
  rw [Ideal.jacobson_bot] at hn
  have hnil : ∀ y : B, IsNilpotent ((x : Module.End F W) * y) := by
    intro y
    have hxy : x * y ∈ Ring.jacobson B := Ideal.mul_mem_right _ _ hx
    refine ⟨n, ?_⟩
    have : (x * y) ^ n ∈ Ring.jacobson B ^ n := Ideal.pow_mem_pow hxy n
    rw [hn] at this
    have h0 : (x * y) ^ n = 0 := (Submodule.mem_bot _).mp this
    have := congrArg (fun z : B => (z : Module.End F W)) h0
    simpa using this
  have : (x : Module.End F W) = 0 := by
    apply h _ x.2
    intro y hy
    exact (LinearMap.isNilpotent_trace_of_isNilpotent (hnil ⟨y, hy⟩)).eq_zero
  exact (Submodule.mem_bot _).mpr (Subtype.ext this)

set_option backward.isDefEq.respectTransparency false in
/-- A faithful finite-dimensional semisimple module makes the subalgebra a semisimple ring. -/
theorem isSemisimpleRing_of_isSemisimpleModule (B : Subalgebra F (Module.End F W))
    [IsSemisimpleModule B W] : IsSemisimpleRing B := by
  let bas := Module.finBasis F W
  let n := Module.finrank F W
  let f : B →ₗ[B] (Fin n →₀ W) :=
    (Finsupp.linearEquivFunOnFinite B W (Fin n)).symm.toLinearMap ∘ₗ
      LinearMap.pi (fun i => LinearMap.toSpanSingleton B W (bas i))
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro b hb
    rw [LinearMap.mem_ker] at hb
    rw [Submodule.mem_bot]
    apply Subtype.ext
    apply bas.ext
    intro i
    have := congrArg (fun φ : Fin n →₀ W => φ i) hb
    simpa [f, Subalgebra.smul_def, Module.End.smul_def] using this
  have : IsSemisimpleModule B (LinearMap.range f) := inferInstance
  refine IsSemisimpleModule.congr (R := B) (N := B) (M := ↥(LinearMap.range f)) ?_
  exact LinearEquiv.ofInjective f hf

/-- **Char 0:** a subalgebra of `End W` over which `W` is semisimple has nondegenerate trace
form. -/
theorem traceNondeg_of_isSemisimpleModule [CharZero F] (B : Subalgebra F (Module.End F W))
    [IsSemisimpleModule B W] : TraceNondeg B := by
  have := isSemisimpleRing_of_isSemisimpleModule B
  let I : Ideal B :=
    { carrier := {x | ∀ y : B, LinearMap.trace F W ((x : Module.End F W) * y) = 0}
      add_mem' := by
        intro a b ha hb y
        simp only [Set.mem_ofPred_eq, Subalgebra.coe_add, add_mul, map_add] at *
        rw [ha y, hb y, add_zero]
      zero_mem' := by intro y; simp
      smul_mem' := by
        intro c x hx y
        simp only [Set.mem_ofPred_eq, smul_eq_mul, Subalgebra.coe_mul] at *
        rw [mul_assoc, LinearMap.trace_mul_comm, mul_assoc]
        have := hx (y * c)
        simpa using this }
  obtain ⟨e, he, hIe⟩ := IsSemisimpleRing.ideal_eq_span_idempotent I
  have heI : e ∈ I := hIe ▸ Ideal.subset_span (Set.mem_singleton e)
  have he' : IsIdempotentElem (e : Module.End F W) := by
    have := congrArg (fun z : B => (z : Module.End F W)) he.eq
    simpa [IsIdempotentElem] using this
  have htr : LinearMap.trace F W (e : Module.End F W) = 0 := by
    have := heI e
    rwa [he'.eq] at this
  have he0 : e = 0 := Subtype.ext ((LinearMap.IsIdempotentElem.trace_eq_zero_iff he').mp htr)
  have hI : I = ⊥ := by rw [hIe, he0, Ideal.span_singleton_eq_bot]
  intro x hx hxy
  have : (⟨x, hx⟩ : B) ∈ I := fun y => hxy y y.2
  rw [hI] at this
  exact congrArg Subtype.val ((Submodule.mem_bot _).mp this)

end General

section Rep

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]

/-- Base change `ρ_E` of a representation along a field extension `E/k` (verbatim from
glue-I3-linalg). -/
def repBaseChange (E : Type*) [Field E] [Algebra k E] (ρ : Representation k G V) :
    Representation E G (TensorProduct k E V) where
  toFun g := (ρ g).baseChange E
  map_one' := by
    change (ρ 1).baseChange E = LinearMap.id
    rw [map_one, Module.End.one_eq_id, LinearMap.baseChange_id]
  map_mul' g h := by
    change (ρ (g * h)).baseChange E = (ρ g).baseChange E ∘ₗ (ρ h).baseChange E
    rw [map_mul, Module.End.mul_eq_comp, LinearMap.baseChange_comp]

/-- `ρ` is semisimple iff `V` is a semisimple module over the span of `ρ(G)`. -/
theorem isSemisimpleRepresentation_iff_range (ρ : Representation k G V) :
    ρ.IsSemisimpleRepresentation ↔ IsSemisimpleModule (asAlgebraHom ρ).range V := by
  rw [isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  let σ : MonoidAlgebra k G →+* (asAlgebraHom ρ).range := (asAlgebraHom ρ).rangeRestrict.toRingHom
  have : RingHomSurjective σ := ⟨AlgHom.rangeRestrict_surjective _⟩
  let l : ρ.asModule →ₛₗ[σ] V :=
    { toFun := ρ.asModuleEquiv
      map_add' := map_add _
      map_smul' := fun r x => asModuleEquiv_map_smul ρ r x }
  exact LinearMap.isSemisimpleModule_iff_of_bijective l ρ.asModuleEquiv.bijective

theorem mem_range_of (ρ : Representation k G V) (g : G) : ρ g ∈ (asAlgebraHom ρ).range :=
  ⟨MonoidAlgebra.of k G g, asAlgebraHom_of ρ g⟩

theorem asAlgebraHom_eq_sum (ρ : Representation k G V) (r : MonoidAlgebra k G) :
    asAlgebraHom ρ r = r.coeff.sum (fun g a => a • ρ g) := by
  rw [asAlgebraHom_def, MonoidAlgebra.lift_apply]

theorem baseChange_mem_range (E : Type*) [Field E] [Algebra k E] (ρ : Representation k G V)
    (y : Module.End k V) (hy : y ∈ (asAlgebraHom ρ).range) :
    y.baseChange E ∈ (asAlgebraHom (repBaseChange E ρ)).range := by
  obtain ⟨s, rfl⟩ := hy
  show (asAlgebraHom ρ s).baseChange E ∈ _
  induction s using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, LinearMap.baseChange_add]; exact Subalgebra.add_mem _ ha hb
  | single g a =>
    rw [asAlgebraHom_single, LinearMap.baseChange_smul, ← algebraMap_smul E a]
    exact Subalgebra.smul_mem _ (mem_range_of (repBaseChange E ρ) g) _

variable [FiniteDimensional k V]

/-- **Base change of the trace-form criterion.** -/
theorem traceNondeg_baseChange (E : Type*) [Field E] [Algebra k E] (ρ : Representation k G V)
    (hA : TraceNondeg (asAlgebraHom ρ).range) :
    TraceNondeg (asAlgebraHom (repBaseChange E ρ)).range := by
  intro x hx hxy
  obtain ⟨r, rfl⟩ := hx
  change (∀ y ∈ _, LinearMap.trace E _ (asAlgebraHom (repBaseChange E ρ) r * y) = 0) at hxy
  show asAlgebraHom (repBaseChange E ρ) r = 0
  rw [asAlgebraHom_eq_sum] at hxy ⊢
  set c := r.coeff
  have hρE : ∀ g, repBaseChange E ρ g = (ρ g).baseChange E := fun g => rfl
  -- every `k`-linear functional of the coefficients gives an element of the radical over `k`
  have key : ∀ f : Module.Dual k E, c.sum (fun g a => f a • ρ g) = 0 := by
    intro f
    apply hA _ (Subalgebra.sum_mem _ fun g _ => Subalgebra.smul_mem _ (mem_range_of ρ g) _)
    intro y hy
    have h0 := congrArg f (hxy _ (baseChange_mem_range E ρ y hy))
    simp only [Finsupp.sum, Finset.sum_mul, smul_mul_assoc, map_sum, map_smul, hρE,
      ← LinearMap.baseChange_mul, LinearMap.trace_baseChange, smul_eq_mul, map_zero] at h0 ⊢
    rw [← h0]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [mul_comm (c g), ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  let b := Module.finBasis k V
  have hv : ∀ v : V, (c.sum (fun g a => a • repBaseChange E ρ g)) (1 ⊗ₜ v) = 0 := by
    intro v
    apply (Algebra.TensorProduct.basis E b).repr.injective
    ext j
    rw [map_zero, Finsupp.zero_apply]
    rw [← Module.forall_dual_apply_eq_zero_iff k]
    intro f
    have hk := congrArg (fun φ : Module.End k V => b.repr (φ v) j) (key f)
    simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, hρE,
      LinearMap.baseChange_tmul, map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
      Finsupp.smul_apply, Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply,
      smul_eq_mul, LinearMap.zero_apply, map_zero, Finsupp.zero_apply] at hk ⊢
    rw [← hk]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [mul_comm (c g), ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  apply (Algebra.TensorProduct.basis E b).ext
  intro i
  rw [Algebra.TensorProduct.basis_apply, hv, LinearMap.zero_apply]

/-- **`SemisimpleBaseChange`, proved.** In characteristic `0`, a semisimple finite-dimensional
representation stays semisimple after any extension of the coefficient field. -/
theorem isSemisimpleRepresentation_baseChange [CharZero k] (E : Type*) [Field E] [Algebra k E]
    (ρ : Representation k G V) (hρ : ρ.IsSemisimpleRepresentation) :
    (repBaseChange E ρ).IsSemisimpleRepresentation := by
  rw [isSemisimpleRepresentation_iff_range] at hρ ⊢
  have hA := traceNondeg_of_isSemisimpleModule (asAlgebraHom ρ).range
  have := isSemisimpleRing_of_traceNondeg _ (traceNondeg_baseChange E ρ hA)
  infer_instance

end Rep

/-- glue-I3-linalg's Prop, verbatim (with `repBaseChange` from this file). -/
def SemisimpleBaseChange : Prop :=
  ∀ (k E G V : Type) [Field k] [CharZero k] [Field E] [Algebra k E] [Monoid G] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] (ρ : Representation k G V),
    ρ.IsSemisimpleRepresentation → (repBaseChange E ρ).IsSemisimpleRepresentation

theorem semisimpleBaseChange : SemisimpleBaseChange :=
  fun _ E _ _ _ _ _ _ _ _ _ _ ρ hρ => isSemisimpleRepresentation_baseChange E ρ hρ

end GlueSSBC
end
end GlueSSBCSec




noncomputable section

namespace HSyn

open scoped MatrixGroups ModularForm

/-! ## §0. Cheap definitions -/

/-- `ℚ̄`. -/
abbrev Qbar := AlgebraicClosure ℚ

/-- `G_ℚ = Gal(ℚ̄/ℚ)`, with Mathlib's Krull topology. -/
abbrev GQ := Qbar ≃ₐ[ℚ] Qbar

/-- `v` is a place of `ℚ̄` above the prime `p`: a valuation subring of `ℚ̄` in which `p` is not a
unit. (Its restriction to `ℚ` is then `ℤ_(p)`.) -/
def LiesOver (v : ValuationSubring Qbar) (p : ℕ) : Prop := (p : Qbar) ∈ v.nonunits

/-- `σ` is an arithmetic Frobenius at the place `v` above `p`: it stabilizes `v` and acts as
`x ↦ x^p` on its residue field. -/
def IsArithFrob (σ : GQ) (v : ValuationSubring Qbar) (p : ℕ) : Prop :=
  σ ∈ v.decompositionSubgroup ℚ ∧ ∀ x ∈ v, σ x - x ^ p ∈ v.nonunits

/-- A continuous `n`-dimensional representation of `G_ℚ` over `ℚ̄_ℓ` (Mathlib's normed
`PadicAlgCl ℓ`). Continuity for the norm topology is equivalent to the usual notion (the image
lies in `GL_n` of a finite extension of `ℚ_ℓ`), by compactness and Baire. -/
structure GaloisRep (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) where
  toHom : GQ →* GL (Fin n) (PadicAlgCl ℓ)
  continuous_toHom : Continuous toHom

variable {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ}

/-- `ρ` is unramified at `p`: every inertia group above `p` acts trivially. -/
def GaloisRep.UnramifiedAt (ρ : GaloisRep ℓ n) (p : ℕ) : Prop :=
  ∀ v : ValuationSubring Qbar, LiesOver v p →
    ∀ σ ∈ v.inertiaSubgroup ℚ, ρ.toHom ((σ : v.decompositionSubgroup ℚ) : GQ) = 1

/-- Every arithmetic Frobenius above `p` has trace `a` (meaningful at unramified `p`). -/
def GaloisRep.FrobTrace (ρ : GaloisRep ℓ n) (p : ℕ) (a : PadicAlgCl ℓ) : Prop :=
  ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v p → IsArithFrob σ v p →
    Matrix.trace (ρ.toHom σ : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) = a

/-- `c` is a complex conjugation: it is induced by `z ↦ z̄` through some embedding `ℚ̄ → ℂ`. -/
def IsComplexConj (c : GQ) : Prop :=
  ∃ ι : Qbar →ₐ[ℚ] ℂ, ∀ x, ι (c x) = starRingEnd ℂ (ι x)

/-- `ρ` is odd: `det ρ(c) = −1` for every complex conjugation `c`. -/
def GaloisRep.IsOdd (ρ : GaloisRep ℓ 2) : Prop :=
  ∀ c, IsComplexConj c → Matrix.det (ρ.toHom c : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)) = -1

/-- `ρ` is (absolutely) irreducible, in Burnside's form: its image spans `M_n(ℚ̄_ℓ)`. Over the
algebraically closed `ℚ̄_ℓ` this is equivalent to irreducibility. -/
def GaloisRep.IsIrreducible (ρ : GaloisRep ℓ n) : Prop :=
  Algebra.adjoin (PadicAlgCl ℓ)
    (Set.range fun σ => (ρ.toHom σ : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ))) = ⊤

/-- `ρ` is semisimple: every invariant subspace has an invariant complement. -/
def GaloisRep.IsSemisimple (ρ : GaloisRep ℓ n) : Prop :=
  ∀ W : Submodule (PadicAlgCl ℓ) (Fin n → PadicAlgCl ℓ),
    (∀ σ, W.map (Matrix.toLin' (ρ.toHom σ : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ))) ≤ W) →
    ∃ W', IsCompl W W' ∧
      ∀ σ, W'.map (Matrix.toLin' (ρ.toHom σ : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ))) ≤ W'

/-- Cusp forms of weight `k` on `Γ₁(N)` (Mathlib). -/
abbrev CF (N : ℕ) (k : ℤ) := CuspForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k

/-- The `m`-th q-expansion coefficient `a_m(f)` (period 1). -/
def coeff {N : ℕ} {k : ℤ} (f : CF N k) (m : ℕ) : ℂ :=
  (UpperHalfPlane.qExpansion 1 f).coeff m

/-- `f` has nebentypus `χ`: `f|_k γ = χ(d) f` for `γ = (a b; c d) ∈ Γ₀(N)`. -/
def HasNebentypus {N : ℕ} {k : ℤ} (f : CF N k) (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ γ ∈ CongruenceSubgroup.Gamma0 N, (⇑f ∣[k] γ) = χ (((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod N) • ⇑f

/-- `f` is a normalized eigenform of all Hecke operators with nebentypus `χ`, expressed through
its coefficients: `a₁ = 1` and `a_m a_n = Σ_{d ∣ (m,n)} χ(d) d^{k−1} a_{mn/d²}` (with `χ(d) = 0`
for `(d, N) > 1`). For a form with nebentypus `χ` this is equivalent to the Hecke definition
(Diamond–Shurman, Prop. 5.3.1; locator UNVERIFIED). -/
def IsNormalizedEigenform {N : ℕ} {k : ℤ} (f : CF N k) (χ : DirichletCharacter ℂ N) : Prop :=
  HasNebentypus f χ ∧ coeff f 1 = 1 ∧
    ∀ m n : ℕ, 0 < m → 0 < n →
      coeff f m * coeff f n =
        ∑ d ∈ (Nat.gcd m n).divisors, χ (d : ZMod N) * (d : ℂ) ^ (k - 1) * coeff f (m * n / d ^ 2)

/-- `ρ` is attached to the eigenform `g` (through embeddings `ιC : ℚ̄ → ℂ`, `ιL : ℚ̄ → ℚ̄_ℓ`): for
`p ∤ Nℓ`, `ρ` is unramified at `p` and its Frobenius trace is `ιL(α)` where `ιC(α) = a_p(g)`. -/
def GaloisRep.AttachedTo (ρ : GaloisRep ℓ 2) (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    {N : ℕ} {k : ℤ} (g : CF N k) : Prop :=
  ∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ →
    ρ.UnramifiedAt p ∧ ∃ α : Qbar, ιC α = coeff g p ∧ ρ.FrobTrace p (ιL α)

/-! ## §1. Leaves statable today over the cheap definitions (not proved here; copied from the
hdec-faithful draft). Numbering of the note: T13 Skolem–Noether, T14 HasseBrauerQ, T17
Kronecker–Weber, T18 FrobeniusDense, T19 Brauer–Nesbitt, R14 EigenformRepExists, R15
DeligneSerreConseq, T24 EigenformTwist. -/

/-- **L14. Skolem–Noether** (Reiner, *Maximal orders*, Thm 7.21; Tau Ceti `skolemNoether`).
Exact. -/
def SkolemNoether : Prop :=
  ∀ (K A B : Type) [Field K] [Ring A] [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A]
    [FiniteDimensional K A] [Ring B] [Algebra K B] [IsSimpleRing B] [FiniteDimensional K B]
    (f g : B →ₐ[K] A), ∃ x : Aˣ, ∀ b, g b = (x : A) * f b * ((x⁻¹ : Aˣ) : A)

/-- **L15(a). Hasse principle for `Br(ℚ)`, in the form used** (Albert–Brauer–Hasse–Noether with
the sum formula; Milne, *Arithmetic duality theorems*, Ch. I). A central simple `ℚ`-algebra that
splits over every `ℚ_p` splits over `ℚ`. Consequence (the real invariant is forced to 0). -/
def HasseBrauerQ : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℚ A] [Algebra.IsCentral ℚ A] [IsSimpleRing A]
    [FiniteDimensional ℚ A] (n : ℕ), Module.finrank ℚ A = n ^ 2 →
    (∀ p : ℕ, ∀ _ : Fact p.Prime,
      Nonempty (TensorProduct ℚ ℚ_[p] A ≃ₐ[ℚ_[p]] Matrix (Fin n) (Fin n) ℚ_[p])) →
    Nonempty (A ≃ₐ[ℚ] Matrix (Fin n) (Fin n) ℚ)

/-- **L17. Kronecker–Weber** (Washington, *Cyclotomic fields*, Thm 14.1; Tau Ceti
`kroneckerWeber`). Exact. -/
def KroneckerWeber : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L],
    (∀ σ τ : L ≃ₐ[ℚ] L, σ * τ = τ * σ) →
    ∃ n : ℕ+, Nonempty (L →ₐ[ℚ] CyclotomicField (n : ℕ) ℚ)

/-- **L18. Chebotarev, in the density form used** (Neukirch VII.13.4; Tau Ceti). Frobenius
elements are dense in `G_ℚ`, avoiding any finite set of primes. Consequence. -/
def FrobeniusDense : Prop :=
  ∀ (U : Subgroup GQ), IsOpen (U : Set GQ) → ∀ (σ : GQ) (S : Finset ℕ),
    ∃ p, p.Prime ∧ p ∉ S ∧ ∃ (v : ValuationSubring Qbar) (τ : GQ),
      LiesOver v p ∧ IsArithFrob τ v p ∧ τ⁻¹ * σ ∈ U

/-- **L19. Brauer–Nesbitt** (Curtis–Reiner §30). Semisimple representations of a group over a
field of characteristic 0 with equal traces are isomorphic. Exact. -/
def BrauerNesbitt : Prop :=
  ∀ (G : Type) [Group G] (E : Type) [Field E] [CharZero E] (n : ℕ)
    (ρ₁ ρ₂ : G →* GL (Fin n) E),
    (∀ W : Submodule E (Fin n → E),
      (∀ g, W.map (Matrix.toLin' (ρ₁ g : Matrix (Fin n) (Fin n) E)) ≤ W) →
      ∃ W', IsCompl W W' ∧ ∀ g, W'.map (Matrix.toLin' (ρ₁ g : Matrix (Fin n) (Fin n) E)) ≤ W') →
    (∀ W : Submodule E (Fin n → E),
      (∀ g, W.map (Matrix.toLin' (ρ₂ g : Matrix (Fin n) (Fin n) E)) ≤ W) →
      ∃ W', IsCompl W W' ∧ ∀ g, W'.map (Matrix.toLin' (ρ₂ g : Matrix (Fin n) (Fin n) E)) ≤ W') →
    (∀ g, Matrix.trace (ρ₁ g : Matrix (Fin n) (Fin n) E) =
      Matrix.trace (ρ₂ g : Matrix (Fin n) (Fin n) E)) →
    ∃ P : GL (Fin n) E, ∀ g, ρ₂ g = P * ρ₁ g * P⁻¹

/-- **L27(a). Galois representations of eigenforms** (Eichler–Shimura `k = 2`, Deligne 1971
`k ≥ 2`, Deligne–Serre 1974 `k = 1`). Consequence (the published statements also give the
determinant). -/
def EigenformRepExists : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : CF N k),
    0 < N → 1 ≤ k → IsNormalizedEigenform g χ →
    ∃ ρ : GaloisRep ℓ 2, ρ.IsSemisimple ∧ ρ.AttachedTo ιC ιL g

/-- **L27(b). Deligne–Serre, in the form used** (Ann. Sci. ÉNS 7 (1974), Thm 4.1, with L18 and
L19). A semisimple representation attached to a weight-one eigenform has finite image.
Consequence. -/
def DeligneSerreConseq : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (ρ : GaloisRep ℓ 2) (N : ℕ) (χ : DirichletCharacter ℂ N) (g : CF N 1),
    0 < N → IsNormalizedEigenform g χ → ρ.IsSemisimple → ρ.AttachedTo ιC ιL g →
    (Set.range ρ.toHom).Finite

/-- **L28(a). Twisting an eigenform** (Shimura 1971, Prop. 3.64; Atkin–Li 1978). The twist of a
normalized eigenform of level `N` by a character mod `m` is a normalized eigenform of level
`Nm²` with coefficients `ψ(p) a_p` at `p ∤ Nm`. Consequence. -/
def EigenformTwist : Prop :=
  ∀ (N m : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ m) (g : CF N k),
    0 < N → 0 < m → IsNormalizedEigenform g χ →
    ∃ (χ' : DirichletCharacter ℂ (N * m ^ 2)) (g' : CF (N * m ^ 2) k),
      IsNormalizedEigenform g' χ' ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ N * m → coeff g' p = ψ (p : ZMod m) * coeff g p


/-! ## §2. Leaves that need definitions Mathlib lacks: placeholders (no content)

Each docstring gives the statement in the form the proof uses, the reference (UNVERIFIED unless
the note says otherwise), and the missing definitions with their cost tier. -/

/-! leaf-adopt (2026-11-12): the placeholders `R01_ShimuraDeligne`, `R02_BabaGranath` and
`R05_GonzalezRotger` are replaced by leaf-qm-fp's concrete field-point statements (section
`LeafQMSec`), with rv-blueprints' repairs Q2, Q4, Q5 (section `LeafAdoptSec`): the bundle uses
`LeafAdopt.R1R2fpRep` (R1(a), (c), (d), R1 at level one, `π₀(X₆) = 1`, R2 with biconditional CM
clauses, R5 on points), `LeafQM.AV.R1rec` (R1(d), object form), `LeafQM.AV.R5fp` (= R5fpStrong,
`LeafAdopt.R5fp_iff_R5fpStrong`) and `LeafQM.AV.R5fpCount`. All of them rest on Lemma QP of
rv-qm-polar (type `μ` fixed, characteristic 0, `𝒪` maximal; see `LeafAdopt.R1R2fpRep`;
leaf-adopt2). Part (b) of R1 stays a placeholder: -/

/-- **R1(b). Complex uniformization, in family form** (rv-blueprints Q3; R1an of bp-qmmoduli).
For `Y₃` and `π : Y₃ → P¹` of `LeafAdopt.R1R2fpRep`: (a) for every `P : QML3 ℂ` there is `τ ∈ ℍ`
with `P.A(ℂ) ≅ ℂ²/ι(𝒪)(τ, 1)ᵀ` compatibly with `ι`; (b) for every `τ ∈ ℍ` there are `P_τ : QML3 ℂ`
and such an isomorphism; (c) `τ ↦ π(Φ⁻¹[P_τ]) ∈ P¹(ℂ)` is holomorphic on `ℍ`. The Hauptmodul
comparison of F1 (`PkgI1.QMHauptmodul` against `π`) uses (b) and (c); a statement at each point
separately is too weak. Shimura, Ann. of Math. 85 (1967), Main Thm I; Deligne, Sém. Bourbaki 389
(1971), §4.15 (analytic families) (UNVERIFIED locators). Missing: analytification of `ℂ`-schemes
and of abelian varieties (large; bp-qmmoduli N14). Rests on Lemma QP (rv-qm-polar) as R1R2fpRep.
Part (a) at a single point would follow from `ZInQ.LeafPush2.UniformizationExists` (T35) with
T11a (the `ℂ`-linear action of `ι(𝒪)` on the lattice), class number one of `𝒪` (Eichler) and the
QM lattice computation (bp-analytic Q1); that reduction is not carried out. (b) and (c) are the
family statements. -/
opaque R01b_ComplexUniformization : Prop

/-! leaf-adopt2 (2026-11-12): the placeholder `R03_LinYang` is replaced by leaf-push2's
`ZInQ.LeafPush2.R03_LinYang` (section `LeafPush2Sec`): over `ℂ`, every abelian surface with
`𝒪 ↪ End A` is `≅ Jac C` for a curve `C` with a sextic model on the Lin–Yang family at some
`j ≠ 0`, or a product of elliptic curves. A consequence of Lin–Yang Example 29 with Weil's
dichotomy and Lemma QP (rv-qm-polar). The `J`/Igusa–Clebsch convention is tied to hdec-elementary's
`OnQMLocus` (`ZInQ.LeafPush2.linYangTuple_onQMLocus`, proved). The `ℚ̄`-form
`R03_LinYang_algClosed` is a glue target (Lefschetz principle). -/



/-! leaf-adopt (2026-11-12): the placeholder `R16_EichlerShimuraJ1` is replaced by
leaf-modcurves' `LeafModCurves.R16_EichlerShimuraJ1'` (section `LeafModCurvesSec`), stated for
every `K_N` model of `X₁(N)` (`IsJ1`), so bp-modcurves' leaf MC9 is not needed (rv-blueprints M1).
Its 2-dimensional constituent of `V_ℓ(J₁(N))` is derived (`LeafModCurves.g13_constituent`, from
the glue target `VSurjOfSurjective`). New textbook leaves from the same file:
`LeafModCurves.JacobianExists ℚ` (T33) and `LeafModCurves.DimJ1Genus` (T34). -/


/-- **R17. Carayol's local–global compatibility** (docstring repaired by rv-loc-leaves, adopted 2026-11-12 by loc-fix; the concrete statement is
`LadicCond.CarayolR17'` of scratch/def-ladic-cond, unchanged). For a weight-2 newform of level `N`,
any prime `ℓ` (including `ℓ = 2`) and any prime `p ≠ ℓ` (including `p ∣ N`), the Artin conductor
exponent of `ρ_{f,λ}|G_{ℚ_p}` is `v_p(N)`. Ann. Sci. ÉNS 19 (1986), Théorème (A), pp. 409-411,
§0.8 p. 411 (coverage of `p ∣ N` and `ℓ = 2` YES per the audit; the extra discrete-series
hypothesis concerns only totally real `F` of even degree, not `ℚ`), with the newform conductor
`a(π_p) = v_p(N)` (Casselman 1973; UNVERIFIED locator). Duals and unramified twists do not change
the conductor. Do not replace by Théorème (B) or by the `Γ₀` elliptic-curve corollary. -/
opaque R17_Carayol : Prop

/-! leaf-adopt2 (2026-11-12): the placeholder `R18_Javanpeykar` is replaced by leaf-push2's
`ZInQ.LeafPush2.R18_Javanpeykar` (section `LeafPush2Sec`): over a number field `K`, for a pointed
curve `X` with Jacobian `J` (`IsJacobian`), `g = dim J ≥ 1` and a Belyi function `t ∈ K(X)` of
degree `d > 0`, `stableFaltingsHeight J ≤ 13·10⁶ · g · d⁵` (in `EReal`). A consequence of ANT 8
(2014) Thm 1.1.1 with H5. Its height is leaf-push2's copy of def-faltings' height over
`PkgI3.AbVar`. -/

/-! leaf-adopt (2026-11-12): the placeholders `R19_GaudronRemond`, `R20_FaltingsHeightLemma`,
`R21_Bost` are replaced by def-faltings' `ZInQ.DefFaltings.R19_GaudronRemond`,
`R20_FaltingsLemma5`, `R21_Bost` over `stableFaltingsHeight` (section `DefFaltingsSec`), with H5
as an explicit leaf `LeafAdopt.H5` (rv-blueprints F2). **The height may be `⊤`** (formerly
worded "not yet known to be non-vacuous"; rv-leaves48 P1): the
three Props `AnalyticUniformizationExists`, `AnalyticUniformizationUnique`,
`HodgeLatticeTheorem` (node AN3 and the Hodge lattice) are open, and until they are proved the
index set of the infimum may be empty (`h = ⊤`): then R21 holds trivially and R19, R20 have no
instance. So R19-R21 are true for the definition, and a defect of it would surface as a false H5
(`StableHeightFinite`), not as vacuity. R19 is normalization-sensitive (a consequence only if Gaudron–Rémond's `h` is Faltings'
original normalization, rv-blueprints F4). -/


/-! leaf-adopt2 (2026-11-12): the placeholder `R22_Pazuki` is replaced by leaf-push2's
`ZInQ.LeafPush2.R22_Pazuki` (section `LeafPush2Sec`): the audit's upper half
`h([θ_m(0, Ω)]) ≤ X/2 + C₂ log(X + 2)` for `X ≥ max(1, h_F + log π)`, for every abelian surface
over a number field, every analytic uniformization at every complex place and every `Ω ∈ 𝔥₂`
that is a period matrix of its lattice (all principal polarizations, no polarization object).
Consequence of Bull. SMF 140 (2012) Cor. 1.3(2) with H5; the identification of Pazuki's level-2
coordinates (Def. 2.6) with `θ[a;b](0, Ω)` is UNVERIFIED (the main risk). The glue form with
`X = max(1, h_F + 3)` is `ZInQ.LeafPush2.R22_plus3` (proved). -/


/-! leaf-adopt3 (2026-11-13): the placeholder `T10_TateDuality` is removed. T10 is now t10-etale's
concrete Galois-equivariant `T10Etale.T10_TateDuality` over Mathlib's pro-étale `ℓ`-adic cohomology
(section `T10EtaleSec`, below the bundles' reopening point). -/

/-! leaf-adopt2 (2026-11-12): the placeholders `T11_RiemannGAGA` and `T12_ArtinComparison` are
removed. T11 is now the two concrete textbook leaves `ZInQ.LeafPush2.T11a_RiemannEnd`
(endomorphisms of `A/ℂ` = `ℂ`-linear maps preserving the lattice of a uniformization) and
`ZInQ.LeafPush2.T11b_Rigidity` (`Hom(A_L, B_L) = Hom(A, B)` over `k = k̄` of characteristic 0).
T12 is glue: its used form `ZInQ.LeafPush2.T12_ComplexConjEigen` (the `±1`-eigenspaces of complex
conjugation on `V_ℓ(A)` have dimension `dim A`) is a glue target from T35, T5, T26 and the
antiholomorphy of complex conjugation. The new textbook leaf T35 is
`ZInQ.LeafPush2.UniformizationExists` (AN3 for abelian varieties: Mumford §1 with GAGA); it is
kept instead of bp-analytic's `UniformizationLeaf` (docs/research/leaf-adopt2.md §2): its
predicate is the one R22 and T11a quantify over, it ties `g` to `dim A`, and it covers every
`K` with `σ : K → ℂ`. -/




/-! hsyn-fold: R8, T9, T23, T29 and T32 are no longer placeholders. Their concrete statements
(task leaf-push) are `PkgI2.GrothendieckMonodromy` (= `LeafPush.R08_GrothendieckMonodromy`,
consequence form), `LeafPush.T09_WeilPairing` (consequence, polarization hidden),
`PkgI4.T23_FontaineClosure` (consequence: matrix form of the published statement, `ℚ_p`
coefficients; rv-leaves48 P4),
`LeafPush.T29a_DivisionNormalizer` and `LeafPush.T29b_SplitNormalizer` (exact),
`LeafPush.T32a_TameQuadratic` and `LeafPush.T32b_QuadraticRamification` (consequences).
leaf-adopt (2026-11-12): T32 is now glue, proved (`HSyn.t32a_glue`, `HSyn.t32b_glue`, §3).
leaf-adopt2 (2026-11-12): T12 is now glue (target `ZInQ.LeafPush2.T12_ComplexConjEigen`,
unproved). -/

/-! ## §3. Glue -/

/-- **T32(a) is glue** (leaf-adopt, 2026-11-12): proved in scratch/glue-t32a (`GlueB3Unram.t32a`,
copied in section `GlueT32aSec`), with no leaf. -/
theorem t32a_glue : LeafPush.T32a_TameQuadratic := GlueB3Unram.t32a

/-- **T32(b) is glue** (leaf-adopt, 2026-11-12): proved in scratch/glue-b3b (`GlueB3Unram.t32b`,
copied with scratch/glue-t32a in section `GlueT32aSec`), with no leaf. -/
theorem t32b_glue : LeafPush.T32b_QuadraticRamification := GlueB3Unram.t32b

/-- **The two complex-conjugation predicates agree** (leaf-adopt2): leaf-push2's
`ZInQ.LeafPush2.IsComplexConj` (used by `T12_ComplexConjEigen`) is pkg-I4's
`PkgI4.IsComplexConj` (used by the oddness of `GaloisRep`s, G10), by definition. -/
theorem isComplexConj_leafPush2_iff (c : Field.absoluteGaloisGroup ℚ) :
    ZInQ.LeafPush2.IsComplexConj c ↔ PkgI4.IsComplexConj c :=
  Iff.rfl

/-- **Glue target (leaf-adopt2, unproved): the two copies of the stable Faltings height agree.**
R18 and R22 (leaf-push2) are stated over `ZInQ.LeafPush2.stableFaltingsHeight` on `PkgI3.AbVar`;
R19-R21 and H5 (def-faltings) over `ZInQ.DefFaltings.stableFaltingsHeight` on def-faltings' copy
of the structure. The two definitions are textual copies (leaf-push2 Part I = def-faltings §§1-18
with `AbVar` replaced), so this is pure transport along `LeafAdopt.abVarEquiv` (every structure of
the Arakelov layer is duplicated, so the proof needs an equivalence of `GroupModel`, `HodgeData`
and `MetrizedModel` and equality of model heights). It is what lets the glue apply H5 to R18 and
R22. Not a leaf. -/
def HeightCopiesAgree : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K),
    ZInQ.LeafPush2.stableFaltingsHeight A =
      ZInQ.DefFaltings.stableFaltingsHeight ((LeafAdopt.abVarEquiv K).symm A)

/-- **B3(v) with no leaf** (glue-t32a): `LeafB3a` of glue-b3-unram is proved. -/
theorem leafB3a_glue : GlueB3Unram.LeafB3a := GlueB3Unram.leafB3a

/-- **G12, weight arithmetic** (N5 L763-764, Tate normalization; from the hdec-faithful draft). -/
theorem weight_match (n k : ℤ) (hk : 1 ≤ k)
    (h : (n = 0 ∧ n + 1 - k = -1) ∨ (n = -1 ∧ n + 1 - k = 0)) : n = 0 ∧ k = 2 := by
  omega

/-- **G15 (D3), pkg-I6's `sq_principalUnits` proved** from glue-conductor's
`exists_sq_eq_one_add` (same statement as `PkgI6.sq_principalUnits`, which is `sorry` there). -/
theorem sq_principalUnits_proved (B : Type) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B] (e : ℕ) (_he1 : 1 ≤ e)
    (he : Ideal.span {(2 : B)} = IsLocalRing.maximalIdeal B ^ e) (r : ℕ) (hr : e < r)
    (y : B) (hy : y ∈ IsLocalRing.maximalIdeal B ^ (r + e)) :
    ∃ x ∈ IsLocalRing.maximalIdeal B ^ r, (1 + x) ^ 2 = 1 + y := by
  obtain ⟨w, hw, h⟩ := GlueConductor.exists_sq_eq_one_add e (r - e) (by omega) he y
    (by rwa [show 2 * e + (r - e) = r + e by omega])
  exact ⟨w, by rwa [show e + (r - e) = r by omega] at hw, h⟩

/-- **D3 (GLUE, proved)**: pkg-I6's `sq_principalUnits`, from glue-conductor's Hensel argument. -/
theorem _root_.HDec.PkgI6.sq_principalUnits (B : Type) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B] (e : ℕ) (he1 : 1 ≤ e)
    (he : Ideal.span {(2 : B)} = IsLocalRing.maximalIdeal B ^ e) (r : ℕ) (hr : e < r)
    (y : B) (hy : y ∈ IsLocalRing.maximalIdeal B ^ (r + e)) :
    ∃ x ∈ IsLocalRing.maximalIdeal B ^ r, (1 + x) ^ 2 = 1 + y :=
  sq_principalUnits_proved B e he1 he r hr y hy


end HSyn

end


section TDifferentSec

/-! ### Copied from `scratch/t-different/All.lean` (task t-different, wave 25; compiled there
against Mathlib only).  Proves the local leaves T20 (`PkgI6.HilbertDifferentFormula`, I6.7),
T21 (`PkgI6.DifferentBound`, I6.6), T22a (`PkgI6.HerbrandQuotient`, I6.8), T22b
(`PkgI6.HerbrandTransitivity`, I6.9) over the Leaves.lean definitions above (section PkgI6Sec).
Deleted as duplicates of Leaves.lean (character-identical): `PkgI6.lowerRam`, `PkgI6.mem_lowerRam`,
`PkgI6.lowerRamR`, `PkgI6.herbrandPhi`, `PkgI6.upperRam`, `PkgI6.lowerRam_tower` and the four leaf
`def`s.  Docs: `docs/research/t-different.md`. -/

open IsLocalRing Polynomial MeasureTheory Set

namespace TDifferent

section Abstract

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

end Abstract

section Trans

variable {G H Q : Type*} [Group G] [Fintype G] [DecidableEq G] [Group H] [Fintype H]
  [DecidableEq H] [Group Q] [Fintype Q] [DecidableEq Q]

end Trans

section Upper

variable {G H Q : Type*} [Group G] [Fintype G] [DecidableEq G] [Group H] [Fintype H]
  [DecidableEq H] [Group Q] [Fintype Q] [DecidableEq Q]

end Upper



attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-! ### If `B = A[x]`, then `σ ∈ G_I ↔ σ x - x ∈ I`. -/

/-! ### Valuations in a DVR. -/

section DVR

variable {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]

end DVR

section Monogenic

variable (A B : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [PerfectField (ResidueField A)]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B]
  [Module.IsTorsionFree A B]

end Monogenic



section GaloisSetup

variable (A B : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra A B] [Module.Finite A B]
  [Module.IsTorsionFree A B] [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
  [IsGalois (FractionRing A) (FractionRing B)]

end GaloisSetup

section Tower

variable (A C B : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [CommRing C] [IsDomain C] [IsIntegrallyClosed C] [Algebra A C] [Module.Finite A C]
  [Module.IsTorsionFree A C] [IsGalois (FractionRing A) (FractionRing C)]
  [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra A B] [Module.Finite A B]
  [Module.IsTorsionFree A B] [IsGalois (FractionRing A) (FractionRing B)]
  [Algebra C B] [IsScalarTower A C B] [Module.IsTorsionFree C B]

end Tower

section Product

end Product

section Prop3

variable (A C B : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] [Algebra A C] [Module.Finite A C]
  [Module.IsTorsionFree A C] [IsGalois (FractionRing A) (FractionRing C)]
  [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra A B] [Module.Finite A B]
  [Module.IsTorsionFree A B] [IsGalois (FractionRing A) (FractionRing B)]
  [Algebra C B] [IsScalarTower A C B] [Module.IsTorsionFree C B]

end Prop3



section Card

variable (C B : Type) [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra C B] [Module.Finite C B]
  [Module.IsTorsionFree C B]

end Card

section Assembly

variable (A C B : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [PerfectField (ResidueField A)]
  [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] [Algebra A C] [Module.Finite A C]
  [Module.IsTorsionFree A C] [IsGalois (FractionRing A) (FractionRing C)]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B]
  [Module.IsTorsionFree A B] [IsGalois (FractionRing A) (FractionRing B)]
  [Algebra C B] [IsScalarTower A C B] [Module.Finite C B] [Module.IsTorsionFree C B]

end Assembly

open PkgI6

/-! ### Counting: `∑_{i<N} (|G_i| - 1) = ∑_{σ ≠ 1} i_G(σ)`. -/

section Counting

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

end Counting

/-! ### The derivative of the minimal polynomial of a generator, Galois case. -/

section Product

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable (A B : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra A B] [Module.Finite A B]
  [Module.IsTorsionFree A B] [Algebra.IsSeparable (FractionRing A) (FractionRing B)]

variable [IsGalois (FractionRing A) (FractionRing B)]

end Product

/-! ### Hilbert's formula when `B = A[x]`. -/

section Main

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

end Main

section Hensel

variable (A B : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [IsAdicComplete (maximalIdeal A) A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B]
  [Module.IsTorsionFree A B]

end Hensel

section Trace

variable (A B : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [IsAdicComplete (maximalIdeal A) A] [PerfectField (ResidueField A)]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B]
  [Module.IsTorsionFree A B] [Algebra.IsSeparable (FractionRing A) (FractionRing B)]

end Trace

end TDifferent

namespace PkgI6

open IsLocalRing

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

end PkgI6

end TDifferentSec

section TSkolemKWSec

/-! ### Copied from `scratch/t-skolem-kw/` (task t-skolem-kw, wave 25; compiled there against
Mathlib only, also concatenated as `AllCheck.lean`): `SkolemNoether.lean`, `BrauerNesbitt.lean`,
`FrobeniusDense.lean` (its part `TSkolemKW.C10`, a verbatim copy of glue-c10's `GlueC10` above, is
deleted and `GlueC10`'s originals are used instead), `KroneckerWeberUse.lean`, and the theorem
`c10_of_chebotarev` of `C10Closed.lean` (restated over `GlueC10`).  `ChebotarevCyclotomic.lean` (a
sanity check of `ChebotarevExists` for cyclotomic fields) is omitted.  The local copies
`TSkolemKW.SkolemNoether`, `TSkolemKW.HSynSkolemNoether`, `TSkolemKW.LeafSkolemNoether`,
`TSkolemKW.BrauerNesbittChar0`, `TSkolemKW.HSynBrauerNesbitt`, `TSkolemKW.HS.FrobeniusDense` (with
`HS.Qbar`, `HS.GQ`, `HS.LiesOver`, `HS.IsArithFrob`), `TSkolemKW.KW.KroneckerWeber` (with `KW.Qbar`,
`KW.GQ`) are character-identical to the Leaves.lean definitions; the bridges at the end restate the
results over the Leaves.lean names.  Docs: `docs/research/t-skolem-kw.md`. -/

-- ===== SkolemNoether.lean =====
/-!
# t-skolem-kw: leaf T13 (Skolem–Noether), proved

The statement `SkolemNoether` is copied verbatim from `scratch/h-decomposition/Leaves.lean`
(`PkgI6.SkolemNoether`; `HSyn.SkolemNoether` is the same Prop up to the name of a bound
variable).  The automorphism form `LeafSkolemNoether` (`Leaves.lean`, glue-descent section) is
derived at the end.

Proof (the standard one, e.g. Farb–Dennis, *Noncommutative algebra*, Thm 3.14 (UNVERIFIED
locator)):
1. `isSimpleRing_tensor`: `C ⊗[K] B` is simple when `C` is central simple and `B` is simple
   (minimal-length argument in a basis of `B`).
2. `nonempty_linearEquiv_of_finrank_eq`: over a simple Artinian `K`-algebra `R`, two modules of
   the same finite `K`-dimension are isomorphic (both are powers of the unique simple module).
3. `A` is a module over `R = Aᵐᵒᵖ ⊗[K] B` in two ways, `(a ⊗ b) • x = f b * x * a` and
   `(a ⊗ b) • x = g b * x * a`; an `R`-isomorphism between them is left multiplication by a unit
   `u` with `u * f b = g b * u`.
-/

open TensorProduct

namespace TSkolemKW

/-! ## The statements (verbatim from `scratch/h-decomposition/Leaves.lean`) -/

/-- **Leaf I6.1 (Skolem–Noether).** Verbatim `PkgI6.SkolemNoether`. -/
def SkolemNoether : Prop :=
  ∀ (K A B : Type) [Field K] [Ring A] [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A]
    [FiniteDimensional K A] [Ring B] [Algebra K B] [IsSimpleRing B] [FiniteDimensional K B]
    (f g : B →ₐ[K] A), ∃ u : Aˣ, ∀ b : B, g b = (u : A) * f b * ((u⁻¹ : Aˣ) : A)

/-- **Leaf L-B1 (Skolem–Noether, automorphism case).** Verbatim `LeafSkolemNoether`. -/
def LeafSkolemNoether : Prop :=
  ∀ (K : Type) [Field K] (A : Type) [Ring A] [Algebra K A] [Algebra.IsCentral K A]
    [IsSimpleRing A] [FiniteDimensional K A] (φ : A ≃ₐ[K] A),
    ∃ u : Aˣ, ∀ a : A, φ a = u * a * (u⁻¹ : Aˣ)

/-! ## Step 1. `C ⊗ B` is simple for `C` central simple and `B` simple -/

section TensorSimple

variable {K C B : Type*} [Field K] [Ring C] [Algebra K C] [Algebra.IsCentral K C]
  [IsSimpleRing C] [Ring B] [Algebra K B] [IsSimpleRing B]

end TensorSimple

/-! ## Step 2. Modules over a simple Artinian algebra are classified by their dimension -/

/-! ## Step 3. `A` as a module through an algebra map to `End_K A` -/

namespace Twist

variable {K R A : Type*} [CommRing K] [Ring R] [Algebra K R] [AddCommGroup A] [Module K A]
  (ρ : R →ₐ[K] Module.End K A)

instance : AddCommGroup (Twist ρ) := inferInstanceAs (AddCommGroup A)
instance : Module K (Twist ρ) := inferInstanceAs (Module K A)
instance : Module R (Twist ρ) := Module.compHom A (ρ : R →+* Module.End K A)

end Twist

/-! ## The theorem -/

end TSkolemKW

-- ===== BrauerNesbitt.lean =====
/-!
# t-skolem-kw: leaf T19 (Brauer–Nesbitt in characteristic 0)

The statement `BrauerNesbittChar0` is copied verbatim from `scratch/h-decomposition/Leaves.lean`
(`PkgI6.BrauerNesbittChar0`, also `GlueC10.BrauerNesbittChar0`).

Proof (standard; cf. Curtis–Reiner (27.13), Lang, *Algebra* XVII Cor. 3.8, both UNVERIFIED
locators), for modules over an arbitrary `k`-algebra `R`:
1. `isNilpotent_of_trace_pow_eq_zero`: in characteristic 0 an endomorphism all of whose powers
   have trace 0 is nilpotent (Cayley–Hamilton gives `det = 0`; induct on the range).
2. `exists_injective_of_trace_eq`: if `M`, `N` have equal traces, `N` is semisimple and `S ⊆ M`
   is simple, then `S` embeds in `N`: the annihilator `J` of `N` acts nilpotently on `M` (1),
   hence kills `S` (if `t • s = s` for some `t ∈ J` then `s = 0`); so `S` is a quotient of
   `R / ann N ⊆ N^d`, hence (semisimplicity) a submodule of `N^d`, hence of `N`.
3. Induction on `dim M`: split off `S` from both sides.
-/

open Module

namespace TSkolemKW

/-! ## The statement (verbatim from `scratch/h-decomposition/Leaves.lean`) -/

/-- **Leaf I6.5 (Brauer–Nesbitt, characteristic 0, trace form).** Verbatim
`PkgI6.BrauerNesbittChar0`. -/
def BrauerNesbittChar0 : Prop :=
  ∀ (k G V W : Type) [Field k] [CharZero k] [Group G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρ : Representation k G V) (σ : Representation k G W),
    IsSemisimpleModule (MonoidAlgebra k G) ρ.asModule →
    IsSemisimpleModule (MonoidAlgebra k G) σ.asModule →
    (∀ g : G, LinearMap.trace k V (ρ g) = LinearMap.trace k W (σ g)) →
    Nonempty (ρ.asModule ≃ₗ[MonoidAlgebra k G] σ.asModule)

/-! ## Step 1. Traces of powers vanish ⇒ nilpotent (characteristic 0) -/

/-! ## The action of `R` on a module, as `k`-linear maps -/

section Act

variable {k R : Type*} [Field k] [Ring R] [Algebra k R]

variable {M P A B : Type*} [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M]
  [AddCommGroup P] [Module k P] [Module R P] [IsScalarTower k R P]
  [AddCommGroup A] [Module k A] [Module R A] [IsScalarTower k R A]
  [AddCommGroup B] [Module k B] [Module R B] [IsScalarTower k R B]

end Act

/-! ## Step 2. A simple constituent of `M` embeds in `N` -/

section Main

variable {k R : Type*} [Field k] [CharZero k] [Ring R] [Algebra k R]

/-! ## Step 3. Brauer–Nesbitt for modules over a `k`-algebra -/

end Main

/-! ## The leaf -/

theorem brauerNesbittChar0 : BrauerNesbittChar0 :=
  _root_.TSkolemKW.brauerNesbittChar0


/-! ## The matrix form `HSyn.BrauerNesbitt` -/

section Matrix

variable {G E : Type} [Group G] [Field E] {n : ℕ}

end Matrix

end TSkolemKW

-- ===== FrobeniusDense.lean (part `TSkolemKW.C10` deleted: it is `GlueC10` of Leaves.lean) =====
/-!
# t-skolem-kw: leaf T18 (Frobenius density) reduced to its finite form

`HSyn.FrobeniusDense` (verbatim below as `HS.FrobeniusDense`, over `HSyn`'s `Qbar`, `GQ`,
`LiesOver`, `IsArithFrob`, also verbatim) is proved from `PkgI6.ChebotarevExists`
(= `GlueC10.ChebotarevExists`, verbatim).  So T18 rests on the finite (existence) form of
Chebotarev's theorem alone.

Part C10 is copied verbatim from `scratch/h-decomposition/Leaves.lean`, section `GlueC10Sec`
(lines 11328-11333, 11375-11630, 11747-11750 at base 01267822): the lift of a finite-level
Frobenius to `G_ℚ` at a prime of `\bar ℤ`.  New here (`HS` section): the localization of `\bar ℤ`
at a prime `𝔓` is a valuation subring of `\bar ℚ` (`zbarLoc`, via the DVR `(𝓞_E)_{𝔓 ∩ 𝓞_E}` of
each finite layer), an arithmetic Frobenius at `𝔓` is an `IsArithFrob` at this place, and the
Krull-topology step.
-/

open NumberField

/-! ## `HSyn.FrobeniusDense` from the finite form -/

namespace TSkolemKW.HS

open scoped Pointwise
-- op-dedupe was: open GlueC10 (ChebotarevExists FrobDense IsFrobAt Zbar toZbar toZbar_coe frobDense)
open _root_.GlueC10 (ChebotarevExists FrobDense IsFrobAt Zbar toZbar toZbar_coe frobDense) -- op-dedupe

/-! ### Definitions (verbatim from `HSyn` §0-§1 of `scratch/h-decomposition/Leaves.lean`) -/

/-- `ℚ̄`. -/
abbrev Qbar := AlgebraicClosure ℚ

/-- `G_ℚ = Gal(ℚ̄/ℚ)`, with Mathlib's Krull topology. -/
abbrev GQ := Qbar ≃ₐ[ℚ] Qbar

/-- `v` is a place of `ℚ̄` above the prime `p`: a valuation subring of `ℚ̄` in which `p` is not a
unit. -/
def LiesOver (v : ValuationSubring Qbar) (p : ℕ) : Prop := (p : Qbar) ∈ v.nonunits

/-- `σ` is an arithmetic Frobenius at the place `v` above `p`. -/
def IsArithFrob (σ : GQ) (v : ValuationSubring Qbar) (p : ℕ) : Prop :=
  σ ∈ v.decompositionSubgroup ℚ ∧ ∀ x ∈ v, σ x - x ^ p ∈ v.nonunits

/-! ### The localization of `\bar ℤ` at a prime is a valuation subring of `\bar ℚ` -/

variable (P : Ideal Zbar) [hP : P.IsPrime]

/-! ### An arithmetic Frobenius at `𝔓` is an `IsArithFrob` at `\bar ℤ_𝔓` -/

/-! ### The reduction -/

end TSkolemKW.HS

-- ===== KroneckerWeberUse.lean =====
/-!
# t-skolem-kw: leaf T17 (Kronecker–Weber) in the form the proof uses

T17 itself (`HSyn.KroneckerWeber`, verbatim below) is NOT proved here (see
`docs/research/t-skolem-kw.md`).  This file proves the glue that turns it into the form step C8
of h-trust uses ("the fixed field of `ker ψ` is finite abelian over `ℚ`, hence cyclotomic, so `ψ`
is a Dirichlet character"; glue-assembly §2.1 listed it as "not written"):

* `ker_ge_of_kroneckerWeber`: for a homomorphism `ψ : G_ℚ → G` to a commutative group with open
  kernel, there is `m ≥ 1` such that `ψ` kills every `σ` fixing all `m`-th roots of unity;
* `eq_of_agree_on_roots`: `ψ σ` depends only on the action of `σ` on the `m`-th roots of unity,
  i.e. `ψ` factors through `Gal(ℚ(μ_m)/ℚ) ≅ (ℤ/m)ˣ`;
* `isOpen_ker_of_continuous`: a continuous homomorphism with finite image to a `T1` group has
  open kernel (the hypothesis as it arises in C8, `ψ` with values in `\bar ℚ₅^×`);
* `KroneckerWeberCyclic` (T17 for cyclic `L/ℚ`, a consequence of T17:
  `kroneckerWeberCyclic_of_kroneckerWeber`) already suffices when `ψ` takes values in a field:
  `ker_ge_of_kroneckerWeberCyclic`, `eq_of_agree_on_roots_cyclic` (`Gal(L/ℚ) ≅ im ψ ⊆ Eˣ` is
  cyclic).
-/

namespace TSkolemKW.KW

/-- `ℚ̄` (as in `HSyn`). -/
abbrev Qbar := AlgebraicClosure ℚ

/-- `G_ℚ = Gal(ℚ̄/ℚ)`, with Mathlib's Krull topology (as in `HSyn`). -/
abbrev GQ := Qbar ≃ₐ[ℚ] Qbar

/-! ## The case C8 uses: cyclic extensions -/

/-! ## The Dirichlet character, through Mathlib's mod-`m` cyclotomic character -/

end TSkolemKW.KW

-- ===== C10Closed.lean (the final theorem only, over Leaves.lean's `GlueC10`) =====

namespace TSkolemKW.C10

/-- `GlueC10.BrauerNesbittChar0` is the same Prop as `TSkolemKW.BrauerNesbittChar0`. -/
theorem brauerNesbittChar0' : GlueC10.BrauerNesbittChar0 := TSkolemKW.brauerNesbittChar0

/-- **C10 from Chebotarev alone (GLUE, proved).** `GlueC10.c10` with the Brauer–Nesbitt
hypothesis discharged by `TSkolemKW.brauerNesbittChar0`. -/
theorem c10_of_chebotarev (hC : GlueC10.ChebotarevExists) (S : Finset ℕ)
    (C : Type) [Field C] (c a : ℕ → C)
    (k₅ V₅ W₅ : Type) [Field k₅] [AddCommGroup V₅] [Module k₅ V₅]
    [AddCommGroup W₅] [Module k₅ W₅] (ι₅ : C →+* k₅)
    (r₅ : Representation k₅ GlueC10.GQ V₅) (ρ₅ : Representation k₅ GlueC10.GQ W₅)
    (h₅ : ∀ g p, p.Prime → p ∉ S → GlueC10.IsFrobAt g p →
      LinearMap.trace k₅ V₅ (r₅ g) = LinearMap.trace k₅ W₅ (ρ₅ g))
    (hr₅ : ∀ g p, p.Prime → p ∉ S → GlueC10.IsFrobAt g p →
      LinearMap.trace k₅ V₅ (r₅ g) = ι₅ (c p))
    (hρ₅ : ∀ g p, p.Prime → p ∉ S → GlueC10.IsFrobAt g p →
      LinearMap.trace k₅ W₅ (ρ₅ g) = ι₅ (a p))
    (k V W ι κ : Type) [Field k] [CharZero k] [TopologicalSpace k] [IsTopologicalRing k]
    [T2Space k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ι₃ : C →+* k)
    (bV : Module.Basis ι k V) (bW : Module.Basis κ k W)
    (r₃ : Representation k GlueC10.GQ V) (ρ₃ : Representation k GlueC10.GQ W)
    (hrc : Continuous fun g => LinearMap.toMatrix bV bV (r₃ g))
    (hρc : Continuous fun g => LinearMap.toMatrix bW bW (ρ₃ g))
    (hr : IsSemisimpleModule (MonoidAlgebra k GlueC10.GQ) r₃.asModule)
    (hρ : IsSemisimpleModule (MonoidAlgebra k GlueC10.GQ) ρ₃.asModule)
    (hr₃ : ∀ g p, p.Prime → p ∉ S → GlueC10.IsFrobAt g p →
      LinearMap.trace k V (r₃ g) = ι₃ (c p))
    (hρ₃ : ∀ g p, p.Prime → p ∉ S → GlueC10.IsFrobAt g p →
      LinearMap.trace k W (ρ₃ g) = ι₃ (a p)) :
    Nonempty (r₃.asModule ≃ₗ[MonoidAlgebra k GlueC10.GQ] ρ₃.asModule) :=
  GlueC10.c10 hC brauerNesbittChar0' S C c a k₅ V₅ W₅ ι₅ r₅ ρ₅ h₅ hr₅ hρ₅ k V W ι κ ι₃ bV bW
    r₃ ρ₃ hrc hρc hr hρ hr₃ hρ₃

end TSkolemKW.C10

/-! ## Bridges to the Leaves.lean statements (types exactly the Leaves.lean Props) -/

namespace TSkolemKW

/-- **T13 proved** (`PkgI6.SkolemNoether`, leaf I6.1). -/
theorem pkgI6_skolemNoether : PkgI6.SkolemNoether := skolemNoether

/-- **T13 proved** (`HSyn.SkolemNoether`, bundle field `t13`). -/
theorem hsyn_t13 : HSyn.SkolemNoether := hsynSkolemNoether

/-- **T13 proved** (`GlueDescent.LeafSkolemNoether`, the automorphism case used by B1). -/
theorem glueDescent_leafSkolemNoether : GlueDescent.LeafSkolemNoether := leafSkolemNoether

/-- **T19 proved** (`PkgI6.BrauerNesbittChar0`, leaf I6.5). -/
theorem pkgI6_brauerNesbittChar0 : PkgI6.BrauerNesbittChar0 := brauerNesbittChar0

/-- **T19 proved** (`HSyn.BrauerNesbitt`, bundle field `t19`). -/
theorem hsyn_t19 : HSyn.BrauerNesbitt := hsynBrauerNesbitt

/-- **T18 reduced to `PkgI6.ChebotarevExists`** (bundle field `t18 : HSyn.FrobeniusDense`). -/
theorem hsyn_t18_of_chebotarev (h : PkgI6.ChebotarevExists) : HSyn.FrobeniusDense :=
  HS.frobeniusDense_of_chebotarev h

/-- **T17: the narrowed leaf follows from the bundle's `HSyn.KroneckerWeber`.** -/
theorem kroneckerWeberCyclic_of_hsyn (h : HSyn.KroneckerWeber) : KW.KroneckerWeberCyclic :=
  KW.kroneckerWeberCyclic_of_kroneckerWeber h

/-- **C8's use form of T17 (GLUE, proved from the narrowed leaf), over `HSyn.GQ`.** A character
`ψ : G_ℚ →* Eˣ` (`E` a field) with open kernel is `χ ∘ cyc_m` for a Dirichlet character `χ`. -/
theorem hsyn_dirichletCharacter_of_kroneckerWeberCyclic (hKW : KW.KroneckerWeberCyclic)
    {E : Type*} [Field E] (ψ : HSyn.GQ →* Eˣ) (hψ : IsOpen (ψ.ker : Set HSyn.GQ)) :
    ∃ (m : ℕ+) (χ : DirichletCharacter E (m : ℕ)),
      ∀ σ : HSyn.GQ, (ψ σ : E) = χ ((KW.cycChar m σ : (ZMod m)ˣ) : ZMod m) :=
  KW.dirichletCharacter_of_kroneckerWeberCyclic hKW ψ hψ

end TSkolemKW

end TSkolemKWSec

/-! # Fold of t30-adelic, part T30 (leaf-adopt3)
Source: scratch/t30-adelic/SqrtCrit.lean. It imports `ZInQKernel.HDecomp.Sqrt.Disj` (which imports
`Sqrt.SqrtLocal`, `Conductor.SqrtChar`, `Conductor.I6Base`) and `ZInQKernel.HDecomp.Descent.B2Glue`.
`GlueDescent.B2Q` (B2Glue) and `PkgI6.LocalKroneckerWeber` (I6Base) are already in this file
(textually identical). The namespaces `GlueI6Rest`, `GlueSqrtLocal`, `GlueSqrtDisj` are NOT, so the
three kernel files `Conductor/SqrtChar.lean`, `Sqrt/SqrtLocal.lean`, `Sqrt/Disj.lean` are copied
below verbatim (imports dropped), each in its own section (their top-level `open`s are file-scoped
there). The G1-adelic part (Adelic.lean, G1Count.lean) is NOT folded. -/

section T30Sec

section T30KernelSqrtCharSec
/-! ### Copied from `ZInQKernel/HDecomp/Conductor/SqrtChar.lean` (kernel; namespace `GlueI6Rest`). -/

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt from
`scratch/glue-I6-rest/SqrtChar.lean`.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/


/-!
# glue-I6-rest: the group-theoretic core of B2's square-root criterion

pkg-I6 (§2, B2, glue item 2): "a character of a profinite abelian group `Γ` is a square iff it
kills `Γ[2]`".  For characters with values in `ℚ/ℤ` (written additively; finite-order characters
of a profinite group take values in `μ_∞ ≅ ℚ/ℤ`) and any abelian group `Γ`, this is proved here
from the divisibility (Baer injectivity) of `ℚ/ℤ`, Mathlib's
`CharacterModule.dual_surjective_of_injective`.  Applied to a finite quotient `Γ` of `G_{ℚ_p}^{ab}`
through which `χ` factors, it gives a square root on `Γ`, hence a continuous one on `G_{ℚ_p}`.
-/

namespace GlueI6Rest

end GlueI6Rest

end T30KernelSqrtCharSec

section T30KernelSqrtLocalSec
/-! ### Copied from `ZInQKernel/HDecomp/Sqrt/SqrtLocal.lean` (kernel; namespace `GlueSqrtLocal`). -/

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt2 from
`scratch/glue-sqrt-local/SqrtLocal.lean`.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/


/-!
# glue-sqrt-local: the local square-root criterion, `p`-power cyclotomic part

* `cyclotomic_prime_pow_irreducible_padic`: `Φ_{p^{n+1}}` is irreducible over `ℚ_p` (Eisenstein).
* `galEquivUnits`, `finrank_eq_totient`: `Gal(L/ℚ_p) ≅ (ℤ/p^{n+1})ˣ`, `[L:ℚ_p] = φ(p^{n+1})` for any
  `p^{n+1}`-th cyclotomic extension `L` of `ℚ_p`.
* `gal_sqrt_criterion` (`p` odd): a `ℚ/ℤ`-character of `Gal(L/ℚ_p)` is twice a character iff it
  kills `τ₋₁` (`τ₋₁ ζ = ζ⁻¹`, `tauNeg_mul_self`).
* `sqrt_criterion_finite` (every `p`): the same criterion on the finite model
  `(ℤ/p^{k+1})ˣ × ℤ/2f → (ℤ/p^k)ˣ × ℤ/f` of `Gal(ℚ_p(μ_{p^{k+1}m'})/ℚ_p) → Gal(ℚ_p(μ_{p^k m})/ℚ_p)`.
-/

open Polynomial

namespace GlueSqrtLocal

variable (p : ℕ) [hp : Fact p.Prime]

/-! Proved by `GlueI6Rest.exists_half_iff` (`Conductor/SqrtChar.lean`). -/
/-! ## The Galois group of a `p^{n+1}`-th cyclotomic extension of `ℚ_p` -/

section Gal

variable (p : ℕ) [hp : Fact p.Prime] (n : ℕ) (L : Type) [Field L] [Algebra ℚ_[p] L]
  [IsCyclotomicExtension {p ^ (n + 1)} ℚ_[p] L]

end Gal

end GlueSqrtLocal

end T30KernelSqrtLocalSec

section T30KernelDisjSec
/-! ### Copied from `ZInQKernel/HDecomp/Sqrt/Disj.lean` (kernel; namespaces `GlueSqrtLocal`,
`GlueSqrtDisj`). -/

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt2 from
`scratch/glue-sqrt-disj/Disj.lean`.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/


open Polynomial IsLocalRing
open scoped Pointwise

namespace GlueSqrtLocal

variable (p : ℕ) [hp : Fact p.Prime] (L : Type) [Field L] [Algebra ℚ_[p] L]
  [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L] [FiniteDimensional ℚ_[p] L] [IsGalois ℚ_[p] L]

/-! ### Locality of the integral closure (spectral norm) -/

local notation "N" => spectralNorm ℚ_[p] L

end GlueSqrtLocal

/-! `GlueSqrtLocal.exists_half_iff`, `redU`, `redU_sq_eq_one` and their helpers
(copied in the draft) are imported from `ZInQKernel.HDecomp.Sqrt.SqrtLocal`. -/

namespace GlueSqrtDisj

variable (p : ℕ) [hp : Fact p.Prime] (L : Type) [Field L] [Algebra ℚ_[p] L]
  [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L] [FiniteDimensional ℚ_[p] L] [IsGalois ℚ_[p] L]

/-! ### Disjointness: `Gal(ℚ_p(μ_{p^k m})/ℚ_p) ≅ (ℤ/p^k)ˣ × ⟨p⟩` -/

section Disj

open GlueSqrtLocal

variable {p L} (k m : ℕ) [NeZero m] (hcop : p.Coprime m) [IsCyclotomicExtension {p ^ k * m} ℚ_[p] L]

end Disj


/-! ### The local square-root criterion at a finite level, with the level change -/

section Crit

open GlueSqrtLocal

variable {p L}

/-! ### Level change `m ↦ p^{2f} - 1` (copied from `Level.lean`) -/

end Crit

end GlueSqrtDisj

/-! `PkgI6.LocalKroneckerWeber` is imported from `Conductor/I6Base.lean`. -/

namespace GlueSqrtDisj

variable (p : ℕ) [hp : Fact p.Prime]

end GlueSqrtDisj


/-! ### The criterion on the subfields `ℚ_p(μ_n)` of `\bar ℚ_p` -/

namespace GlueSqrtDisj

section MuField

variable (p : ℕ) [hp : Fact p.Prime]

end MuField

end GlueSqrtDisj

end T30KernelDisjSec

section T30SqrtCritSec
/-! ### t30-adelic: `scratch/t30-adelic/SqrtCrit.lean` (verbatim, imports and `#print` dropped).
Bridge: `T30.leafSqrtCrit_of_t16a : (∀ (p : ℕ) [Fact p.Prime], PkgI6.LocalKroneckerWeber p) →
GlueDescent.B2Q.LeafSqrtCrit` (HSyn's `t16a` ⇒ HSyn's `t30`). -/

/-!
# t30-adelic, part T30: the local square-root criterion from local Kronecker–Weber

`GlueDescent.B2Q.LeafSqrtCrit` (leaf L-B2c) is proved from `PkgI6.LocalKroneckerWeber p` at
every prime `p` (leaf T16).  The finite-level criterion is `GlueSqrtDisj` (imported); this file
does the descent through `Gal(ℚ_p(μ_n)/ℚ_p)` and the inflation to `G_{ℚ_p}`.
-/

open GlueDescent.B2Q GlueSqrtDisj

namespace T30

local instance (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

/-! ### Elementary lemmas on roots of unity -/

section Roots

variable {F : Type*} [Field F]

end Roots

/-! ### The decomposition map and the cyclotomic character -/

section Resp

variable (p : Nat.Primes)

end Resp

/-! ### The action of `σ` on the roots of unity of a cyclotomic level -/

section Level

variable (p : Nat.Primes)

end Level

/-! ### Square roots of `ℂˣ`-valued characters -/

section SqrtC

end SqrtC

/-! ### Two-torsion at the bigger level (from the proof of `sqrt_criterion_level`) -/

section Torsion

open GlueSqrtLocal

end Torsion

/-! ### The criterion over `G_{ℚ_p}` -/

section Main

variable (p : Nat.Primes)

end Main

/-! ### The leaf -/

end T30

end T30SqrtCritSec

end T30Sec

/-! # Fold of t10-etale (leaf-adopt3)
Source: scratch/t10-etale/T10Etale.lean (imports `ZInQKernel.HDecomp.Objects`, whose `PkgI3`
section is textually identical to Leaves.lean lines 2425-2771). Replaces the placeholder
`opaque HSyn.T10_TateDuality` by `T10Etale.T10_TateDuality` (field `t10` of `TextbookLeaves`). -/

section T10EtaleSec

/-! # t10-etale: T10 over Mathlib's `ℓ`-adic cohomology

Mathlib v4.35 defines `Scheme.EllAdicCohomology X ℓ n` (pro-étale cohomology with coefficients in
the sheaf `U ↦ C(U, ℤ_ℓ)`, Bhatt–Scholze 2015 Def. 6.8.1) as an abelian group only. This file
1. gives it its `ℤ_ℓ`-module structure (multiplication by `a ∈ ℤ_ℓ` on the coefficient sheaf,
   applied through the functoriality `Sheaf.H.map` of sheaf cohomology), and checks it:
   `H⁰(X, ℤ_ℓ) ≃ₗ[ℤ_ℓ] C(X, ℤ_ℓ)` (`H0Equiv`);
2. constructs the transport `e_* : Hⁿ(X, ℤ_ℓ) → Hⁿ(Y, ℤ_ℓ)` along a scheme isomorphism
   `e : X ≅ Y` (equivalence of pro-étale sites → equivalence of sheaf categories → `Ext`), proves it
   `ℤ_ℓ`-linear (`transport_smul`) and bijective (`transport_bijective`), and checks it in degree 0
   (`transport_H0`: it is `f ↦ f ∘ e⁻¹` on global sections);
3. defines the Galois action `galH` of `Gal(K̄/K)` on `H¹(A_K̄, ℤ_ℓ)` by transport along
   `1 × Spec(σ⁻¹)`;
4. states T10: `T10_linIso` (`ℤ_ℓ`-linear isomorphism `H¹(A_K̄, ℤ_ℓ) ≅ Hom_{ℤ_ℓ}(T_ℓ A, ℤ_ℓ)`) and
   **`T10_TateDuality`** (the same, Galois-equivariant), with `T10_TateDuality → T10_linIso →
   T10_groupIso` (leaf-push2's form) and the content check `T10_linIso_zero`.
No `sorry`; only the axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

open CategoryTheory Limits AlgebraicGeometry


universe u
namespace T10Etale

section Coh

set_option backward.isDefEq.respectTransparency.types false

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- The sections of the coefficient sheaf are `ULift C(U, ℤ_ℓ)` (by `rfl`). -/
example (U : X.ProEt) : ((F X ℓ).obj.obj (Opposite.op U) : Type (u+1)) = ULift.{u+1} C(U.left, ℤ_[ℓ]) := rfl

/-- The `ℤ_ℓ`-module structure on `Hⁿ_proet(X, ℤ_ℓ)`: `a` acts through the sheaf endomorphism
"multiplication by `a`" of the coefficient sheaf `U ↦ C(U, ℤ_ℓ)`. -/
noncomputable instance (n : ℕ) : Module ℤ_[ℓ] (X.EllAdicCohomology ℓ n) where
  smul a x := Sheaf.H.map (smulEnd X ℓ a) n x
  one_smul x := by
    change Sheaf.H.map (smulEnd X ℓ 1) n x = x
    rw [smulEnd_one]; exact Sheaf.H.map_id_apply _
  mul_smul a b x := by
    change Sheaf.H.map (smulEnd X ℓ (a * b)) n x =
      Sheaf.H.map (smulEnd X ℓ a) n (Sheaf.H.map (smulEnd X ℓ b) n x)
    rw [smulEnd_mul]; exact Sheaf.H.map_comp_apply _ _ _
  smul_zero a := map_zero (Sheaf.H.map (smulEnd X ℓ a) n)
  smul_add a x y := map_add (Sheaf.H.map (smulEnd X ℓ a) n) x y
  add_smul a b x := by
    change Sheaf.H.map (smulEnd X ℓ (a + b)) n x =
      Sheaf.H.map (smulEnd X ℓ a) n x + Sheaf.H.map (smulEnd X ℓ b) n x
    rw [smulEnd_add]; exact Sheaf.H.map_add_apply _ _ _
  zero_smul x := by
    change Sheaf.H.map (smulEnd X ℓ 0) n x = 0
    rw [smulEnd_zero]
    have h := Sheaf.H.map_add_apply (0 : F X ℓ ⟶ F X ℓ) 0 (x : (F X ℓ).H n)
    rw [add_zero] at h
    simpa using h


/-! ## Sanity check: `H⁰(X, ℤ_ℓ) = C(X, ℤ_ℓ)` as `ℤ_ℓ`-modules -/

end Coh

/-! ## Transport along scheme isomorphisms (for the Galois action) -/

section Transport

set_option backward.isDefEq.respectTransparency.types false

open Scheme Opposite

variable {X Y : Scheme.{u}} (ℓ : ℕ) [Fact ℓ.Prime]

end Transport

/-! ## T10 as a `ℤ_ℓ`-linear isomorphism -/

section AbVarSec

open PkgI3 MonoidalCategory CartesianMonoidalCategory MonObj

/-- The linear form implies leaf-push2's group form. -/
theorem T10_groupIso_of_linIso (h : T10_linIso) : ZInQ.LeafPush2.T10_groupIso := by
  intro K _ A ℓ _ hℓ
  obtain ⟨e⟩ := h K A ℓ hℓ
  exact ⟨e.toAddEquiv⟩

/-! ## The Galois action on `H¹(A_K̄, ℤ_ℓ)` and the equivariant form of T10 -/

example {K : Type} [Field K] (A : AbVar K) : (A.baseChange (AlgebraicClosure K)).X.left = AKbar A :=
  rfl

end AbVarSec

end T10Etale

/-! ## leaf-adopt3 bridge -/

namespace T10Etale

/-- The Galois-equivariant leaf implies leaf-push2's group form `ZInQ.LeafPush2.T10_groupIso`. -/
theorem T10_groupIso_of_tateDuality (h : T10_TateDuality) : ZInQ.LeafPush2.T10_groupIso :=
  T10_groupIso_of_linIso (T10_linIso_of_tateDuality h)

end T10Etale

end T10EtaleSec

/-! # Fold of pi0-x6 (leaf-adopt3)
Source: scratch/pi0-x6/Pi0X6.lean (imports `ZInQKernel.HDecomp.QM.Leaves`; every `LeafQM.AV`
declaration it uses is textually identical to the copy in section `LeafQMSec` of Leaves.lean).
Adds the reduction of the clause `LeafAdopt.R1pi0Props X` as proved theorems; the bundle
`LeafAdopt.R1R2fpRep` is unchanged. -/

section Pi0X6Sec

/-!
# pi0-x6: `π₀(X₆) = 1` from the bundle's clauses, modulo exact CM and algebraic geometry

See `docs/research/pi0-x6.md`.
* §1-§4: the Galois input, stabilizers of `ℚ̄`-points, the core `subsingleton_of_galois`, and
  its hypotheses from `R5ptProps`, `R5fpCount` (`subsingleton_of_bundle`).
* §5: the closed facts for `ℚ(i) = ℚ(ζ₄)`.
* §6: the closed facts for `ℚ(√−3) = ℚ(ζ₃)`.
* §7: the exact-CM clause `R2X6CMExact` (input (c), option c1), the Galois action on
  `X_ℚ̄` and the proved compatibility `compOf_galois`, the algebraic-geometry inputs `AGInputs`
  (input (d) minus Galois compatibility; unproved glue), and the final theorem
  `r1pi0Props_of_bundle : R5ptProps → R5fpCount → R2X6CMExact → AGInputs → R1pi0Props`.
No `sorry`, no `axiom`.
-/

noncomputable section

namespace Pi0X6

section CoreSec


/-! ## §1 Galois input -/



local notation "Qb" => AlgebraicClosure ℚ

open Polynomial IntermediateField

theorem not_isSquare_three_int (m : ℤ) : m * m ≠ 3 := by
  intro h
  have h1 : -2 < m := by nlinarith
  have h2 : m < 2 := by nlinarith
  interval_cases m <;> omega

theorem rat_sq_ne_three (q : ℚ) : q * q ≠ 3 := by
  intro h
  have hsq : IsSquare (3 : ℚ) := ⟨q, h.symm⟩
  rw [Rat.isSquare_iff] at hsq
  obtain ⟨⟨m, hm⟩, -⟩ := hsq
  exact not_isSquare_three_int m (by simpa using hm.symm)

/-- `ℚ(√−3)` contains no square root of `−1`. -/
theorem sqrt_neg_one_not_mem (z s : Qb) (hz : z ^ 2 = -1) (hs : s ^ 2 = -3) :
    z ∉ ℚ⟮s⟯ := by
  intro hmem
  have hint : IsIntegral ℚ s := Algebra.IsIntegral.isIntegral s
  let pb := IntermediateField.adjoin.powerBasis hint
  obtain ⟨f, hfdeg, hf⟩ := pb.exists_eq_aeval ⟨z, hmem⟩
  have hdim : pb.dim ≤ 2 := by
    rw [IntermediateField.adjoin.powerBasis_dim]
    have hp : (X ^ 2 + C (3 : ℚ)) ≠ 0 := by
      intro h0
      have := congrArg natDegree h0
      rw [natDegree_X_pow_add_C] at this
      simp at this
    have hdvd : minpoly ℚ s ∣ X ^ 2 + C (3 : ℚ) := by
      apply minpoly.dvd
      simp [hs]
    have := natDegree_le_of_dvd hdvd hp
    rwa [natDegree_X_pow_add_C] at this
  have hf1 : f.natDegree ≤ 1 := by omega
  obtain ⟨a, b, rfl⟩ := exists_eq_X_add_C_of_natDegree_le_one hf1
  have hz' : z = (a : Qb) * s + (b : Qb) := by
    have := congrArg Subtype.val hf
    simp only [map_add, map_mul, aeval_C, aeval_X] at this
    rw [this]
    simp [eq_ratCast, pb, IntermediateField.adjoin.powerBasis_gen]
  rw [hz'] at hz
  have key : ((2 * a * b : ℚ) : Qb) * s = ((-1 + 3 * a ^ 2 - b ^ 2 : ℚ) : Qb) := by
    push_cast
    linear_combination hz - (a : Qb) ^ 2 * hs
  by_cases hab : (2 * a * b : ℚ) = 0
  · rw [hab] at key
    simp only [Rat.cast_zero, zero_mul] at key
    have key' : (-1 + 3 * a ^ 2 - b ^ 2 : ℚ) = 0 := by exact_mod_cast key.symm
    rcases mul_eq_zero.1 hab with ha | hb
    · have ha0 : a = 0 := by linarith
      subst ha0; nlinarith [sq_nonneg b]
    · subst hb
      exact rat_sq_ne_three (3 * a) (by nlinarith)
  · set q : ℚ := (-1 + 3 * a ^ 2 - b ^ 2) / (2 * a * b)
    have hsq : s = (q : Qb) := by
      have hne : ((2 * a * b : ℚ) : Qb) ≠ 0 := by exact_mod_cast hab
      rw [show q = (-1 + 3 * a ^ 2 - b ^ 2) / (2 * a * b) from rfl, Rat.cast_div, ← key]
      field_simp
    rw [hsq] at hs
    have : q ^ 2 = -3 := by exact_mod_cast hs
    nlinarith [sq_nonneg q]

/-- **Galois input**: for `z² = −1` and `s² = −3` in `ℚ̄` there is `σ ∈ Aut(ℚ̄/ℚ)` fixing `s` and
moving `z` (so `Gal(ℚ̄/ℚ(√−3)) ⊄ Gal(ℚ̄/ℚ(i))`). -/
theorem exists_fix_moves (z s : Qb) (hz : z ^ 2 = -1) (hs : s ^ 2 = -3) :
    ∃ σ : Qb ≃ₐ[ℚ] Qb, σ s = s ∧ σ z ≠ z := by
  by_contra h
  push Not at h
  apply sqrt_neg_one_not_mem z s hz hs
  rw [← InfiniteGalois.fixedField_fixingSubgroup ℚ⟮s⟯]
  intro σ
  apply h σ.1
  exact σ.2 ⟨s, IntermediateField.mem_adjoin_simple_self ℚ s⟩


/-! ## §2 Stabilizers of `ℚ̄`-points -/

open CategoryTheory AlgebraicGeometry LeafQM LeafQM.AV

variable {X : Over (Spec (CommRingCat.of ℚ))}

/-- `Aut(ℚ̄/ℚ)` acting on `X(ℚ̄)`: `x ↦ x ∘ Spec σ`. -/
def galPt (σ : Qbar ≃ₐ[ℚ] Qbar) (x : fieldPt Qbar ⟶ X) : fieldPt Qbar ⟶ X :=
  fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ x

theorem galPt_left (σ : Qbar ≃ₐ[ℚ] Qbar) (x : fieldPt Qbar ⟶ X) :
    (galPt σ x).left = Spec.map (CommRingCat.ofHom (σ : Qbar →+* Qbar)) ≫ x.left := rfl

/-- If `σ` fixes `F` pointwise it fixes `F`'s generators' adjunction (helper). -/
theorem fixes_adjoin (σ : Qbar ≃ₐ[ℚ] Qbar) (S : Set Qbar) (hS : ∀ z ∈ S, σ z = z) :
    ∀ z ∈ IntermediateField.adjoin ℚ S, σ z = z := by
  have hle : IntermediateField.adjoin ℚ S ≤
      IntermediateField.fixedField (Subgroup.zpowers σ) := by
    rw [IntermediateField.adjoin_le_iff]
    intro z hz
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    intro f hf
    have hst : σ ∈ MulAction.stabilizer (Qbar ≃ₐ[ℚ] Qbar) z := by
      rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]; exact hS z hz
    have := (Subgroup.zpowers_le.2 hst) hf
    rwa [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at this
  intro z hz
  exact (IntermediateField.mem_fixedField_iff _ _).1 (hle hz) σ (Subgroup.mem_zpowers σ)

/-- The stabilizer of a `ℚ̄`-point of a scheme (as a morphism `Spec ℚ̄ → X`). -/
theorem spec_comp_eq_self_iff {Z : Scheme.{0}} (σ : Qbar ≃ₐ[ℚ] Qbar)
    (y : Spec (CommRingCat.of Qbar) ⟶ Z) :
    Spec.map (CommRingCat.ofHom (σ : Qbar →+* Qbar)) ≫ y = y ↔
      ∀ z ∈ residueImage (X := Z) y, σ z = z := by
  rw [← (Scheme.SpecToEquivOfField Qbar Z).injective.eq_iff, specToEquivOfField_comp]
  set p := Scheme.SpecToEquivOfField Qbar Z y with hp
  constructor
  · intro h z hz
    have h2 : p.2 ≫ CommRingCat.ofHom (σ : Qbar →+* Qbar) = p.2 := by
      have := (Sigma.mk.inj_iff.1 h).2
      exact eq_of_heq this
    refine fixes_adjoin σ _ ?_ z hz
    rintro _ ⟨t, rfl⟩
    exact congrArg (fun g => g.hom t) h2
  · intro h
    have h2 : p.2 ≫ CommRingCat.ofHom (σ : Qbar →+* Qbar) = p.2 := by
      ext t
      exact h _ (IntermediateField.subset_adjoin ℚ _ ⟨t, rfl⟩)
    rw [h2]

/-- **The stabilizer of a `ℚ̄`-point is the fixing group of its residue field**: `σx = x` iff
`σ` fixes `ℚ(x)` (`residueImage`) pointwise. -/
theorem galPt_eq_self_iff (σ : Qbar ≃ₐ[ℚ] Qbar) (x : fieldPt Qbar ⟶ X) :
    galPt σ x = x ↔ ∀ z ∈ residueImage (X := X.left) x.left, σ z = z := by
  have hx : ∀ y y' : fieldPt Qbar ⟶ X, y = y' ↔ y.left = y'.left :=
    fun y y' => ⟨fun h => h ▸ rfl, fun h => Over.OverMorphism.ext h⟩
  rw [hx, galPt_left]
  exact spec_comp_eq_self_iff σ x.left

/-- If `ℚ(x) = ℚ⟮z⟯` then `σx = x ↔ σ z = z`. -/
theorem galPt_eq_self_iff_of_eq_adjoin (σ : Qbar ≃ₐ[ℚ] Qbar) (x : fieldPt Qbar ⟶ X) (z : Qbar)
    (hz : residueImage (X := X.left) x.left = IntermediateField.adjoin ℚ {z}) :
    galPt σ x = x ↔ σ z = z := by
  rw [galPt_eq_self_iff, hz]
  constructor
  · intro h; exact h z (IntermediateField.mem_adjoin_simple_self ℚ z)
  · intro h; exact fixes_adjoin σ {z} (by simpa using h)

/-- `π`-values are rational at a `ℚ`-rational value: `π(σx) = σ(π x)`. -/
theorem val_galPt (π : ToP1 X.left) (σ : Qbar ≃ₐ[ℚ] Qbar) (x : fieldPt Qbar ⟶ X) :
    π.val (K := Qbar) (galPt σ x).left = (π.val (K := Qbar) x.left).map (σ : Qbar →+* Qbar) :=
  π.val_comp (σ : Qbar →+* Qbar) x.left

/-! ## §3 The core -/

/-- **The `π₀`-core (glue, compiled).** Let `c : X(ℚ̄) → S` be compatible with `Aut(ℚ̄/ℚ)` (two
points in one class stay in one class after `σ`), and suppose every class contains a point over
`0` and a point over `∞`. Suppose the fibre of `π` over `0` has at most two `ℚ̄`-points, each with
residue field `ℚ⟮z⟯`, `z² = −1`, and every point over `∞` has residue field `ℚ⟮s⟯`, `s² = −3`.
Then `S` has at most one element.

Application (docs/research/pi0-x6.md §3): `S = π₀(X_ℚ̄)`, `c x` = the component of `x`; the
residue fields come from `R5ptProps` (`k = ℚ(i)`, `ℚ(√−3)`), the count from `R5fpCount`
(`#CM(ℤ[i]) = 2`). -/
theorem subsingleton_of_galois (π : ToP1 X.left) {S : Type*} (c : (fieldPt Qbar ⟶ X) → S)
    (hc : ∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (x x' : fieldPt Qbar ⟶ X), c x = c x' →
      c (galPt σ x) = c (galPt σ x'))
    (h0 : ∀ t : S, ∃ x : fieldPt Qbar ⟶ X, c x = t ∧ π.val (K := Qbar) x.left = OnePoint.some 0)
    (hinf : ∀ t : S, ∃ y : fieldPt Qbar ⟶ X, c y = t ∧ π.val (K := Qbar) y.left = OnePoint.infty)
    (hcount : ∀ x x' x'' : fieldPt Qbar ⟶ X, π.val (K := Qbar) x.left = OnePoint.some 0 →
      π.val (K := Qbar) x'.left = OnePoint.some 0 → π.val (K := Qbar) x''.left = OnePoint.some 0 →
      x = x' ∨ x = x'' ∨ x' = x'')
    (hres0 : ∀ x : fieldPt Qbar ⟶ X, π.val (K := Qbar) x.left = OnePoint.some 0 →
      ∃ z : Qbar, z ^ 2 = -1 ∧ residueImage (X := X.left) x.left = IntermediateField.adjoin ℚ {z})
    (hresinf : ∀ y : fieldPt Qbar ⟶ X, π.val (K := Qbar) y.left = OnePoint.infty →
      ∃ s : Qbar, s ^ 2 = -3 ∧ residueImage (X := X.left) y.left = IntermediateField.adjoin ℚ {s}) :
    Subsingleton S := by
  refine ⟨fun t₁ t₂ => ?_⟩
  obtain ⟨x₁, rfl, hx₁⟩ := h0 t₁
  obtain ⟨x₂, rfl, hx₂⟩ := h0 t₂
  obtain ⟨y, hy, hyv⟩ := hinf (c x₁)
  obtain ⟨z, hz, hzr⟩ := hres0 x₁ hx₁
  obtain ⟨s, hs, hsr⟩ := hresinf y hyv
  obtain ⟨σ, hσs, hσz⟩ := exists_fix_moves z s hz hs
  have hσy : galPt σ y = y := (galPt_eq_self_iff_of_eq_adjoin σ y s hsr).2 hσs
  have hσx : galPt σ x₁ ≠ x₁ := fun h => hσz ((galPt_eq_self_iff_of_eq_adjoin σ x₁ z hzr).1 h)
  have hv : π.val (K := Qbar) (galPt σ x₁).left = OnePoint.some 0 := by
    rw [val_galPt, hx₁]; simp
  rcases hcount x₁ x₂ (galPt σ x₁) hx₁ hx₂ hv with h | h | h
  · rw [h]
  · exact (hσx h.symm).elim
  · have := hc σ y x₁ hy
    rw [hσy, ← h] at this
    rw [← hy, this]

/-! ## §4 The hypotheses of the core from the bundle's clauses `R5ptProps`, `R5fpCount`

The concrete facts about `ℚ(i)` and `ℚ(√−3)` (`inertCount6 = 1`, `#Pic 𝒪 = 1`, conductor 1) are
hypotheses here (closed number-theoretic facts, glue not done). "CM by `R`" at the points over a
branch value is the hypothesis `hexact` (`com ≅ R`; the bundle's `HasCM4` only gives `φ² = −1`
in `com`). -/

variable {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)}

/-- A degree-2 subfield of `ℚ̄` receiving `k ∋ w`, `w² = d` non-square, is `ℚ⟮z⟯`, `z² = d`. -/
theorem eq_adjoin_of_finrank_two (F : IntermediateField ℚ Qbar) (hdeg : Module.finrank ℚ F = 2)
    (k : Type) [Field k] [Algebra ℚ k] (φ : k →ₐ[ℚ] F) (w : k) (d : ℚ) (hw : w ^ 2 = (d : k))
    (hd : ¬ IsSquare d) :
    ∃ z : Qbar, z ^ 2 = (d : Qbar) ∧ F = IntermediateField.adjoin ℚ {z} := by
  have hz : ((φ w : F) : Qbar) ^ 2 = (d : Qbar) := by
    have h1 : φ (w ^ 2) = φ (d : k) := by rw [hw]
    rw [map_pow, map_ratCast] at h1
    have h2 := congrArg (fun t : F => (t : Qbar)) h1
    simpa using h2
  refine ⟨(φ w : Qbar), hz, ?_⟩
  have : FiniteDimensional ℚ F := Module.finite_of_finrank_pos (by rw [hdeg]; norm_num)
  have hle : IntermediateField.adjoin ℚ {(φ w : Qbar)} ≤ F :=
    IntermediateField.adjoin_simple_le_iff.2 (φ w).2
  symm
  refine IntermediateField.eq_of_le_of_finrank_le hle ?_
  rw [hdeg]
  have : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {(φ w : Qbar)}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
  have hpos : 0 < Module.finrank ℚ (IntermediateField.adjoin ℚ {(φ w : Qbar)}) :=
    Module.finrank_pos
  have hne : Module.finrank ℚ (IntermediateField.adjoin ℚ {(φ w : Qbar)}) ≠ 1 := by
    intro h1
    rw [IntermediateField.finrank_eq_one_iff, IntermediateField.adjoin_simple_eq_bot_iff,
      IntermediateField.mem_bot] at h1
    obtain ⟨q, hq⟩ := h1
    apply hd
    refine ⟨q, ?_⟩
    rw [← hq, eq_ratCast] at hz
    have : ((q * q : ℚ) : Qbar) = (d : Qbar) := by push_cast; rw [← hz]; ring
    exact (Rat.cast_injective this).symm
  omega

/-- **Residue fields from `R5ptProps`.** If `b(k) = 1`, `#Pic R = 1` and `k = ℚ(w)` with
`w² = d` (`d` not a square), a `ℚ̄`-point of `X₆` with `com ≅ R` has residue field `ℚ⟮z⟯`,
`z² = d`. -/
theorem residue_eq_adjoin_of_R5pt (h5 : R5ptProps X Ψ)
    (k : Type) [Field k] [NumberField k] [NumberField.IsTotallyComplex k]
    (hk : Module.finrank ℚ k = 2) (R : Subring k) (hR : R ≤ (integralClosure ℤ k).toSubring)
    (hc : Nat.Coprime (conductor R) 6) (hb : inertCount6 k = 1)
    (hh : Nat.card (CommRing.Pic R) = 1) (w : k) (d : ℚ) (hw : w ^ 2 = (d : k))
    (hd : ¬ IsSquare d) (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar) (hP : Ψ x = Quotient.mk _ P)
    (hRP : Nonempty (com P.q ≃+* R)) :
    ∃ z : Qbar, z ^ 2 = (d : Qbar) ∧
      residueImage (X := X.left) x.left = IntermediateField.adjoin ℚ {z} := by
  obtain ⟨hdeg, hemb⟩ := h5 k hk R hR hc x P hP hRP
  rw [hb, hh] at hdeg
  simp only [one_ne_zero, ite_false, mul_one] at hdeg
  obtain ⟨φ⟩ := hemb (by rw [hb]; exact one_ne_zero)
  exact eq_adjoin_of_finrank_two _ hdeg k φ w d hw hd

/-- **At most two points over a value, from `R5fpCount`.** If every `ℚ̄`-point over `t` has
`com ≅ R` (`hexact`) with `b(k) = 1` and `#Pic R = 1`, there are at most `2^1·1 = 2` of them. -/
theorem fibre_le_two_of_R5count (hcnt : R5fpCount) (π : ToP1 X.left) (t : OnePoint Qbar)
    (k : Type) [Field k] [NumberField k] [NumberField.IsTotallyComplex k]
    (hk : Module.finrank ℚ k = 2) (R : Subring k) (hR : R ≤ (integralClosure ℤ k).toSubring)
    (hc : Nat.Coprime (conductor R) 6) (hb : inertCount6 k = 1)
    (hh : Nat.card (CommRing.Pic R) = 1)
    (hexact : ∀ (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar), Ψ x = Quotient.mk _ P →
      π.val (K := Qbar) x.left = t → Nonempty (com P.q ≃+* R))
    (x x' x'' : fieldPt Qbar ⟶ X) (h : π.val (K := Qbar) x.left = t)
    (h' : π.val (K := Qbar) x'.left = t) (h'' : π.val (K := Qbar) x''.left = t) :
    x = x' ∨ x = x'' ∨ x' = x'' := by
  have hm : ∀ y : fieldPt Qbar ⟶ X, π.val (K := Qbar) y.left = t →
      ∃ P : QMPair Qbar, Quotient.mk _ P = Ψ y ∧ Nonempty (com P.q ≃+* R) := fun y hy =>
    ⟨(Ψ y).out, Quotient.out_eq _, hexact y _ (Quotient.out_eq _).symm hy⟩
  have hcard := hcnt k hk R hR hc (by
    obtain ⟨P, -, hP⟩ := hm x h
    exact ⟨P, hP⟩)
  rw [hb, hh] at hcard
  norm_num at hcard
  let T := {c : Quotient (pairSetoid Qbar) //
    ∃ P : QMPair Qbar, Quotient.mk _ P = c ∧ Nonempty (com P.q ≃+* R)}
  have hT : Nat.card T = 2 := hcard
  have : Finite T := Nat.finite_of_card_ne_zero (by rw [hT]; norm_num)
  let e := Finite.equivFin T
  let a : T := ⟨Ψ x, hm x h⟩
  let b : T := ⟨Ψ x', hm x' h'⟩
  let c : T := ⟨Ψ x'', hm x'' h''⟩
  have ha := (e a).isLt
  have hb' := (e b).isLt
  have hc' := (e c).isLt
  have key : (e a).val = (e b).val ∨ (e a).val = (e c).val ∨ (e b).val = (e c).val := by omega
  rcases key with k1 | k1 | k1
  · exact Or.inl (Ψ.injective (congrArg Subtype.val (e.injective (Fin.ext k1))))
  · exact Or.inr (Or.inl (Ψ.injective (congrArg Subtype.val (e.injective (Fin.ext k1)))))
  · exact Or.inr (Or.inr (Ψ.injective (congrArg Subtype.val (e.injective (Fin.ext k1)))))

/-- **`π₀`-core from the bundle's clauses (glue, compiled).** `R5ptProps` and `R5fpCount` at
`k₄ = ℚ(i)` (`R₄ = ℤ[i]`) and `k₃ = ℚ(√−3)` (`R₃ = ℤ[ζ₃]`), with the closed facts about these
two fields as hypotheses, and "CM exactly by `R₄` over `0`, by `R₃` over `∞`" (`hexact₄`,
`hexact₃`): every Galois-compatible map `c` whose classes all meet the fibres over `0` and `∞`
is constant. With `S = π₀(X_ℚ̄)` (the algebraic-geometry inputs `hc`, `h0`, `hinf`) this is
`π₀(X₆_ℚ̄) = 1`. -/
theorem subsingleton_of_bundle (h5 : R5ptProps X Ψ) (hcnt : R5fpCount) (π : ToP1 X.left)
    (k₄ : Type) [Field k₄] [NumberField k₄] [NumberField.IsTotallyComplex k₄]
    (hk₄ : Module.finrank ℚ k₄ = 2) (R₄ : Subring k₄)
    (hR₄ : R₄ ≤ (integralClosure ℤ k₄).toSubring) (hc₄ : Nat.Coprime (conductor R₄) 6)
    (hb₄ : inertCount6 k₄ = 1) (hh₄ : Nat.card (CommRing.Pic R₄) = 1) (i₄ : k₄)
    (hi₄ : i₄ ^ 2 = ((-1 : ℚ) : k₄))
    (k₃ : Type) [Field k₃] [NumberField k₃] [NumberField.IsTotallyComplex k₃]
    (hk₃ : Module.finrank ℚ k₃ = 2) (R₃ : Subring k₃)
    (hR₃ : R₃ ≤ (integralClosure ℤ k₃).toSubring) (hc₃ : Nat.Coprime (conductor R₃) 6)
    (hb₃ : inertCount6 k₃ = 1) (hh₃ : Nat.card (CommRing.Pic R₃) = 1) (s₃ : k₃)
    (hs₃ : s₃ ^ 2 = ((-3 : ℚ) : k₃))
    (hexact₄ : ∀ (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar), Ψ x = Quotient.mk _ P →
      π.val (K := Qbar) x.left = OnePoint.some 0 → Nonempty (com P.q ≃+* R₄))
    (hexact₃ : ∀ (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar), Ψ x = Quotient.mk _ P →
      π.val (K := Qbar) x.left = OnePoint.infty → Nonempty (com P.q ≃+* R₃))
    {S : Type*} (c : (fieldPt Qbar ⟶ X) → S)
    (hc : ∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (x x' : fieldPt Qbar ⟶ X), c x = c x' →
      c (galPt σ x) = c (galPt σ x'))
    (h0 : ∀ t : S, ∃ x : fieldPt Qbar ⟶ X, c x = t ∧ π.val (K := Qbar) x.left = OnePoint.some 0)
    (hinf : ∀ t : S, ∃ y : fieldPt Qbar ⟶ X, c y = t ∧
      π.val (K := Qbar) y.left = OnePoint.infty) :
    Subsingleton S := by
  have hsq1 : ¬ IsSquare (-1 : ℚ) := by
    rintro ⟨q, hq⟩; nlinarith [mul_self_nonneg q]
  have hsq3 : ¬ IsSquare (-3 : ℚ) := by
    rintro ⟨q, hq⟩; nlinarith [mul_self_nonneg q]
  refine subsingleton_of_galois π c hc h0 hinf
    (fun x x' x'' h h' h'' => fibre_le_two_of_R5count hcnt π _ k₄ hk₄ R₄ hR₄ hc₄ hb₄ hh₄
      hexact₄ x x' x'' h h' h'') (fun x hx => ?_) (fun y hy => ?_)
  · obtain ⟨z, hz, hzr⟩ := residue_eq_adjoin_of_R5pt h5 k₄ hk₄ R₄ hR₄ hc₄ hb₄ hh₄ i₄ (-1) hi₄
      hsq1 x _ (Quotient.out_eq _).symm (hexact₄ x _ (Quotient.out_eq _).symm hx)
    exact ⟨z, by rw [hz]; push_cast; ring, hzr⟩
  · obtain ⟨s, hs, hsr⟩ := residue_eq_adjoin_of_R5pt h5 k₃ hk₃ R₃ hR₃ hc₃ hb₃ hh₃ s₃ (-3) hs₃
      hsq3 y _ (Quotient.out_eq _).symm (hexact₃ y _ (Quotient.out_eq _).symm hy)
    exact ⟨s, by rw [hs]; push_cast; ring, hsr⟩


end CoreSec

/-! ## §5 Closed facts for `ℚ(i)` -/

section QiSec


open NumberField LeafQM LeafQM.AV

/-! ## The closed facts for `k₄ = ℚ(i) = ℚ(ζ₄)` -/

abbrev K4 := CyclotomicField 4 ℚ

instance : NeZero ((4 : ℕ) : ℚ) := ⟨by norm_num⟩

instance : IsCyclotomicExtension {4} ℚ K4 := CyclotomicField.isCyclotomicExtension 4 ℚ

theorem hζ4 : IsPrimitiveRoot (IsCyclotomicExtension.zeta 4 ℚ K4) 4 :=
  IsCyclotomicExtension.zeta_spec 4 ℚ K4

theorem zeta4_sq : (IsCyclotomicExtension.zeta 4 ℚ K4) ^ 2 = -1 := by
  have h := hζ4.pow_eq_one
  have h2 : (IsCyclotomicExtension.zeta 4 ℚ K4) ^ 2 ≠ 1 := by
    intro h2
    have := hζ4.pow_eq_one_iff_dvd 2
    rw [this] at h2
    norm_num at h2
  have : ((IsCyclotomicExtension.zeta 4 ℚ K4) ^ 2 - 1) *
      ((IsCyclotomicExtension.zeta 4 ℚ K4) ^ 2 + 1) = 0 := by
    linear_combination h
  rcases mul_eq_zero.1 this with h3 | h3
  · exact (h2 (sub_eq_zero.1 h3)).elim
  · exact eq_neg_of_add_eq_zero_left h3

instance : NumberField.IsTotallyComplex K4 :=
  IsCyclotomicExtension.Rat.isTotallyComplex (n := 4) K4 (by norm_num)

theorem finrank_K4 : Module.finrank ℚ K4 = 2 := by
  rw [IsCyclotomicExtension.finrank K4 (Polynomial.cyclotomic.irreducible_rat (n := 4) (by norm_num))]
  decide

/-- `i := ζ₄ ∈ 𝓞 ℚ(ζ₄)`, with `i² = −1`. -/
def iInt : 𝓞 K4 := hζ4.toInteger

theorem alg_iInt : algebraMap (𝓞 K4) K4 iInt = IsCyclotomicExtension.zeta 4 ℚ K4 := rfl

theorem iInt_mul_self : iInt * iInt = ((-1 : ℤ) : 𝓞 K4) := by
  apply RingOfIntegers.coe_injective
  rw [map_mul, alg_iInt, map_intCast]; push_cast; rw [← pow_two, zeta4_sq]

/-- `ℤ[i] → 𝓞 ℚ(ζ₄)`, `a + bi ↦ a + bζ₄`. -/
def gaussToO : GaussianInt →+* 𝓞 K4 := Zsqrtd.lift ⟨iInt, iInt_mul_self⟩

theorem gaussToO_apply (z : GaussianInt) :
    gaussToO z = (z.re : 𝓞 K4) + (z.im : 𝓞 K4) * iInt := by
  simp [gaussToO, Zsqrtd.lift]

theorem gaussToO_bijective : Function.Bijective gaussToO := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    rw [gaussToO_apply] at hz
    have hK := congrArg (algebraMap (𝓞 K4) K4) hz
    rw [map_add, map_mul, alg_iInt, map_intCast, map_intCast, map_zero] at hK
    have him : z.im = 0 := by
      by_contra hb
      have hb' : ((z.im : ℚ) : K4) ≠ 0 := by exact_mod_cast hb
      have hζ : IsCyclotomicExtension.zeta 4 ℚ K4 = ((-(z.re : ℚ) / z.im : ℚ) : K4) := by
        push_cast
        field_simp
        linear_combination hK
      have := zeta4_sq
      rw [hζ] at this
      have h' : ((-(z.re : ℚ) / z.im) ^ 2 : ℚ) = -1 := by exact_mod_cast this
      nlinarith [sq_nonneg (-(z.re : ℚ) / z.im)]
    have hre : z.re = 0 := by
      rw [him] at hK
      simp at hK
      exact_mod_cast hK
    exact Zsqrtd.ext hre him
  · intro y
    let pb := hζ4.integralPowerBasis
    obtain ⟨f, hfdeg, hf⟩ := pb.exists_eq_aeval y
    have hdim : pb.dim = 2 := by
      simp only [pb, IsPrimitiveRoot.integralPowerBasis_dim]; decide
    have hf1 : f.natDegree ≤ 1 := by omega
    obtain ⟨a, b, rfl⟩ := Polynomial.exists_eq_X_add_C_of_natDegree_le_one hf1
    refine ⟨⟨b, a⟩, ?_⟩
    rw [gaussToO_apply, hf]
    simp only [map_add, map_mul, Polynomial.aeval_X,
      IsPrimitiveRoot.integralPowerBasis_gen, pb, iInt, eq_intCast, map_intCast]
    ring

/-- `ℤ[i] ≃ 𝓞 ℚ(ζ₄)`. -/
def gaussEquiv : GaussianInt ≃+* 𝓞 K4 := RingEquiv.ofBijective gaussToO gaussToO_bijective

theorem gaussEquiv_natCast (n : ℕ) : gaussEquiv (n : GaussianInt) = (n : 𝓞 K4) := map_natCast _ n

theorem prime_three_O4 : Prime (3 : 𝓞 K4) := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h := (GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime 3).2 (by norm_num)
  have := (MulEquiv.prime_iff gaussEquiv.toMulEquiv).2 h
  have e3 : gaussEquiv.toMulEquiv ((3 : ℕ) : GaussianInt) = (3 : 𝓞 K4) := by
    change gaussEquiv ((3 : ℕ) : GaussianInt) = 3
    rw [map_natCast]; norm_num
  rwa [e3] at this

theorem not_prime_two_O4 : ¬ Prime (2 : 𝓞 K4) := by
  have : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  intro h2
  have h := (GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime 2).1
  have : Prime ((2 : ℕ) : GaussianInt) := by
    have := (MulEquiv.prime_iff gaussEquiv.symm.toMulEquiv).2 h2
    have e2 : gaussEquiv.symm.toMulEquiv (2 : 𝓞 K4) = ((2 : ℕ) : GaussianInt) := by
      change gaussEquiv.symm 2 = _
      rw [map_ofNat]; norm_num
    rwa [e2] at this
  have := h this
  norm_num at this

theorem inertCount6_K4 : inertCount6 K4 = 1 := by
  unfold inertCount6
  have h2 : ¬ (Ideal.span {(2 : 𝓞 K4)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by norm_num)]; exact not_prime_two_O4
  have h3 : (Ideal.span {(3 : 𝓞 K4)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by norm_num)]; exact prime_three_O4
  simp [h2, h3]

/-- `R₄ = 𝓞 ℚ(ζ₄)` as a subring. -/
abbrev R4 : Subring K4 := (integralClosure ℤ K4).toSubring

theorem conductor_R4 : conductor R4 = 1 := AddSubgroup.relIndex_self _

theorem pic_R4 : Nat.card (CommRing.Pic R4) = 1 := by
  have e : GaussianInt ≃+* R4 := gaussEquiv.trans (RingEquiv.refl _)
  have : IsPrincipalIdealRing R4 := IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective
  have : Subsingleton (CommRing.Pic R4) := inferInstance
  exact Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨1⟩⟩

theorem zeta4_sq' : (IsCyclotomicExtension.zeta 4 ℚ K4) ^ 2 = (((-1 : ℚ)) : K4) := by
  rw [zeta4_sq]; push_cast; ring


end QiSec

/-! ## §6 Closed facts for `ℚ(√−3)` -/

section Q3Sec


open NumberField LeafQM LeafQM.AV

/-! ## The closed facts for `k₃ = ℚ(√−3) = ℚ(ζ₃)` -/

abbrev K3 := CyclotomicField 3 ℚ

instance : NeZero ((3 : ℕ) : ℚ) := ⟨by norm_num⟩

instance : IsCyclotomicExtension {3} ℚ K3 := CyclotomicField.isCyclotomicExtension 3 ℚ

theorem hζ3 : IsPrimitiveRoot (IsCyclotomicExtension.zeta 3 ℚ K3) 3 :=
  IsCyclotomicExtension.zeta_spec 3 ℚ K3

local notation "ζ₃" => IsCyclotomicExtension.zeta 3 ℚ K3

theorem zeta3_sq : ζ₃ ^ 2 + ζ₃ + 1 = 0 := by
  have h := hζ3.pow_eq_one
  have h1 : ζ₃ ≠ 1 := hζ3.ne_one (by norm_num)
  have : (ζ₃ - 1) * (ζ₃ ^ 2 + ζ₃ + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.1 this with h3 | h3
  · exact (h1 (sub_eq_zero.1 h3)).elim
  · exact h3

instance : NumberField.IsTotallyComplex K3 :=
  IsCyclotomicExtension.Rat.isTotallyComplex (n := 3) K3 (by norm_num)

theorem finrank_K3 : Module.finrank ℚ K3 = 2 := by
  rw [IsCyclotomicExtension.finrank K3 (Polynomial.cyclotomic.irreducible_rat (n := 3) (by norm_num))]
  decide

/-- `√−3 = 2ζ₃ + 1`. -/
theorem sqrt3_sq : (2 * ζ₃ + 1) ^ 2 = (((-3 : ℚ)) : K3) := by
  push_cast; linear_combination 4 * zeta3_sq

/-- `ζ₃ ∈ 𝓞 ℚ(ζ₃)`. -/
def zInt : 𝓞 K3 := hζ3.toInteger

theorem alg_zInt : algebraMap (𝓞 K3) K3 zInt = ζ₃ := rfl

theorem zInt_sq : zInt ^ 2 = -zInt - 1 := by
  apply RingOfIntegers.coe_injective
  rw [map_pow, map_sub, map_neg, map_one, alg_zInt]
  linear_combination zeta3_sq

/-- `1, ζ₃` are independent over `ℤ`. -/
theorem coord_eq_zero (a b : ℤ) (h : (a : 𝓞 K3) + (b : 𝓞 K3) * zInt = 0) : a = 0 ∧ b = 0 := by
  have hK := congrArg (algebraMap (𝓞 K3) K3) h
  rw [map_add, map_mul, alg_zInt, map_intCast, map_intCast, map_zero] at hK
  have hb : b = 0 := by
    by_contra hb
    have hb' : ((b : ℚ) : K3) ≠ 0 := by exact_mod_cast hb
    have hζ : ζ₃ = ((-(a : ℚ) / b : ℚ) : K3) := by
      push_cast
      field_simp
      linear_combination hK
    have := zeta3_sq
    rw [hζ] at this
    have h' : ((-(a : ℚ) / b) ^ 2 + (-(a : ℚ) / b) + 1 : ℚ) = 0 := by exact_mod_cast this
    nlinarith [sq_nonneg (-(a : ℚ) / b + 1 / 2)]
  refine ⟨?_, hb⟩
  rw [hb] at hK
  simp at hK
  exact_mod_cast hK

/-- Every element of `𝓞 ℚ(ζ₃)` is `a + bζ₃`. -/
theorem exists_coord (y : 𝓞 K3) : ∃ a b : ℤ, y = (a : 𝓞 K3) + (b : 𝓞 K3) * zInt := by
  let pb := hζ3.integralPowerBasis
  obtain ⟨f, hfdeg, hf⟩ := pb.exists_eq_aeval y
  have hdim : pb.dim = 2 := by
    simp only [pb, IsPrimitiveRoot.integralPowerBasis_dim]; decide
  have hf1 : f.natDegree ≤ 1 := by omega
  obtain ⟨a, b, rfl⟩ := Polynomial.exists_eq_X_add_C_of_natDegree_le_one hf1
  refine ⟨b, a, ?_⟩
  rw [hf]
  simp only [map_add, map_mul, Polynomial.aeval_X,
    IsPrimitiveRoot.integralPowerBasis_gen, pb, zInt, eq_intCast, map_intCast]
  ring

theorem coord_eq (a b c d : ℤ)
    (h : (a : 𝓞 K3) + (b : 𝓞 K3) * zInt = (c : 𝓞 K3) + (d : 𝓞 K3) * zInt) : a = c ∧ b = d := by
  have := coord_eq_zero (a - c) (b - d) (by push_cast; linear_combination h)
  omega

theorem dvd_iff_coord (n a b : ℤ) :
    (n : 𝓞 K3) ∣ (a : 𝓞 K3) + (b : 𝓞 K3) * zInt ↔ n ∣ a ∧ n ∣ b := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨c, d, rfl⟩ := exists_coord y
    have := coord_eq a b (n * c) (n * d) (by rw [hy]; push_cast; ring)
    exact ⟨⟨c, this.1⟩, ⟨d, this.2⟩⟩
  · rintro ⟨⟨c, rfl⟩, ⟨d, rfl⟩⟩
    exact ⟨(c : 𝓞 K3) + (d : 𝓞 K3) * zInt, by push_cast; ring⟩

theorem not_prime_three_O3 : ¬ Prime (3 : 𝓞 K3) := by
  intro h
  -- `λ = ζ − 1`, `λ² = −3ζ`
  have hl : (3 : 𝓞 K3) ∣ (zInt - 1) * (zInt - 1) :=
    ⟨-zInt, by linear_combination zInt_sq⟩
  have h1 := h.dvd_or_dvd hl
  have h2 : ¬ ((3 : ℤ) : 𝓞 K3) ∣ ((-1 : ℤ) : 𝓞 K3) + ((1 : ℤ) : 𝓞 K3) * zInt := by
    rw [dvd_iff_coord]; omega
  apply h2
  have e : ((-1 : ℤ) : 𝓞 K3) + ((1 : ℤ) : 𝓞 K3) * zInt = zInt - 1 := by push_cast; ring
  rw [e]
  rcases h1 with h1 | h1 <;> exact_mod_cast h1

theorem parity_lemma : ∀ a b c d : ZMod 2, a * c - b * d = 0 → a * d + b * c - b * d = 0 →
    (a = 0 ∧ b = 0) ∨ (c = 0 ∧ d = 0) := by decide

theorem prime_two_O3 : Prime (2 : 𝓞 K3) := by
  refine ⟨two_ne_zero, ?_, ?_⟩
  · intro hu
    have : ((2 : ℤ) : 𝓞 K3) ∣ ((1 : ℤ) : 𝓞 K3) + ((0 : ℤ) : 𝓞 K3) * zInt := by
      have : (2 : 𝓞 K3) ∣ 1 := hu.dvd
      push_cast; simpa using this
    rw [dvd_iff_coord] at this; omega
  · intro x y hxy
    obtain ⟨a, b, rfl⟩ := exists_coord x
    obtain ⟨c, d, rfl⟩ := exists_coord y
    have hprod : ((a : 𝓞 K3) + (b : 𝓞 K3) * zInt) * ((c : 𝓞 K3) + (d : 𝓞 K3) * zInt) =
        ((a * c - b * d : ℤ) : 𝓞 K3) + ((a * d + b * c - b * d : ℤ) : 𝓞 K3) * zInt := by
      push_cast; linear_combination (b : 𝓞 K3) * d * zInt_sq
    rw [hprod, show (2 : 𝓞 K3) = ((2 : ℤ) : 𝓞 K3) by norm_num, dvd_iff_coord] at hxy
    rw [show (2 : 𝓞 K3) = ((2 : ℤ) : 𝓞 K3) by norm_num, dvd_iff_coord, dvd_iff_coord]
    obtain ⟨h1, h2⟩ := hxy
    have e : ∀ n : ℤ, (2 : ℤ) ∣ n ↔ ((n : ZMod 2) = 0) := fun n => by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; norm_num
    simp only [e] at h1 h2 ⊢
    push_cast at h1 h2
    exact parity_lemma _ _ _ _ h1 h2

theorem inertCount6_K3 : inertCount6 K3 = 1 := by
  unfold inertCount6
  have h2 : (Ideal.span {(2 : 𝓞 K3)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by norm_num)]; exact prime_two_O3
  have h3 : ¬ (Ideal.span {(3 : 𝓞 K3)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by norm_num)]; exact not_prime_three_O3
  simp [h2, h3]

/-- `R₃ = 𝓞 ℚ(ζ₃)` as a subring. -/
abbrev R3 : Subring K3 := (integralClosure ℤ K3).toSubring

theorem conductor_R3 : conductor R3 = 1 := AddSubgroup.relIndex_self _

theorem pic_R3 : Nat.card (CommRing.Pic R3) = 1 := by
  have e : 𝓞 K3 ≃+* R3 := RingEquiv.refl _
  have : IsPrincipalIdealRing (𝓞 K3) := IsCyclotomicExtension.Rat.three_pid K3
  have : IsPrincipalIdealRing R3 := IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective
  have : Subsingleton (CommRing.Pic R3) := inferInstance
  exact Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨1⟩⟩


end Q3Sec

/-! ## §7 The exact-CM clause, the algebraic-geometry inputs, and the final theorem -/

section Final

open CategoryTheory AlgebraicGeometry Limits NumberField LeafQM LeafQM.AV

variable {X : Over (Spec (CommRingCat.of ℚ))}

/-- **R2's CM clauses at `0` and `∞` with "CM by `R`" in its printed meaning** (`End_𝒪(A) ≅ R`,
not merely `φ ∈ com` with `φ² = −1`): a `ℚ̄`-point lies over `0` iff its pair has `com ≅ ℤ[i]`,
and over `∞` iff `com ≅ ℤ[ζ₃]`. *Published*: Baba–Granath 2008 Thm 2.1 and the §3.1 table (the
fibres over `0`, `∞` are the CM points of discriminants `−4`, `−3`), as for `R2X6PropsIff`; a
consequence of the same statement. Only the forward directions are used. -/
def R2X6CMExact (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (π₆ : ToP1 X.left) : Prop :=
  ∀ (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar), Ψ x = Quotient.mk _ P →
    (π₆.val (K := Qbar) x.left = OnePoint.some 0 ↔ Nonempty (com P.q ≃+* R4)) ∧
    (π₆.val (K := Qbar) x.left = OnePoint.infty ↔ Nonempty (com P.q ≃+* R3))

/-- `X_ℚ̄ = X ×_ℚ Spec ℚ̄`. -/
abbrev Xbar (X : Over (Spec (CommRingCat.of ℚ))) : Scheme :=
  pullback X.hom (Spec.map (CommRingCat.ofHom (algebraMap ℚ Qbar)))

/-- The section `Spec ℚ̄ → X_ℚ̄` of a morphism `y : Spec ℚ̄ → X` over `ℚ`. -/
def secOf (y : Spec (CommRingCat.of Qbar) ⟶ X.left)
    (w : y ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap ℚ Qbar))) :
    Spec (CommRingCat.of Qbar) ⟶ Xbar X :=
  pullback.lift y (𝟙 _) (by rw [w, Category.id_comp])

/-- The point of `Spec ℚ̄`. -/
def ptQ : Spec (CommRingCat.of Qbar) := (IsLocalRing.closedPoint Qbar : PrimeSpectrum Qbar)

/-- The point of `X_ℚ̄` of a `ℚ̄`-point `x` (the image of the section `(x, id)`). -/
def ptOf (x : fieldPt Qbar ⟶ X) : Xbar X :=
  secOf x.left (Over.w x) ptQ

/-- The connected component of `X_ℚ̄` containing the point of `x`. -/
def compOf (x : fieldPt Qbar ⟶ X) : _root_.ConnectedComponents (Xbar X) :=
  _root_.ConnectedComponents.mk (ptOf x)

/-- `σ ∈ Aut(ℚ̄/ℚ)` acting on `X_ℚ̄ = X ×_ℚ Spec ℚ̄` through the second factor (`id × Spec σ⁻¹`). -/
def galXbar (σ : Qbar ≃ₐ[ℚ] Qbar) : Xbar X ⟶ Xbar X :=
  pullback.map X.hom (Spec.map (CommRingCat.ofHom (algebraMap ℚ Qbar))) X.hom
    (Spec.map (CommRingCat.ofHom (algebraMap ℚ Qbar))) (𝟙 _)
    (Spec.map (CommRingCat.ofHom ((σ.symm : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar))) (𝟙 _)
    (by simp) (by
      rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext q
      simp)

theorem specMap_sigma_comp_symm (σ : Qbar ≃ₐ[ℚ] Qbar) :
    Spec.map (CommRingCat.ofHom (σ : Qbar →+* Qbar)) ≫
      Spec.map (CommRingCat.ofHom ((σ.symm : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) = 𝟙 _ := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have : ((σ : Qbar →+* Qbar)).comp ((σ.symm : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar) =
      RingHom.id Qbar := by
    ext q; simp
  rw [this]
  exact Spec.map_id _

theorem secOf_comp (σ : Qbar ≃ₐ[ℚ] Qbar) (y : Spec (CommRingCat.of Qbar) ⟶ X.left)
    (w : y ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap ℚ Qbar)))
    (w' : (Spec.map (CommRingCat.ofHom (σ : Qbar →+* Qbar)) ≫ y) ≫ X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ Qbar))) :
    secOf (Spec.map (CommRingCat.ofHom (σ : Qbar →+* Qbar)) ≫ y) w' =
      Spec.map (CommRingCat.ofHom (σ : Qbar →+* Qbar)) ≫ secOf y w ≫ galXbar σ := by
  apply pullback.hom_ext
  · simp only [secOf, galXbar, Category.assoc, pullback.lift_fst, pullback.map,
      Category.comp_id]
  · simp only [secOf, galXbar, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
      pullback.map, Category.id_comp]
    rw [specMap_sigma_comp_symm]

theorem secOf_galois_apply (σ : Qbar ≃ₐ[ℚ] Qbar) (y : Spec (CommRingCat.of Qbar) ⟶ X.left)
    (w : y ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap ℚ Qbar)))
    (w' : (Spec.map (CommRingCat.ofHom (σ : Qbar →+* Qbar)) ≫ y) ≫ X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ Qbar))) :
    secOf (Spec.map (CommRingCat.ofHom (σ : Qbar →+* Qbar)) ≫ y) w'
        ptQ =
      galXbar σ (secOf y w ptQ) := by
  rw [secOf_comp σ y w w', Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  congr 2
  exact Subsingleton.elim _ _

/-- **The Galois action on `X(ℚ̄)` is the action on `X_ℚ̄`**: `pt(σ · x) = galXbar σ (pt x)`. -/
theorem ptOf_galPt (σ : Qbar ≃ₐ[ℚ] Qbar) (x : fieldPt Qbar ⟶ X) :
    ptOf (galPt σ x) = galXbar σ (ptOf x) :=
  secOf_galois_apply σ x.left (Over.w x) (Over.w (galPt σ x))

theorem compOf_galois (σ : Qbar ≃ₐ[ℚ] Qbar) (x x' : fieldPt Qbar ⟶ X)
    (h : compOf x = compOf x') : compOf (galPt σ x) = compOf (galPt σ x') := by
  unfold compOf at *
  rw [ptOf_galPt, ptOf_galPt, ← (galXbar σ).continuous.connectedComponentsMap_mk,
    ← (galXbar σ).continuous.connectedComponentsMap_mk, h]

/-- **The algebraic-geometry inputs (input (d) of docs/research/pi0-x6.md §2; glue, NOT proved,
Mathlib v4.35 lacks the theory).** For `X₆` with `π₆`:
(the Galois compatibility of components is NOT an input: it is proved, `compOf_galois`);
(i)-(ii) every connected component of `X_ℚ̄` contains a `ℚ̄`-point over `0` and one over `∞`
(components are smooth proper irreducible curves over `ℚ̄`; `π₆` is nonconstant on each since its
fibres are finite twist orbits, `Aut(𝒪)/Inn(𝒪^×) ≅ (ℤ/2)²`; the image is closed, irreducible, not
a point, hence `P¹`; closed points are `ℚ̄`-points);
(iii) connected over `ℚ̄` implies geometrically connected, for any `ℚ`-scheme (Stacks, Varieties,
"geometrically connected"; UNVERIFIED tag). -/
structure AGInputs (π₆ : ToP1 X.left) : Prop where
  over0 : ∀ t : _root_.ConnectedComponents (Xbar X), ∃ x : fieldPt Qbar ⟶ X,
    compOf x = t ∧ π₆.val (K := Qbar) x.left = OnePoint.some 0
  overInf : ∀ t : _root_.ConnectedComponents (Xbar X), ∃ y : fieldPt Qbar ⟶ X,
    compOf y = t ∧ π₆.val (K := Qbar) y.left = OnePoint.infty
  descend : ConnectedSpace (Xbar X) → GeometricallyConnected X.hom

/-- **`π₀(X₆_ℚ̄) = 1` (glue, compiled) from the bundle's clauses `R5ptProps`, `R5fpCount`, the
exact-CM clause `R2X6CMExact`, and the algebraic-geometry inputs `AGInputs` (unproved).** The
closed facts about `ℚ(i)` and `ℚ(√−3)` are proved (§5, §6). -/
theorem subsingleton_components_of_bundle {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)}
    {π₆ : ToP1 X.left} (h5 : R5ptProps X Ψ) (hcnt : R5fpCount) (hex : R2X6CMExact Ψ π₆)
    (hag : AGInputs π₆) : Subsingleton (_root_.ConnectedComponents (Xbar X)) :=
  subsingleton_of_bundle h5 hcnt π₆ K4 finrank_K4 R4 le_rfl (by rw [conductor_R4]; norm_num)
    inertCount6_K4 pic_R4 (IsCyclotomicExtension.zeta 4 ℚ K4) zeta4_sq'
    K3 finrank_K3 R3 le_rfl (by rw [conductor_R3]; norm_num) inertCount6_K3 pic_R3
    (2 * IsCyclotomicExtension.zeta 3 ℚ K3 + 1) sqrt3_sq
    (fun x P hP h0 => ((hex x P hP).1).1 h0) (fun x P hP hi => ((hex x P hP).2).1 hi)
    compOf compOf_galois hag.over0 hag.overInf

/-- Subsingleton components and a point give a connected space. -/
theorem connectedSpace_of_subsingleton {α : Type*} [TopologicalSpace α] (x : α)
    (h : Subsingleton (_root_.ConnectedComponents α)) : ConnectedSpace α := by
  have hu : connectedComponent x = Set.univ := Set.eq_univ_of_forall fun y =>
    ConnectedComponents.coe_eq_coe'.1 (Subsingleton.elim (ConnectedComponents.mk y) _)
  exact { isPreconnected_univ := hu ▸ isPreconnected_connectedComponent, toNonempty := ⟨x⟩ }

/-- **The clause `R1pi0Props X` (`GeometricallyConnected X.hom`) from `R5ptProps`, `R5fpCount`,
`R2X6CMExact`, `AGInputs` and one `ℚ̄`-point of `X` (`X6Props` supplies it).** -/
theorem r1pi0Props_of_bundle {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)}
    {π₆ : ToP1 X.left} (h5 : R5ptProps X Ψ) (hcnt : R5fpCount) (hex : R2X6CMExact Ψ π₆)
    (hag : AGInputs π₆) (x₀ : fieldPt Qbar ⟶ X) : GeometricallyConnected X.hom :=
  hag.descend (connectedSpace_of_subsingleton (ptOf x₀)
    (subsingleton_components_of_bundle h5 hcnt hex hag))

/-- **The same, from the repaired bundle's clauses on one `X₆`**: `X6Props` (for the `ℚ̄`-point),
`R5ptProps`, plus `R5fpCount`, `R2X6CMExact`, `AGInputs`. -/
theorem r1pi0Props_of_X6Props {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)} {fY : Y ⟶ X} {π₆ : ToP1 X.left}
    (h6 : X6Props Y Φ X Ψ fY) (h5 : R5ptProps X Ψ) (hcnt : R5fpCount)
    (hex : R2X6CMExact Ψ π₆) (hag : AGInputs π₆) : GeometricallyConnected X.hom := by
  obtain ⟨-, -, ⟨x₀⟩, -, -, -⟩ := h6
  exact r1pi0Props_of_bundle h5 hcnt hex hag x₀

end Final

end Pi0X6

end


/-! ## leaf-adopt3 bridges: the conclusion stated as the clause `LeafAdopt.R1pi0Props X` -/

namespace Pi0X6

open CategoryTheory AlgebraicGeometry LeafQM LeafQM.AV

/-- **Reduction of the clause `LeafAdopt.R1pi0Props X` (Q4, `π₀(X₆) = 1`)** to the bundle's
clauses `R5ptProps X Ψ`, `R5fpCount`, the exact-CM clause `R2X6CMExact Ψ π₆` (Baba–Granath, CM
"by `R`" in its printed meaning), the algebraic-geometry inputs `AGInputs π₆` (unproved glue) and
one `ℚ̄`-point of `X`. -/
theorem leafAdopt_r1pi0Props_of_bundle {X : Over (Spec (CommRingCat.of ℚ))}
    {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)} {π₆ : ToP1 X.left}
    (h5 : R5ptProps X Ψ) (hcnt : R5fpCount) (hex : R2X6CMExact Ψ π₆) (hag : AGInputs π₆)
    (x₀ : fieldPt Qbar ⟶ X) : LeafAdopt.R1pi0Props X :=
  r1pi0Props_of_bundle h5 hcnt hex hag x₀

/-- The same, with the `ℚ̄`-point supplied by the bundle clause `X6Props`. -/
theorem leafAdopt_r1pi0Props_of_X6Props {X Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)} {fY : Y ⟶ X} {π₆ : ToP1 X.left}
    (h6 : X6Props Y Φ X Ψ fY) (h5 : R5ptProps X Ψ) (hcnt : R5fpCount)
    (hex : R2X6CMExact Ψ π₆) (hag : AGInputs π₆) : LeafAdopt.R1pi0Props X :=
  r1pi0Props_of_X6Props h6 h5 hcnt hex hag

end Pi0X6

end Pi0X6Sec

section HodgeLatticeSec
/-! ### leaf-adopt3 fold (2026-11-13): task hodge-lattice

Copied from `scratch/hodge-lattice/HodgeLattice.lean` (compiled there against the kernel module
`ZInQKernel.HDecomp.Faltings.Models`). Changes: the `import` line and the `#print axioms` lines are
dropped, and the nine lines `open PkgI3 (AbVar)` are deleted. In the kernel `ZInQ.DefFaltings` has
no `AbVar` of its own (it uses `PkgI3.AbVar`); in this file it has def-faltings' copy
`ZInQ.DefFaltings.AbVar`, over which `GroupModel` and `HodgeLatticeTheorem` are stated. Inside
`namespace ZInQ.DefFaltings.HodgeLattice` the bare name `AbVar` resolves to that copy through the
namespace prefix, so every statement below is over `ZInQ.DefFaltings.AbVar`. All other kernel
declarations used (`GroupModel`, `genericFibre`, `genericPt`, `secIndex`, `hodgeSpace`,
`detLattice`, `omegaAt`, ...) are textually identical in section `DefFaltingsSec` above. -/

/-! # `HodgeLatticeTheorem`: the algebraic reduction (task hodge-lattice)

`ZInQ.DefFaltings.HodgeLatticeTheorem` (ZInQKernel/HDecomp/Faltings/Models.lean) asks, for a smooth
group model `𝒢` of `A_L` with `A.dim = g`, that
* `hodgeSpace g = L ⊗_{𝓞_L} ⋀^g_{𝓞_L} (𝔪_ξ/𝔪_ξ²)` is an `L`-line, and
* `detLattice g = 𝓞_L-span {1 ⊗ v₁ ∧ ⋯ ∧ v_g : vᵢ ∈ ω_𝒢}` is a full lattice in it.

§1 proves this, for an arbitrary `𝓞_K`-module `M` and submodule `ω` in place of
`(𝔪_ξ/𝔪_ξ², ω_𝒢)`, from three hypotheses: `ω` finitely generated, `K ⊗ M` of `K`-rank `g`, and
`ω` spanning `K ⊗ M` over `K` (`hodgeLattice_of_lattice`). §2 states the three hypotheses over the
genuine objects of `Models.lean` (`OmegaFG`, `CotangentRank`, `OmegaSpans`) and derives
`HodgeLatticeTheorem` from them (`hodgeLatticeTheorem_of`). §3-§5 prove `OmegaFG` and `OmegaSpans`
(`omegaLocal`: `ω_𝒢` is a finitely generated full lattice). §6 reduces `CotangentRank` to the
regularity and Krull dimension of `𝒪_{𝒢,ξ}`; §7 is a corollary; §8-§9 move these to statements about
abelian varieties over a field and the local rings of a generic fibre; §10 proves the latter
(`genericFibreStalkIso`); §11 needs only the tangent dimension at the origin. Final form:

`hodgeLatticeTheorem_of_tangent : TangentDimAtOrigin → DimBaseChange → HodgeLatticeTheorem`
(and `tangentDimAtOrigin_of : RegularAtOrigin → DimAtOrigin → TangentDimAtOrigin`).

No unproved step, no `axiom` (in the source file). -/

namespace ZInQ.DefFaltings.HodgeLattice

open NumberField TensorProduct

/-! ## 1. Commutative algebra -/

/-- A top-degree alternating map on `R^g`, with values in any module, is `det · F(e)`. -/
theorem alt_eq_smulRight {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N] {g : ℕ}
    (F : (Fin g → R) [⋀^Fin g]→ₗ[R] N) :
    F = (Pi.basisFun R (Fin g)).det.smulRight (F (Pi.basisFun R (Fin g))) := by
  refine Module.Basis.ext_alternating (Pi.basisFun R (Fin g)) fun i h => ?_
  let σ : Equiv.Perm (Fin g) := Equiv.ofBijective i (Finite.injective_iff_bijective.1 h)
  change F (Pi.basisFun R (Fin g) ∘ σ) =
    ((Pi.basisFun R (Fin g)).det.smulRight (F (Pi.basisFun R (Fin g)))) (Pi.basisFun R (Fin g) ∘ σ)
  rw [AlternatingMap.smulRight_apply, AlternatingMap.map_perm, AlternatingMap.map_perm,
    Module.Basis.det_self]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]

/-- Clearing denominators in `K ⊗_{𝓞_K} M`: if every `1 ⊗ v` is a `K`-combination of the
`1 ⊗ w_j`, then some nonzero multiple of `v` is an `𝓞_K`-combination of the `w_j` in `M`. -/
theorem exists_clear {g : ℕ} (w : Fin g → M)
    (hb : ∀ v : M, (1 : K) ⊗ₜ[𝓞 K] v ∈
      Submodule.span K (Set.range fun j => (1 : K) ⊗ₜ[𝓞 K] w j)) (v : M) :
    ∃ D : 𝓞 K, D ≠ 0 ∧ ∃ a : Fin g → 𝓞 K, D • v = ∑ j, a j • w j := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp (hb v)
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 K)) Finset.univ c
  choose a ha using fun j => hd j (Finset.mem_univ j)
  have key : (TensorProduct.mk (𝓞 K) K M 1) ((d : 𝓞 K) • v) =
      TensorProduct.mk (𝓞 K) K M 1 (∑ j, a j • w j) := by
    simp only [TensorProduct.mk_apply, TensorProduct.tmul_sum, TensorProduct.tmul_smul]
    rw [← hc, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← algebraMap_smul K (a j), ha j, smul_assoc]
  have : IsLocalizedModule (nonZeroDivisors (𝓞 K)) (TensorProduct.mk (𝓞 K) K M 1) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors (𝓞 K)) K _).mpr
      (TensorProduct.isBaseChange _ _ _)
  obtain ⟨e, he⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors (𝓞 K)) key
  refine ⟨(e : 𝓞 K) * d, mul_ne_zero (nonZeroDivisors.ne_zero e.2)
    (nonZeroDivisors.ne_zero d.2), fun j => (e : 𝓞 K) * a j, ?_⟩
  have he' : (e : 𝓞 K) • ((d : 𝓞 K) • v) = (e : 𝓞 K) • ∑ j, a j • w j := he
  rw [mul_smul, he', Finset.smul_sum]
  simp only [mul_smul]

/-- The wedge of any `g` vectors is an `K`-multiple of the wedge of `w`, as soon as every vector
has a nonzero multiple in the `𝓞_K`-span of `w`. -/
theorem tmul_ιMulti_mem_span {g : ℕ} (w : Fin g → M)
    (hw : ∀ v : M, ∃ D : 𝓞 K, D ≠ 0 ∧ ∃ a : Fin g → 𝓞 K, D • v = ∑ j, a j • w j)
    (v : Fin g → M) :
    (1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g v ∈
      Submodule.span K {(1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g w} := by
  choose D hD a ha using hw
  set ψ := Fintype.linearCombination (𝓞 K) w with hψ
  have h1 : exteriorPower.ιMulti (𝓞 K) g (fun i => D (v i) • v i) =
      (∏ i, D (v i)) • exteriorPower.ιMulti (𝓞 K) g v :=
    MultilinearMap.map_smul_univ _ _ _
  have h2 : (fun i => D (v i) • v i) = fun i => ψ (a (v i)) := by
    funext i; rw [ha, hψ, Fintype.linearCombination_apply]
  have he : (fun i => ψ (Pi.basisFun (𝓞 K) (Fin g) i)) = w := by
    funext i
    classical
    rw [Pi.basisFun_apply, hψ, Fintype.linearCombination_apply_single, one_smul]
  have hF := congrArg (fun F => F (fun i => a (v i)))
    (alt_eq_smulRight ((exteriorPower.ιMulti (𝓞 K) g).compLinearMap ψ))
  simp only [AlternatingMap.compLinearMap_apply, AlternatingMap.smulRight_apply] at hF
  set c : 𝓞 K := (Pi.basisFun (𝓞 K) (Fin g)).det (fun i => a (v i))
  have hF' : (∏ i, D (v i)) • exteriorPower.ιMulti (𝓞 K) g v =
      c • exteriorPower.ιMulti (𝓞 K) g w := by
    rw [← h1, h2, hF, he]
  have hP : (∏ i, D (v i)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hD _
  have hPK : algebraMap (𝓞 K) K (∏ i, D (v i)) ≠ 0 := fun h =>
    hP (IsFractionRing.injective (𝓞 K) K (by rw [h, map_zero]))
  rw [Submodule.mem_span_singleton]
  refine ⟨(algebraMap (𝓞 K) K (∏ i, D (v i)))⁻¹ * algebraMap (𝓞 K) K c, ?_⟩
  rw [mul_smul, algebraMap_smul K c, ← TensorProduct.tmul_smul, ← hF',
    TensorProduct.tmul_smul, ← algebraMap_smul K (∏ i, D (v i)), smul_smul, inv_mul_cancel₀ hPK,
    one_smul]

/-- The Hodge lattice of `ω ⊆ M` in `K ⊗ ⋀^g M` (the shape of `GroupModel.detLattice`). -/
noncomputable def detLat (ω : Submodule (𝓞 K) M) (g : ℕ) :
    Submodule (𝓞 K) (K ⊗[𝓞 K] ⋀[𝓞 K]^g M) :=
  Submodule.span (𝓞 K) (Set.range fun v : Fin g → ω =>
    (1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g (fun i => (v i : M)))

/-- **The algebraic content of `HodgeLatticeTheorem`.** If `ω ⊆ M` is finitely generated,
`K ⊗ M` has `K`-rank `g`, and `ω` spans `K ⊗ M` over `K`, then `K ⊗ ⋀^g M` is a `K`-line and
`detLat ω g` is a full lattice in it (some nonzero element generates a subgroup of finite index). -/
theorem hodgeLattice_of_lattice {g : ℕ} (ω : Submodule (𝓞 K) M) (hfg : ω.FG)
    (hrank : Module.rank K (K ⊗[𝓞 K] M) = g)
    (hspan : Submodule.span K (Set.range fun x : ω => (1 : K) ⊗ₜ[𝓞 K] (x : M)) = ⊤) :
    Module.finrank K (K ⊗[𝓞 K] ⋀[𝓞 K]^g M) = 1 ∧
      ∃ s ∈ detLat ω g, s ≠ 0 ∧ secIndex (detLat ω g) s ≠ 0 := by
  classical
  set V := K ⊗[𝓞 K] M
  set f : ω → V := fun x => (1 : K) ⊗ₜ[𝓞 K] (x : M) with hf
  have : FiniteDimensional K V := Module.finite_of_rank_eq_nat hrank
  have hfin : Module.finrank K V = g := Module.finrank_eq_of_rank_eq hrank
  -- Step 1: a `K`-basis of `V` of the form `1 ⊗ w_j` with `w_j ∈ ω`.
  obtain ⟨s, hs_sub, hs_span, hs_li⟩ := exists_linearIndependent K (Set.range f)
  let bs : Module.Basis s K V := Module.Basis.mk hs_li (by
    rw [Subtype.range_coe, hs_span, hspan])
  let b : Module.Basis (Fin g) K V :=
    bs.reindex (bs.indexEquiv (Module.finBasisOfFinrankEq K V hfin))
  have hmem : ∀ j, ∃ x : ω, f x = b j := fun j => by
    have : (b j : V) ∈ s := by
      simp only [b, Module.Basis.reindex_apply, bs, Module.Basis.coe_mk]
      exact Subtype.mem _
    exact hs_sub this
  choose w hw using hmem
  set w' : Fin g → M := fun j => (w j : M) with hw'
  have hbw : ∀ j, (1 : K) ⊗ₜ[𝓞 K] w' j = b j := hw
  -- Step 2: every vector of `M` has a nonzero multiple in the `𝓞_K`-span of `w'`.
  have hclear := exists_clear (K := K) w' (fun v => by
    have hr : Set.range (fun j => (1 : K) ⊗ₜ[𝓞 K] w' j) = Set.range b := by
      rw [show (fun j => (1 : K) ⊗ₜ[𝓞 K] w' j) = b from funext hbw]
    rw [hr, b.span_eq]; exact Submodule.mem_top)
  -- Step 3: `s₀ = 1 ⊗ w'_1 ∧ ⋯ ∧ w'_g` spans `K ⊗ ⋀^g M` over `K`.
  set s0 : K ⊗[𝓞 K] ⋀[𝓞 K]^g M := (1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g w' with hs0
  have hone : ∀ x : ⋀[𝓞 K]^g M, (1 : K) ⊗ₜ[𝓞 K] x ∈ Submodule.span K {s0} := by
    intro x
    have hx : x ∈ Submodule.span (𝓞 K) (Set.range (exteriorPower.ιMulti (𝓞 K) g)) := by
      rw [exteriorPower.ιMulti_span]; exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v, rfl⟩ := hy
      exact tmul_ιMulti_mem_span w' hclear v
    | zero => rw [TensorProduct.tmul_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ hy hz
    | smul r y _ hy =>
      rw [TensorProduct.tmul_smul]; exact Submodule.smul_of_tower_mem _ r hy
  have htop : Submodule.span K {s0} = ⊤ := by
    rw [eq_top_iff]
    rintro h -
    induction h using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | tmul k x =>
      have : k ⊗ₜ[𝓞 K] x = k • ((1 : K) ⊗ₜ[𝓞 K] x) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this]; exact Submodule.smul_mem _ k (hone x)
    | add x y hx hy => exact Submodule.add_mem _ hx hy
  -- Step 4: `s₀ ≠ 0`, through the functional induced by `det_b`.
  let φ : M [⋀^Fin g]→ₗ[𝓞 K] K :=
    { toMultilinearMap := (b.det.toMultilinearMap.restrictScalars (𝓞 K)).compLinearMap
        (fun _ => TensorProduct.mk (𝓞 K) K M 1)
      map_eq_zero_of_eq' := fun v i j hv hij =>
        b.det.map_eq_zero_of_eq (fun k => (1 : K) ⊗ₜ[𝓞 K] v k) (by simp [hv]) hij }
  let Ψ : (K ⊗[𝓞 K] ⋀[𝓞 K]^g M) →ₗ[K] K :=
    (exteriorPower.alternatingMapLinearEquiv φ).liftBaseChange K
  have hΨ : Ψ s0 = 1 := by
    simp only [Ψ, hs0, LinearMap.liftBaseChange_one_tmul,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    change b.det (fun k => (1 : K) ⊗ₜ[𝓞 K] w' k) = 1
    rw [show (fun k => (1 : K) ⊗ₜ[𝓞 K] w' k) = b from funext hbw, Module.Basis.det_self]
  have hs0ne : s0 ≠ 0 := fun h => by rw [h, map_zero] at hΨ; exact zero_ne_one hΨ
  refine ⟨?_, s0, Submodule.subset_span ⟨w, rfl⟩, hs0ne, ?_⟩
  · rw [← finrank_top K, ← htop]
    exact finrank_span_singleton hs0ne
  -- Step 5: `detLat ω g` lies in a finitely generated module, hence in `𝓞_K · t₀` with
  -- `s₀ = d • t₀`; so `𝓞_K s₀` has finite index in it.
  have : Module.Finite (𝓞 K) ω := Module.Finite.iff_fg.mpr hfg
  set R : Submodule (𝓞 K) (K ⊗[𝓞 K] ⋀[𝓞 K]^g M) := LinearMap.range
    ((TensorProduct.mk (𝓞 K) K (⋀[𝓞 K]^g M) 1) ∘ₗ exteriorPower.map g ω.subtype) with hR
  have hRfg : R.FG := by
    rw [hR, LinearMap.range_eq_map]; exact (Module.Finite.fg_top).map _
  have hDR : detLat ω g ≤ R := by
    rw [detLat, Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    exact ⟨exteriorPower.ιMulti (𝓞 K) g v, by
      simp [exteriorPower.map_apply_ιMulti]; rfl⟩
  obtain ⟨S, hS⟩ := hRfg
  have hc : ∀ t : K ⊗[𝓞 K] ⋀[𝓞 K]^g M, ∃ c : K, c • s0 = t := fun t => by
    have : t ∈ Submodule.span K {s0} := by rw [htop]; exact Submodule.mem_top
    exact Submodule.mem_span_singleton.mp this
  choose c hc using hc
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 K)) S c
  have hd0 : (d : 𝓞 K) ≠ 0 := nonZeroDivisors.ne_zero d.2
  have hdK : algebraMap (𝓞 K) K (d : 𝓞 K) ≠ 0 := fun h =>
    hd0 (IsFractionRing.injective (𝓞 K) K (by rw [h, map_zero]))
  set t0 : K ⊗[𝓞 K] ⋀[𝓞 K]^g M := (algebraMap (𝓞 K) K (d : 𝓞 K))⁻¹ • s0 with ht0
  have hst : s0 = (d : 𝓞 K) • t0 := by
    rw [ht0, ← algebraMap_smul K (d : 𝓞 K), smul_smul, mul_inv_cancel₀ hdK, one_smul]
  have hRt : R ≤ Submodule.span (𝓞 K) {t0} := by
    rw [← hS, Submodule.span_le]
    intro t ht
    obtain ⟨a, ha⟩ := hd t ht
    rw [SetLike.mem_coe, Submodule.mem_span_singleton]
    refine ⟨a, ?_⟩
    rw [← algebraMap_smul K a, ha, ht0, smul_smul]
    conv_rhs => rw [← hc t]
    congr 1
    rw [Algebra.smul_def, mul_comm, ← mul_assoc, inv_mul_cancel₀ hdK, one_mul]
  have ht0ne : t0 ≠ 0 := fun h => hs0ne (by rw [hst, h, smul_zero])
  have hidx : secIndex (Submodule.span (𝓞 K) {t0}) s0 ≠ 0 := by
    rw [hst, secIndex_smul _ (Submodule.mem_span_singleton_self t0) ht0ne]
    have h1 : secIndex (Submodule.span (𝓞 K) {t0}) t0 = 1 := by
      unfold secIndex; exact AddSubgroup.relIndex_self _
    rw [h1, mul_one]
    simp [Int.natAbs_eq_zero, (Algebra.norm_ne_zero_iff (R := ℤ)).mpr hd0]
  unfold secIndex at hidx ⊢
  intro h0
  exact hidx (AddSubgroup.relIndex_eq_zero_of_le_right
    (show (detLat ω g).toAddSubgroup ≤ (Submodule.span (𝓞 K) {t0}).toAddSubgroup from
      fun x hx => hRt (hDR hx)) h0)

/-! ## 2. The three geometric inputs, over the objects of `Models.lean`

For a smooth group model `𝒢` of `A_L` (`GroupModel A L`), write `cot = 𝔪_ξ/𝔪_ξ²`
(`GroupModel.cotangent`, an `𝓞_L`-module through `structMap`) and `ω_𝒢 = ⋂_s (ω_𝒢)_s ⊆ cot`
(`GroupModel.omega`). -/


/-- **(G1)** `ω_𝒢` is a finitely generated `𝓞_L`-module. (Geometrically: `ω_𝒢 = Γ(S, e*Ω¹_{𝒢/S})`
with `e*Ω¹` coherent, indeed locally free of rank `g`, on `S = Spec 𝓞_L`.) -/
def OmegaFG : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L), 𝒢.omega.FG

/-- **(G2)** `L ⊗_{𝓞_L} 𝔪_ξ/𝔪_ξ²` (which is `𝔪_ξ/𝔪_ξ² = ω_{A_L}` itself) has `L`-dimension
`g = dim A`. (Geometrically: `𝒪_{𝒢,ξ} = 𝒪_{A_L,0}`, and the local ring of a smooth `L`-variety
of pure dimension `g` at a rational point is regular of dimension `g`.) -/
def CotangentRank : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (g : ℕ), A.dim = g →
    Module.rank L (L ⊗[𝓞 L] 𝒢.cotangent) = g

/-- **(G3)** `ω_𝒢` spans `ω_{A_L}` over `L`: the image of `L ⊗ ω_𝒢 → L ⊗ cot` is everything.
(Geometrically: the generic stalk of the coherent sheaf `e*Ω¹_{𝒢/S}` is `ω_{A_L}`, and a coherent
sheaf on an affine scheme is generated by global sections.) -/
def OmegaSpans : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L),
    Submodule.span L (Set.range fun x : 𝒢.omega => (1 : L) ⊗ₜ[𝓞 L] (x : 𝒢.cotangent)) = ⊤

/-- `detLattice` is the generic `detLat` of `§1`. -/
theorem detLattice_eq {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L]
    [Algebra K L] (𝒢 : GroupModel A L) (g : ℕ) : 𝒢.detLattice g = detLat 𝒢.omega g := rfl

/-- **Main result.** `HodgeLatticeTheorem` follows from the three geometric inputs; everything
else (the exterior algebra, the line, the full lattice) is proved. -/
theorem hodgeLatticeTheorem_of (h1 : OmegaFG) (h2 : CotangentRank) (h3 : OmegaSpans) :
    HodgeLatticeTheorem := by
  intro K _ A L _ _ _ 𝒢 g hg
  rw [detLattice_eq]
  exact hodgeLattice_of_lattice 𝒢.omega (h1 K A L 𝒢) (h2 K A L 𝒢 g hg) (h3 K A L 𝒢)

end ZInQ.DefFaltings.HodgeLattice

namespace ZInQ.DefFaltings.HodgeLattice

open NumberField TensorProduct

/-! ## 3. Local-to-global over `Spec R` (pure algebra)

For a family `Ω s` of submodules indexed by the points of `Spec R`, finiteness and fullness of
`⋂_s Ω s` follow from local statements on a cover by basic opens `D(a)`. -/

section LocalGlobal

variable {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V]

/-- Finitely many basic opens `D(a s)` cover `Spec R` if `s ∈ D(a s)` for every `s`. -/
theorem exists_finset_cover (a : PrimeSpectrum R → R) (ha : ∀ s, a s ∉ s.asIdeal) :
    ∃ F : Finset (PrimeSpectrum R), ∀ s' : PrimeSpectrum R, ∃ s ∈ F, a s ∉ s'.asIdeal := by
  classical
  have htop : Ideal.span (Set.range a) = ⊤ := by
    by_contra h
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
    exact ha ⟨m, hm.isPrime⟩ (hle (Ideal.subset_span ⟨_, rfl⟩))
  obtain ⟨T, hT, hTtop⟩ := (Ideal.span_eq_top_iff_finite _).mp htop
  refine ⟨T.attach.image (fun r => (hT r.2).choose), fun s' => ?_⟩
  by_contra hno
  push_neg at hno
  have : Ideal.span (T : Set R) ≤ s'.asIdeal := by
    rw [Ideal.span_le]
    intro r hr
    have := hno _ (Finset.mem_image_of_mem _ (Finset.mem_attach T ⟨r, hr⟩))
    rwa [(hT hr).choose_spec] at this
  exact s'.isPrime.ne_top (top_le_iff.mp (hTtop ▸ this))

/-- **Finiteness, local to global.** -/
theorem fg_iInf_of_local [IsNoetherianRing R] (Ω : PrimeSpectrum R → Submodule R V)
    (h : ∀ s : PrimeSpectrum R, ∃ a : R, a ∉ s.asIdeal ∧ ∃ N : Submodule R V, N.FG ∧
      ∀ s' : PrimeSpectrum R, a ∉ s'.asIdeal → ∀ x ∈ Ω s', ∃ t ∉ s'.asIdeal, t • x ∈ N) :
    (⨅ s, Ω s).FG := by
  classical
  choose a ha N hN hloc using h
  obtain ⟨F, hF⟩ := exists_finset_cover a ha
  set N0 := F.sup N
  have hN0 : N0.FG := Submodule.fg_finset_sup F N fun i _ => hN i
  refine Submodule.FG.of_le hN0 fun x hx => ?_
  set J : Ideal R := N0.comap (LinearMap.toSpanSingleton R V x)
  have hJ : J = ⊤ := by
    by_contra hJ
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hJ
    obtain ⟨s, hsF, hs⟩ := hF ⟨m, hm.isPrime⟩
    obtain ⟨t, ht, htN⟩ := hloc s ⟨m, hm.isPrime⟩ hs x (Submodule.mem_iInf _ |>.mp hx _)
    exact ht (hle (show t ∈ J from Finset.le_sup (f := N) hsF htN))
  have : (1 : R) ∈ J := hJ ▸ Submodule.mem_top
  simpa [J] using this

/-- **Fullness, local to global.** -/
theorem exists_smul_mem_iInf_of_local [IsDomain R] (Ω : PrimeSpectrum R → Submodule R V)
    (h : ∀ s : PrimeSpectrum R, ∃ a : R, a ∉ s.asIdeal ∧ ∃ N : Submodule R V,
      (∀ x : V, ∃ c : R, c ≠ 0 ∧ c • x ∈ N) ∧
      ∀ s' : PrimeSpectrum R, a ∉ s'.asIdeal → N ≤ Ω s') (x : V) :
    ∃ c : R, c ≠ 0 ∧ c • x ∈ ⨅ s, Ω s := by
  classical
  choose a ha N hN hle using h
  obtain ⟨F, hF⟩ := exists_finset_cover a ha
  choose c hc0 hcN using fun s => hN s x
  refine ⟨∏ s ∈ F, c s, Finset.prod_ne_zero_iff.mpr fun s _ => hc0 s, ?_⟩
  rw [Submodule.mem_iInf]
  intro s'
  obtain ⟨s, hsF, hs⟩ := hF s'
  apply hle s s' hs
  rw [← Finset.mul_prod_erase F c hsF, mul_comm, mul_smul]
  exact Submodule.smul_mem _ _ (hcN s)

end LocalGlobal

/-! ## 4. `OmegaFG` and `OmegaSpans` from one local statement

`OmegaLocal` says: near every point `s` of `S = Spec 𝓞_L` (on a basic open `D(a) ∋ s`), the
stalks `(ω_𝒢)_{s'}` (`omegaAt s'`) are the localizations of one finitely generated `N ⊆ ω_{A_L}`
that spans `ω_{A_L}` over `L`. This is "`e*Ω¹_{𝒢/S}` is quasi-coherent of finite type with generic
stalk `ω_{A_L}`" in the form needed: for an affine open `U = Spec B ⊆ 𝒢` with `e(D(a)) ⊆ U` and
`ε : B → 𝓞_L[1/a]` the section, take `N` = the `𝓞_L`-span of `d i`, `i` running over generators
of `I = ker ε` (finitely many: `B` is noetherian). It uses only that `𝒢` is locally of finite type
over `𝓞_L` (not smoothness). -/

/-- **(G-loc)** The local finiteness and fullness of `e*Ω¹_{𝒢/S}`. -/
def OmegaLocal : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (s : PrimeSpectrum (𝓞 L)), ∃ a : 𝓞 L, a ∉ s.asIdeal ∧
    ∃ N : Submodule (𝓞 L) 𝒢.cotangent, N.FG ∧ (∀ x : 𝒢.cotangent, ∃ c : 𝓞 L, c ≠ 0 ∧ c • x ∈ N) ∧
      ∀ s' : PrimeSpectrum (𝓞 L), a ∉ s'.asIdeal →
        N ≤ 𝒢.omegaAt s' ∧ ∀ x ∈ 𝒢.omegaAt s', ∃ t ∉ s'.asIdeal, t • x ∈ N

theorem omegaFG_of_omegaLocal (h : OmegaLocal) : OmegaFG := by
  intro K _ A L _ _ _ 𝒢
  exact fg_iInf_of_local (R := 𝓞 L) (fun s => 𝒢.omegaAt s) fun s => by
    obtain ⟨a, ha, N, hN, -, hloc⟩ := h K A L 𝒢 s
    exact ⟨a, ha, N, hN, fun s' hs' => (hloc s' hs').2⟩

theorem omegaSpans_of_omegaLocal (h : OmegaLocal) : OmegaSpans := by
  intro K _ A L _ _ _ 𝒢
  rw [eq_top_iff]
  rintro y -
  induction y using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | tmul k x =>
    obtain ⟨c, hc0, hc⟩ := exists_smul_mem_iInf_of_local (R := 𝓞 L) (fun s => 𝒢.omegaAt s)
      (fun s => by
        obtain ⟨a, ha, N, -, hspan, hloc⟩ := h K A L 𝒢 s
        exact ⟨a, ha, N, hspan, fun s' hs' => (hloc s' hs').1⟩) x
    have hcK : algebraMap (𝓞 L) L c ≠ 0 := fun h0 =>
      hc0 (IsFractionRing.injective (𝓞 L) L (by rw [h0, map_zero]))
    have hmem : (1 : L) ⊗ₜ[𝓞 L] (c • x) ∈
        Submodule.span L (Set.range fun x : 𝒢.omega => (1 : L) ⊗ₜ[𝓞 L] (x : 𝒢.cotangent)) :=
      Submodule.subset_span ⟨⟨c • x, hc⟩, rfl⟩
    have : k ⊗ₜ[𝓞 L] x = (k * (algebraMap (𝓞 L) L c)⁻¹) • ((1 : L) ⊗ₜ[𝓞 L] (c • x)) := by
      rw [TensorProduct.tmul_smul, ← algebraMap_smul L c, smul_smul, mul_assoc,
        inv_mul_cancel₀ hcK, mul_one, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ hmem

/-- **Main result, sharpened.** `HodgeLatticeTheorem` from `OmegaLocal` (finite type) and
`CotangentRank` (the dimension of the tangent space at the origin). -/
theorem hodgeLatticeTheorem_of_local (h1 : OmegaLocal) (h2 : CotangentRank) :
    HodgeLatticeTheorem :=
  hodgeLatticeTheorem_of (omegaFG_of_omegaLocal h1) h2 (omegaSpans_of_omegaLocal h1)

end ZInQ.DefFaltings.HodgeLattice

/-! ## 5. `OmegaLocal` is a theorem (affine charts, stalks as localizations) -/

namespace ZInQ.DefFaltings.HodgeLattice
open NumberField CategoryTheory AlgebraicGeometry Limits MonoidalCategory MonObj

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

local notation "S" => Spec (CommRingCat.of (𝓞 L))

theorem unitSection_comp : 𝒢.unitSection ≫ 𝒢.G.hom = 𝟙 _ := by
  unfold GroupModel.unitSection
  rw [Over.w]
  rfl

/-- `ε(π^* c) = c`, at the level of stalks. -/
theorem stalkMap_structGerm (s : S) (c : 𝓞 L) :
    𝒢.unitSection.stalkMap s (𝒢.G.left.presheaf.germ ⊤ (𝒢.unitSection s) (TopologicalSpace.Opens.mem_top _)
      (𝒢.G.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv c))) =
    (S).presheaf.germ ⊤ s (TopologicalSpace.Opens.mem_top _) ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv c) := by
  rw [Scheme.Hom.germ_stalkMap_apply]
  have h : 𝒢.unitSection.appTop (𝒢.G.hom.appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv c)) =
      (Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv c := by
    have h1 : (Scheme.Hom.appTop (𝒢.unitSection ≫ 𝒢.G.hom)).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv c) =
        (Scheme.Hom.appTop (𝟙 (S))).hom ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv c) := by
      rw [unitSection_comp]
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop] at h1
    exact h1
  exact congrArg _ h

theorem structMap_eq (c : 𝓞 L) : 𝒢.structMap c = 𝒢.G.left.presheaf.germ ⊤ 𝒢.genericUnit
      (TopologicalSpace.Opens.mem_top _)
      (𝒢.G.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv c)) := rfl

theorem isUnit_germ_iff (s : S) (t : 𝓞 L) :
    IsUnit ((S).presheaf.germ ⊤ s (TopologicalSpace.Opens.mem_top _) ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv t)) ↔
      t ∉ (s : PrimeSpectrum (𝓞 L)).asIdeal := by
  rw [← Scheme.mem_basicOpen _ _ _ (TopologicalSpace.Opens.mem_top _),
    AlgebraicGeometry.basicOpen_eq_of_affine]
  rfl

/-- On an affine open, every element of a stalk is a fraction of sections. -/
theorem exists_germ_frac {X : Scheme} {U : X.Opens} (hU : IsAffineOpen U) (x : X) (hx : x ∈ U)
    (f : X.presheaf.stalk x) : ∃ b u : Γ(X, U), IsUnit (X.presheaf.germ U x hx u) ∧
      f * X.presheaf.germ U x hx u = X.presheaf.germ U x hx b := by
  let := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have hl := hU.isLocalization_stalk ⟨x, hx⟩
  obtain ⟨⟨b, u⟩, h⟩ := IsLocalization.surj (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl f
  exact ⟨b, u, IsLocalization.map_units _ u, h⟩

/-- The specialization `𝒪_{𝒢,e(s')} → 𝒪_{𝒢,ξ}`. -/
noncomputable abbrev spec (s' : S) : 𝒢.G.left.presheaf.stalk (𝒢.unitSection s') →+* 𝒢.genStalk :=
  (𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s')).hom

theorem genericPt_specializes (s' : S) : genericPt L ⤳ s' :=
  (PrimeSpectrum.le_iff_specializes (genericPt L) s').mp bot_le

/-- **Residue lemma.** Every germ at `e(s')`, specialized to `ξ`, is congruent modulo `𝔪_ξ` to a
fraction `c/t` with `c, t ∈ 𝓞_L`, `t ∉ s'`. -/
theorem residue (s' : S) (w : 𝒢.G.left.presheaf.stalk (𝒢.unitSection s')) :
    ∃ c t : 𝓞 L, t ∉ (s' : PrimeSpectrum (𝓞 L)).asIdeal ∧
      𝒢.structMap t * spec 𝒢 s' w - 𝒢.structMap c ∈ IsLocalRing.maximalIdeal 𝒢.genStalk := by
  set z := 𝒢.unitSection.stalkMap s' w
  obtain ⟨r, u, hu, hru⟩ := exists_germ_frac (isAffineOpen_top (S)) s'
    (TopologicalSpace.Opens.mem_top _) z
  set iso := Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))
  have hr : iso.inv (iso.hom r) = r := iso.hom_inv_id_apply r
  have hu' : iso.inv (iso.hom u) = u := iso.hom_inv_id_apply u
  refine ⟨iso.hom r, iso.hom u, ?_, ?_⟩
  · rw [← isUnit_germ_iff, hu']; exact hu
  by_contra hnot
  have hunit : IsUnit (𝒢.structMap (iso.hom u) * spec 𝒢 s' w - 𝒢.structMap (iso.hom r)) := by
    by_contra h'
    exact hnot ((IsLocalRing.mem_maximalIdeal _).mpr h')
  let φ : 𝒢.genStalk →+* (S).presheaf.stalk (genericPt L) :=
    (𝒢.unitSection.stalkMap (genericPt L)).hom
  have himg := hunit.map φ
  have hη := genericPt_specializes (L := L) s'
  have hspec : φ (spec 𝒢 s' w) =
      (S).presheaf.stalkSpecializes hη z :=
    Scheme.Hom.stalkSpecializes_stalkMap_apply 𝒢.unitSection (genericPt L) s' hη w
  have hst : ∀ c : 𝓞 L, φ (𝒢.structMap c) =
      (S).presheaf.germ ⊤ (genericPt L) (TopologicalSpace.Opens.mem_top _) (iso.inv c) :=
    fun c => stalkMap_structGerm 𝒢 (genericPt L) c
  rw [map_sub, map_mul, hspec, hst, hst, hr, hu'] at himg
  have hz : (S).presheaf.stalkSpecializes hη z *
      (S).presheaf.germ ⊤ (genericPt L) (TopologicalSpace.Opens.mem_top _) u =
      (S).presheaf.germ ⊤ (genericPt L) (TopologicalSpace.Opens.mem_top _) r := by
    have := congrArg ((S).presheaf.stalkSpecializes hη).hom hru
    rw [map_mul, TopCat.Presheaf.germ_stalkSpecializes_apply,
      TopCat.Presheaf.germ_stalkSpecializes_apply] at this
    exact this
  rw [mul_comm, hz, sub_self] at himg
  exact not_isUnit_zero himg

/-- `c • x` on `cot` is `structMap c • x`. -/
theorem smul_cot_of_congr {y : 𝒢.genStalk} {c t : 𝓞 L}
    (h : 𝒢.structMap t * y - 𝒢.structMap c ∈ IsLocalRing.maximalIdeal 𝒢.genStalk)
    (n : 𝒢.cotangent) : t • (y • n) = c • n := by
  change 𝒢.structMap t • (y • n) = 𝒢.structMap c • n
  rw [smul_smul]
  have : 𝒢.structMap t * y = 𝒢.structMap c + (𝒢.structMap t * y - 𝒢.structMap c) := by ring
  rw [this, add_smul]
  have h0 : (𝒢.structMap t * y - 𝒢.structMap c) • n = 0 :=
    Ideal.Cotangent.smul_eq_zero_of_mem h n
  rw [h0, add_zero]

theorem dCls_add (x y : 𝒢.genStalk) (hx : x ∈ IsLocalRing.maximalIdeal 𝒢.genStalk)
    (hy : y ∈ IsLocalRing.maximalIdeal 𝒢.genStalk)
    (hxy : x + y ∈ IsLocalRing.maximalIdeal 𝒢.genStalk) :
    𝒢.dCls ⟨x + y, hxy⟩ = 𝒢.dCls ⟨x, hx⟩ + 𝒢.dCls ⟨y, hy⟩ :=
  (IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent.map_add ⟨x, hx⟩ ⟨y, hy⟩

theorem dCls_mul (a g : 𝒢.genStalk) (hg : g ∈ IsLocalRing.maximalIdeal 𝒢.genStalk)
    (hag : a * g ∈ IsLocalRing.maximalIdeal 𝒢.genStalk) :
    𝒢.dCls ⟨a * g, hag⟩ = a • 𝒢.dCls ⟨g, hg⟩ :=
  (IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent.map_smul a ⟨g, hg⟩

theorem dCls_zero (h : (0 : 𝒢.genStalk) ∈ IsLocalRing.maximalIdeal 𝒢.genStalk) :
    𝒢.dCls ⟨0, h⟩ = 0 := by
  unfold GroupModel.dCls
  exact (IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent.map_zero

/-- `d g` for a germ `g` (and `0` if `g ∉ 𝔪_ξ`). -/
noncomputable def dOf (g : 𝒢.genStalk) : 𝒢.cotangent := by
  classical
  exact if h : g ∈ IsLocalRing.maximalIdeal 𝒢.genStalk then 𝒢.dCls ⟨g, h⟩ else 0

theorem dOf_eq (g : 𝒢.genStalk) (h : g ∈ IsLocalRing.maximalIdeal 𝒢.genStalk) :
    dOf 𝒢 g = 𝒢.dCls ⟨g, h⟩ := by
  unfold dOf; rw [dif_pos h]

theorem dCls_sum {J : Type*} (T : Finset J) (a g : J → 𝒢.genStalk)
    (hg : ∀ i ∈ T, g i ∈ IsLocalRing.maximalIdeal 𝒢.genStalk)
    (hy : ∑ i ∈ T, a i * g i ∈ IsLocalRing.maximalIdeal 𝒢.genStalk) :
    𝒢.dCls ⟨∑ i ∈ T, a i * g i, hy⟩ = ∑ i ∈ T, a i • dOf 𝒢 (g i) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact dCls_zero 𝒢 _
  | insert j T hj ih =>
    have hgT : ∀ i ∈ T, g i ∈ IsLocalRing.maximalIdeal 𝒢.genStalk :=
      fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hgj := hg j (Finset.mem_insert_self j T)
    have hT : ∑ i ∈ T, a i * g i ∈ IsLocalRing.maximalIdeal 𝒢.genStalk :=
      Ideal.sum_mem _ fun i hi => Ideal.mul_mem_left _ _ (hgT i hi)
    simp only [Finset.sum_insert hj]
    rw [dCls_add 𝒢 _ _ (Ideal.mul_mem_left _ _ hgj) hT, dCls_mul 𝒢 _ _ hgj, ih hgT hT,
      dOf_eq 𝒢 _ hgj]

/-- A regular function `i` on an open `U ∋ e(s')` whose pullback along the unit section vanishes
near `s'` gives an element `d i` of the local lattice `(ω_𝒢)_{s'}`. -/
theorem dCls_mem_omegaAt (U : 𝒢.G.left.Opens) (i : Γ(𝒢.G.left, U))
    (s' : Spec (CommRingCat.of (𝓞 L))) (hs' : 𝒢.unitSection s' ∈ U)
    (h0 : (Spec (CommRingCat.of (𝓞 L))).presheaf.germ (𝒢.unitSection ⁻¹ᵁ U) s' hs'
      (𝒢.unitSection.app U i) = 0)
    (hm : 𝒢.G.left.presheaf.germ U 𝒢.genericUnit
      ((𝒢.specializes_genericUnit s').mem_open U.isOpen hs') i ∈
        IsLocalRing.maximalIdeal 𝒢.genStalk) :
    𝒢.dCls ⟨_, hm⟩ ∈ 𝒢.omegaAt s' := by
  apply Submodule.subset_span
  refine ⟨𝒢.G.left.presheaf.germ U (𝒢.unitSection s') hs' i, ?_, ?_, ?_⟩
  · rw [RingHom.mem_ker, Scheme.Hom.germ_stalkMap_apply]; exact h0
  · rw [TopCat.Presheaf.germ_stalkSpecializes_apply]; exact hm
  · congr 2
    rw [TopCat.Presheaf.germ_stalkSpecializes_apply]

/-- `{x | ∃ t ∉ p, t • x ∈ N}`: the elements of `V` that lie in `N_p`. -/
def locSub {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] (p : Ideal R) [p.IsPrime]
    (N : Submodule R V) : Submodule R V where
  carrier := {x | ∃ t ∉ p, t • x ∈ N}
  add_mem' := by
    rintro x y ⟨t, ht, hx⟩ ⟨u, hu, hy⟩
    refine ⟨t * u, fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim ht hu, ?_⟩
    rw [smul_add]
    refine N.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact N.smul_mem _ hx
    · rw [mul_smul]; exact N.smul_mem _ hy
  zero_mem' := ⟨1, fun h => (‹p.IsPrime›).ne_top ((Ideal.eq_top_iff_one _).mpr h), by simp⟩
  smul_mem' := by
    rintro c x ⟨t, ht, hx⟩
    exact ⟨t, ht, by rw [smul_comm]; exact N.smul_mem _ hx⟩

end ZInQ.DefFaltings.HodgeLattice

namespace ZInQ.DefFaltings.HodgeLattice
open NumberField CategoryTheory AlgebraicGeometry Limits MonoidalCategory MonObj

/-- **`OmegaLocal` holds** (it uses only that `𝒢 → Spec 𝓞_L` is locally of finite type, through
smoothness, and that `e` is a section). -/
theorem omegaLocal : OmegaLocal := by
  intro K _ A L _ _ _ 𝒢 s
  classical
  -- an affine chart `U ∋ e(s)` and a basic open `D(a) ∋ s` with `e(D(a)) ⊆ U`
  obtain ⟨U, hU, hsU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    𝒢.G.left.isBasis_affineOpens) (TopologicalSpace.Opens.mem_top (𝒢.unitSection s))
  obtain ⟨_, ⟨a, rfl⟩, hsa, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (show s ∈ ((𝒢.unitSection ⁻¹ᵁ U : (Spec (CommRingCat.of (𝓞 L))).Opens) :
        Set (Spec (CommRingCat.of (𝓞 L)))) from hsU) (𝒢.unitSection ⁻¹ᵁ U).isOpen
  have hD : ∀ s' : PrimeSpectrum (𝓞 L), a ∉ s'.asIdeal → 𝒢.unitSection s' ∈ U :=
    fun s' h => hsub ((PrimeSpectrum.mem_basicOpen _ _).mpr h)
  have hsa' : a ∉ s.asIdeal := (PrimeSpectrum.mem_basicOpen _ _).mp hsa
  -- `Γ(U)` is noetherian; `I = ker(e^* : Γ(U) → Γ(e⁻¹U))` is finitely generated
  have : IsLocallyNoetherian 𝒢.G.left := LocallyOfFiniteType.isLocallyNoetherian 𝒢.G.hom
  have : IsNoetherianRing Γ(𝒢.G.left, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  set I : Ideal Γ(𝒢.G.left, U) := RingHom.ker (𝒢.unitSection.app U).hom with hIdef
  obtain ⟨T, hT⟩ : I.FG := IsNoetherian.noetherian I
  have hTI : ∀ i ∈ T, i ∈ I := fun i hi => hT ▸ Submodule.subset_span hi
  have hξU : 𝒢.genericUnit ∈ U := (𝒢.specializes_genericUnit s).mem_open U.isOpen hsU
  set gξ := 𝒢.G.left.presheaf.germ U 𝒢.genericUnit hξU
  have hmI : ∀ i ∈ I, gξ i ∈ IsLocalRing.maximalIdeal 𝒢.genStalk := by
    intro i hi
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    let φ : 𝒢.genStalk →+* (Spec (CommRingCat.of (𝓞 L))).presheaf.stalk (genericPt L) :=
      (𝒢.unitSection.stalkMap (genericPt L)).hom
    have h1 := hunit.map φ
    have h0 : φ (gξ i) = 0 :=
      (Scheme.Hom.germ_stalkMap_apply 𝒢.unitSection U (genericPt L) hξU i).trans
        (by rw [RingHom.mem_ker.mp hi, map_zero])
    rw [h0] at h1
    exact not_isUnit_zero h1
  set N : Submodule (𝓞 L) 𝒢.cotangent :=
    Submodule.span (𝓞 L) ((fun i => dOf 𝒢 (gξ i)) '' (T : Set Γ(𝒢.G.left, U))) with hNdef
  have hNfg : N.FG := ⟨T.image fun i => dOf 𝒢 (gξ i), by rw [Finset.coe_image]⟩
  -- (C): the stalks `(ω_𝒢)_{s'}` lie in `N_{s'}`
  have hC : ∀ s' : PrimeSpectrum (𝓞 L), a ∉ s'.asIdeal →
      𝒢.omegaAt s' ≤ locSub s'.asIdeal N := by
    intro s' hs'
    have hs'U := hD s' hs'
    unfold GroupModel.omegaAt
    rw [Submodule.span_le]
    rintro _ ⟨f, hf, hfm, rfl⟩
    obtain ⟨b, u, hu, hfu⟩ := exists_germ_frac hU (𝒢.unitSection s') hs'U f
    have hb : b ∈ I := by
      rw [RingHom.mem_ker]
      have h1 : (𝒢.unitSection.stalkMap s').hom
          (𝒢.G.left.presheaf.germ U (𝒢.unitSection s') hs'U b) = 0 := by
        rw [← hfu, map_mul, RingHom.mem_ker.mp hf, zero_mul]
      have h2 := (Scheme.Hom.germ_stalkMap_apply 𝒢.unitSection U
        (show Spec (CommRingCat.of (𝓞 L)) from s') hs'U b).symm.trans h1
      exact germ_injective_of_isIntegral (Spec (CommRingCat.of (𝓞 L))) _ hs'U
        (h2.trans (map_zero _).symm)
    rw [← hT] at hb
    obtain ⟨r, -, hr⟩ := Submodule.mem_span_finset.mp hb
    set v := hu.unit⁻¹
    have hf' : f = 𝒢.G.left.presheaf.germ U (𝒢.unitSection s') hs'U b * ↑v := by
      rw [← hfu, _root_.mul_assoc, IsUnit.mul_val_inv, _root_.mul_one]
    set w : Γ(𝒢.G.left, U) → 𝒢.G.left.presheaf.stalk (𝒢.unitSection s') := fun i =>
      𝒢.G.left.presheaf.germ U (𝒢.unitSection s') hs'U (r i) * ↑v
    have hsf : spec 𝒢 s' f = ∑ i ∈ T, spec 𝒢 s' (w i) * gξ i := by
      rw [hf', ← hr, map_sum, Finset.sum_mul, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [w, smul_eq_mul, map_mul, spec, TopCat.Presheaf.germ_stalkSpecializes_apply]
      ring
    choose c t ht hct using fun i => residue 𝒢 s' (w i)
    refine ⟨∏ i ∈ T, t i, ?_, ?_⟩
    · intro hmem
      obtain ⟨i, -, hi⟩ := (Ideal.IsPrime.prod_mem_iff).mp hmem
      exact ht i hi
    · have hsum : ∑ i ∈ T, spec 𝒢 s' (w i) * gξ i ∈ IsLocalRing.maximalIdeal 𝒢.genStalk :=
        hsf ▸ hfm
      have he : (⟨spec 𝒢 s' f, hfm⟩ : IsLocalRing.maximalIdeal 𝒢.genStalk) =
          ⟨∑ i ∈ T, spec 𝒢 s' (w i) * gξ i, hsum⟩ := Subtype.ext hsf
      change (∏ i ∈ T, t i) • 𝒢.dCls ⟨spec 𝒢 s' f, hfm⟩ ∈ N
      rw [he, dCls_sum 𝒢 T _ _ (fun i hi => hmI i (hTI i hi)), Finset.smul_sum]
      refine Submodule.sum_mem _ fun i hi => ?_
      rw [← Finset.mul_prod_erase T t hi, mul_comm, mul_smul, smul_cot_of_congr 𝒢 (hct i)]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩))
  refine ⟨a, hsa', N, hNfg, ?_, fun s' hs' => ⟨?_, fun x hx => hC s' hs' hx⟩⟩
  · intro x
    have ha0 : a ∉ (genericPt L : PrimeSpectrum (𝓞 L)).asIdeal := by
      intro h
      have : a = 0 := h
      exact hsa' (this ▸ Ideal.zero_mem _)
    have hx : x ∈ 𝒢.omegaAt (genericPt L) := by rw [𝒢.omegaAt_genericPt]; trivial
    obtain ⟨t, ht, htx⟩ := hC (genericPt L) ha0 hx
    exact ⟨t, fun h0 => ht (h0 ▸ Ideal.zero_mem _), htx⟩
  · rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    have hiI := hTI i hi
    have h := dCls_mem_omegaAt 𝒢 U i s' (hD s' hs')
      (by rw [RingHom.mem_ker.mp hiI, map_zero]) (hmI i hiI)
    have e := dOf_eq 𝒢 _ (hmI i hiI)
    exact (congrArg (· ∈ 𝒢.omegaAt s') e).mpr h

end ZInQ.DefFaltings.HodgeLattice


namespace ZInQ.DefFaltings.HodgeLattice

/-- **Main result.** `HodgeLatticeTheorem` follows from `CotangentRank` alone. -/
theorem hodgeLatticeTheorem_of_cotangentRank (h : CotangentRank) : HodgeLatticeTheorem :=
  hodgeLatticeTheorem_of_local omegaLocal h

end ZInQ.DefFaltings.HodgeLattice

/-! ## 6. `CotangentRank` from the regularity and the dimension of `𝒪_{𝒢,ξ}`

The residue field `κ(ξ)` of `𝒪_{𝒢,ξ}` is a fraction field of `𝓞_L` (through `structMap`; the
residue lemma of §5 at the generic point), so `L ⊗_{𝓞_L} 𝔪_ξ/𝔪_ξ² ≅ 𝔪_ξ/𝔪_ξ²` has `L`-rank the
`κ(ξ)`-dimension of the cotangent space (`rank_tensor_cotangent`). With Mathlib's
`IsRegularLocalRing.iff_finrank_cotangentSpace` this reduces `CotangentRank` to two statements
about the local ring `𝒪_{𝒢,ξ} = 𝒪_{A_L,0}`: it is regular (`RegularOrigin`) and has Krull
dimension `dim A` (`DimOrigin`). -/

namespace ZInQ.DefFaltings.HodgeLattice
open NumberField CategoryTheory AlgebraicGeometry TensorProduct

/-- **(G2')** The tangent space of `A_L` at the origin has dimension `dim A` over `κ(ξ)`. -/
def TangentDim : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (g : ℕ), A.dim = g →
    Module.finrank (IsLocalRing.ResidueField 𝒢.genStalk)
      (IsLocalRing.CotangentSpace 𝒢.genStalk) = g

/-- **(G2a)** `𝒪_{𝒢,ξ}` (`= 𝒪_{A_L,0}`) is a regular local ring. -/
def RegularOrigin : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L), IsRegularLocalRing 𝒢.genStalk

/-- **(G2b)** `𝒪_{𝒢,ξ}` (`= 𝒪_{A_L,0}`) has Krull dimension `dim A`. -/
def DimOrigin : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (g : ℕ), A.dim = g → ringKrullDim 𝒢.genStalk = g

section Tangent

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

theorem isUnit_structMap {c : 𝓞 L} (hc : c ≠ 0) : IsUnit (𝒢.structMap c) := by
  have hfield : IsField ((Spec (CommRingCat.of (𝓞 L))).presheaf.stalk (genericPt L)) := by
    have : genericPt L = genericPoint (Spec (CommRingCat.of (𝓞 L))) :=
      (genericPoint_eq_bot_of_affine (CommRingCat.of (𝓞 L))).symm
    rw [this]; exact Field.toIsField _
  let φ : 𝒢.genStalk →+* (Spec (CommRingCat.of (𝓞 L))).presheaf.stalk (genericPt L) :=
    (𝒢.unitSection.stalkMap (genericPt L)).hom
  haveI : IsLocalHom φ := inferInstanceAs (IsLocalHom (𝒢.unitSection.stalkMap (genericPt L)).hom)
  have hφ : φ (𝒢.structMap c) = (Spec (CommRingCat.of (𝓞 L))).presheaf.germ ⊤ (genericPt L)
      (TopologicalSpace.Opens.mem_top _) ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv c) :=
    stalkMap_structGerm 𝒢 (genericPt L) c
  have hne : φ (𝒢.structMap c) ≠ 0 := by
    rw [hφ]; intro h0
    have h1 : (Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv c = 0 :=
      germ_injective_of_isIntegral (Spec (CommRingCat.of (𝓞 L))) (genericPt L)
        (TopologicalSpace.Opens.mem_top _) (h0.trans (map_zero _).symm)
    apply hc
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).hom h1
    rwa [Iso.inv_hom_id_apply, map_zero] at this
  obtain ⟨b, hb⟩ := hfield.mul_inv_cancel hne
  exact isUnit_of_map_unit φ _ (isUnit_iff_exists_inv.mpr ⟨b, hb⟩)

theorem spec_genericPt (y : 𝒢.genStalk) : spec 𝒢 (genericPt L) y = y := by
  show (𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit (genericPt L))).hom y = y
  rw [show 𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit (genericPt L)) =
    𝟙 _ from TopCat.Presheaf.stalkSpecializes_refl _ _]
  rfl

/-- `rank_L (L ⊗_{𝓞_L} 𝔪_ξ/𝔪_ξ²) = rank_{κ(ξ)} (𝔪_ξ/𝔪_ξ²)`. -/
theorem rank_tensor_cotangent :
    Module.rank L (L ⊗[𝓞 L] 𝒢.cotangent) =
      Module.rank (IsLocalRing.ResidueField 𝒢.genStalk) (IsLocalRing.CotangentSpace 𝒢.genStalk) := by
  classical
  set κ := IsLocalRing.ResidueField 𝒢.genStalk
  set ψ : 𝓞 L →+* κ := (IsLocalRing.residue 𝒢.genStalk).comp 𝒢.structMap with hψ
  have hψ0 : ∀ c : 𝓞 L, c ≠ 0 → ψ c ≠ 0 := fun c hc =>
    (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr (isUnit_structMap 𝒢 hc)
  let _ : Algebra (𝓞 L) κ := ψ.toAlgebra
  have halg : ∀ c, algebraMap (𝓞 L) κ c = ψ c := fun _ => rfl
  have : IsFractionRing (𝓞 L) κ := by
    refine (isLocalization_iff (nonZeroDivisors (𝓞 L)) κ).mpr ⟨fun y => ?_, fun z => ?_, fun {x y} h => ?_⟩
    · rw [halg]; exact (hψ0 _ (nonZeroDivisors.ne_zero y.2)).isUnit
    · obtain ⟨w, rfl⟩ := IsLocalRing.residue_surjective z
      obtain ⟨c, t, ht, hct⟩ := residue 𝒢 (genericPt L) w
      have ht0 : t ≠ 0 := fun h => ht (h ▸ Ideal.zero_mem _)
      refine ⟨(c, ⟨t, mem_nonZeroDivisors_of_ne_zero ht0⟩), ?_⟩
      rw [spec_genericPt] at hct
      have h0 := (IsLocalRing.residue_eq_zero_iff _).mpr hct
      rw [map_sub, map_mul] at h0
      simp only [halg, hψ, RingHom.comp_apply]
      linear_combination h0
    · refine ⟨1, ?_⟩
      have h0 : ψ (x - y) = 0 := by rw [map_sub, ← halg, ← halg, h, sub_self]
      by_cases hxy : x - y = 0
      · simp [sub_eq_zero.mp hxy]
      · exact absurd h0 (hψ0 _ hxy)
  set e : L ≃ₐ[𝓞 L] κ := IsLocalization.algEquiv (nonZeroDivisors (𝓞 L)) L κ
  let _ : Module L 𝒢.cotangent := (Module.compHom (IsLocalRing.CotangentSpace 𝒢.genStalk)
    e.toRingHom : Module L (IsLocalRing.CotangentSpace 𝒢.genStalk))
  have key : ∀ (r : 𝒢.genStalk) (n : IsLocalRing.CotangentSpace 𝒢.genStalk),
      (algebraMap 𝒢.genStalk κ r) • n = r • n := fun r n => algebraMap_smul κ r n
  have : IsScalarTower (𝓞 L) L 𝒢.cotangent :=
      ⟨fun c l (n : IsLocalRing.CotangentSpace 𝒢.genStalk) => by
    change (e (c • l)) • n = 𝒢.structMap c • ((e l) • n)
    rw [map_smul, Algebra.smul_def, halg, mul_smul]
    exact key _ _⟩
  have hloc : IsLocalizedModule (nonZeroDivisors (𝓞 L))
      (LinearMap.id : 𝒢.cotangent →ₗ[𝓞 L] 𝒢.cotangent) := isLocalizedModule_id _ _ L
  have hbc : IsBaseChange L (LinearMap.id : 𝒢.cotangent →ₗ[𝓞 L] 𝒢.cotangent) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors (𝓞 L)) L _).mp hloc
  rw [hbc.equiv.rank_eq]
  exact rank_eq_of_equiv_equiv e
    (AddEquiv.refl 𝒢.cotangent : 𝒢.cotangent ≃+ IsLocalRing.CotangentSpace 𝒢.genStalk)
    e.bijective (fun l n => rfl)

end Tangent

theorem cotangentRank_of_tangentDim (h : TangentDim) : CotangentRank := by
  intro K _ A L _ _ _ 𝒢 g hg
  rw [rank_tensor_cotangent 𝒢]
  haveI : IsLocallyNoetherian 𝒢.G.left := LocallyOfFiniteType.isLocallyNoetherian 𝒢.G.hom
  rw [← Module.finrank_eq_rank, h K A L 𝒢 g hg]

theorem tangentDim_of_regular (h1 : RegularOrigin) (h2 : DimOrigin) : TangentDim := by
  intro K _ A L _ _ _ 𝒢 g hg
  haveI : IsLocallyNoetherian 𝒢.G.left := LocallyOfFiniteType.isLocallyNoetherian 𝒢.G.hom
  have := (IsRegularLocalRing.iff_finrank_cotangentSpace 𝒢.genStalk).mp (h1 K A L 𝒢)
  rw [h2 K A L 𝒢 g hg] at this
  exact_mod_cast this

/-- **Main result, final form.** `HodgeLatticeTheorem` follows from the two statements on the
local ring `𝒪_{𝒢,ξ} = 𝒪_{A_L,0}`: it is regular, of Krull dimension `dim A`. -/
theorem hodgeLatticeTheorem_of_regular (h1 : RegularOrigin) (h2 : DimOrigin) :
    HodgeLatticeTheorem :=
  hodgeLatticeTheorem_of_cotangentRank (cotangentRank_of_tangentDim (tangentDim_of_regular h1 h2))

end ZInQ.DefFaltings.HodgeLattice

/-! ## 7. Corollary: `ω_𝒢` and `⋀^g ω_𝒢` are lattices, and `L ⊗ ⋀^g ω_𝒢 → hodgeSpace g` is onto

(Projectivity of the rank-one `𝓞_L`-module `detLattice g` then follows from: finitely generated and
torsion-free over a Dedekind domain; STANDARD, not in Mathlib in this form.) -/

namespace ZInQ.DefFaltings.HodgeLattice
open NumberField TensorProduct

theorem detLat_fg {K : Type*} [Field K] [NumberField K] {M : Type*} [AddCommGroup M]
    [Module (𝓞 K) M] (ω : Submodule (𝓞 K) M) (hfg : ω.FG) (g : ℕ) : (detLat ω g).FG := by
  have : Module.Finite (𝓞 K) ω := Module.Finite.iff_fg.mpr hfg
  have hRfg : (LinearMap.range ((TensorProduct.mk (𝓞 K) K (⋀[𝓞 K]^g M) 1) ∘ₗ
      exteriorPower.map g ω.subtype)).FG := by
    rw [LinearMap.range_eq_map]; exact (Module.Finite.fg_top).map _
  refine Submodule.FG.of_le hRfg ?_
  rw [detLat, Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  exact ⟨exteriorPower.ιMulti (𝓞 K) g v, by simp [exteriorPower.map_apply_ιMulti]; rfl⟩

/-- Under `RegularOrigin` and `DimOrigin`: `ω_𝒢` and `detLattice g` are finitely generated, and
`detLattice g` spans the Hodge line over `L`. -/
theorem hodgeLattice_lattice_of_regular (h1 : RegularOrigin) (h2 : DimOrigin)
    (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (g : ℕ) (hg : A.dim = g) :
    𝒢.omega.FG ∧ (𝒢.detLattice g).FG ∧
      Submodule.span L (𝒢.detLattice g : Set (𝒢.hodgeSpace g)) = ⊤ := by
  have hfg := omegaFG_of_omegaLocal omegaLocal K A L 𝒢
  refine ⟨hfg, by rw [detLattice_eq]; exact detLat_fg _ hfg g, ?_⟩
  obtain ⟨hrank, s, hs, hs0, -⟩ := hodgeLatticeTheorem_of_regular h1 h2 K A L 𝒢 g hg
  rw [eq_top_iff]
  intro w _
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' s hs0).mp hrank w
  exact Submodule.smul_mem _ c (Submodule.subset_span hs)

end ZInQ.DefFaltings.HodgeLattice

/-! ## 8. The remaining inputs, stated over abelian varieties

`RegularOrigin` and `DimOrigin` concern the model `𝒢`. Both follow from statements about the
abelian variety `B = A_L` over the field `L` alone, plus one scheme-theoretic identification
(`OriginStalkIso`: the local ring of `𝒢` at the identity `ξ` of its generic fibre is the local ring
of `A_L` at its origin; true because `Spec L → Spec 𝓞_L` is a localization and `𝒢.gen` is an
isomorphism of group schemes). -/

namespace ZInQ.DefFaltings.HodgeLattice
open NumberField CategoryTheory AlgebraicGeometry MonoidalCategory MonObj

/-- The origin `0 ∈ B` of an abelian variety over a field `L` (image of the point of `Spec L`
under the unit section). -/
noncomputable def originPt {L : Type} [Field L] (B : AbVar L) : B.X.left :=
  (η[B.X] : 𝟙_ (Over (Spec (CommRingCat.of L))) ⟶ B.X).left
    (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum L)

/-- **(S)** `𝒪_{𝒢,ξ} ≅ 𝒪_{A_L,0}`. -/
def OriginStalkIso : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L),
    Nonempty (𝒢.genStalk ≃+* (A.baseChange L).X.left.presheaf.stalk (originPt (A.baseChange L)))

/-- **(V1)** The local ring of an abelian variety at its origin is regular (a smooth variety is
regular). -/
def RegularAtOrigin : Prop :=
  ∀ (L : Type) [Field L] (B : AbVar L), IsRegularLocalRing (B.X.left.presheaf.stalk (originPt B))

/-- **(V2)** The local ring of an abelian variety of dimension `g` at its origin has Krull dimension
`g` (the local ring of an irreducible variety at a closed point has dimension `dim`). -/
def DimAtOrigin : Prop :=
  ∀ (L : Type) [Field L] (B : AbVar L) (g : ℕ), B.dim = g →
    ringKrullDim (B.X.left.presheaf.stalk (originPt B)) = g

/-- **(V3)** Dimension is invariant under extension of the base field. -/
def DimBaseChange : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [Algebra K L],
    (A.baseChange L).dim = A.dim

theorem regularOrigin_of (h0 : OriginStalkIso) (h1 : RegularAtOrigin) : RegularOrigin := by
  intro K _ A L _ _ _ 𝒢
  obtain ⟨e⟩ := h0 K A L 𝒢
  haveI := h1 L (A.baseChange L)
  exact IsRegularLocalRing.of_ringEquiv e.symm

theorem dimOrigin_of (h0 : OriginStalkIso) (h2 : DimAtOrigin) (h3 : DimBaseChange) :
    DimOrigin := by
  intro K _ A L _ _ _ 𝒢 g hg
  obtain ⟨e⟩ := h0 K A L 𝒢
  rw [ringKrullDim_eq_of_ringEquiv e]
  exact h2 L (A.baseChange L) g ((h3 K A L).trans hg)

/-- **Main result, over abelian varieties.** -/
theorem hodgeLatticeTheorem_of_abVar (h0 : OriginStalkIso) (h1 : RegularAtOrigin)
    (h2 : DimAtOrigin) (h3 : DimBaseChange) : HodgeLatticeTheorem :=
  hodgeLatticeTheorem_of_regular (regularOrigin_of h0 h1) (dimOrigin_of h0 h2 h3)

end ZInQ.DefFaltings.HodgeLattice

/-! ## 9. `OriginStalkIso` from the local rings of the generic fibre

`p : 𝒢_L = 𝒢 ×_{𝓞_L} L → 𝒢` sends the identity `ξ_L` of `𝒢_L` to `ξ` (`fst_genericFibreUnit`, from
`η_{𝒢_L} = ε ≫ (pullback).map η_𝒢` and `Over.w ε`), and `𝒢.gen` sends `ξ_L` to the origin of
`A_L` (`gen_genericFibreUnit`, from `IsMonHom.one_hom`). So `OriginStalkIso` follows from
`GenericFibreStalkIso`: `p` induces isomorphisms on local rings (true for any scheme over `𝓞_L`,
since `Spec L → Spec 𝓞_L` is a localization). -/

namespace ZInQ.DefFaltings.HodgeLattice
open NumberField CategoryTheory AlgebraicGeometry Limits MonoidalCategory MonObj

/-- `Spec L → Spec 𝓞_L`. -/
noncomputable abbrev toGeneric (L : Type) [Field L] [NumberField L] :
    Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of (𝓞 L)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L))

/-- **(S')** The projection `X_L = X ×_{𝓞_L} L → X` induces isomorphisms on local rings. -/
def GenericFibreStalkIso : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (X : Over (Spec (CommRingCat.of (𝓞 L))))
    (x : (genericFibre L X).left), IsIso ((pullback.fst X.hom (toGeneric L)).stalkMap x)

section
variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

theorem fst_genericFibre_unit :
    letI : GrpObj (genericFibre L 𝒢.G) := Functor.grpObjObj
    (η[genericFibre L 𝒢.G] : 𝟙_ _ ⟶ genericFibre L 𝒢.G).left ≫
      pullback.fst 𝒢.G.hom (toGeneric L) = toGeneric L ≫ 𝒢.unitSection := by
  let _ : GrpObj (genericFibre L 𝒢.G) := Functor.grpObjObj
  change (Functor.LaxMonoidal.ε (Over.pullback (toGeneric L)) ≫
    (Over.pullback (toGeneric L)).map η[𝒢.G]).left ≫ pullback.fst 𝒢.G.hom (toGeneric L) = _
  rw [Over.comp_left, Category.assoc]
  have h1 : ((Over.pullback (toGeneric L)).map η[𝒢.G]).left ≫
      pullback.fst 𝒢.G.hom (toGeneric L) =
      pullback.fst _ (toGeneric L) ≫ (η[𝒢.G] : 𝟙_ _ ⟶ 𝒢.G).left := by
    simp
  rw [h1, ← Category.assoc]
  have h2 : (Functor.LaxMonoidal.ε (Over.pullback (toGeneric L))).left ≫
      pullback.snd ((𝟙_ (Over (Spec (CommRingCat.of (𝓞 L))))).hom) (toGeneric L) = 𝟙 _ :=
    Over.w (Functor.LaxMonoidal.ε (Over.pullback (toGeneric L)))
  have hc := pullback.condition (f := (𝟙_ (Over (Spec (CommRingCat.of (𝓞 L))))).hom)
    (g := toGeneric L)
  have hc' : pullback.fst ((𝟙_ (Over (Spec (CommRingCat.of (𝓞 L))))).hom) (toGeneric L) =
      pullback.snd _ _ ≫ toGeneric L := by
    rw [← hc]; exact (Category.comp_id _).symm
  rw [hc', ← Category.assoc, h2, Category.id_comp]
  rfl

omit [NumberField L] in
theorem toGeneric_pt [NumberField L] :
    (toGeneric L) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum L) = genericPt L := by
  change PrimeSpectrum.comap (algebraMap (𝓞 L) L) ⟨⊥, Ideal.isPrime_bot⟩ = _
  refine PrimeSpectrum.ext (Ideal.ext fun x => ?_)
  simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, Ideal.mem_bot, genericPt]
  exact map_eq_zero_iff _ (IsFractionRing.injective (𝓞 L) L)

/-- The identity `ξ_L` of the generic fibre. -/
noncomputable def genericFibreUnit : (genericFibre L 𝒢.G).left :=
  letI : GrpObj (genericFibre L 𝒢.G) := Functor.grpObjObj
  (η[genericFibre L 𝒢.G] : 𝟙_ _ ⟶ genericFibre L 𝒢.G).left
    (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum L)

theorem fst_genericFibreUnit :
    pullback.fst 𝒢.G.hom (toGeneric L) (genericFibreUnit 𝒢) = 𝒢.genericUnit := by
  have h := congrArg (fun φ => φ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum L))
    (fst_genericFibre_unit 𝒢)
  exact ((Scheme.Hom.comp_apply _ _ _).symm.trans h).trans
    ((Scheme.Hom.comp_apply _ _ _).trans (congrArg (fun y => 𝒢.unitSection y) (toGeneric_pt (L := L))))

theorem gen_genericFibreUnit :
    𝒢.gen.hom.left (genericFibreUnit 𝒢) = originPt (A.baseChange L) := by
  letI : GrpObj (genericFibre L 𝒢.G) := Functor.grpObjObj
  haveI := 𝒢.gen_hom
  have h := congrArg (fun φ : (𝟙_ _ ⟶ (A.baseChange L).X) =>
    φ.left (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum L)) (IsMonHom.one_hom (f := 𝒢.gen.hom))
  simp only [Over.comp_left] at h
  exact (Scheme.Hom.comp_apply _ _ _).symm.trans h

end

theorem originStalkIso_of (h : GenericFibreStalkIso) : OriginStalkIso := by
  intro K _ A L _ _ _ 𝒢
  have hp : IsIso ((pullback.fst 𝒢.G.hom (toGeneric L)).stalkMap (genericFibreUnit 𝒢)) :=
    h L 𝒢.G _
  have hφ : IsOpenImmersion ((Over.forget _).mapIso 𝒢.gen).hom := inferInstance
  have hφs : IsIso (((Over.forget _).mapIso 𝒢.gen).hom.stalkMap (genericFibreUnit 𝒢)) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp hφ).2 _
  let e1 : 𝒢.genStalk ≅ (genericFibre L 𝒢.G).left.presheaf.stalk (genericFibreUnit 𝒢) :=
    𝒢.G.left.presheaf.stalkCongr (Inseparable.of_eq (fst_genericFibreUnit 𝒢).symm) ≪≫
      @asIso _ _ _ _ _ hp
  let e2 : (A.baseChange L).X.left.presheaf.stalk (originPt (A.baseChange L)) ≅
      (genericFibre L 𝒢.G).left.presheaf.stalk (genericFibreUnit 𝒢) :=
    (A.baseChange L).X.left.presheaf.stalkCongr
      (Inseparable.of_eq (gen_genericFibreUnit 𝒢).symm) ≪≫ @asIso _ _ _ _ _ hφs
  exact ⟨(e1 ≪≫ e2.symm).commRingCatIsoToRingEquiv⟩

/-- **Main result, final form.** `HodgeLatticeTheorem` from one scheme-theoretic fact (local rings of
the generic fibre) and three facts about abelian varieties over a field. -/
theorem hodgeLatticeTheorem_of_varieties (h0 : GenericFibreStalkIso) (h1 : RegularAtOrigin)
    (h2 : DimAtOrigin) (h3 : DimBaseChange) : HodgeLatticeTheorem :=
  hodgeLatticeTheorem_of_abVar (originStalkIso_of h0) h1 h2 h3

end ZInQ.DefFaltings.HodgeLattice


/-! ## 10. `GenericFibreStalkIso` is a theorem

"All stalk maps bijective" is Zariski-local on the target (Mathlib's
`stalkwiseIsZariskiLocalAtTarget_of_respectsIso`); over an affine chart `Spec A → X` the projection
is, up to the pasting isomorphisms, `Spec (A ⊗_{𝓞_L} L) → Spec A` (`pullbackSpecIso`), and
`A ⊗_{𝓞_L} L` is the localization of `A` at the image of `𝓞_L ∖ 0` (`IsLocalization.tensor`), whose
stalk maps are isomorphisms (`isIso_specMap_stalkMap_localization`). -/

namespace ZInQ.DefFaltings.HodgeLattice
open NumberField CategoryTheory AlgebraicGeometry Limits TensorProduct

/-- Bijectivity of ring maps respects isomorphisms. -/
theorem bijective_respectsIso :
    RingHom.RespectsIso (fun {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) =>
      Function.Bijective f) :=
  ⟨fun f e hf => e.bijective.comp hf, fun f e hf => hf.comp e.bijective⟩

local notation "Pb" => stalkwise (fun {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) =>
      Function.Bijective f)

/-- `Spec (A ⊗_R K) → Spec A` has bijective stalk maps when `K` is a localization of `R`. -/
theorem stalkwise_tensor_localization (R : Type) [CommRing R] (K : Type) [CommRing K]
    [Algebra R K] (M : Submonoid R) [IsLocalization M K] (A : Type) [CommRing A] [Algebra R A] :
    Pb (Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[R] K)))) := by
  have := stalkwise_respectsIso bijective_respectsIso
  set M' := Algebra.algebraMapSubmonoid A M
  let e : A ⊗[R] K ≃ₐ[A] Localization M' := IsLocalization.algEquiv M' _ _
  have hfac : CommRingCat.ofHom (algebraMap A (A ⊗[R] K)) =
      CommRingCat.ofHom (algebraMap A (Localization M')) ≫
        CommRingCat.ofHom e.symm.toAlgHom.toRingHom := by
    ext a
    simp
  have : IsIso (CommRingCat.ofHom e.symm.toAlgHom.toRingHom) :=
    ⟨⟨CommRingCat.ofHom e.toAlgHom.toRingHom,
      CommRingCat.hom_ext (RingHom.ext fun y => e.apply_symm_apply y),
      CommRingCat.hom_ext (RingHom.ext fun y => e.symm_apply_apply y)⟩⟩
  rw [hfac, Spec.map_comp]
  refine (MorphismProperty.cancel_left_of_respectsIso _ _ _).mpr ?_
  intro x
  have h := isIso_specMap_stalkMap_localization (CommRingCat.of A) M' x
  exact (ConcreteCategory.isIso_iff_bijective _).mp h

/-- On an affine chart: `Spec A ×_{𝓞_L} Spec L → Spec A` has bijective stalk maps. -/
theorem stalkwise_fst_toGeneric {L : Type} [Field L] [NumberField L] {A : CommRingCat}
    (g : Spec A ⟶ Spec (CommRingCat.of (𝓞 L))) : (Pb) (pullback.fst g (toGeneric L)) := by
  have : (Pb).RespectsIso := stalkwise_respectsIso bijective_respectsIso
  let φ := Spec.preimage g
  letI : Algebra (𝓞 L) A := φ.hom.toAlgebra
  have hg : g = Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) A)) := by
    rw [← Spec.map_preimage g]; rfl
  have he2 : (pullback.congrHom hg rfl).hom ≫ pullback.fst _ _ = pullback.fst g (toGeneric L) := by
    simp [pullback.congrHom]
  rw [← he2]
  refine (MorphismProperty.cancel_left_of_respectsIso _ _ _).mpr ?_
  rw [← pullbackSpecIso_hom_fst' (𝓞 L) A L]
  refine (MorphismProperty.cancel_left_of_respectsIso _ _ _).mpr ?_
  exact stalkwise_tensor_localization (𝓞 L) L (nonZeroDivisors (𝓞 L)) A

/-- **`GenericFibreStalkIso` holds**: base change along `Spec L → Spec 𝓞_L` does not change local
rings (Zariski-local on the target; on an affine chart it is `Spec (A ⊗_{𝓞_L} L) → Spec A`, a
localization). -/
theorem genericFibreStalkIso : GenericFibreStalkIso := by
  intro L _ _ X x
  have : (Pb).RespectsIso := stalkwise_respectsIso bijective_respectsIso
  have : IsZariskiLocalAtTarget (Pb) :=
    stalkwiseIsZariskiLocalAtTarget_of_respectsIso bijective_respectsIso
  suffices H : (Pb) (pullback.fst X.hom (toGeneric L)) from
    (ConcreteCategory.isIso_iff_bijective _).mpr (H x)
  refine IsZariskiLocalAtTarget.of_openCover X.left.affineOpenCover.openCover ?_
  intro i
  show (Pb) (pullback.snd (pullback.fst X.hom (toGeneric L)) (X.left.affineOpenCover.f i))
  have he : (pullbackSymmetry (pullback.fst X.hom (toGeneric L)) (X.left.affineOpenCover.f i) ≪≫
      pullbackRightPullbackFstIso X.hom (toGeneric L) (X.left.affineOpenCover.f i)).hom ≫
        pullback.fst (X.left.affineOpenCover.f i ≫ X.hom) (toGeneric L) =
      pullback.snd (pullback.fst X.hom (toGeneric L)) (X.left.affineOpenCover.f i) := by
    simp
  rw [← he]
  refine (MorphismProperty.cancel_left_of_respectsIso _ _ _).mpr ?_
  exact stalkwise_fst_toGeneric _

/-- **Main result, final form.** `HodgeLatticeTheorem` from three facts about abelian varieties over
a field: the local ring at the origin is regular, of Krull dimension `dim B`, and dimension is
invariant under field extension. -/
theorem hodgeLatticeTheorem_of_abVarFacts (h1 : RegularAtOrigin) (h2 : DimAtOrigin)
    (h3 : DimBaseChange) : HodgeLatticeTheorem :=
  hodgeLatticeTheorem_of_varieties genericFibreStalkIso h1 h2 h3

end ZInQ.DefFaltings.HodgeLattice


/-! ## 11. Two facts suffice: the tangent space at the origin, and base change of dimension

`RegularAtOrigin` and `DimAtOrigin` are used only through their consequence `TangentDimAtOrigin`
(the cotangent space at the origin has dimension `dim B`), which is itself a standard fact. -/

namespace ZInQ.DefFaltings.HodgeLattice
open NumberField CategoryTheory AlgebraicGeometry IsLocalRing

/-- **(V)** The tangent space of an abelian variety `B/L` at the origin has dimension `dim B`. -/
def TangentDimAtOrigin : Prop :=
  ∀ (L : Type) [Field L] (B : AbVar L) (g : ℕ), B.dim = g →
    Module.finrank (ResidueField (B.X.left.presheaf.stalk (originPt B)))
      (CotangentSpace (B.X.left.presheaf.stalk (originPt B))) = g

theorem tangentDimAtOrigin_of (h1 : RegularAtOrigin) (h2 : DimAtOrigin) : TangentDimAtOrigin := by
  intro L _ B g hg
  haveI := h1 L B
  have := (IsRegularLocalRing.iff_finrank_cotangentSpace _).mp this
  rw [h2 L B g hg] at this
  exact_mod_cast this

theorem tangentDim_of_abVar (h1 : TangentDimAtOrigin) (h3 : DimBaseChange) : TangentDim := by
  intro K _ A L _ _ _ 𝒢 g hg
  obtain ⟨e⟩ := originStalkIso_of genericFibreStalkIso K A L 𝒢
  have h := h1 L (A.baseChange L) g ((h3 K A L).trans hg)
  haveI : IsLocallyNoetherian 𝒢.G.left := LocallyOfFiniteType.isLocallyNoetherian 𝒢.G.hom
  haveI : IsLocallyNoetherian (A.baseChange L).X.left :=
    LocallyOfFiniteType.isLocallyNoetherian (A.baseChange L).X.hom
  rw [← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace] at h ⊢
  rw [← map_ringEquiv_maximalIdeal e, Ideal.spanFinrank_map_eq_of_ringEquiv] at h
  exact h

/-- **Main result, two-fact form.** -/
theorem hodgeLatticeTheorem_of_tangent (h1 : TangentDimAtOrigin) (h3 : DimBaseChange) :
    HodgeLatticeTheorem :=
  hodgeLatticeTheorem_of_cotangentRank (cotangentRank_of_tangentDim (tangentDim_of_abVar h1 h3))

end ZInQ.DefFaltings.HodgeLattice

end HodgeLatticeSec

section H5NeronSec
/-! ### leaf-adopt3 fold (2026-11-13): task h5-neron

Copied from `scratch/h5-neron/H5Neron.lean` (compiled there against the kernel module
`ZInQKernel.HDecomp.Faltings.Leaves`). Changes: the `import` line and the `#print axioms` lines are
dropped; the four lines `open PkgI3 (AbVar)` are deleted (in this file `open DefFaltings` already
brings def-faltings' copy `ZInQ.DefFaltings.AbVar`, and keeping both would make `AbVar` ambiguous);
`AbVar.zero` (= `PkgI3.AbVar.zero` in the kernel) is restated for the copy as
`ZInQ.H5Neron.AbVar.zero`, just before `section ZeroAV`. The bridges at the end are new. All
`ZInQ.DefFaltings` declarations used (`GroupModel`, `IsNeronModel`, `height`, `MetrizedModel`,
`stableFaltingsHeight_eq_iInf_height`, `NeronModelMinimal`, `StableHeightFinite`, `isogDeg`,
`ptObj`, `grKappa`, ...) are textually identical in section `DefFaltingsSec` above. -/

/-! # h5-neron: Néron models and the stable Faltings height (node H5), combined file

Self-contained combination of `Neron.lean` (part A), `ZeroAV.lean` (part B) and
`Reduction.lean` (part C) of `scratch/h5-neron/`, with part D (the leaves and glue for the zero
abelian variety). Mathlib + project only; no unproved step, no `axiom`. See `docs/research/h5-neron.md`. -/

namespace ZInQ.H5Neron


open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory

section General

variable {S S' : Scheme.{0}} (j : S' ⟶ S) (P : Over S → Prop)

variable {j P}

end General

section GroupModels

open NumberField DefFaltings

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

end GroupModels

/-! ## Transport along isomorphisms, and the additivity direction `h(A) + h(B) ≤ h(A × B)` -/

section Transport

variable {S S' : Scheme.{0}} {j : S' ⟶ S} {P : Over S → Prop}

end Transport

section Additivity

open NumberField DefFaltings

variable {K : Type} [Field K]

end Additivity



open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField MeasureTheory DefFaltings
open scoped TensorProduct

section DimZero

variable {L : Type} [Field L] [NumberField L] {K : Type} [Field K] [Algebra K L] {A : AbVar K}

end DimZero

-- op-dedupe: the copy `ZInQ.H5Neron.AbVar.zero` (for the copy `ZInQ.DefFaltings.AbVar`) is removed; as in the
-- kernel, `AbVar.zero` is `PkgI3.AbVar.zero`.

section ZeroAV

variable (K : Type) [Field K] (L : Type) [Field L] [NumberField L] [Algebra K L]

end ZeroAV



open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings

section Defs

variable {K : Type} [Field K] {A : AbVar K}

end Defs

/-! ## Leaves -/

/-! ## Glue (stated; to be proved by the project) -/

/-! ## Glue (proved): composita -/

/-! ## The reduction (proved) -/

/-! ## Part D: the leaves N1, N2 and the glue hold for the zero abelian variety (proved)

So the hypotheses of `stableFaltingsHeight_eq_neron` and `stableFaltingsHeight_add_le` are
consistent with the definitions in the only case Mathlib can construct. -/

section ZeroInstances

end ZeroInstances

/-! ## Part E: the glue `ProductGroupModelExists`, proved; additivity from three hypotheses -/

section ProductProof

open scoped Obj

end ProductProof

end ZInQ.H5Neron

/-! ### leaf-adopt3 fold: bridges to `LeafAdopt.H5` and to g0-split's `HeightAdditivity`

No theorem of h5-neron concludes `LeafAdopt.H5` or either of its halves for a general `A`:
`NeronModelMinimal` is a *hypothesis* of every reduction, and `StableHeightFinite` is proved only for
the zero abelian variety (`stableHeightFinite_zero`). The bridges below therefore take `LeafAdopt.H5`
(the bundle field `ResearchLeaves.h5`) as the source of `NeronModelMinimal`. -/

namespace ZInQ.H5Neron

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj

/-- **H5, the form R19-R21 need, from the bundle field `h5`** (its `NeronModelMinimal` half), N1, N2
and the three base-change glue statements. -/
theorem stableFaltingsHeight_eq_neron_all_of_H5 (h5 : LeafAdopt.H5) (hN1 : NeronModelExists)
    (hN2 : SemistableNeronIdentityComponent) (hbc : ModelHeightBaseChange)
    (hbcE : GroupModelBaseChangeExists) (hop : OpenSubgroupHeight)
    (K : Type) [Field K] [NumberField K] (A : ZInQ.DefFaltings.AbVar K) :
    ∃ (L₀ : Type) (_ : Field L₀) (_ : NumberField L₀) (_ : Algebra K L₀)
      (𝒩₀ : ZInQ.DefFaltings.GroupModel A L₀),
      𝒩₀.IsNeronModel ∧ ZInQ.DefFaltings.stableFaltingsHeight A = 𝒩₀.height ∧
      ∀ (L' : Type) [Field L'] [NumberField L'] [Algebra K L'] [Algebra L₀ L']
        [IsScalarTower K L₀ L'] (𝒩' : ZInQ.DefFaltings.GroupModel A L'), 𝒩'.IsNeronModel →
        ZInQ.DefFaltings.stableFaltingsHeight A = 𝒩'.height :=
  stableFaltingsHeight_eq_neron_all hN1 hN2 h5.2 hbc hbcE hop K A

/-- **Additivity `h(A) + h(B) ≤ h(C)` for `C ≅ A × B`, from the bundle field `h5`**, N1 and P2. -/
theorem stableFaltingsHeight_add_le_of_H5 (h5 : LeafAdopt.H5) (hN1 : NeronModelExists)
    (hH : ProductModelHeight) {K : Type} [Field K] (A B C : ZInQ.DefFaltings.AbVar K)
    (hC : IsProductAbVar C A B) :
    ZInQ.DefFaltings.stableFaltingsHeight A + ZInQ.DefFaltings.stableFaltingsHeight B ≤
      ZInQ.DefFaltings.stableFaltingsHeight C :=
  stableFaltingsHeight_add_le' hN1 h5.2 hH A B C hC

/-- **g0-split's glue piece `HeightAdditivity`, with `IsProductOf` unfolded** (g0-split's
`HSyn.G0Split.HeightAdditivity` and `IsProductOf` come later in this file, so they cannot be named
here). From N1, `NeronModelMinimal` and P2 (`ProductModelHeight`). The bridge, to be placed after
g0-split's definitions:
`fun L _ _ P A Z ⟨p₁, p₂, h₁, h₂, h⟩ => heightAdditivity_unfolded hN1 hmin hH L P A Z p₁ p₂ h₁ h₂ h`. -/
theorem heightAdditivity_unfolded (hN1 : NeronModelExists)
    (hmin : ZInQ.DefFaltings.NeronModelMinimal) (hH : ProductModelHeight) :
    ∀ (L : Type) [Field L] [NumberField L] (P A Z : ZInQ.DefFaltings.AbVar L)
      (p₁ : P.X ⟶ A.X) (p₂ : P.X ⟶ Z.X), IsMonHom p₁ → IsMonHom p₂ → IsIso (CartesianMonoidalCategory.lift p₁ p₂) →
      ∀ a z p : ℝ, ZInQ.DefFaltings.stableFaltingsHeight A = a →
        ZInQ.DefFaltings.stableFaltingsHeight Z = z →
        ZInQ.DefFaltings.stableFaltingsHeight P = p → a + z ≤ p := by
  intro L _ _ P A Z p₁ p₂ h₁ h₂ hiso a z p ha hz hp
  have hC : IsProductAbVar P A Z := by
    refine ⟨asIso (CartesianMonoidalCategory.lift p₁ p₂), ?_, ?_⟩
    · rw [asIso_hom, CartesianMonoidalCategory.lift_fst]; exact h₁
    · rw [asIso_hom, CartesianMonoidalCategory.lift_snd]; exact h₂
  have key := stableFaltingsHeight_add_le' hN1 hmin hH A Z P hC
  rw [ha, hz, hp] at key
  exact_mod_cast key

end ZInQ.H5Neron

end H5NeronSec

/-! ## x1-belyi (wave 25; leaf-adopt3 fold): `X1ModelExists` and `BelyiX1` from five leaves

Copied verbatim from `scratch/x1-belyi/X1Belyi.lean` (which imported
`ZInQKernel.HDecomp.ModCurves.Glue`; every kernel name it uses is in `LeafModCurvesSec` above with
the same body). Changes: the import and the `#print axioms` lines are dropped; the file-level
`set_option linter.unusedSimpArgs false` is scoped to this section; the bridge
`X1Belyi.exists_J1_of_leaves` is added at the end. New leaf Props: `X1Belyi.TorsionStructure`,
`GoodReductionUnramified`, `CurveOfFunctionFieldQ`, `X1ConstantField`, `X1RationalCusp` (bundled
as `X1Belyi.X1Leaves`). No proof holes. -/

section X1BelyiSec

set_option linter.unusedSimpArgs false


/-!
# x1-belyi: the glue targets `X1ModelExists` and `BelyiX1` from literature leaves

Task x1-belyi (2026-11-12), nodes MC4, MC5, MC10 of `docs/research/bp-modcurves.md`.
The targets are the definitions `LeafModCurves.X1ModelExists` and `LeafModCurves.BelyiX1` of
`ZInQKernel/HDecomp/ModCurves/Leaves.lean` (imported, not restated).

Leaves (`def … : Prop`, published statements or consequences of them, over genuine
definitions):
* `TorsionStructure`: `E[N](K) ≅ ℤ/N × ℤ/N` over an algebraically closed field of
  characteristic 0 (Silverman, AEC, Cor. III.6.4(b), UNVERIFIED number).
* `GoodReductionUnramified`: good reduction at a place of `k(T)` with residue characteristic 0
  ⇒ the field of an `N`-torsion `x`-coordinate is unramified there (Serre–Tate 1968, Thm 1 /
  Néron–Ogg–Shafarevich, Silverman AEC Prop. VII.4.1, UNVERIFIED numbers).
* `CurveOfFunctionFieldQ`: a finite extension `F` of `ℚ(T)` with constant field `ℚ` is the
  function field of a smooth proper geometrically connected integral curve over `ℚ`, which has a
  `ℚ`-point when `F` has a place of degree 1 (Stacks, Curves and function fields; UNVERIFIED tags).
* `X1ConstantField`: `ℚ` is algebraically closed in `K_N = ℚ(j)(x(P))` (Igusa; geometric
  irreducibility of `X₁(N)` over `ℚ`; UNVERIFIED).
* `X1RationalCusp`: `K_N` has a place of degree 1 over `ℚ` (a `ℚ`-rational cusp of `X₁(N)`;
  UNVERIFIED).

Proved (glue): `belyiX1_of_leaves : TorsionStructure → GoodReductionUnramified → BelyiX1` and
`x1ModelExists_of_leaves : TorsionStructure → CurveOfFunctionFieldQ → X1ConstantField →
X1RationalCusp → X1ModelExists`.
-/

noncomputable section

namespace X1Belyi

open LeafModCurves
open WeierstrassCurve AlgebraicGeometry CategoryTheory
open Polynomial

/-! ## Definitions -/

/-! ## Leaves -/

/-! ## Basic facts -/

instance : CharZero Kbar :=
  charZero_of_injective_algebraMap (algebraMap Qj Kbar).injective

instance : EjBar.IsElliptic := inferInstanceAs ((Ej.map (algebraMap Qj Kbar)).IsElliptic)

/-! ## The degree bound `[K_N : ℚ(j)] ≤ N²` (from leaf T1) -/

/-! ## `X1ModelExists` (MC4 + MC10) -/

/-! ## `BelyiX1` (MC5) -/

/-! ## The bundle -/

/-- **Bridge (non-vacuity of `IsJ1`).** With T33 (`JacobianExists ℚ`, field `t33`) and the five
leaves of this file, a `J₁(N)` exists for every `N ≥ 1`. -/
theorem exists_J1_of_leaves (L : X1Leaves) (hJ : LeafModCurves.JacobianExists ℚ) (N : ℕ)
    (hN : 0 < N) : ∃ J : PkgI3.AbVar ℚ, LeafModCurves.IsJ1 N J :=
  LeafModCurves.exists_J1 hJ (x1ModelExists_and_belyiX1 L).1 N hN

end X1Belyi

end

end X1BelyiSec

/-! ## e1-sub (wave 25; leaf-adopt3 fold): `VSurjOfSurjective` proved; E1 for R16

From `scratch/e1-sub/E1Sub.lean` (which imported `ZInQKernel.HDecomp.ModCurves.Glue`,
`ZInQKernel.HDecomp.I3Linalg.C2`, `ZInQKernel.HDecomp.I3Linalg.TateBC`). Kernel declarations used
by it that are NOT in Leaves.lean are supplied first, under their kernel names:
* `GlueI3.isSemisimpleRepresentation_baseChange`, `GlueI3.semisimpleBaseChange`
  (kernel `I3Linalg/C2.lean` §SSBC): here one-line wrappers around glue-ssbc's
  `GlueSSBC.isSemisimpleRepresentation_baseChange` (section `GlueSSBCSec`, inserted before this
  fragment); `GlueSSBC.repBaseChange` and `GlueI3.repBaseChange` have the same body, so the
  types agree by unfolding. (`GlueI3.isSemisimpleRepresentation_baseChange` is also used by the
  c9-rhof fragment.)
* `PkgI3.E1_exists_hom_ne_zero'` (kernel `I3Linalg/C2.lean`), verbatim.
* `PkgI3.Tate.map_injective` ... `PkgI3.Tate.map_bijective` (all of kernel
  `I3Linalg/TateBC.lean` §2), verbatim.
The e1-sub text is verbatim except: no import, no `#print axioms`, and the two
`open LeafModCurves` lines get `hiding` (see the comment there). No proof holes. -/

section E1SubSec

noncomputable section

/-! ### Kernel `I3Linalg/C2.lean`, glue-ssbc part (not in Leaves.lean), through `GlueSSBC` -/

namespace GlueI3

/-- **`SemisimpleBaseChange`, proved** (kernel name; proof: glue-ssbc,
`GlueSSBC.isSemisimpleRepresentation_baseChange`). -/
theorem isSemisimpleRepresentation_baseChange {k G V : Type*} [Field k] [Monoid G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] [CharZero k] (E : Type*) [Field E]
    [Algebra k E] (ρ : Representation k G V) (hρ : ρ.IsSemisimpleRepresentation) :
    (repBaseChange E ρ).IsSemisimpleRepresentation :=
  GlueSSBC.isSemisimpleRepresentation_baseChange E ρ hρ

end GlueI3

/-! ### Kernel `I3Linalg/C2.lean`: E1 with `SemisimpleBaseChange` discharged (verbatim) -/

namespace PkgI3

open GlueI3 AbVar

end PkgI3

/-! ### Kernel `I3Linalg/TateBC.lean` §2 (verbatim; not in Leaves.lean) -/

/-! ## 2. Injective maps of groups: saturation and bijectivity on Tate modules -/

namespace PkgI3.Tate

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {M N : Type*} [AddCommGroup M] [AddCommGroup N]

end PkgI3.Tate

/-! ### e1-sub (verbatim from `scratch/e1-sub/E1Sub.lean`, lines 20-870) -/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3 PkgI3.AbVar
open scoped TensorProduct

namespace E1Sub

/-! ## §1. A surjective homomorphism is surjective on `V_ℓ` -/

section VSurj

variable {K : Type} [Field K]

variable (ℓ : ℕ) [Fact ℓ.Prime]

end VSurj

/-! ## §2. Equivariant sections out of a semisimple representation -/

section Section

variable {k G V W : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V] [AddCommGroup W]
  [Module k W]

end Section

/-! ## §3. `ρ_{f,ι}` is a subrepresentation of `V_ℓ(J) ⊗ ℚ̄_ℓ` (over `G_ℚ`) -/

section RhoSub

-- leaf-adopt3: `hiding` added (Leaves.lean has `LeafModCurves` copies of these `PkgI4` names)
open LeafModCurves hiding Qbar GQ LiesOver IsArithFrob CF coeff HasNebentypus IsNormalizedEigenform
  scaleH oldSpace IsNewform
-- op-dedupe was: open PkgI4 (GQ)
open _root_.PkgI4 (GQ) -- op-dedupe

variable (ℓ : ℕ) [Fact ℓ.Prime]

end RhoSub

end E1Sub

/-! ## §4. `V_ℓ` under base change -/

section BCsec
open scoped CategoryTheory.Obj

namespace E1Sub

section BaseChange

variable {K : Type} [Field K] {L : Type} [Field L] [Algebra K L]

variable (L) in
/-- Points of `A` with values in an `L`-algebra `M` become points of `A_L`. -/
def bcPt (J : AbVar K) (M : Type) [Field M] [Algebra L M] [Algebra K M] [IsScalarTower K L M] :
    J.Pt M →* (J.baseChange L).Pt M where
  toFun Q := ptUnit M ≫ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map Q
  map_one' := by
    change ptUnit M ≫ (Over.pullback _).map (1 : ptObj (K := K) M ⟶ J.X) = 1
    rw [Functor.map_one, MonObj.comp_one]
    -- leaf-adopt3: `rfl` dropped here (the goal is closed by `rw` in Leaves.lean's context)
  map_mul' Q Q' := by
    change ptUnit M ≫ (Over.pullback _).map (Q * Q') =
      (ptUnit M ≫ (Over.pullback _).map Q) * (ptUnit M ≫ (Over.pullback _).map Q')
    rw [Functor.map_mul, MonObj.comp_mul]
    rfl

lemma bcPt_fst (J : AbVar K) (M : Type) [Field M] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M] (Q : J.Pt M) :
    (bcPt L J M Q).left ≫ pullback.fst _ _ = Q.left := by
  change ((ptUnit (K := K) (L := L) M).left ≫
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map Q).left) ≫
      pullback.fst _ _ = Q.left
  simp only [ptUnit, Over.pullback_map_left, Category.assoc, pullback.lift_fst]
  exact (pullback.lift_fst_assoc _ _ _ _).trans (Category.id_comp _)

lemma bcPt_injective (J : AbVar K) (M : Type) [Field M] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M] : Function.Injective (bcPt L J M) := by
  intro Q Q' h
  apply Over.OverMorphism.ext
  rw [← bcPt_fst (L := L) J M Q, ← bcPt_fst (L := L) J M Q', h]

end BaseChange

section BC2

variable {K : Type} [Field K] {L : Type} [Field L] [Algebra K L]

/-- The point map `A(K̄) → A_L(L̄)` along a `K`-embedding `i : K̄ → L̄`. -/
def bcPhi (J : AbVar K) (i : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) :
    J.Pt (AlgebraicClosure K) →* (J.baseChange L).Pt (AlgebraicClosure L) :=
  (bcPt L J (AlgebraicClosure L)).comp (precompPt J i)

lemma bcPhi_injective (J : AbVar K) (i : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) :
    Function.Injective (bcPhi J i) := by
  intro a b h
  exact precompPt_injective J i (bcPt_injective (L := L) J (AlgebraicClosure L) h)

/-- **Equivariance of the point map.** For `τ ∈ G_L` and `σ ∈ G_K` with `i ∘ σ = τ ∘ i`. -/
lemma bcPhi_galAct (J : AbVar K) (i : AlgebraicClosure K →ₐ[K] AlgebraicClosure L)
    (τ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (h : ∀ x, i (σ x) = τ (i x)) (P : J.Pt (AlgebraicClosure K)) :
    bcPhi J i (J.galAct σ P) = (J.baseChange L).galAct τ (bcPhi J i P) := by
  change ptUnit (AlgebraicClosure L) ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map
        (specHom i ≫ galHom σ ≫ P) =
    galHom τ ≫ ptUnit (AlgebraicClosure L) ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map (specHom i ≫ P)
  rw [← Category.assoc (galHom τ), galHom_ptUnit, Category.assoc, ← Functor.map_comp,
    ← Category.assoc (specHom i), specHom_galHom i τ σ h, Category.assoc]

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- `T_ℓ(A) → T_ℓ(A_L)` along `i`. -/
def bcT (J : AbVar K) (i : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) :
    J.T ℓ →ₗ[ℤ_[ℓ]] (J.baseChange L).T ℓ :=
  Tate.map (MonoidHom.toAdditive (bcPhi J i))

lemma bcT_injective (J : AbVar K) (i : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) :
    Function.Injective (bcT ℓ J i) :=
  Tate.map_injective _ (bcPhi_injective J i)

lemma bcT_galT (J : AbVar K) (i : AlgebraicClosure K →ₐ[K] AlgebraicClosure L)
    (τ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (h : ∀ x, i (σ x) = τ (i x)) (x : J.T ℓ) :
    bcT ℓ J i (J.galT σ x) = (J.baseChange L).galT τ (bcT ℓ J i x) := by
  apply Subtype.ext; funext n
  change Additive.ofMul (bcPhi J i (J.galAct σ (Additive.toMul (x.1 n)))) =
    Additive.ofMul ((J.baseChange L).galAct τ (bcPhi J i (Additive.toMul (x.1 n))))
  rw [bcPhi_galAct J i τ σ h]

/-- `V_ℓ(A) → V_ℓ(A_L)` along `i`. -/
def bcV (J : AbVar K) (i : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) :
    J.V ℓ →ₗ[ℚ_[ℓ]] (J.baseChange L).V ℓ :=
  (bcT ℓ J i).baseChange ℚ_[ℓ]

lemma bcV_injective (J : AbVar K) (i : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) :
    Function.Injective (bcV ℓ J i) := by
  haveI : Module.Flat ℤ_[ℓ] ℚ_[ℓ] := IsLocalization.flat ℚ_[ℓ] (nonZeroDivisors ℤ_[ℓ])
  exact Module.Flat.lTensor_preserves_injective_linearMap _ (bcT_injective ℓ J i)

lemma bcV_galRep (J : AbVar K) (i : AlgebraicClosure K →ₐ[K] AlgebraicClosure L)
    (τ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (h : ∀ x, i (σ x) = τ (i x)) :
    bcV ℓ J i ∘ₗ J.galRep ℓ σ = (J.baseChange L).galRep ℓ τ ∘ₗ bcV ℓ J i := by
  have h1 : bcT ℓ J i ∘ₗ J.galT σ = (J.baseChange L).galT τ ∘ₗ bcT ℓ J i :=
    LinearMap.ext fun x => bcT_galT ℓ J i τ σ h x
  change (bcT ℓ J i).baseChange ℚ_[ℓ] ∘ₗ (J.galT σ).baseChange ℚ_[ℓ] =
    ((J.baseChange L).galT τ).baseChange ℚ_[ℓ] ∘ₗ (bcT ℓ J i).baseChange ℚ_[ℓ]
  rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, h1]

/-- **`V_ℓ` under base change (GLUE, proved).** For an abelian variety `J` over `K`, a field
extension `L/K` and a `K`-embedding `i : K̄ → L̄`, `V_ℓ(i) : V_ℓ(J) → V_ℓ(J_L)` is injective and
intertwines `σ ∈ G_K` with `τ ∈ G_L` whenever `i ∘ σ = τ ∘ i`; after extension of scalars to any
field `E ⊇ ℚ_ℓ` it stays injective and equivariant. (With `TateModuleFree` over `K` and `L` and
`dim J_L = dim J` it is bijective, `PkgI3.Tate.map_bijective`; injectivity suffices for E1.) -/
theorem bcVE_injective (E : Type) [Field E] [Algebra ℚ_[ℓ] E] (J : AbVar K)
    (i : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) :
    Function.Injective ((bcV ℓ J i).baseChange E) :=
  Module.Flat.lTensor_preserves_injective_linearMap _ (bcV_injective ℓ J i)

theorem bcVE_equivariant (E : Type) [Field E] [Algebra ℚ_[ℓ] E] (J : AbVar K)
    (i : AlgebraicClosure K →ₐ[K] AlgebraicClosure L)
    (τ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (h : ∀ x, i (σ x) = τ (i x)) (v : TensorProduct ℚ_[ℓ] E (J.V ℓ)) :
    (bcV ℓ J i).baseChange E (GlueI3.repBaseChange E (J.galRep ℓ) σ v) =
      GlueI3.repBaseChange E ((J.baseChange L).galRep ℓ) τ ((bcV ℓ J i).baseChange E v) := by
  change ((bcV ℓ J i).baseChange E ∘ₗ (J.galRep ℓ σ).baseChange E) v =
    (((J.baseChange L).galRep ℓ τ).baseChange E ∘ₗ (bcV ℓ J i).baseChange E) v
  rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, bcV_galRep ℓ J i τ σ h]

end BC2

/-! ### The restriction `G_L → G_K` along `i` and bijectivity under `TateModuleFree` -/

section Res

variable {K : Type} [Field K] {L : Type} [Field L] [Algebra K L]

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- **`T_ℓ` under base change is bijective (GLUE, proved from `TateModuleFree` and the
dimension being unchanged by base change).** `dim A_L = dim A` is a standard fact (dimension of
a scheme locally of finite type over a field is invariant under field extension; Stacks, Tag
00P4 for algebras, UNVERIFIED tag) taken here as a hypothesis; it is not needed for E1. -/
theorem bcT_bijective (hT : TateModuleFree) (J : AbVar K)
    (i : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) (hℓ : (ℓ : K) ≠ 0)
    (hdim : (J.baseChange L).dim = J.dim) : Function.Bijective (bcT ℓ J i) := by
  have hℓL : (ℓ : L) ≠ 0 := by
    rw [← map_natCast (algebraMap K L)]
    exact (map_ne_zero_iff _ (algebraMap K L).injective).2 hℓ
  obtain ⟨hfr, hfi, hr⟩ := hT K J ℓ hℓ
  obtain ⟨-, hfiL, hrL⟩ := hT L (J.baseChange L) ℓ hℓL
  refine Tate.map_bijective _ (bcPhi_injective J i) ?_
  have : ((Module.finrank ℤ_[ℓ] (J.T ℓ) : ℕ∞) : WithBot ℕ∞) =
      ((Module.finrank ℤ_[ℓ] ((J.baseChange L).T ℓ) : ℕ∞) : WithBot ℕ∞) := by
    rw [hr, hrL, hdim]
  exact_mod_cast this

end Res

end E1Sub

end BCsec

/-! ## §5. E1 for R16: `ρ_{f,ι}` is a subrepresentation of `V_ℓ(J₁(N)_L) ⊗ ℚ̄_ℓ` -/

namespace E1Sub

section Final

-- leaf-adopt3: `hiding` added (Leaves.lean has `LeafModCurves` copies of these `PkgI4` names)
open LeafModCurves hiding Qbar GQ LiesOver IsArithFrob CF coeff HasNebentypus IsNormalizedEigenform
  scaleH oldSpace IsNewform
-- op-dedupe was: open PkgI4 (GQ)
open _root_.PkgI4 (GQ) -- op-dedupe

end Final

end E1Sub

end

end E1SubSec

/-! ## c9-rhof (wave 25; leaf-adopt3 fold): glue C9 for R16's `ρ_{f,ι}` (`LeafModCurves.rhoF`)

From `scratch/c9-rhof/C9.lean` (which imported `ZInQKernel.HDecomp.ModCurves.Glue`,
`ZInQKernel.HDecomp.I3Linalg.C2`, `ZInQKernel.HDecomp.I3Linalg.RhoCont`). Needs the e1-sub
fragment before it (for `GlueI3.isSemisimpleRepresentation_baseChange`, which needs glue-ssbc's
section `GlueSSBCSec`).
* Kernel `I3Linalg/RhoCont.lean` (glue-rho-cont), none of which is in Leaves.lean, is copied
  first, verbatim (namespaces `PkgI3.RhoCont`, `PkgI3.Tate`, and
  `PkgI3.continuous_galRep_of_tateModuleFree`). It declares the global instances
  `PkgI3.RhoCont.instTopologicalSpacePt`, `PkgI3.RhoCont.instTopologicalSpaceV` (module topology on
  `V_ℓ(A)`) and two `DiscreteTopology`/`IsModuleTopology` instances.
* The c9-rhof text is verbatim except: no import, no `#print axioms`; its §7 (`PkgI4.EigenformRepExists`,
  `PkgI4.EigenformTwist`, `PkgI4.NewformOfEigenform`, `PkgI4.GaloisRep.AttachedUpToTwist`) is deleted
  (identical copies already in Leaves.lean, section `PkgI4`); `open ... LeafModCurves` gets `hiding`.
  `C9Rhof.FrobeniusDense` (a verbatim copy of `HSyn.FrobeniusDense` over `PkgI4`'s names) is kept;
  bridges to the bundle forms are added at the end (`frobeniusDense_of_hsyn`, `c9_hsyn`, ...).
No proof holes (the task file's one occurrence of the word is in its module docstring, not copied). -/

section C9RhofSec

noncomputable section

/-! ### Kernel `I3Linalg/RhoCont.lean` §3 (verbatim; not in Leaves.lean) -/

/-! pkg-I3's object layer and leaves (§1-§4 of the draft, a verbatim copy of
`scratch/pkg-I3/I3.lean`) are imported from `ZInQKernel.HDecomp.Objects` (§A), whose
QM leaf is `PkgI3.QMDichotomyYu`. -/

/-! ## 3. Continuity of `ρ_ℓ` (new: task glue-rho-cont) -/

/-! ### 3a. A discrete action with open stabilizers is continuous -/

namespace PkgI3.RhoCont

end PkgI3.RhoCont

/-! ### 3b. The inverse-limit topology on `T_ℓ(M)` for a discrete group `M`

`T ℓ M` is a subgroup of `ℕ → M`; with `M` discrete it carries the subspace topology of the
product, i.e. the inverse-limit topology of the discrete groups `M[ℓⁿ]` (Mathlib's instances,
no new definition). -/

namespace PkgI3.Tate

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {M : Type*} [AddCommGroup M] [TopologicalSpace M]
  [DiscreteTopology M]

end PkgI3.Tate

namespace PkgI3.Tate

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {M : Type*} [AddCommGroup M] [TopologicalSpace M]
  [DiscreteTopology M]

end PkgI3.Tate

/-! ### 3c. Open stabilizers on `A(K̄)`

Each `K̄`-point `P` of a scheme locally of finite type over `K` is fixed by the open subgroup
`Gal(K̄/E)` for a finite extension `E/K`: the stalk map `κ = 𝒪_{A,x} → K̄` of `P` is determined
by finitely many values (`𝒪_{A,x}` is essentially of finite type over `K`), and these generate
a finite extension `E` because `K̄/K` is algebraic. -/

namespace PkgI3.RhoCont

open CategoryTheory AlgebraicGeometry Limits AbVar

universe u

variable {K : Type u} [Field K]

local notation "Kbar" => AlgebraicClosure K

end PkgI3.RhoCont

/-! ### 3d. Continuity of `ρ_ℓ` on `T_ℓ(A)` and on `V_ℓ(A)` -/

namespace PkgI3.RhoCont

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj AbVar
open scoped TensorProduct

universe u

variable {K : Type u} [Field K]

local notation "Kbar" => AlgebraicClosure K

variable (ℓ : ℕ) [Fact ℓ.Prime]

end PkgI3.RhoCont

/-! ### 3e. With pkg-I3's leaf I3.M0 -/

namespace PkgI3

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj AbVar

/-! `TateModuleFree` (leaf I3.M0) is `PkgI3.TateModuleFree` of `Objects`. -/

end PkgI3

/-! ### c9-rhof (verbatim from `scratch/c9-rhof/C9.lean`; §7 deleted as duplicate) -/

namespace C9Rhof

-- op-dedupe was: open PkgI4 (Qbar GQ LiesOver IsArithFrob CF coeff IsNewform IsNormalizedEigenform GaloisRep GaloisChar)
open _root_.PkgI4 (Qbar GQ LiesOver IsArithFrob CF coeff IsNewform IsNormalizedEigenform GaloisRep GaloisChar) -- op-dedupe
-- leaf-adopt3: `LeafModCurves` opened with `hiding` (Leaves.lean has `LeafModCurves` copies of
-- these `PkgI4` names; the kernel had none, so the names below are `PkgI4`'s as in the kernel)
open PkgI3 PkgI3.AbVar
open LeafModCurves hiding Qbar GQ LiesOver IsArithFrob CF coeff HasNebentypus IsNormalizedEigenform
  scaleH oldSpace IsNewform

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-! ## §1. `rhoF` as a quotient of `V_ℓ(A) ⊗ ℚ̄_ℓ` -/

section Quot

variable (A : AbVar ℚ) {F : Type} [Field F] (θ : F →+* A.End0) (emb : F →+* PadicAlgCl ℓ)

end Quot

/-! ## §2. Semisimplicity -/

section SS

variable (A : AbVar ℚ) {F : Type} [Field F] (θ : F →+* A.End0) (emb : F →+* PadicAlgCl ℓ)

instance : CharZero (PadicAlgCl ℓ) :=
  charZero_of_injective_algebraMap (algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)).injective

end SS

/-! ## §3. Continuity -/

section Cont

variable (A : AbVar ℚ) {F : Type} [Field F] (θ : F →+* A.End0) (emb : F →+* PadicAlgCl ℓ)

end Cont

/-! ## §4. Density of arithmetic Frobenius elements (leaf T18) -/

/-! ## §5. Brauer–Nesbitt (leaf T19) with arithmetic Frobenius traces -/

section BN

variable {k V W ι κ : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [T2Space k]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

end BN

/-! ## §6. C9 -/

section C9

end C9

end C9Rhof

namespace C9Rhof

-- op-dedupe was: open PkgI4 (Qbar GQ LiesOver IsArithFrob CF coeff IsNewform IsNormalizedEigenform GaloisRep GaloisChar)
open _root_.PkgI4 (Qbar GQ LiesOver IsArithFrob CF coeff IsNewform IsNormalizedEigenform GaloisRep GaloisChar) -- op-dedupe
-- leaf-adopt3: `LeafModCurves` opened with `hiding` (Leaves.lean has `LeafModCurves` copies of
-- these `PkgI4` names; the kernel had none, so the names below are `PkgI4`'s as in the kernel)
open PkgI3 PkgI3.AbVar
open LeafModCurves hiding Qbar GQ LiesOver IsArithFrob CF coeff HasNebentypus IsNormalizedEigenform
  scaleH oldSpace IsNewform

/-! ## §8. `GaloisRep` (matrix form) as a `Representation` -/

section Bridge

variable {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ}

end Bridge

/-! ## §9. C9 against R14 and against C8's `r₅` -/

section Apps

variable (ℓ : ℕ) [Fact ℓ.Prime]

end Apps

/-! ## leaf-adopt3: bridges to the bundle forms of the leaves

`TextbookLeaves.t18 : HSyn.FrobeniusDense`, `ResearchLeaves.r14 : HSyn.EigenformRepExists` and
`TextbookLeaves.t24 : HSyn.EigenformTwist` are stated over `HSyn`'s copies of `Qbar`, `GQ`,
`LiesOver`, `IsArithFrob`, `GaloisRep`, `CF`, `coeff`, `IsNormalizedEigenform`; this file uses
`PkgI4`'s (same bodies). The three conversions are definitional unfoldings. -/

section HSynBridges

/-- T18, bundle form (`HSyn.FrobeniusDense`, field `t18`) ⇒ this file's verbatim copy. -/
theorem frobeniusDense_of_hsyn (h : HSyn.FrobeniusDense) : FrobeniusDense := by
  intro U hU σ S
  obtain ⟨p, hp, hpS, v, τ, hv, hτ, hU'⟩ := h U hU σ S
  exact ⟨p, hp, hpS, v, τ, hv, hτ, hU'⟩

/-- R14, bundle form (`HSyn.EigenformRepExists`, field `r14`, over `HSyn.GaloisRep`) ⇒
`PkgI4.EigenformRepExists` (the same statement over `PkgI4.GaloisRep`). -/
theorem eigenformRepExists_of_hsyn (h : HSyn.EigenformRepExists) :
    PkgI4.EigenformRepExists := by
  intro ℓ _ ιC ιL N k χ g hN hk hg
  obtain ⟨ρ, hss, hatt⟩ := h ℓ ιC ιL N k χ g hN hk hg
  exact ⟨⟨ρ.toHom, ρ.continuous_toHom⟩, hss, hatt⟩

/-- T24, bundle form (`HSyn.EigenformTwist`, field `t24`) ⇒ `PkgI4.EigenformTwist`. -/
theorem eigenformTwist_of_hsyn (h : HSyn.EigenformTwist) : PkgI4.EigenformTwist := by
  intro N m k χ ψ g hN hm hg
  obtain ⟨χ', g', hg', hc⟩ := h N m k χ ψ g hN hm hg
  exact ⟨χ', g', hg', hc⟩

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- **C9, bundle form**: `c9` with T18 as `HSyn.FrobeniusDense` (field `t18`). Other hypotheses:
R16 (`r16`), Faltings Satz 3 (`r9a`), I3.M0 (`t26`), T19 module form
(`GlueC10.BrauerNesbittChar0`; proved by t-skolem-kw, `TSkolemKW.brauerNesbittChar0`). -/
theorem c9_hsyn (hR16 : R16_EichlerShimuraJ1') (hS : FaltingsSemisimple) (hT : TateModuleFree)
    (hBN : GlueC10.BrauerNesbittChar0) (hD : HSyn.FrobeniusDense)
    (N : ℕ) (hN : 0 < N) (χ : DirichletCharacter ℂ N) (f : CF N 2) (hf : IsNewform f χ)
    (J : AbVar ℚ) (hJ : IsJ1 N J) (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (S : Finset ℕ) {W κ : Type} [AddCommGroup W] [Module (PadicAlgCl ℓ) W]
    [FiniteDimensional (PadicAlgCl ℓ) W] [Fintype κ] [DecidableEq κ]
    (bW : Module.Basis κ (PadicAlgCl ℓ) W) (r : Representation (PadicAlgCl ℓ) GQ W)
    (hrc : Continuous fun g => LinearMap.toMatrix bW bW (r g))
    (hr : IsSemisimpleModule (MonoidAlgebra (PadicAlgCl ℓ) GQ) r.asModule)
    (hatt : ∀ p, p.Prime → p ∉ S → ¬ p ∣ N * ℓ → ∃ α : Qbar, ιC α = coeff f p ∧
      ∀ (v : ValuationSubring Qbar) (τ : GQ), LiesOver v p → IsArithFrob τ v p →
        LinearMap.trace (PadicAlgCl ℓ) W (r τ) = ιL α) :
    ∃ (_ : FiniteDimensional ℚ (coeffField f)) (A : AbVar ℚ) (π : Hom J A)
      (θ : coeffField f →+* A.End0), AlgebraicGeometry.Surjective π.hom.left ∧
      Module.finrank (PadicAlgCl ℓ)
        (Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ (embOf ℓ ιC ιL (coeffField f)))) = 2 ∧
      (rhoF ℓ A θ (embOf ℓ ιC ιL (coeffField f))).IsSemisimpleRepresentation ∧
      (∀ {ι' : Type} [Fintype ι'] [DecidableEq ι'] (b : Module.Basis ι' (PadicAlgCl ℓ)
          (Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ (embOf ℓ ιC ιL (coeffField f))))),
        Continuous fun g => LinearMap.toMatrix b b (rhoF ℓ A θ (embOf ℓ ιC ιL (coeffField f)) g)) ∧
      Nonempty (r.asModule ≃ₗ[MonoidAlgebra (PadicAlgCl ℓ) GQ]
        (rhoF ℓ A θ (embOf ℓ ιC ιL (coeffField f))).asModule) ∧
      (∀ g : GQ, LinearMap.trace (PadicAlgCl ℓ) W (r g) =
        LinearMap.trace (PadicAlgCl ℓ) _ (rhoF ℓ A θ (embOf ℓ ιC ιL (coeffField f)) g)) ∧
      (∀ (g : GQ) (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → IsFrobAt g p →
        LinearMap.trace (PadicAlgCl ℓ) _ (rhoF ℓ A θ (embOf ℓ ιC ιL (coeffField f)) g) =
          embOf ℓ ιC ιL (coeffField f) ⟨coeff f p, coeff_mem_coeffField f p⟩) :=
  c9 ℓ hR16 hS hT hBN (frobeniusDense_of_hsyn hD) N hN χ f hf J hJ ιC ιL S bW r hrc hr hatt

/-- **C9 against R14, bundle form** (`r14`, `r16`, `r9a`, `t26`, `t18`; T19 module form). -/
theorem c9_R14_hsyn (hR14 : HSyn.EigenformRepExists) (hR16 : R16_EichlerShimuraJ1')
    (hS : FaltingsSemisimple) (hT : TateModuleFree) (hBN : GlueC10.BrauerNesbittChar0)
    (hD : HSyn.FrobeniusDense) (N : ℕ) (hN : 0 < N) (χ : DirichletCharacter ℂ N) (f : CF N 2)
    (hf : IsNewform f χ) (J : AbVar ℚ) (hJ : IsJ1 N J) (ιC : Qbar →ₐ[ℚ] ℂ)
    (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ) :
    ∃ ρ : GaloisRep ℓ 2, ρ.IsSemisimple ∧ ρ.AttachedTo ιC ιL f ∧
      ∃ (_ : FiniteDimensional ℚ (coeffField f)) (A : AbVar ℚ) (π : Hom J A)
        (θ : coeffField f →+* A.End0), AlgebraicGeometry.Surjective π.hom.left ∧
        Nonempty ((toRep ρ).asModule ≃ₗ[MonoidAlgebra (PadicAlgCl ℓ) GQ]
          (rhoF ℓ A θ (embOf ℓ ιC ιL (coeffField f))).asModule) ∧
        ∀ g : GQ, (ρ.mat g).trace =
          LinearMap.trace (PadicAlgCl ℓ) _ (rhoF ℓ A θ (embOf ℓ ιC ιL (coeffField f)) g) :=
  c9_R14 ℓ (eigenformRepExists_of_hsyn hR14) hR16 hS hT hBN (frobeniusDense_of_hsyn hD) N hN χ f
    hf J hJ ιC ιL

/-- **C9 for C8's `r₅`, bundle form** (`t24`, `t25`, `r16`, `r9a`, `t26`, `t18`; T19 module
form). -/
theorem c9_r5_hsyn (hTw : HSyn.EigenformTwist) (hNew : PkgI4.NewformOfEigenform)
    (hR16 : R16_EichlerShimuraJ1') (hS : FaltingsSemisimple) (hT : TateModuleFree)
    (hBN : GlueC10.BrauerNesbittChar0) (hD : HSyn.FrobeniusDense)
    (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (M : ℕ) (hM : 0 < M) (χg : DirichletCharacter ℂ M) (g : CF M 2)
    (hg : IsNormalizedEigenform g χg) (m : ℕ) (hm : 0 < m) (ψD : DirichletCharacter ℂ m)
    (ψ : GaloisChar ℓ) (S : Finset ℕ) (r : GaloisRep ℓ 2) (hr : r.IsSemisimple)
    (hrg : r.AttachedUpToTwist ψ ιC ιL g S)
    (hψ : ∀ p : ℕ, p.Prime → p ∉ S → ∃ β : Qbar, ιC β = ψD (p : ZMod m) ∧
      ∀ (v : ValuationSubring Qbar) (τ : GQ), LiesOver v p → IsArithFrob τ v p →
        (ψ.toHom τ : PadicAlgCl ℓ) = ιL β) :
    ∃ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2), 0 < N ∧ N ∣ M * m ^ 2 ∧
      IsNewform f χ ∧ ∀ J : AbVar ℚ, IsJ1 N J →
      ∃ (_ : FiniteDimensional ℚ (coeffField f)) (A : AbVar ℚ) (π : Hom J A)
        (θ : coeffField f →+* A.End0), AlgebraicGeometry.Surjective π.hom.left ∧
        Nonempty ((toRep r).asModule ≃ₗ[MonoidAlgebra (PadicAlgCl ℓ) GQ]
          (rhoF ℓ A θ (embOf ℓ ιC ιL (coeffField f))).asModule) ∧
        (∀ g : GQ, LinearMap.trace (PadicAlgCl ℓ) _ (toRep r g) =
          LinearMap.trace (PadicAlgCl ℓ) _ (rhoF ℓ A θ (embOf ℓ ιC ιL (coeffField f)) g)) ∧
        (∀ (g : GQ) (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → IsFrobAt g p →
          LinearMap.trace (PadicAlgCl ℓ) _ (rhoF ℓ A θ (embOf ℓ ιC ιL (coeffField f)) g) =
            embOf ℓ ιC ιL (coeffField f) ⟨coeff f p, coeff_mem_coeffField f p⟩) :=
  c9_r5 ℓ (eigenformTwist_of_hsyn hTw) hNew hR16 hS hT hBN (frobeniusDense_of_hsyn hD) ιC ιL M hM
    χg g hg m hm ψD ψ S r hr hrg hψ

end HSynBridges

end C9Rhof

end

end C9RhofSec

noncomputable section

namespace HSyn

open scoped MatrixGroups ModularForm

/-- **The research-level leaves of route P** (note §2.1), bundled. Placeholders are
uninterpreted. Genuine statements: `R4` (pkg-I1), `R6`, `R7` (pkg-I2), `R9` (pkg-I3), `R10`,
`R11`+`R12`, `R13` (pkg-I4), `R14`, `R15` (§1 here); leaf-adopt (2026-11-12): R1 (a, c, d),
R2, R5 (leaf-qm-fp, repaired), R16 (leaf-modcurves), R19-R21 and H5 (def-faltings);
leaf-adopt2 (2026-11-12): R3, R18, R22 (leaf-push2). Remaining placeholders: R1(b), R17.
leaf-adopt3 (2026-11-13): no field changed. -/
structure ResearchLeaves : Prop where
  /-- R1 (a), (c), (d), `π₀(X₆) = 1` (rv-blueprints Q4), R1 at level one, R2 with biconditional CM
  clauses (Q5) and R5 on points of `X₆`, on one `Y₃`, `X₆` (leaf-qm-fp, repaired by leaf-adopt).
  Premise (rv-qm-polar Lemma QP): for a QM pair `(A, ι)` in characteristic 0 there is exactly one
  principal polarization whose Rosati involution is `x ↦ μ⁻¹x̄μ` on `ι(𝒪)` (`μ = 2j + ij`, the
  type fixed by the PEL datum); see the definition. Checked by model reviews (rv-qm-polar), no
  human review. -/
  r1r2 : LeafAdopt.R1R2fpRep
  /-- R1(b), complex uniformization in family form (Q3): still a placeholder. -/
  r1an : R01b_ComplexUniformization
  /-- R1(d), Shimura reciprocity, object form (leaf-qm-fp; premise Lemma QP, rv-qm-polar). -/
  r1rec : LeafQM.AV.R1rec
  /-- R3, Lin–Yang over `ℂ`, existential and polarization-free (leaf-push2; premise Lemma QP). -/
  r3 : ZInQ.LeafPush2.R03_LinYang
  r4 : PkgI1.ThetaModularity
  /-- R5(ii), González–Rotger Thm 5.12, fields of moduli (= rv-blueprints' R5fpStrong, Q2;
  premise Lemma QP, rv-qm-polar). -/
  r5 : LeafQM.AV.R5fp
  /-- R5(i), González–Rotger Prop. 5.6, `#CM(R) = 2^b h(R)` (premise Lemma QP, rv-qm-polar). -/
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
  r17 : R17_Carayol
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
  /-- H5 (rv-blueprints F2): the stable height is finite and attained by Néron models. -/
  h5 : LeafAdopt.H5

/-- **The textbook foundations** (note §2.2), bundled. -/
structure TextbookLeaves : Prop where
  -- leaf-fold2: field `t1` deleted (no proof on the route uses it; g0-assemble2 §7)
  -- leaf-fold2: field `t2` deleted (no proof on the route uses it; g0-assemble2 §7)
  -- leaf-fold2: field `t3` deleted (no proof on the route uses it; g0-assemble2 §7)
  -- leaf-fold2: field `t4` deleted (no proof on the route uses it; g0-assemble2 §7)
  t5 : PkgI2.TorsionStructure.{0}
  t6 : PkgI3.HomFreeFinite
  t7 : PkgI3.CharPolyIndepOfEll
  t8 : PkgI3.PoincareReducibility
  t9 : LeafPush.T09_WeilPairing.{0}
  /-- T10, Galois-equivariant Tate duality (t10-etale, leaf-adopt3; replaces the placeholder): for
  an abelian variety `A/K` and a prime `ℓ ≠ char K`, a `ℤ_ℓ`-linear isomorphism
  `H¹_proet(A_K̄, ℤ_ℓ) ≅ Hom_{ℤ_ℓ}(T_ℓ A, ℤ_ℓ)` intertwining the Galois action `T10Etale.galH`
  (transport along `1 × Spec σ⁻¹`) with the contragredient action. Milne 1986 Thm 15.1(a) with the
  pro-étale/étale comparison of Bhatt–Scholze 2015 §5.6 (UNVERIFIED numbers). -/
  t10 : T10Etale.T10_TateDuality
  /-- T11(a), Riemann/GAGA for endomorphisms (leaf-push2). -/
  t11a : ZInQ.LeafPush2.T11a_RiemannEnd
  /-- T11(b), rigidity of homomorphisms under extension of an algebraically closed field
  (leaf-push2). -/
  t11b : ZInQ.LeafPush2.T11b_Rigidity
  -- leaf-adopt2: T12 is glue (`ZInQ.LeafPush2.T12_ComplexConjEigen`, a target), no longer a field.
  -- leaf-adopt3: T13 (Skolem–Noether) is proved (t-skolem-kw, `TSkolemKW.hsyn_t13`), no longer a field.
  -- hsyn-fix: the cochain forms I6.2a′-c′ (rv-leaves-b repair 3; Mathlib does not yet compare
  -- `continuousCohomology` with inhomogeneous cochains). `PkgI6.BrauerHasse2` etc. remain in the file.
  t14a : PkgI6.BrauerHasse2C
  t14b : PkgI6.BrauerReciprocity2C
  t15 : PkgI6.LocalH2CardC
  t16a : ∀ (p : ℕ) [Fact p.Prime], PkgI6.LocalKroneckerWeber p
  -- leaf-fold2: field `t16b` deleted (no proof on the route uses it; g0-assemble2 §7)
  /-- T17 narrowed (t-skolem-kw, leaf-adopt3): Kronecker–Weber for cyclic `L/ℚ`, the case C8
  uses; a consequence of `HSyn.KroneckerWeber` (`TSkolemKW.kroneckerWeberCyclic_of_hsyn`). C8's
  use form is proved from it (`TSkolemKW.hsyn_dirichletCharacter_of_kroneckerWeberCyclic`). -/
  t17 : TSkolemKW.KW.KroneckerWeberCyclic
  /-- T18 narrowed (t-skolem-kw, leaf-adopt3): Chebotarev, existence form; the density form
  `HSyn.FrobeniusDense` is proved from it (`TSkolemKW.hsyn_t18_of_chebotarev`). -/
  t18 : PkgI6.ChebotarevExists
  -- leaf-adopt3: T19 (Brauer–Nesbitt, char 0) is proved (t-skolem-kw, `TSkolemKW.hsyn_t19`).
  -- leaf-fold2: field `t20` deleted (no proof on the route uses it; g0-assemble2 §7)
  -- leaf-fold2: field `t21` deleted (no proof on the route uses it; g0-assemble2 §7)
  -- leaf-adopt3: T20, T21 in local form are proved (t-different: `PkgI6.hilbertDifferentFormula`,
  -- `PkgI6.differentBound`); the global forms above remain leaves. T22 (both parts) is proved
  -- (`PkgI6.herbrandQuotient`, `PkgI6.herbrandTransitivity`), no longer a field.
  t23 : ∀ (p : ℕ) [Fact p.Prime], PkgI4.T23_FontaineClosure p
  t24 : EigenformTwist
  t25 : PkgI4.NewformOfEigenform
  t26 : PkgI3.TateModuleFree
  t27 : PkgI3.QMDichotomyYu
  -- leaf-fold2: field `t28` deleted (no proof on the route uses it; g0-assemble2 §7)
  -- leaf-fold2: field `t29a` deleted (no proof on the route uses it; g0-assemble2 §7)
  -- leaf-fold2: field `t29b` deleted (no proof on the route uses it; g0-assemble2 §7)
  -- leaf-adopt3: T30 is proved from T16(a) (t30-adelic, `T30.leafSqrtCrit_of_t16a`).
  t31 : GlueDescent.B2Q.LeafUnramified
  -- leaf-adopt: T32 is glue (`HSyn.t32a_glue`, `HSyn.t32b_glue`), no longer a field.
  /-- T33 (new, leaf-modcurves): existence of the Jacobian of a pointed curve (Weil; Milne 1986). -/
  t33 : LeafModCurves.JacobianExists ℚ
  /-- T34 (new, leaf-modcurves): `dim J₁(N)` is the genus of `Γ₁(N)` (Shimura 1971 Prop. 1.40 with
  §6.7 and `dim Jac = genus`). -/
  t34 : LeafModCurves.DimJ1Genus
  /-- T35 (new, leaf-push2): analytic uniformization of `A(ℂ)_σ` by `ℂ^{dim A}` with a full
  lattice (Mumford §1 with GAGA; AN3 for abelian varieties). -/
  t35 : ZInQ.LeafPush2.UniformizationExists
  /-- T36-T40 (new, x1-belyi, leaf-adopt3): the five leaves from which `LeafModCurves.X1ModelExists`
  (`X1Belyi.x1ModelExists_of_leaves`) and `LeafModCurves.BelyiX1` (`X1Belyi.belyiX1_of_leaves`) are
  proved: T36 `TorsionStructure` (`E[N] ≅ (ℤ/N)²` over an algebraically closed field of
  characteristic 0; Silverman AEC III.6.4(b)), T37 `GoodReductionUnramified` (Néron–Ogg–Shafarevich
  over `k(T)`; Serre–Tate 1968 Thm 1), T38 `CurveOfFunctionFieldQ` (a function field over `ℚ` with
  constant field `ℚ` is that of a smooth proper curve; Hartshorne I.6, II.6.7), T39
  `X1ConstantField` (`ℚ` algebraically closed in `K_N`; Igusa 1959, Shimura 1971 §6.2), T40
  `X1RationalCusp` (`K_N` has a degree-one place). Locators UNVERIFIED. With T33 they make `r16`,
  `t34` non-vacuous (`X1Belyi.exists_J1_of_leaves`; rv-leaves48 P2). -/
  x1 : X1Belyi.X1Leaves
  /-- T41 (new, h5-neron, leaf-adopt3): **Néron models exist** (leaf N1): for an abelian variety
  `A/K` and a number field `L ⊇ K`, `A_L` has a smooth group model over `𝓞_L` with the Néron
  mapping property (Bosch–Lütkebohmert–Raynaud 1.2/1, 1.4/3; UNVERIFIED locators). With H5's
  `NeronModelMinimal` and the glue piece `ProductModelHeight` it gives E4's additivity
  (`ZInQ.H5Neron.heightAdditivity_unfolded`). -/
  t41 : ZInQ.H5Neron.NeronModelExists


/-! ### leaf-adopt3 (2026-11-13): former bundle fields, now theorems or consequences of narrower fields

Wave 25 proved T13, T19, T22 (both parts) and T30 (from T16(a)), narrowed T17 and T18, made T10
concrete and added the leaves T36-T41. The former fields remain available as theorems. -/

/-- T13, Skolem–Noether (t-skolem-kw; proved, no leaf). -/
theorem t13_proved : SkolemNoether := TSkolemKW.hsyn_t13

/-- T19, Brauer–Nesbitt in characteristic 0, matrix form (t-skolem-kw; proved, no leaf). -/
theorem t19_proved : BrauerNesbitt := TSkolemKW.hsyn_t19

/-- T22(a), Herbrand's quotient formula (t-different; proved, no leaf). -/
theorem t22a_proved : PkgI6.HerbrandQuotient := PkgI6.herbrandQuotient

/-- T22(b), transitivity of Herbrand's function (t-different; proved, no leaf). -/
theorem t22b_proved : PkgI6.HerbrandTransitivity := PkgI6.herbrandTransitivity

/-- T20 in local form (I6.7, t-different; proved). The global form `t20` remains a leaf. -/
theorem t20_local_proved : PkgI6.HilbertDifferentFormula := PkgI6.hilbertDifferentFormula

/-- T21 in local form (I6.6, t-different; proved). The global form `t21` remains a leaf. -/
theorem t21_local_proved : PkgI6.DifferentBound := PkgI6.differentBound

/-- T18's density form from the narrowed field `t18 : ChebotarevExists` (t-skolem-kw). -/
theorem TextbookLeaves.frobeniusDense (t : TextbookLeaves) : FrobeniusDense :=
  TSkolemKW.hsyn_t18_of_chebotarev t.t18

/-- T30 from T16(a) (t30-adelic). -/
theorem TextbookLeaves.leafSqrtCrit (t : TextbookLeaves) : GlueDescent.B2Q.LeafSqrtCrit :=
  T30.leafSqrtCrit_of_t16a t.t16a

/-- leaf-push2's group-isomorphism form of T10 from the Galois-equivariant field (t10-etale). -/
theorem TextbookLeaves.t10_groupIso (t : TextbookLeaves) : ZInQ.LeafPush2.T10_groupIso :=
  T10Etale.T10_groupIso_of_tateDuality t.t10

/-- `X₁(N)` has a model over `ℚ` (leaf-modcurves' glue target, x1-belyi; from T36, T38-T40). -/
theorem TextbookLeaves.x1ModelExists (t : TextbookLeaves) : LeafModCurves.X1ModelExists :=
  (X1Belyi.x1ModelExists_and_belyiX1 t.x1).1

/-- `j/1728` is a Belyi function of degree `≤ N²` on `K_N` (E2's Belyi half, x1-belyi; from T36,
T37). -/
theorem TextbookLeaves.belyiX1 (t : TextbookLeaves) : LeafModCurves.BelyiX1 :=
  (X1Belyi.x1ModelExists_and_belyiX1 t.x1).2

/-- Non-vacuity of `IsJ1` (so of `r16`, `t34`; rv-leaves48 P2): a `J₁(N)` exists, from T33 and
T36, T38-T40 (x1-belyi). -/
theorem TextbookLeaves.exists_J1 (t : TextbookLeaves) (N : ℕ) (hN : 0 < N) :
    ∃ J : PkgI3.AbVar ℚ, LeafModCurves.IsJ1 N J :=
  X1Belyi.exists_J1_of_leaves t.x1 t.t33 N hN

/-- leaf-modcurves' bundle `ModCurveLeaves` from the two bundles (x1-belyi). -/
theorem modCurveLeaves_of_bundles (r : ResearchLeaves) (t : TextbookLeaves) :
    LeafModCurves.ModCurveLeaves :=
  X1Belyi.modCurveLeaves_of t.x1 t.t33 r.r16 t.t34


/-! ## §3′. g0-split: the glue G1-G17, G19 split into named pieces (task g0-split, 2026-11-12;
folded into this file by leaf-adopt3, 2026-11-13, following g0-split's recipe, doc §4)

`GlueAssembly.GlueOutputs Mult.S_mul` asks, for each `u ∉ 𝒞`, for a number field `K'`, a point
`z ∈ K'¹⁰`, a real `h_A`, and

* (o1) `Φ(z) = J(u)` (step F1, glue G19),
* (o2) Pazuki's bound `h(z) ≤ …(h_A)` (step F3, glue G19, leaf R22),
* (o3) `NonCMOutput Q M h_A`: a level `N` with `1 ≤ N ≤ QM²` (G13-G16), `h_F(J₁(N)) ≤ 1.3·10⁷N¹²`
  (G18/E2, leaf R18), `2 ≤ g ≤ N²` (G17 for `2 ≤ g`; E2 for `g ≤ N²`, proved from T34),
  `1 ≤ d = [L':ℚ] ≤ QM` (G7, B3), Gaudron-Rémond's `log deg φ` (E3, R19, on the isogeny of G17),
  Faltings' variation with additivity (E4, R20 + additivity) and Bost (R21); or the CM branch,
  which the route does not use (G6, NoCM).

Below, `h_A` is the stable Faltings height (def-faltings) of an abelian surface `A` over a number
field `L'` attached to `u` (`FibreOver`). Proved pieces applied: A4 (`exists_fibre_object`,
leaf-qm-fp), `model_dim`, H5's finiteness, E1 (`PkgI3.E1_exists_hom_ne_zero` with glue-ssbc's
`SemisimpleBaseChange`, copied in section `GlueSSBCSec`), T8 (Poincaré, a leaf), E2's
`dim J₁(N) ≤ N²` (`LeafModCurves.dim_J1_le`, from T34), `javanpeykarJ1` (from leaf-push2's
concrete R18), `thetaPazuki` (from leaf-push2's concrete R22) and the E3-E4 numerics
(`transfer_core`, from R19, R20, R21), `isogenousProduct`. leaf-adopt3: R18 and R22 are now the bundle
fields `r.r18`, `r.r22` (leaf-push2's statements over `ZInQ.LeafPush2.stableFaltingsHeight`);
g0-split's transported forms `R18_JavanpeykarConcrete`, `R22_PazukiConcrete` (over def-faltings'
height) are derived from them with the glue piece `HSyn.HeightCopiesAgree` (leaf-adopt2's glue
target, pure transport between the two textual copies of the height): `r18Concrete_of`,
`r22Concrete_of`. g0-split's copies of leaf-push2's R22 definitions and of `ffAlgebra`,
`javanpeykarBound` are replaced by the `ZInQ.LeafPush2` originals (identical text). The ten
missing glue pieces, smallest first (sizes SPECULATIVE), and `HeightCopiesAgree` form the bundle
`HSyn.GluePieces`:
1. `DimFinite` (an abelian variety has finite dimension),
2. `DimBaseChange` (dimension invariant under field extension),
3. `X1BelyiOnModel` (`BelyiX1` on the model of `IsJ1`; leaf-adopt3: proved, not in the bundle),
4. `FibreSimple` (G5-G6 on `A`),
5. `HeightAdditivity` (E4; leaf-adopt3: proved from T41, H5 and the piece `ProductModelHeight`),
6. `StableHeightBaseChange` (stable height invariant under base change),
7. `ProductExists` (G17: `A × Z` is an abelian variety),
8. `ReverseIsogeny` (G17: the isogeny `J → A × Z`),
9. `ThetaPointOfFibre` (G19, F1 on `A`),
10. `ModularConstituent` (G2, G4, G7-G16).
`glueOutputs_of_leaves` takes them as the bundle `HSyn.GluePieces`. -/

namespace G0Split

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ ZInQ.JHeight LeafQM.AV ZInQ.DefFaltings

/-- `A`, an abelian variety over the number field `K` (def-faltings' `AbVar`), is (up to
isomorphism of `ℚ̄`-schemes, after some embedding `K → ℚ̄`) the abelian surface of an object
`(A, ι, η)` of `Y₃` at a `ℚ̄`-point `y` of `Y₃` lying over `J(u)` (for the moduli data
`(Y, Φ, π)` that R1-R2 provide). -/
def FibreOver (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (K : GlueAssembly.NF) (A : ZInQ.DefFaltings.AbVar K.K) : Prop :=
  ∃ (emb : K.K →+* Qbar) (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar),
    Φ Qbar y = M3.mk P ∧ π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar (Jmap u)) ∧
    (letI : Algebra K.K Qbar := emb.toAlgebra; Nonempty ((A.baseChange Qbar).X ≅ P.A.X))

/-- `P ≅ A × Z` as group schemes: homomorphisms `p₁ : P → A`, `p₂ : P → Z` with
`(p₁, p₂) : P → A × Z` an isomorphism. -/
def IsProductOf {K : Type} [Field K] (P A Z : Over (Spec (CommRingCat.of K))) [MonObj P]
    [MonObj A] [MonObj Z] : Prop :=
  ∃ (p₁ : P ⟶ A) (p₂ : P ⟶ Z), IsMonHom p₁ ∧ IsMonHom p₂ ∧ IsIso (lift p₁ p₂)

/-- The hypotheses of E1 (`PkgI3.E1_exists_hom_ne_zero`): for some prime `ℓ` and field `E ⊇ ℚ_ℓ`,
`V_ℓ(A) ⊗ E` and `V_ℓ(J) ⊗ E` have a common nonzero constituent, as `G_K`-representations. -/
def CommonConstituent {K : Type} [Field K] [NumberField K] (A J : PkgI3.AbVar K) : Prop :=
  ∃ (ℓ : ℕ) (_ : Fact ℓ.Prime) (E : Type) (_ : Field E) (_ : Algebra ℚ_[ℓ] E)
    (U : Subrepresentation (GlueI3.repBaseChange E (A.galRep ℓ)))
    (U' : Subrepresentation (GlueI3.repBaseChange E (J.galRep ℓ)))
    (e : U.toSubmodule ≃ₗ[E] U'.toSubmodule), U ≠ ⊥ ∧
    ∀ g (u : U.toSubmodule),
      (e ⟨GlueI3.repBaseChange E (A.galRep ℓ) g u, U.apply_mem_toSubmodule g u.2⟩ :
        TensorProduct ℚ_[ℓ] E (J.V ℓ)) = GlueI3.repBaseChange E (J.galRep ℓ) g (e u)

/-! ### The missing pieces, smallest first -/

/-- **Missing piece 2 (definition-level glue; used by G18/E2 and G17).** The dimension of an
abelian variety is invariant under extension of the base field (Stacks, Tag 00P4 for finitely
generated algebras over a field; STANDARD). -/
def DimBaseChange : Prop :=
  ∀ (K : Type) [Field K] (L : Type) [Field L] [Algebra K L] (A : ZInQ.DefFaltings.AbVar K),
    (A.baseChange L).dim = A.dim

/-- **Missing piece 6 (definition-level glue; used by E3-E4).** The *stable* Faltings
height is invariant under finite extension of the number field (Faltings 1983 §1; Deligne,
Sém. Bourbaki 616). For def-faltings' infimum this needs semistable reduction and the Néron
models of H5 (`NeronModelMinimal`); it is a property of the definition, not a literature leaf. -/
def StableHeightBaseChange : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (L : Type) [Field L] [NumberField L] [Algebra K L]
    (A : ZInQ.DefFaltings.AbVar K),
    stableFaltingsHeight (A.baseChange L) = stableFaltingsHeight A

/-- **R18 (Javanpeykar, ANT 8 (2014), Thm 1.1.1), transported: leaf-push2's `R18_Javanpeykar`**
(`ResearchLeaves.r18`) on this file's copies (`LeafModCurves.IsCurve`, `IsJacobian`,
`IsBelyiFunction` are textual copies of leaf-push2's; the height is def-faltings'
`stableFaltingsHeight` through `LeafAdopt.abVarEquiv`). leaf-adopt3: no longer a hypothesis; it is
derived (`r18Concrete_of`) from `r.r18` and the glue piece `HSyn.HeightCopiesAgree`. -/
def R18_JavanpeykarConcrete : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (X : Over (Spec (CommRingCat.of K)))
    [LeafModCurves.IsCurve X] [IsIntegral X.left] (P₀ : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ X)
    (J : PkgI3.AbVar K) (aj : X ⟶ J.X), LeafModCurves.IsJacobian X P₀ J aj →
    ∀ g : ℕ, J.dim = (g : WithBot ℕ∞) → 1 ≤ g →
    ∀ t : X.left.functionField,
      letI := ZInQ.LeafPush2.ffAlgebra X
      LeafModCurves.IsBelyiFunction K X.left.functionField t →
      ∀ d : ℕ, Module.finrank (IntermediateField.adjoin K {t}) X.left.functionField = d → 0 < d →
        stableFaltingsHeight ((LeafAdopt.abVarEquiv K).symm J) ≤ ((ZInQ.LeafPush2.javanpeykarBound g d : ℝ) : EReal)

/-- **Missing piece 3 (glue E2, Belyi half: `LeafModCurves.BelyiX1` on the model of `IsJ1`).**
Every `J₁(N)` over `ℚ` (`IsJ1 N J`) is the Jacobian of a pointed curve `X` whose function field
carries a Belyi function `t` (`j/1728`) of degree `[ℚ(X) : ℚ(t)] ≤ N²`. From `BelyiX1` (a glue
target of leaf-modcurves: good reduction of `E_j` away from `j = 0, 1728, ∞`, and
`[K_N : ℚ(j)] ≤ N²`) by transport along `ℚ(X) ≅ K_N` (`IsX1Model`). leaf-adopt3: the transport
is done (`x1BelyiOnModel_of_belyiX1`) and `BelyiX1` is proved from T36, T37 (x1-belyi), so this
is no longer a glue piece. -/
def X1BelyiOnModel : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ J : PkgI3.AbVar ℚ, LeafModCurves.IsJ1 N J →
    ∃ (X : Over (Spec (CommRingCat.of ℚ))) (_ : LeafModCurves.IsCurve X) (_ : IsIntegral X.left)
      (P₀ : 𝟙_ (Over (Spec (CommRingCat.of ℚ))) ⟶ X) (aj : X ⟶ J.X),
      LeafModCurves.IsJacobian X P₀ J aj ∧ ∃ t : X.left.functionField,
        (letI := ZInQ.LeafPush2.ffAlgebra X; LeafModCurves.IsBelyiFunction ℚ X.left.functionField t) ∧
        ∃ d : ℕ,
          (letI := ZInQ.LeafPush2.ffAlgebra X
           Module.finrank (IntermediateField.adjoin ℚ {t}) X.left.functionField = d) ∧
          0 < d ∧ d ≤ N ^ 2

/-- **G18/E2: R18 applied to `X₁(N)` (proved below, `javanpeykarJ1`, from
`R18_JavanpeykarConcrete`, `X1BelyiOnModel` and T34).** For every `N ≥ 1` and every `J₁(N)` of
positive dimension over `ℚ`, `h_F(J₁(N)) ≤ 1.3·10⁷N¹²`. -/
def JavanpeykarJ1 : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ J : PkgI3.AbVar ℚ, LeafModCurves.IsJ1 N J →
    ∀ g : ℕ, J.dim = (g : WithBot ℕ∞) → 1 ≤ g →
    ∀ x : ℝ, stableFaltingsHeight ((LeafAdopt.abVarEquiv ℚ).symm J) = x →
      x ≤ 13000000 * (N : ℝ) ^ 12

/-- **Missing piece 5 (glue E4, the additivity half that the transfer uses).**
`h_F(A) + h_F(Z) ≤ h_F(A × Z)` for abelian varieties over a number field (equality holds;
Faltings 1983 §1; needs Néron models and H5, rv-blueprints F1). -/
def HeightAdditivity : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (P A Z : ZInQ.DefFaltings.AbVar L),
    IsProductOf P.X A.X Z.X → ∀ a z p : ℝ, stableFaltingsHeight A = a →
      stableFaltingsHeight Z = z → stableFaltingsHeight P = p → a + z ≤ p

/-- **Missing piece 1 (definition-level glue).** An abelian variety has finite dimension: its
Krull dimension is a natural number (a scheme of finite type over a field; STANDARD). -/
def DimFinite : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K), ∃ n : ℕ, A.dim = (n : WithBot ℕ∞)

/-- **Missing piece 7 (definition-level glue; G17).** The product `A × Z` of abelian varieties is an
abelian variety `P` (proper, smooth, geometrically integral group scheme), with
`dim P = dim A + dim Z` (Mumford §4; STANDARD; geometric integrality of products is not in
Mathlib). -/
def ProductExists : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (A Z : PkgI3.AbVar L),
    ∃ P : ZInQ.DefFaltings.AbVar L, IsProductOf P.X A.X Z.X ∧ P.dim = A.dim + Z.dim

/-- **Missing piece 8 (glue G17, after Poincaré).** If `(f, g) : A × Z → J` is finite and surjective
(T8's output) and `P ≅ A × Z`, there is an isogeny `J → P` in the other direction, and
`dim J = dim P` (Mumford §8, Thm 4 / Remark, UNVERIFIED: an isogeny of degree `n` has a
quasi-inverse `ψ` with `φψ = [n]`). Needs finite group schemes and quotients, not in Mathlib. -/
def ReverseIsogeny : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (A J Z : PkgI3.AbVar L) (P : ZInQ.DefFaltings.AbVar L)
    (f : PkgI3.AbVar.Hom A J) (g : PkgI3.AbVar.Hom Z J), IsProductOf P.X A.X Z.X →
    PkgI3.AbVar.IsIsogenyMor (fst A.X Z.X ≫ f.hom * snd A.X Z.X ≫ g.hom) →
    ∃ φ : ((LeafAdopt.abVarEquiv L).symm J).X ⟶ P.X, ZInQ.DefFaltings.IsIsogeny φ ∧ J.dim = P.dim

/-- **G17 after Poincaré (proved below, `isogenousProduct`, from `DimFinite`, `ProductExists`,
`ReverseIsogeny`).** From T8's isogeny `(f, g) : A × Z → J` to Gaudron-Rémond's input: `P ≅ A × Z`,
an isogeny `J → P`, and `dim J = dim A + dim Z`. -/
def IsogenousProduct : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (A J Z : PkgI3.AbVar L) (f : PkgI3.AbVar.Hom A J)
    (g : PkgI3.AbVar.Hom Z J),
    PkgI3.AbVar.IsIsogenyMor (fst A.X Z.X ≫ f.hom * snd A.X Z.X ≫ g.hom) →
    ∃ (P : ZInQ.DefFaltings.AbVar L) (φ : ((LeafAdopt.abVarEquiv L).symm J).X ⟶ P.X),
      ZInQ.DefFaltings.IsIsogeny φ ∧ IsProductOf P.X A.X Z.X ∧
      ∀ a n : ℕ, A.dim = a → J.dim = n → ∃ m : ℕ, Z.dim = m ∧ a + m = n

/-- **Missing piece 4 (glue G5-G6 on the actual `A`: QM dichotomy and NoCM).** For `u ∉ 𝒞`, the
fibre surface `A` (any number-field model of it) is simple over its field: every nonzero
endomorphism is an isogeny (because `End⁰(A_ℚ̄) = B` is a division algebra). Proved parts: T27 at
`B = (2,-3)` (`PkgI3.qmDichotomy_B6`), the Elkies identities and the free `W`-orbit
(`GlueRepo.PR.fibre_free`), `cm_of_val`. Missing: the instantiation on `A` and the counting with
R5 (h-decomposition G6). -/
def FibreSimple : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ u : ℚ, u ∉ contactSet →
    ∀ (K : GlueAssembly.NF) (A : ZInQ.DefFaltings.AbVar K.K), FibreOver Y Φ π u K A →
      PkgI3.EndDivision (LeafAdopt.abVarEquiv K.K A)

/-- **R22 (Pazuki, Bull. SMF 140 (2012), Cor. 1.3(2)), transported: leaf-push2's `R22_Pazuki`**
(`ResearchLeaves.r22`; same statement, the height is def-faltings' `stableFaltingsHeight` through
`LeafAdopt.abVarEquiv`). leaf-adopt3: no longer a hypothesis; it is derived (`r22Concrete_of`)
from `r.r22` and the glue piece `HSyn.HeightCopiesAgree`. -/
def R22_PazukiConcrete : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K), A.dim = (2 : WithBot ℕ∞) →
    ∀ x : ℝ, stableFaltingsHeight ((LeafAdopt.abVarEquiv K).symm A) = x →
    ∀ X : ℝ, max 1 (x + Real.log Real.pi) ≤ X →
    ∀ (σ : K →+* ℂ) (Λ : Submodule ℤ (Fin 2 → ℂ)) (Φ : (Fin 2 → ℂ) → ZInQ.LeafPush2.CPts A σ),
      ZInQ.LeafPush2.IsUniformization σ Λ Φ →
    ∀ Ω : Matrix (Fin 2) (Fin 2) ℂ, ZInQ.LeafPush2.IsSiegel Ω → ZInQ.LeafPush2.IsPeriodMatrix Λ Ω →
    ∀ (L : Type) [Field L] [NumberField L] (emb : L →+* ℂ) (z : ZInQ.LeafPush2.Char2 → L) (c : ℂ), c ≠ 0 →
      (∀ m, emb (z m) = c * ZInQ.LeafPush2.thetaConst Ω m) →
      ZInQ.LeafPush2.absLogHeight z ≤ X / 2 + ZInQ.LeafPush2.pazukiC2 * Real.log (X + 2)

/-- **Missing piece 9 (glue G19, F1 on the actual `A`).** For `u ∉ 𝒞` and the fibre surface `A`
over `J(u)` (any number-field model): at some complex place `σ` there are an analytic
uniformization `Φ` of `A(ℂ)_σ` with kernel `Λ`, a period matrix `Ω ∈ 𝔥₂` of `Λ` (for the principal
polarization), and an algebraic representative `z ∈ L¹⁶` of the theta-null point `[θ_m(0, Ω)]`;
and its ten even coordinates `z'` (in a number field `K'`) satisfy `Φ(z') = J(u)` with
`h(z') ≤ h(z)` (the six odd theta nulls vanish). F1: Lin-Yang's Igusa invariants on the QM locus
(R3) with the theta expressions of `ψ₄`, `χ₁₀` (R4). Proved parts: F1's algebra
(`PkgI1.f1_algebra`), theta-structure independence (`PkgI1.thetaRatio_invariant`), leaf-push2's
`linYangTuple_onQMLocus` (not copied). Missing: the analytic side (R1(b), uniformization:
leaf-push2's `UniformizationExists`), R3 and R4 applied to `A`, algebraicity of the theta point,
the odd-zero height comparison. -/
def ThetaPointOfFibre : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ u : ℚ, u ∉ contactSet →
    ∀ (K : GlueAssembly.NF) (A : ZInQ.DefFaltings.AbVar K.K), FibreOver Y Φ π u K A →
    ∃ (σ : K.K →+* ℂ) (Λ : Submodule ℤ (Fin 2 → ℂ))
      (Φu : (Fin 2 → ℂ) → ZInQ.LeafPush2.CPts (LeafAdopt.abVarEquiv K.K A) σ), ZInQ.LeafPush2.IsUniformization σ Λ Φu ∧
    ∃ Ω : Matrix (Fin 2) (Fin 2) ℂ, ZInQ.LeafPush2.IsSiegel Ω ∧ ZInQ.LeafPush2.IsPeriodMatrix Λ Ω ∧
    ∃ (L : GlueAssembly.NF) (emb : L.K →+* ℂ) (z : ZInQ.LeafPush2.Char2 → L.K) (c : ℂ), c ≠ 0 ∧
      (∀ m, emb (z m) = c * ZInQ.LeafPush2.thetaConst Ω m) ∧
    ∃ (K' : GlueAssembly.NF) (z' : Fin 10 → K'.K),
      3779136 * (∏ i, z' i) ^ 4 / (∑ i, z' i ^ 8) ^ 5 = algebraMap ℚ K'.K (Jmap u) ∧
      Height.logHeight z' / Module.finrank ℚ K'.K ≤ ZInQ.LeafPush2.absLogHeight z

/-- **G19: F1 and F3 on the actual `A` (proved below, `thetaPazuki`, from
`R22_PazukiConcrete` and `ThetaPointOfFibre`).** For `u ∉ 𝒞` and the fibre surface `A` over
`J(u)` with stable height `x`, a point `z ∈ K'¹⁰` with `Φ(z) = J(u)` and Pazuki's bound. -/
def ThetaPazuki : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ u : ℚ, u ∉ contactSet →
    ∀ (K : GlueAssembly.NF) (A : ZInQ.DefFaltings.AbVar K.K), FibreOver Y Φ π u K A →
    A.dim = 2 → ∀ x : ℝ, stableFaltingsHeight A = x →
      ∃ (K' : GlueAssembly.NF) (z : Fin 10 → K'.K),
        3779136 * (∏ i, z i) ^ 4 / (∑ i, z i ^ 8) ^ 5 = algebraMap ℚ K'.K (Jmap u) ∧
        GlueAssembly.PazukiOutput (Height.logHeight z / Module.finrank ℚ K'.K) x

/-- **Missing piece 10 (glue G2, G4, G7-G16: fibre field, scalar descent, modularity, conductor).**
For `u ∉ 𝒞` and an object `P` of `Y₃` over `ℚ̄` at a point over `J(u)`: there are a number field
`L' ⊆ ℚ̄` with `[L':ℚ] ≤ QM` (G2, G4, G7: the fibre field, the Hom field and B3) and a model `A`
of `P`'s surface over `L'`, a level `1 ≤ N ≤ QM²` (G13-G16: the conductor of the newform `f`), a
`J₁(N)` over `ℚ`, and a common constituent of `V_ℓ(A)` and `V_ℓ(J₁(N)_{L'})` as
`G_{L'}`-representations (G8-G14: `r_ℓ`, its twist, Pan-Berger modularity, the newform and
Eichler-Shimura). Here `Q = Q_D`, `M = M_{S_mul}(u)`. The model and the field are produced
together because `[L':ℚ] ≤ QM` bounds the field of `A`: quantifying over all models would make the
piece false. Proved cores (not on the actual `A`): `GlueDescent.B3Q.b3_degree_le_QM` (B3),
`GlueConductor.level_le` (G16), `GlueConductor.D1_genuine` (D1), `PkgI2.D2_fixed_of_raynaud`,
`PkgI6.artinConductor_le_of_upper`, `PkgI3.C2_absolutelyIrreducible`, `HSyn.weight_match`,
`GlueAssembly.twist_finite`, `LeafModCurves.g13_constituent`, `GlueC10.c10`,
`PkgI2.goodReduction_of_QM_rational3` (G3), `PkgI2.inertiaTrivial_of_goodReduction` (G11).
Missing: the instantiation of all of these on `A`, the appendix lemma (G9), oddness (G10, needs
T11-T12, placeholders) and Carayol's conductor (R17, a placeholder). -/
def ModularConstituent : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ u : ℚ, u ∉ contactSet →
    ∀ (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar), Φ Qbar y = M3.mk P →
      π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar (Jmap u)) →
    ∃ (L : GlueAssembly.NF) (emb : L.K →+* Qbar) (A : ZInQ.DefFaltings.AbVar L.K) (N : ℕ)
      (J : PkgI3.AbVar ℚ),
      (letI : Algebra L.K Qbar := emb.toAlgebra; Nonempty ((A.baseChange Qbar).X ≅ P.A.X)) ∧
      0 < N ∧ LeafModCurves.IsJ1 N J ∧
      (N : ℝ) ≤ heightQ heightD * (contactSupport Mult.S_mul u : ℝ) ^ 2 ∧
      (Module.finrank ℚ L.K : ℝ) ≤ heightQ heightD * (contactSupport Mult.S_mul u : ℝ) ∧
      CommonConstituent (LeafAdopt.abVarEquiv L.K A)
        (LeafAdopt.abVarEquiv L.K (((LeafAdopt.abVarEquiv ℚ).symm J).baseChange L.K))

/-! ### Proved connective pieces -/

/-- **R18 transported (proved, leaf-adopt3)** from leaf-push2's `R18_Javanpeykar` (the bundle
field `r18`) and `HeightCopiesAgree`. The curve, Jacobian and Belyi predicates of
`LeafModCurves` and `ZInQ.LeafPush2` are textual copies, converted field by field. -/
theorem r18Concrete_of (h : ZInQ.LeafPush2.R18_Javanpeykar) (hH : HeightCopiesAgree) :
    R18_JavanpeykarConcrete := by
  intro K _ _ X hX _ P₀ J aj hJac g hg hg1 t ht d hd hd0
  haveI : ZInQ.LeafPush2.IsCurve X := ⟨hX.proper, hX.smooth, hX.geomConnected⟩
  rw [← hH K J]
  exact h K X P₀ J aj ⟨hJac.base, hJac.univ⟩ g hg hg1 t ht d hd hd0

/-- **R22 transported (proved, leaf-adopt3)** from leaf-push2's `R22_Pazuki` (the bundle field
`r22`) and `HeightCopiesAgree`. -/
theorem r22Concrete_of (h : ZInQ.LeafPush2.R22_Pazuki) (hH : HeightCopiesAgree) :
    R22_PazukiConcrete := by
  intro K _ _ A hA x hx
  rw [← hH K A] at hx
  exact h K A hA x hx

/-- Isomorphic schemes over `S` have the same Krull dimension. -/
theorem dim_eq_of_iso {S : Scheme} {X Y : Over S} (e : X ≅ Y) :
    topologicalKrullDim X.left = topologicalKrullDim Y.left :=
  IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso ((Over.forget S).mapIso e)).isHomeomorph

/-- **The model is a surface (proved from `DimBaseChange`).** A model over `L` of an abelian
surface over `ℚ̄` has dimension `2`. -/
theorem model_dim (hDim : DimBaseChange) {L : Type} [Field L] (emb : L →+* Qbar)
    (A : ZInQ.DefFaltings.AbVar L) (B : PkgI3.AbVar Qbar)
    (hiso : letI : Algebra L Qbar := emb.toAlgebra; Nonempty ((A.baseChange Qbar).X ≅ B.X))
    (hB : B.dim = 2) : A.dim = 2 := by
  letI : Algebra L Qbar := emb.toAlgebra
  obtain ⟨e⟩ : Nonempty ((A.baseChange Qbar).X ≅ B.X) := hiso
  rw [← hDim L Qbar A, ← hB]
  exact dim_eq_of_iso e

/-- **G18/E2, Javanpeykar on `J₁(N)` (proved).** From the concrete R18, the Belyi data on the
model (`X1BelyiOnModel`) and E2's `dim J₁(N) ≤ N²` (`LeafModCurves.dim_J1_le`, from T34):
`13·10⁶·g·d⁵ ≤ 13·10⁶·N²·(N²)⁵`. -/
theorem javanpeykarJ1 (hR18 : R18_JavanpeykarConcrete) (hB : X1BelyiOnModel)
    (hT34 : LeafModCurves.DimJ1Genus) : JavanpeykarJ1 := by
  intro N hN J hJ g hg hg1 x hx
  obtain ⟨X, _, _, P₀, aj, hJac, t, ht, d, hd, hd0, hdN⟩ := hB N hN J hJ
  have h := hR18 ℚ X P₀ J aj hJac g hg hg1 t ht d hd hd0
  rw [hx] at h
  have hxb : x ≤ ZInQ.LeafPush2.javanpeykarBound g d := EReal.coe_le_coe_iff.mp h
  obtain ⟨g', hg', hgN⟩ := LeafModCurves.dim_J1_le hT34 N hN J hJ
  have hgg : g = g' := by
    have : (g : WithBot ℕ∞) = (g' : WithBot ℕ∞) := hg.symm.trans hg'
    exact_mod_cast this
  subst hgg
  have hgR : (g : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hgN
  have hdR : (d : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hdN
  calc x ≤ ZInQ.LeafPush2.javanpeykarBound g d := hxb
    _ = 13 * 10 ^ 6 * (g : ℝ) * (d : ℝ) ^ 5 := rfl
    _ ≤ 13 * 10 ^ 6 * ((N : ℝ) ^ 2) * ((N : ℝ) ^ 2) ^ 5 := by gcongr
    _ = 13000000 * (N : ℝ) ^ 12 := by ring

/-- **G19, F1 + F3 (proved)** from the concrete R22 at `X = max(1, h_F(A) + 3) ≥ max(1, h_F(A) +
log π)` (the hardened form of `PazukiOutput`, rv-leaves-a) and the
theta point of `ThetaPointOfFibre`. -/
theorem thetaPazuki (hR22 : R22_PazukiConcrete) (hT : ThetaPointOfFibre) : ThetaPazuki := by
  intro Y Φ π h1 h2 u hu K A hFib hA2 x hx
  obtain ⟨σ, Λ, Φu, hΦu, Ω, hΩ, hP, L, emb, z, c, hc, hz, K', z', hF1, hle⟩ :=
    hT Y Φ π h1 h2 u hu K A hFib
  refine ⟨K', z', hF1, ?_⟩
  have hx' : stableFaltingsHeight ((LeafAdopt.abVarEquiv K.K).symm
      (LeafAdopt.abVarEquiv K.K A)) = x := by
    rw [Equiv.symm_apply_apply]; exact hx
  have hpi : Real.log Real.pi ≤ 3 := by
    have h4 : Real.log Real.pi ≤ Real.log 4 :=
      Real.log_le_log Real.pi_pos (by linarith [Real.pi_lt_four])
    have h42 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith [Real.log_two_lt_d9]
  have h := hR22 K.K (LeafAdopt.abVarEquiv K.K A) hA2 x hx' (max 1 (x + 3))
    (max_le_max le_rfl (by linarith)) σ Λ Φu hΦu Ω hΩ hP L.K emb z c hc hz
  unfold GlueAssembly.PazukiOutput
  unfold ZInQ.LeafPush2.pazukiC2 at h
  linarith

/-- **G17 after Poincaré (proved)** from `DimFinite`, `ProductExists`, `ReverseIsogeny`. -/
theorem isogenousProduct (hF : DimFinite) (hP : ProductExists) (hR : ReverseIsogeny) :
    IsogenousProduct := by
  intro L _ _ A J Z f g hiso
  obtain ⟨P, hPA, hPd⟩ := hP L A Z
  obtain ⟨φ, hφ, hJd⟩ := hR L A J Z P f g hPA hiso
  refine ⟨P, φ, hφ, hPA, fun a n ha hn => ?_⟩
  obtain ⟨m, hm⟩ := hF L Z
  refine ⟨m, hm, ?_⟩
  have h : ((n : ℕ) : WithBot ℕ∞) = ((a + m : ℕ) : WithBot ℕ∞) := by
    rw [← hn, hJd, hPd, ha, hm, Nat.cast_add]
  exact_mod_cast h.symm

/-- `log κ` of Gaudron-Rémond, computed. -/
theorem log_grKappa (g d : ℕ) (x : ℝ) (hg : 1 ≤ g) (hd : 1 ≤ d) :
    Real.log (grKappa g d x) = 1024 * (g : ℝ) ^ 3 * (64 * (g : ℝ) ^ 2 * Real.log (14 * g) +
      Real.log d + 2 * Real.log (max x (max (Real.log d) 1))) := by
  have hg' : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h14 : (0 : ℝ) < 14 * g := by positivity
  have hm : (1 : ℝ) ≤ max (max x (Real.log d)) 1 := le_max_right _ _
  have ha : ((14 * g : ℝ) ^ (64 * g ^ 2)) ≠ 0 := (pow_pos h14 _).ne'
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have hm2 : (max (max x (Real.log d)) 1) ^ 2 ≠ 0 := (pow_pos (by linarith) _).ne'
  unfold grKappa
  rw [Real.log_pow, Real.log_mul (mul_ne_zero ha hd0) hm2, Real.log_mul ha hd0, Real.log_pow,
    Real.log_pow, max_assoc]
  push_cast
  ring

theorem one_le_grKappa (g d : ℕ) (x : ℝ) (hg : 1 ≤ g) (hd : 1 ≤ d) : 1 ≤ grKappa g d x := by
  have hg' : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h14 : (1 : ℝ) ≤ 14 * g := by linarith
  have hm : (1 : ℝ) ≤ max (max x (Real.log d)) 1 := le_max_right _ _
  unfold grKappa
  apply one_le_pow₀
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ h14) hd')
    (one_le_pow₀ hm)

/-- **E3-E4 numerics on concrete objects (proved from R19, R20, R21).** Over a number field `L`,
for `J` of dimension `g ≥ 2` with an isogeny `J → P`, `h_F(A) + h_F(Z) ≤ h_F(P)`, `dim Z ≤ g`,
the bounds on `N`, `[L:ℚ]`, `h_F(J)` and `g ≤ N²` give glue-assembly's `NonCMOutput`. -/
theorem transfer_core (r19 : R19_GaudronRemond) (r20 : R20_FaltingsLemma5) (r21 : R21_Bost)
    {L : Type} [Field L] [NumberField L] (J P A Z : ZInQ.DefFaltings.AbVar L) (g gZ : ℕ)
    (hJd : J.dim = (g : WithBot ℕ∞)) (hZd : Z.dim = (gZ : WithBot ℕ∞)) (hgZ : gZ ≤ g)
    (hg2 : 2 ≤ g) (φ : J.X ⟶ P.X) (hφ : IsIsogeny φ) (x y a z : ℝ)
    (hx : stableFaltingsHeight J = x) (hy : stableFaltingsHeight P = y)
    (hz : stableFaltingsHeight Z = z) (hadd : a + z ≤ y) {Q M N : ℝ} (hN1 : 1 ≤ N)
    (hN : N ≤ Q * M ^ 2) (hJav : x ≤ 13000000 * N ^ 12) (hgN : (g : ℝ) ≤ N ^ 2)
    (hd : (Module.finrank ℚ L : ℝ) ≤ Q * M) :
    GlueAssembly.NonCMOutput Q M a := by
  obtain ⟨⟨ψ, hψ, hdeg⟩, -⟩ := r19 L J P g x hJd hx ⟨φ, hφ⟩
  have hvar := r20 L J P ψ hψ x y hx hy
  have hB := r21 L Z gZ hZd
  rw [hz] at hB
  have hB' : -(3 / 2) * (gZ : ℝ) ≤ z := EReal.coe_le_coe_iff.mp hB
  set d := Module.finrank ℚ L with hdd
  have hd1 : 1 ≤ d := Module.finrank_pos
  have hg1 : 1 ≤ g := by omega
  have hκ := log_grKappa g d x hg1 hd1
  have hκ1 := one_le_grKappa g d x hg1 hd1
  have hlogdeg : Real.log (isogDeg ψ) ≤ Real.log (grKappa g d x) := by
    rcases Nat.eq_zero_or_pos (isogDeg ψ) with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero]; exact Real.log_nonneg hκ1
    · exact Real.log_le_log (by exact_mod_cast hpos) hdeg
  refine ⟨N, g, d, x, Real.log (isogDeg ψ), z, hN1, hN, hJav, by exact_mod_cast hg2, hgN,
    by exact_mod_cast hd1, hd, ?_, ?_, ?_⟩
  · rw [hκ] at hlogdeg; exact hlogdeg
  · have := (abs_le.mp hvar).1
    linarith
  · have hgZr : (gZ : ℝ) ≤ g := by exact_mod_cast hgZ
    linarith

/-- **E4's additivity (g0-split's piece 5) from h5-neron (proved, leaf-adopt3)**: T41 (Néron
models exist), H5's `NeronModelMinimal` and the model-level glue `ProductModelHeight`. -/
theorem heightAdditivity_of_h5neron (hN1 : ZInQ.H5Neron.NeronModelExists)
    (hmin : ZInQ.DefFaltings.NeronModelMinimal) (hH : ZInQ.H5Neron.ProductModelHeight) :
    HeightAdditivity :=
  fun L _ _ P A Z ⟨p₁, p₂, h₁, h₂, h⟩ =>
    ZInQ.H5Neron.heightAdditivity_unfolded hN1 hmin hH L P A Z p₁ p₂ h₁ h₂ h

/-! #### leaf-adopt3: glue piece 3 (`X1BelyiOnModel`) proved from `BelyiX1` by transport
along `ℚ(X) ≅ K_N` (the data of `IsJ1`): `IsBelyiFunction` moves along a `ℚ`-algebra isomorphism,
and `ℚ(t) ⊆ ℚ(X)` is the image of `ℚ(j)`, so `[ℚ(X) : ℚ(t)] = [K_N : ℚ(j)] ≤ N²`. With
`TextbookLeaves.belyiX1` (x1-belyi, from T36, T37) it is no longer a glue piece. -/

/-- A Belyi function is carried to a Belyi function by a `k`-algebra isomorphism. -/
theorem isBelyiFunction_map {k F F' : Type} [Field k] [Field F] [Field F'] [Algebra k F]
    [Algebra k F'] (ψ : F ≃ₐ[k] F') {t : F} (h : LeafModCurves.IsBelyiFunction k F t) :
    LeafModCurves.IsBelyiFunction k F' (ψ t) := by
  obtain ⟨hT, hB⟩ := h
  refine ⟨fun ha => hT ((isAlgebraic_algHom_iff (ψ : F →ₐ[k] F') ψ.injective).mp ha), ?_⟩
  intro w hk ht q hqm hqi hqX hqX1 hq x hx
  have hnu : ∀ y : F, y ∈ (w.comap (ψ : F →+* F')).nonunits ↔ ψ y ∈ w.nonunits := by
    intro y
    rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
      ValuationSubring.mem_comap]
    simp [map_inv₀]
  have haev : ∀ y : F, ψ (Polynomial.aeval y q) = Polynomial.aeval (ψ y) q :=
    fun y => (Polynomial.aeval_algHom_apply (ψ : F →ₐ[k] F') y q).symm
  obtain ⟨y, hy, hxy⟩ := hB (w.comap (ψ : F →+* F'))
    (fun c => by rw [ValuationSubring.mem_comap]; simpa using hk c)
    (by rw [ValuationSubring.mem_comap]; exact ht)
    q hqm hqi hqX hqX1 ((hnu _).2 (by rw [haev]; exact hq)) (ψ.symm x)
    ((hnu _).2 (by simpa using hx))
  refine ⟨ψ y, ValuationSubring.mem_comap.1 hy, ?_⟩
  have h2 := congrArg ψ hxy
  rw [map_mul, haev] at h2
  simpa using h2

/-- The image of a polynomial in `ℚ(j)` under a ring hom `g` lies in `ℚ(g j)`. -/
theorem polyImage_mem {F' : Type} [Field F'] [Algebra ℚ F'] (g : LeafModCurves.Qj →+* F')
    (p : Polynomial ℚ) :
    g (algebraMap (Polynomial ℚ) LeafModCurves.Qj p) ∈
      IntermediateField.adjoin ℚ {g RatFunc.X} := by
  have hring : g.comp (algebraMap (Polynomial ℚ) LeafModCurves.Qj) =
      Polynomial.eval₂RingHom (algebraMap ℚ F') (g RatFunc.X) := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · have e1 := eq_ratCast ((g.comp (algebraMap (Polynomial ℚ) LeafModCurves.Qj)).comp
        Polynomial.C) a
      have e2 := eq_ratCast (algebraMap ℚ F') a
      simp only [RingHom.comp_apply] at e1
      simp only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      rw [e1, e2]
    · simp [RatFunc.algebraMap_X]
  have h1 : g (algebraMap (Polynomial ℚ) LeafModCurves.Qj p) = Polynomial.aeval (g RatFunc.X) p := by
    rw [← RingHom.comp_apply, hring, Polynomial.aeval_def]; rfl
  rw [h1]
  exact IntermediateField.algebra_adjoin_le_adjoin ℚ _
    (Polynomial.aeval_mem_adjoin_singleton ℚ (g RatFunc.X))

theorem image_mem {F' : Type} [Field F'] [Algebra ℚ F'] (g : LeafModCurves.Qj →+* F')
    (x : LeafModCurves.Qj) : g x ∈ IntermediateField.adjoin ℚ {g RatFunc.X} := by
  rw [← RatFunc.num_div_denom x, map_div₀]
  exact div_mem (polyImage_mem g _) (polyImage_mem g _)

/-- **g0-split's glue piece 3 from `BelyiX1` (proved, leaf-adopt3).** -/
theorem x1BelyiOnModel_of_belyiX1 (hB : LeafModCurves.BelyiX1) : X1BelyiOnModel := by
  rintro N hN J ⟨X, P₀, aj, ⟨hC, hI, P, hP, ⟨φ⟩⟩, hJac⟩
  letI := ZInQ.LeafPush2.ffAlgebra X
  obtain ⟨hBel, hdeg⟩ := hB N P hN hP
  let ψ : LeafModCurves.fieldX1 P ≃ₐ[ℚ] X.left.functionField := φ.symm.toRatAlgEquiv
  let g : LeafModCurves.Qj →+* X.left.functionField :=
    (φ.symm : LeafModCurves.fieldX1 P →+* X.left.functionField).comp
      (algebraMap LeafModCurves.Qj (LeafModCurves.fieldX1 P))
  let t : X.left.functionField :=
    ψ (algebraMap LeafModCurves.Qj (LeafModCurves.fieldX1 P) (RatFunc.X / 1728))
  have ht : t = g (RatFunc.X / 1728) := rfl
  have h1728 : (1728 : X.left.functionField) ≠ 0 := by
    rw [← map_ofNat g 1728]; exact (map_ne_zero g).2 (by norm_num)
  have hgX : g RatFunc.X = 1728 * t := by
    rw [ht, map_div₀, map_ofNat]
    field_simp
  have hmem : ∀ x, g x ∈ IntermediateField.adjoin ℚ {t} := by
    intro x
    have h1 : IntermediateField.adjoin ℚ {g RatFunc.X} ≤ IntermediateField.adjoin ℚ {t} := by
      rw [IntermediateField.adjoin_simple_le_iff, hgX]
      exact mul_mem (by simpa using IntermediateField.natCast_mem _ 1728)
        (IntermediateField.mem_adjoin_simple_self ℚ t)
    exact h1 (image_mem g x)
  have hsurj : ∀ y ∈ IntermediateField.adjoin ℚ {t}, ∃ x, g x = y := by
    intro y hy
    let S : IntermediateField ℚ X.left.functionField :=
      g.fieldRange.toIntermediateField (fun q => ⟨(q : LeafModCurves.Qj), by simp⟩)
    have hle : IntermediateField.adjoin ℚ {t} ≤ S := by
      rw [IntermediateField.adjoin_simple_le_iff]
      exact ⟨RatFunc.X / 1728, rfl⟩
    obtain ⟨x, hx⟩ := hle hy
    exact ⟨x, hx⟩
  let i0 : LeafModCurves.Qj →+* IntermediateField.adjoin ℚ {t} := g.codRestrict _ hmem
  have hi0 : Function.Bijective i0 := by
    refine ⟨fun a b hab => g.injective (congrArg Subtype.val hab), fun y => ?_⟩
    obtain ⟨x, hx⟩ := hsurj y.1 y.2
    exact ⟨x, Subtype.ext hx⟩
  let i := RingEquiv.ofBijective i0 hi0
  have hfin : Module.finrank LeafModCurves.Qj (LeafModCurves.fieldX1 P) =
      Module.finrank (IntermediateField.adjoin ℚ {t}) X.left.functionField :=
    Algebra.finrank_eq_of_equiv_equiv i φ.symm (RingHom.ext fun _ => rfl)
  haveI : FiniteDimensional LeafModCurves.Qj (LeafModCurves.fieldX1 P) :=
    IntermediateField.adjoin.finiteDimensional
      (Algebra.IsIntegral.isIntegral (R := LeafModCurves.Qj) (LeafModCurves.xCoord P))
  refine ⟨X, hC, hI, P₀, aj, hJac, t, isBelyiFunction_map ψ hBel, _, hfin.symm,
    Module.finrank_pos, hdeg⟩


/-- g0-split's `DimBaseChange` is hodge-lattice's (same statement, binders reordered; leaf-adopt3). -/
theorem dimBaseChange_iff_hodgeLattice :
    DimBaseChange ↔ ZInQ.DefFaltings.HodgeLattice.DimBaseChange :=
  ⟨fun h K _ A L _ _ => h K L A, fun h K _ L _ _ A => h K A L⟩

/-- **AN3's algebraic third from glue piece 2 (leaf-adopt3)**: `HodgeLatticeTheorem` (def-faltings)
from hodge-lattice's two remaining Props and g0-split's `DimBaseChange`. -/
theorem hodgeLatticeTheorem_of_dimBaseChange (hDim : DimBaseChange)
    (h1 : ZInQ.DefFaltings.HodgeLattice.RegularAtOrigin)
    (h2 : ZInQ.DefFaltings.HodgeLattice.DimAtOrigin) : ZInQ.DefFaltings.HodgeLatticeTheorem :=
  ZInQ.DefFaltings.HodgeLattice.hodgeLatticeTheorem_of_abVarFacts h1 h2
    (dimBaseChange_iff_hodgeLattice.mp hDim)

/-- glue-ssbc's theorem in `GlueI3`'s statement. -/
theorem semisimpleBaseChange : GlueI3.SemisimpleBaseChange :=
  fun k E G V _ _ _ _ _ _ _ _ ρ hρ => GlueSSBC.semisimpleBaseChange k E G V ρ hρ

/-- **E1 on a common constituent (proved)**: `PkgI3.E1_exists_hom_ne_zero` with R9 (Faltings),
T26 and glue-ssbc. -/
theorem hom_of_common (r : ResearchLeaves) (t : TextbookLeaves) {K : Type} [Field K]
    [NumberField K] (A J : PkgI3.AbVar K) (h : CommonConstituent A J) :
    ∃ f : PkgI3.AbVar.Hom A J, f ≠ 0 := by
  obtain ⟨ℓ, _, E, _, _, U, U', e, hU, he⟩ := h
  exact PkgI3.E1_exists_hom_ne_zero r.r9a r.r9b t.t26 semisimpleBaseChange A J ℓ E U U' hU e he

/-! ### qm-pin's comparison: the three QM pieces reduce to one triple (task pin-apply)

`FibreSimple`, `ThetaPointOfFibre` and `ModularConstituent` quantify over every triple
`(Y, Φ, π)` satisfying `R1fpProps` and `R2fpProps`. With qm-pin's repaired `R1fpProps`
(`R1famProps`, `R1univProps`), any two such triples are compared by a morphism `g : Y' → Y` with
`Φ' = Φ ∘ g` (`LeafQM.AV.Pin.phi_part`, proved) and `π' = π ∘ g` (`LeafQM.AV.Pin.MobiusGlue`, a
named glue Prop). So each piece is equivalent to its statement for any single triple satisfying the
clauses (`fibreSimple_iff_at` etc.), for instance the leaf's own triple; the `…W` forms state the
piece for some triple. The relabeling attack of rv-g0pieces no longer applies
(`LeafQM.AV.Pin.r1fpPin_relabel_iff`). -/

/-- `FibreSimple` for one triple `(Y, Φ, π)`. -/
def FibreSimpleAt (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) :
    Prop :=
  ∀ u : ℚ, u ∉ contactSet →
    ∀ (K : GlueAssembly.NF) (A : ZInQ.DefFaltings.AbVar K.K), FibreOver Y Φ π u K A →
      PkgI3.EndDivision (LeafAdopt.abVarEquiv K.K A)

/-- `ThetaPointOfFibre` for one triple `(Y, Φ, π)`. -/
def ThetaPointOfFibreAt (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (π : ToP1 Y.left) : Prop :=
  ∀ u : ℚ, u ∉ contactSet →
    ∀ (K : GlueAssembly.NF) (A : ZInQ.DefFaltings.AbVar K.K), FibreOver Y Φ π u K A →
    ∃ (σ : K.K →+* ℂ) (Λ : Submodule ℤ (Fin 2 → ℂ))
      (Φu : (Fin 2 → ℂ) → ZInQ.LeafPush2.CPts (LeafAdopt.abVarEquiv K.K A) σ), ZInQ.LeafPush2.IsUniformization σ Λ Φu ∧
    ∃ Ω : Matrix (Fin 2) (Fin 2) ℂ, ZInQ.LeafPush2.IsSiegel Ω ∧ ZInQ.LeafPush2.IsPeriodMatrix Λ Ω ∧
    ∃ (L : GlueAssembly.NF) (emb : L.K →+* ℂ) (z : ZInQ.LeafPush2.Char2 → L.K) (c : ℂ), c ≠ 0 ∧
      (∀ m, emb (z m) = c * ZInQ.LeafPush2.thetaConst Ω m) ∧
    ∃ (K' : GlueAssembly.NF) (z' : Fin 10 → K'.K),
      3779136 * (∏ i, z' i) ^ 4 / (∑ i, z' i ^ 8) ^ 5 = algebraMap ℚ K'.K (Jmap u) ∧
      Height.logHeight z' / Module.finrank ℚ K'.K ≤ ZInQ.LeafPush2.absLogHeight z

/-- `ModularConstituent` for one triple `(Y, Φ, π)`. -/
def ModularConstituentAt (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (π : ToP1 Y.left) : Prop :=
  ∀ u : ℚ, u ∉ contactSet →
    ∀ (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar), Φ Qbar y = M3.mk P →
      π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar (Jmap u)) →
    ∃ (L : GlueAssembly.NF) (emb : L.K →+* Qbar) (A : ZInQ.DefFaltings.AbVar L.K) (N : ℕ)
      (J : PkgI3.AbVar ℚ),
      (letI : Algebra L.K Qbar := emb.toAlgebra; Nonempty ((A.baseChange Qbar).X ≅ P.A.X)) ∧
      0 < N ∧ LeafModCurves.IsJ1 N J ∧
      (N : ℝ) ≤ heightQ heightD * (contactSupport Mult.S_mul u : ℝ) ^ 2 ∧
      (Module.finrank ℚ L.K : ℝ) ≤ heightQ heightD * (contactSupport Mult.S_mul u : ℝ) ∧
      CommonConstituent (LeafAdopt.abVarEquiv L.K A)
        (LeafAdopt.abVarEquiv L.K (((LeafAdopt.abVarEquiv ℚ).symm J).baseChange L.K))

/-- The three pieces are their `…At` forms for every triple satisfying the clauses (definitional). -/
theorem fibreSimple_eq_forall_at : FibreSimple ↔ ∀ (Y : Over (Spec (CommRingCat.of ℚ)))
    (Φ : PtEquiv Y) (π : ToP1 Y.left), R1fpProps Y Φ → R2fpProps Y Φ π → FibreSimpleAt Y Φ π :=
  Iff.rfl

theorem thetaPointOfFibre_eq_forall_at : ThetaPointOfFibre ↔
    ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpProps Y Φ → R2fpProps Y Φ π → ThetaPointOfFibreAt Y Φ π :=
  Iff.rfl

theorem modularConstituent_eq_forall_at : ModularConstituent ↔
    ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpProps Y Φ → R2fpProps Y Φ π → ModularConstituentAt Y Φ π :=
  Iff.rfl

/-- `FibreOver` (an `∃`-form) transfers along a comparison morphism (qm-pin `transfer_exists`,
for `SameTripleMor`). -/
theorem fibreOver_of_sameTripleMor {Y Y' : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {Φ' : PtEquiv Y'} {π : ToP1 Y.left} {π' : ToP1 Y'.left}
    (hS : LeafQM.AV.Pin.SameTripleMor Y Y' Φ Φ' π π') {u : ℚ} {K : GlueAssembly.NF}
    {A : ZInQ.DefFaltings.AbVar K.K} (h : FibreOver Y' Φ' π' u K A) : FibreOver Y Φ π u K A := by
  obtain ⟨g, hΦ, hπ⟩ := hS
  obtain ⟨emb, y, P, hP, hy, hiso⟩ := h
  exact ⟨emb, y ≫ g, P, (hΦ Qbar y).symm.trans hP, (hπ y).symm.trans hy, hiso⟩

/-- **The comparison from the leaves** (qm-pin `sameTripleMor_of_mobius`, CM objects from
`cm_objects_of_R1R2fp`): any two triples satisfying the repaired clause lists are compared by a
morphism, given `MobiusGlue`. -/
theorem sameTripleMor_of_leaves (hM : LeafQM.AV.Pin.MobiusGlue) (hQM : LeafQM.AV.R1R2fp)
    {Y Y' : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {Φ' : PtEquiv Y'}
    {π : ToP1 Y.left} {π' : ToP1 Y'.left}
    (h1 : R1fpProps Y Φ) (h2 : R2fpProps Y Φ π) (h1' : R1fpProps Y' Φ')
    (h2' : R2fpProps Y' Φ' π') : LeafQM.AV.Pin.SameTripleMor Y Y' Φ Φ' π π' :=
  LeafQM.AV.Pin.sameTripleMor_of_mobius hM (LeafQM.AV.Pin.cm_objects_of_R1R2fp hQM) h1 h2 h1' h2'

theorem fibreSimple_of_at (hM : LeafQM.AV.Pin.MobiusGlue) (hQM : LeafQM.AV.R1R2fp)
    {Y₀ : Over (Spec (CommRingCat.of ℚ))} {Φ₀ : PtEquiv Y₀} {π₀ : ToP1 Y₀.left}
    (h1 : R1fpProps Y₀ Φ₀) (h2 : R2fpProps Y₀ Φ₀ π₀) (h : FibreSimpleAt Y₀ Φ₀ π₀) :
    FibreSimple :=
  fun _ _ _ h1' h2' u hu K A hF =>
    h u hu K A (fibreOver_of_sameTripleMor (sameTripleMor_of_leaves hM hQM h1 h2 h1' h2') hF)

theorem thetaPointOfFibre_of_at (hM : LeafQM.AV.Pin.MobiusGlue) (hQM : LeafQM.AV.R1R2fp)
    {Y₀ : Over (Spec (CommRingCat.of ℚ))} {Φ₀ : PtEquiv Y₀} {π₀ : ToP1 Y₀.left}
    (h1 : R1fpProps Y₀ Φ₀) (h2 : R2fpProps Y₀ Φ₀ π₀) (h : ThetaPointOfFibreAt Y₀ Φ₀ π₀) :
    ThetaPointOfFibre :=
  fun _ _ _ h1' h2' u hu K A hF =>
    h u hu K A (fibreOver_of_sameTripleMor (sameTripleMor_of_leaves hM hQM h1 h2 h1' h2') hF)

theorem modularConstituent_of_at (hM : LeafQM.AV.Pin.MobiusGlue) (hQM : LeafQM.AV.R1R2fp)
    {Y₀ : Over (Spec (CommRingCat.of ℚ))} {Φ₀ : PtEquiv Y₀} {π₀ : ToP1 Y₀.left}
    (h1 : R1fpProps Y₀ Φ₀) (h2 : R2fpProps Y₀ Φ₀ π₀) (h : ModularConstituentAt Y₀ Φ₀ π₀) :
    ModularConstituent := by
  intro Y Φ π h1' h2' u hu y P hP hy
  obtain ⟨g, hΦ, hπ⟩ := sameTripleMor_of_leaves hM hQM h1 h2 h1' h2'
  exact h u hu (y ≫ g) P ((hΦ Qbar y).symm.trans hP) ((hπ y).symm.trans hy)

/-- **`FibreSimple` is its statement for any one triple** satisfying the repaired clauses (given
`MobiusGlue`): the universal quantifier over `(Y, Φ, π)` costs nothing. -/
theorem fibreSimple_iff_at (hM : LeafQM.AV.Pin.MobiusGlue) (hQM : LeafQM.AV.R1R2fp)
    {Y₀ : Over (Spec (CommRingCat.of ℚ))} {Φ₀ : PtEquiv Y₀} {π₀ : ToP1 Y₀.left}
    (h1 : R1fpProps Y₀ Φ₀) (h2 : R2fpProps Y₀ Φ₀ π₀) :
    FibreSimple ↔ FibreSimpleAt Y₀ Φ₀ π₀ :=
  ⟨fun h => h Y₀ Φ₀ π₀ h1 h2, fibreSimple_of_at hM hQM h1 h2⟩

theorem thetaPointOfFibre_iff_at (hM : LeafQM.AV.Pin.MobiusGlue) (hQM : LeafQM.AV.R1R2fp)
    {Y₀ : Over (Spec (CommRingCat.of ℚ))} {Φ₀ : PtEquiv Y₀} {π₀ : ToP1 Y₀.left}
    (h1 : R1fpProps Y₀ Φ₀) (h2 : R2fpProps Y₀ Φ₀ π₀) :
    ThetaPointOfFibre ↔ ThetaPointOfFibreAt Y₀ Φ₀ π₀ :=
  ⟨fun h => h Y₀ Φ₀ π₀ h1 h2, thetaPointOfFibre_of_at hM hQM h1 h2⟩

theorem modularConstituent_iff_at (hM : LeafQM.AV.Pin.MobiusGlue) (hQM : LeafQM.AV.R1R2fp)
    {Y₀ : Over (Spec (CommRingCat.of ℚ))} {Φ₀ : PtEquiv Y₀} {π₀ : ToP1 Y₀.left}
    (h1 : R1fpProps Y₀ Φ₀) (h2 : R2fpProps Y₀ Φ₀ π₀) :
    ModularConstituent ↔ ModularConstituentAt Y₀ Φ₀ π₀ :=
  ⟨fun h => h Y₀ Φ₀ π₀ h1 h2, modularConstituent_of_at hM hQM h1 h2⟩

/-- `FibreSimple` for some triple satisfying the clauses. -/
def FibreSimpleW : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ ∧ R2fpProps Y Φ π ∧ FibreSimpleAt Y Φ π

/-- `ThetaPointOfFibre` for some triple satisfying the clauses. -/
def ThetaPointOfFibreW : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ ∧ R2fpProps Y Φ π ∧ ThetaPointOfFibreAt Y Φ π

/-- `ModularConstituent` for some triple satisfying the clauses. -/
def ModularConstituentW : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ ∧ R2fpProps Y Φ π ∧ ModularConstituentAt Y Φ π

/-- **The three QM pieces are equivalent to their one-triple forms** (given the QM leaf bundle,
which supplies a triple, and `MobiusGlue`). -/
theorem qmPieces_iff_w (hM : LeafQM.AV.Pin.MobiusGlue) (hQM : LeafQM.AV.R1R2fp) :
    (FibreSimple ↔ FibreSimpleW) ∧ (ThetaPointOfFibre ↔ ThetaPointOfFibreW) ∧
      (ModularConstituent ↔ ModularConstituentW) := by
  obtain ⟨Y, Φ, π, h1, h2, -⟩ := LeafQM.AV.exists_fibre_object hQM
  refine ⟨⟨fun h => ⟨Y, Φ, π, h1, h2, h Y Φ π h1 h2⟩, ?_⟩,
    ⟨fun h => ⟨Y, Φ, π, h1, h2, h Y Φ π h1 h2⟩, ?_⟩,
    ⟨fun h => ⟨Y, Φ, π, h1, h2, h Y Φ π h1 h2⟩, ?_⟩⟩
  · rintro ⟨Y₀, Φ₀, π₀, h1₀, h2₀, h⟩; exact fibreSimple_of_at hM hQM h1₀ h2₀ h
  · rintro ⟨Y₀, Φ₀, π₀, h1₀, h2₀, h⟩; exact thetaPointOfFibre_of_at hM hQM h1₀ h2₀ h
  · rintro ⟨Y₀, Φ₀, π₀, h1₀, h2₀, h⟩; exact modularConstituent_of_at hM hQM h1₀ h2₀ h


end G0Split

/-- **The glue pieces** (g0-split's missing pieces, smallest first, without piece 3 (proved here)
and with piece 5 narrowed to h5-neron's `ProductModelHeight`, and leaf-adopt2's
`HeightCopiesAgree`: ten Props), bundled (leaf-adopt3). Each is a `def … : Prop` whose docstring names its
glue step; none is a literature leaf, and each is to be proved in Lean by the project. -/
structure GluePieces : Prop where
  /-- 1. An abelian variety has finite dimension (definition level). -/
  dimFinite : G0Split.DimFinite
  /-- 2. Dimension is invariant under field extension (Stacks 00P4). -/
  dimBaseChange : G0Split.DimBaseChange
  -- 3. (leaf-adopt3) g0-split's `X1BelyiOnModel` is proved (`G0Split.x1BelyiOnModel_of_belyiX1`
  -- with `TextbookLeaves.belyiX1`, x1-belyi), no longer a piece.
  /-- 4. G5-G6 on the fibre surface: simplicity. -/
  fibreSimple : G0Split.FibreSimple
  /-- 5. E4 at model level (h5-neron's glue P2, leaf-adopt3; replaces g0-split's
  `HeightAdditivity`, which now follows from it with T41 (Néron models exist) and H5's
  `NeronModelMinimal`, `G0Split.heightAdditivity_of_h5neron`): the height of a product group model
  is at least the sum of the heights. -/
  productModelHeight : ZInQ.H5Neron.ProductModelHeight
  /-- 6. Stable height invariant under base change. -/
  stableHeightBaseChange : G0Split.StableHeightBaseChange
  /-- 7. G17: products of abelian varieties exist. -/
  productExists : G0Split.ProductExists
  /-- 8. G17: the reverse isogeny `J → A × Z`. -/
  reverseIsogeny : G0Split.ReverseIsogeny
  /-- 9. G19, F1 on the fibre surface: the theta point. -/
  thetaPoint : G0Split.ThetaPointOfFibre
  /-- 10. G2, G4, G7-G16: field, model, level and common constituent. -/
  modularConstituent : G0Split.ModularConstituent
  /-- 11. The two textual copies of the stable Faltings height agree (leaf-adopt2's target). -/
  heightCopies : HeightCopiesAgree

open G0Split in
/-- **The glue G1-G17 and G19 (non-Arakelov part), split (g0-split).** The leaves and the ten
missing glue pieces (each a `def … : Prop` in `G0Split` whose docstring names its glue step) give
glue-assembly's interface `GlueOutputs` at `S = Mult.S_mul`. Applied proved pieces: A4
(`LeafQM.AV.exists_fibre_object`, from R1-R2), `model_dim`, H5's finiteness
(`faltingsHeight_coe`), E1 (`hom_of_common`: R9, T26, glue-ssbc), T8 (Poincaré, a leaf), E2's
`dim J₁(N) ≤ N²` (`LeafModCurves.dim_J1_le`, from T34), `javanpeykarJ1` (concrete R18),
`thetaPazuki` (concrete R22), `isogenousProduct`, and the E3-E4 numerics (`transfer_core`, from
R19-R21). The non-CM disjunct is used (G6, NoCM). -/
theorem glueOutputs_of_leaves (r : ResearchLeaves) (t : TextbookLeaves) (gp : GluePieces) :
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
  obtain ⟨f, hf⟩ := hom_of_common r t _ _ hCC
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

/-- **G18-G20, proved** (glue-assembly): `GlueOutputs Mult.S_mul → SixContactMin`, through F2
over Mathlib's Weil heights, the E2-E4 and F3 arithmetic, the final constant, and F4.
`GlueAssembly.SixContactMinAt Mult.S_mul` is `ZInQ.SixContactMin` by definition. -/
theorem sixContactMin_of_glueOutputs (h : GlueAssembly.GlueOutputs ZInQ.Mult.S_mul) :
    ZInQ.SixContactMin :=
  GlueAssembly.sixContactMinAt_of_glueOutputs h

/-- The scratch copy of `JHeightBound` in glue-assembly is the repository's. -/
theorem jHeightBound_copy_iff :
    GlueAssembly.JHeightBound ZInQ.Mult.S_mul ↔ ZInQ.JHeight.JHeightBound ZInQ.Mult.S_mul :=
  Iff.rfl

/-- **G0. The leaves and the glue pieces imply `SixContactMin`** (no `sorry`). Hypotheses: exactly
the three bundles `ResearchLeaves`, `TextbookLeaves`, `GluePieces`. -/
theorem sixContactMin_of_leaves (r : ResearchLeaves) (t : TextbookLeaves) (gp : GluePieces) :
    ZInQ.SixContactMin :=
  sixContactMin_of_glueOutputs (glueOutputs_of_leaves r t gp)

/-- **The glue pieces, one-triple form** (task pin-apply, after qm-pin): `GluePieces` with the
three QM pieces 4, 9, 10 stated for some triple satisfying the repaired clause lists
(`G0Split.FibreSimpleW`, `ThetaPointOfFibreW`, `ModularConstituentW`) and qm-pin's curve glue
`MobiusGlue` as an eleventh named piece. Given the leaves, it is equivalent to `GluePieces` plus
`MobiusGlue` (`gluePieces_of_pin`, `gluePiecesPin_of`). -/
structure GluePiecesPin : Prop where
  dimFinite : G0Split.DimFinite
  dimBaseChange : G0Split.DimBaseChange
  /-- 4. G5-G6 on the fibre surface, for one triple. -/
  fibreSimple : G0Split.FibreSimpleW
  productModelHeight : ZInQ.H5Neron.ProductModelHeight
  stableHeightBaseChange : G0Split.StableHeightBaseChange
  productExists : G0Split.ProductExists
  reverseIsogeny : G0Split.ReverseIsogeny
  /-- 9. G19 on the fibre surface, for one triple. -/
  thetaPoint : G0Split.ThetaPointOfFibreW
  /-- 10. G2, G4, G7-G16, for one triple. -/
  modularConstituent : G0Split.ModularConstituentW
  heightCopies : HeightCopiesAgree
  /-- 12. qm-pin's curve glue: two triples compared on `Φ` by `g` are compared on `π` by `g`. -/
  mobius : LeafQM.AV.Pin.MobiusGlue

theorem gluePieces_of_pin (r : ResearchLeaves) (gp : GluePiecesPin) : GluePieces := by
  obtain ⟨a, b, c, d, e, f, g, h, i, j, hM⟩ := gp
  obtain ⟨h4, h9, h10⟩ := G0Split.qmPieces_iff_w hM (LeafAdopt.R1R2fp_of_rep r.r1r2)
  exact ⟨a, b, h4.2 c, d, e, f, g, h9.2 h, h10.2 i, j⟩

theorem gluePiecesPin_of (r : ResearchLeaves) (gp : GluePieces) (hM : LeafQM.AV.Pin.MobiusGlue) :
    GluePiecesPin := by
  obtain ⟨a, b, c, d, e, f, g, h, i, j⟩ := gp
  obtain ⟨h4, h9, h10⟩ := G0Split.qmPieces_iff_w hM (LeafAdopt.R1R2fp_of_rep r.r1r2)
  exact ⟨a, b, h4.1 c, d, e, f, g, h9.1 h, h10.1 i, j, hM⟩

/-- **G0, one-triple form** (no `sorry`): the leaves and `GluePiecesPin` imply `SixContactMin`. -/
theorem sixContactMin_of_leaves_pin (r : ResearchLeaves) (t : TextbookLeaves)
    (gp : GluePiecesPin) : ZInQ.SixContactMin :=
  sixContactMin_of_leaves r t (gluePieces_of_pin r gp)

/-- **G20 alone** (the existing proof in `ZInQKernel`), for reference. -/
example (h : ZInQ.JHeight.JHeightBound ZInQ.Mult.S_mul) : ZInQ.SixContactMin :=
  ZInQ.JHeight.sixContactMin_of_jHeightBound h

end HSyn


end

/-! ## leaf-fold: leaf T2 (`PkgI2.AbhyankarDVR`) proved

Copied verbatim from `scratch/t-brauer-purity/T2Full.lean` (task t-brauer-purity), lines 3-725:
the proof against this file's definition `PkgI2.AbhyankarDVR` (T2Full's copy of the definition is
verbatim this file's, lines 742-757 there). -/

section LeafFoldT2

/-!
# t-brauer-purity: Abhyankar's lemma, DVR form (leaf T2, `PkgI2.AbhyankarDVR`), proved

Contents: copies of `AbhyankarBricks.lean` and `KummerUnramified.lean` (scratch files cannot import
each other), then the assembly following docs/research/t-brauer-purity.md §4.
-/

/-!
# t-brauer-purity: the unit-radicand Kummer step of Abhyankar's lemma is unramified

Step (b) of the proof of leaf T2 (`PkgI2.AbhyankarDVR`, docs/research/t-brauer-purity.md §2, §4):
adjoining an `e`-th root `w` of an element `u` of a Dedekind domain `A`, with `e` invertible, gives
an extension unramified at every prime `P` of the integral closure `B` with `u ∉ P`.

Proof: if `P` were ramified it would divide the different ideal (`dvd_differentIdeal_iff`), which
contains `g'(w)` for `g` the minimal polynomial of `w` (`aeval_derivative_mem_differentIdeal`).
`g ∣ Xᵉ - u` gives `e wᵉ⁻¹ = g'(w) h(w) ∈ P`, hence `wᵉ = u ∈ P`.
-/

open Polynomial

namespace TBrauerPurity

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

theorem isUnramifiedAt_of_pow_eq (A K L B : Type*) [CommRing A] [IsDedekindDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [CommRing B] [IsDedekindDomain B] [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L] [IsFractionRing B L] [Module.IsTorsionFree A B] [Module.Finite A B]
    (e : ℕ) (he0 : 0 < e) (he : IsUnit (e : A)) (w : B) (u : A)
    (hw : w ^ e = algebraMap A B u) (hgen : Algebra.adjoin K {algebraMap B L w} = ⊤)
    (P : Ideal B) [P.IsPrime] (hu : algebraMap A B u ∉ P) : Algebra.IsUnramifiedAt A P := by
  have : Algebra.IsSeparable (FractionRing A) (FractionRing B) := by
    refine Algebra.IsSeparable.of_equiv_equiv (FractionRing.algEquiv A K).symm.toRingEquiv
      (FractionRing.algEquiv B L).symm.toRingEquiv ?_
    ext _
    exact IsFractionRing.algEquiv_commutes (FractionRing.algEquiv A K).symm
      (FractionRing.algEquiv B L).symm _
  by_contra hP
  rw [← dvd_differentIdeal_iff] at hP
  have hle : differentIdeal A B ≤ P := Ideal.le_of_dvd hP
  have hmem := hle (aeval_derivative_mem_differentIdeal A K L w hgen)
  have hint : IsIntegral A w := IsIntegralClosure.isIntegral A L w
  have haev : aeval w (X ^ e - C u) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, hw, sub_self]
  obtain ⟨h, hh⟩ := minpoly.isIntegrallyClosed_dvd hint haev
  have hder : aeval w (derivative (X ^ e - C u)) =
      aeval w (derivative (minpoly A w)) * aeval w h := by
    rw [hh, derivative_mul, map_add, map_mul, map_mul, minpoly.aeval, zero_mul, add_zero]
  have hin : aeval w (derivative (X ^ e - C u : A[X])) ∈ P := by
    rw [hder]; exact P.mul_mem_right _ hmem
  rw [derivative_sub, derivative_C, sub_zero, derivative_X_pow, map_mul, aeval_C, map_pow,
    aeval_X] at hin
  have heB : IsUnit (algebraMap A B (e : A)) := he.map _
  have hpow : w ^ (e - 1) ∈ P := by
    rcases (Ideal.IsPrime.mem_or_mem ‹_› hin) with h1 | h1
    · rw [map_natCast] at h1 heB
      exact absurd (P.eq_top_of_isUnit_mem h1 heB) (Ideal.IsPrime.ne_top ‹_›)
    · exact h1
  apply hu
  rw [← hw, show e = (e - 1) + 1 by omega, pow_succ]
  exact P.mul_mem_right _ hpow

/-- Corollary: ramification index one at such `P`. -/
theorem ramificationIdx_eq_one_of_pow_eq (A K L B : Type*) [CommRing A] [IsDedekindDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [CommRing B] [IsDedekindDomain B] [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L] [IsFractionRing B L] [Module.IsTorsionFree A B] [Module.Finite A B]
    (e : ℕ) (he0 : 0 < e) (he : IsUnit (e : A)) (w : B) (u : A)
    (hw : w ^ e = algebraMap A B u) (hgen : Algebra.adjoin K {algebraMap B L w} = ⊤)
    (P : Ideal B) [P.IsPrime] (hu : algebraMap A B u ∉ P) : P.ramificationIdx A = 1 := by
  have := isUnramifiedAt_of_pow_eq A K L B e he0 he w u hw hgen P hu
  exact Ideal.ramificationIdx_eq_one P A

end TBrauerPurity


/-!
# t-brauer-purity: bricks toward Abhyankar's lemma (leaf T2, `PkgI2.AbhyankarDVR`)

In the setting of `PkgI2.AbhyankarDVR` (scratch/h-decomposition/Leaves.lean, ZInQKernel/HDecomp/
Objects.lean), with the same instance context:

* `abhyankar_finiteDimensional`, `abhyankar_isSeparable`: `M = L(t)`, `tⁿ = π`, `n` invertible in
  `R`, force `M/K` finite separable, so `integralClosure R M` is a Dedekind domain
  (`abhyankar_isDedekindDomain`).
* `dvd_ramificationIdx_of_pow_eq` (general): over a DVR `R` with uniformizer `π`, if `tⁿ = π` in a
  Dedekind `R`-algebra `S` with `𝔪S ≠ ⊥`, then `n` divides the ramification index of every prime of
  `S` over `𝔪`.
* `abhyankar_dvd_ramificationIdx`: hence in the leaf's setting `n ∣ e(Q | 𝔪)` for every prime `Q` of
  `integralClosure R M` over `𝔪`: the lower half of the leaf's conclusion `e(Q | 𝔪) = n`
  (the upper half `e ≤ n` and the residue separability need the local Kummer analysis and remain
  open; see docs/research/t-brauer-purity.md).
-/

open Polynomial IsLocalRing

namespace TBrauerPurity

/-- **General divisibility.** `R` a DVR with uniformizer `π`, `S` a Dedekind domain over `R` with
`𝔪S ≠ ⊥`, and `t ∈ S` with `tⁿ = π`: every prime `Q` of `S` over `𝔪` has `n ∣ e(Q|𝔪)`. -/
theorem dvd_ramificationIdx_of_pow_eq {R S : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing S] [IsDedekindDomain S] [Algebra R S]
    {π : R} (hπ : Irreducible π) (n : ℕ) (t : S) (ht : t ^ n = algebraMap R S π)
    (Q : Ideal S) [Q.LiesOver (maximalIdeal R)]
    (h0 : (maximalIdeal R).map (algebraMap R S) ≠ ⊥) :
    n ∣ Q.ramificationIdx R := by
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count (maximalIdeal R) Q h0]
  have hm : (maximalIdeal R).map (algebraMap R S) = Ideal.span {t} ^ n := by
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ, Ideal.map_span,
      Set.image_singleton, ← ht, Ideal.span_singleton_pow]
  rw [hm, UniqueFactorizationMonoid.normalizedFactors_pow, Multiset.count_nsmul]
  exact dvd_mul_right _ _

section Setting

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable (R K L M : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Field M] [Algebra L M] [Algebra K M] [Algebra R M]
    [IsScalarTower K L M] [IsScalarTower R K M]

include K in
/-- The tower `R → L → M` commutes in the leaf's setting. -/
theorem abhyankar_isScalarTower_RLM : IsScalarTower R L M := by
  refine IsScalarTower.of_algebraMap_eq fun r => ?_
  rw [IsScalarTower.algebraMap_apply R K M, IsScalarTower.algebraMap_apply R K L,
    IsScalarTower.algebraMap_apply K L M]

variable {R K L M}

include K in
/-- `π ≠ 0` and `n ≠ 0` in `L` for a uniformizer `π` and `n` invertible in `R`. -/
lemma abhyankar_ne_zero {π : R} (hπ : Irreducible π) {n : ℕ} (hn : IsUnit (n : R)) :
    algebraMap R L π ≠ 0 ∧ (n : L) ≠ 0 := by
  have hinj : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)
  refine ⟨fun h => hπ.ne_zero (hinj (by rw [h, map_zero])), fun h => ?_⟩
  have := hn.map (algebraMap R L)
  rw [map_natCast, h] at this
  exact not_isUnit_zero this

include K in
/-- `t` is a root of the separable polynomial `Xⁿ - π` over `L`. -/
lemma abhyankar_aeval {π : R} {n : ℕ} {t : M} (ht : t ^ n = algebraMap R M π) :
    aeval t (X ^ n - C (algebraMap R L π)) = 0 := by
  haveI := abhyankar_isScalarTower_RLM R K L M
  rw [map_sub, map_pow, aeval_X, aeval_C, ← IsScalarTower.algebraMap_apply, ht, sub_self]

include K in
/-- `M` is finite over `L` (hence over `K`). -/
theorem abhyankar_finiteDimensional_L {π : R} {n : ℕ} (hn0 : 0 < n) {t : M}
    (ht : t ^ n = algebraMap R M π) (hM : IntermediateField.adjoin L {t} = ⊤) :
    FiniteDimensional L M := by
  have hint : IsIntegral L t :=
    ⟨X ^ n - C (algebraMap R L π), monic_X_pow_sub_C _ hn0.ne', by
      rw [← aeval_def]; exact abhyankar_aeval (K := K) ht⟩
  haveI := IntermediateField.adjoin.finiteDimensional hint
  exact LinearEquiv.finiteDimensional
    ((IntermediateField.equivOfEq hM).trans IntermediateField.topEquiv).toLinearEquiv

theorem abhyankar_finiteDimensional {π : R} {n : ℕ} (hn0 : 0 < n) {t : M}
    (ht : t ^ n = algebraMap R M π) (hM : IntermediateField.adjoin L {t} = ⊤) :
    FiniteDimensional K M := by
  haveI := abhyankar_finiteDimensional_L (K := K) hn0 ht hM
  exact Module.Finite.trans L M

/-- `M/K` is separable. -/
theorem abhyankar_isSeparable {π : R} (hπ : Irreducible π) {n : ℕ} (hn : IsUnit (n : R))
    {t : M} (ht : t ^ n = algebraMap R M π) (hM : IntermediateField.adjoin L {t} = ⊤) :
    Algebra.IsSeparable K M := by
  obtain ⟨hπ0, hn0⟩ := abhyankar_ne_zero (L := L) (K := K) hπ hn
  have hsep : IsSeparable L t :=
    (separable_X_pow_sub_C _ hn0 hπ0).of_dvd (minpoly.dvd L t (abhyankar_aeval (K := K) ht))
  haveI := (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable L M).mpr hsep
  haveI : Algebra.IsSeparable L M := Algebra.IsSeparable.of_algHom L
    (IntermediateField.adjoin L {t})
    ((IntermediateField.equivOfEq hM).trans IntermediateField.topEquiv).symm.toAlgHom
  exact Algebra.IsSeparable.trans K L M

include K in
/-- `integralClosure R M` is a Dedekind domain. -/
theorem abhyankar_isDedekindDomain {π : R} (hπ : Irreducible π) {n : ℕ} (hn0 : 0 < n)
    (hn : IsUnit (n : R)) {t : M} (ht : t ^ n = algebraMap R M π)
    (hM : IntermediateField.adjoin L {t} = ⊤) :
    IsDedekindDomain (integralClosure R M) := by
  haveI := abhyankar_finiteDimensional (K := K) hn0 ht hM
  haveI := abhyankar_isSeparable (K := K) hπ hn ht hM
  exact integralClosure.isDedekindDomain R K M

include K in
/-- **Lower half of the conclusion of `PkgI2.AbhyankarDVR`.** In the leaf's setting (and under
its hypotheses on `π`, `n`, `t`; the tameness hypothesis on `L` is not needed for this half),
every prime `Q` of `integralClosure R M` over `𝔪` has `n ∣ e(Q | 𝔪)`. -/
theorem abhyankar_dvd_ramificationIdx (π : R) (hπ : Irreducible π) (n : ℕ) (hn0 : 0 < n)
    (hn : IsUnit (n : R)) (t : M) (ht : t ^ n = algebraMap R M π)
    (hM : IntermediateField.adjoin L {t} = ⊤)
    (Q : Ideal (integralClosure R M)) [Q.IsPrime] [Q.LiesOver (maximalIdeal R)] :
    n ∣ Q.ramificationIdx R := by
  haveI := abhyankar_isDedekindDomain (K := K) hπ hn0 hn ht hM
  have htint : IsIntegral R t :=
    ⟨X ^ n - C π, monic_X_pow_sub_C _ hn0.ne', by
      rw [eval₂_sub, eval₂_X_pow, eval₂_C, ht, sub_self]⟩
  let t' : integralClosure R M := ⟨t, htint⟩
  have ht' : t' ^ n = algebraMap R (integralClosure R M) π := Subtype.ext ht
  refine dvd_ramificationIdx_of_pow_eq hπ n t' ht' Q ?_
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ, Ideal.map_span,
    Set.image_singleton, Ne, Ideal.span_singleton_eq_bot, ← ht']
  intro h
  have h2 : t ^ n = 0 := congrArg Subtype.val h
  rw [ht] at h2
  obtain ⟨hπ0, -⟩ := abhyankar_ne_zero (L := L) (K := K) hπ hn
  apply hπ0
  haveI := abhyankar_isScalarTower_RLM R K L M
  rw [IsScalarTower.algebraMap_apply R L M] at h2
  exact (algebraMap L M).injective (by rw [h2, map_zero])

end Setting

section KummerUniformizer

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {R K M : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field M] [Algebra K M] [Algebra R M] [IsScalarTower R K M]

/-- `[K(t) : K] ≤ m` for a root `t` of `Xᵐ - π`. -/
lemma finrank_le_of_pow_eq {π : R} {m : ℕ} (hm0 : 0 < m) {t : M}
    (ht : t ^ m = algebraMap R M π) (hM : IntermediateField.adjoin K {t} = ⊤) :
    Module.finrank K M ≤ m := by
  have haev : aeval t (X ^ m - C (algebraMap R K π)) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, ← IsScalarTower.algebraMap_apply, ht, sub_self]
  have hmon : (X ^ m - C (algebraMap R K π)).Monic := monic_X_pow_sub_C _ hm0.ne'
  have hint : IsIntegral K t := ⟨_, hmon, by rw [← aeval_def]; exact haev⟩
  rw [← ((IntermediateField.equivOfEq hM).trans IntermediateField.topEquiv).toLinearEquiv.finrank_eq,
    IntermediateField.adjoin.finrank hint]
  calc (minpoly K t).natDegree ≤ (X ^ m - C (algebraMap R K π)).natDegree :=
        natDegree_le_of_dvd (minpoly.dvd K t haev) hmon.ne_zero
    _ = m := natDegree_X_pow_sub_C

/-- **Abhyankar's lemma for `L = K`, i.e. a Kummer extension by an `m`-th root of a uniformizer
is totally ramified.** `R` a DVR with fraction field `K` and uniformizer `π`, `m ≥ 1` invertible in
`R`, `M = K(t)` with `tᵐ = π`.  Every prime `Q` of `integralClosure R M` over `𝔪` has
`e(Q|𝔪) = m` and `f(Q|𝔪) = 1` (so its residue field is `R/𝔪`, trivially separable). -/
theorem ramificationIdx_eq_and_inertiaDeg_eq_one_of_pow_eq (π : R) (hπ : Irreducible π) (m : ℕ)
    (hm0 : 0 < m) (hm : IsUnit (m : R)) (t : M) (ht : t ^ m = algebraMap R M π)
    (hM : IntermediateField.adjoin K {t} = ⊤)
    (Q : Ideal (integralClosure R M)) [Q.IsPrime] [Q.LiesOver (maximalIdeal R)] :
    Q.ramificationIdx R = m ∧ Q.inertiaDeg R = 1 := by
  haveI := abhyankar_isDedekindDomain (R := R) (K := K) (L := K) hπ hm0 hm ht hM
  haveI := abhyankar_finiteDimensional (R := R) (K := K) (L := K) hm0 ht hM
  haveI := abhyankar_isSeparable (R := R) (K := K) (L := K) hπ hm ht hM
  have hdvd := abhyankar_dvd_ramificationIdx (R := R) (K := K) (L := K) π hπ m hm0 hm t ht hM Q
  haveI : Module.Finite R (integralClosure R M) := IsIntegralClosure.finite R K M _
  haveI : Module.IsTorsionFree R M := by
    rw [Module.isTorsionFree_iff_algebraMap_injective, IsScalarTower.algebraMap_eq R K M]
    exact (algebraMap K M).injective.comp (IsFractionRing.injective R K)
  haveI : Module.IsTorsionFree R (integralClosure R M) := inferInstance
  have hrank : Module.finrank R (integralClosure R M) = Module.finrank K M :=
    IsIntegralClosure.rank R K M _
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (maximalIdeal R) (integralClosure R M)
  rw [hrank] at hsum
  have hle := finrank_le_of_pow_eq (K := K) hm0 ht hM
  have hQ : Q.ramificationIdx R * Q.inertiaDeg R ≤ m := by
    refine le_trans ?_ (hsum.trans_le hle)
    exact Finset.single_le_sum (f := fun q : (maximalIdeal R).primesOver (integralClosure R M) =>
        q.1.ramificationIdx R * q.1.inertiaDeg R) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ (Ideal.primesOver.mk (maximalIdeal R) Q))
  have he0 : 0 < Q.ramificationIdx R := Ideal.ramificationIdx_pos R Q
  have hf0 : 0 < Q.inertiaDeg R := Ideal.inertiaDeg_pos Q R
  have hem : m ≤ Q.ramificationIdx R := Nat.le_of_dvd he0 hdvd
  constructor
  · nlinarith
  · nlinarith

/-- **`PkgI2.AbhyankarDVR`'s conclusion in the case `L = K`** (the leaf's exact conclusion:
ramification index `n` and separable residue extension, with the leaf's quotient algebra
instance). -/
theorem abhyankarDVR_conclusion_of_L_eq_K (π : R) (hπ : Irreducible π) (n : ℕ) (hn0 : 0 < n)
    (hn : IsUnit (n : R)) (t : M) (ht : t ^ n = algebraMap R M π)
    (hM : IntermediateField.adjoin K {t} = ⊤)
    (Q : Ideal (integralClosure R M)) [Q.IsPrime] [Q.LiesOver (maximalIdeal R)] :
    Q.ramificationIdx R = n ∧
      Algebra.IsSeparable (R ⧸ maximalIdeal R) (integralClosure R M ⧸ Q) := by
  obtain ⟨he, hf⟩ := ramificationIdx_eq_and_inertiaDeg_eq_one_of_pow_eq π hπ n hn0 hn t ht hM Q
  refine ⟨he, ?_⟩
  haveI : Q.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal Q (maximalIdeal R)
  rw [Ideal.inertiaDeg_eq_of_isMaximal (maximalIdeal R) Q] at hf
  letI : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  letI : Field (integralClosure R M ⧸ Q) := Ideal.Quotient.field _
  haveI : Module.Free (R ⧸ maximalIdeal R) (integralClosure R M ⧸ Q) :=
    Module.Free.of_divisionRing _ _
  have hbot := (Subalgebra.bot_eq_top_iff_finrank_eq_one (F := R ⧸ maximalIdeal R)
    (E := integralClosure R M ⧸ Q)).mpr hf
  refine ⟨fun x => ?_⟩
  have hx : x ∈ (⊥ : Subalgebra (R ⧸ maximalIdeal R) (integralClosure R M ⧸ Q)) := by
    rw [hbot]; trivial
  obtain ⟨y, rfl⟩ := Algebra.mem_bot.mp hx
  exact isSeparable_algebraMap y

end KummerUniformizer

section Assembly

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

open IntermediateField

/-- `[F(t) : F] ≤ m` for a root `t` of `Xᵐ - c`, `c ∈ F`. -/
lemma finrank_le_of_pow_eq_field {F E : Type*} [Field F] [Field E] [Algebra F E] {m : ℕ}
    (hm0 : 0 < m) {t : E} {c : F} (ht : t ^ m = algebraMap F E c)
    (hE : IntermediateField.adjoin F {t} = ⊤) : Module.finrank F E ≤ m := by
  have haev : aeval t (X ^ m - C c) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, ht, sub_self]
  have hmon : (X ^ m - C c).Monic := monic_X_pow_sub_C _ hm0.ne'
  have hint : IsIntegral F t := ⟨_, hmon, by rw [← aeval_def]; exact haev⟩
  rw [← ((IntermediateField.equivOfEq hE).trans IntermediateField.topEquiv).toLinearEquiv.finrank_eq,
    IntermediateField.adjoin.finrank hint]
  calc (minpoly F t).natDegree ≤ (X ^ m - C c).natDegree :=
        natDegree_le_of_dvd (minpoly.dvd F t haev) hmon.ne_zero
    _ = m := natDegree_X_pow_sub_C

/-- `Algebra.adjoin F {x} = ⊤` inside `F⟮x⟯` for integral `x`. -/
lemma algebra_adjoin_gen_eq_top {F E : Type*} [Field F] [Field E] [Algebra F E] {x : E}
    (hx : IsIntegral F x) :
    Algebra.adjoin F {(⟨x, IntermediateField.mem_adjoin_simple_self F x⟩ : F⟮x⟯)} = ⊤ := by
  apply Subalgebra.map_injective (f := (F⟮x⟯).val) (F⟮x⟯).val.injective
  rw [AlgHom.map_adjoin, Set.image_singleton, Algebra.map_top, IntermediateField.range_val,
    IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hx.isAlgebraic]
  rfl

/-- **Step (a).** In a Dedekind domain `A` integral over the DVR `R`, for a prime `Q` over `𝔪` with
ramification index `e`, the uniformizer factors as `π = u ϖᵉ` with `u ∉ Q`. -/
lemma exists_pow_mul_eq (R A : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing A] [IsDedekindDomain A] [Algebra R A] [Algebra.IsIntegral R A]
    [Module.IsTorsionFree R A] (π : R) (hπ : Irreducible π) (Q : Ideal A) [Q.IsPrime]
    [Q.LiesOver (IsLocalRing.maximalIdeal R)] :
    ∃ ϖ b a : A, ϖ ≠ 0 ∧ b ∉ Q ∧ a ∉ Q ∧
      b * algebraMap R A π = ϖ ^ (Q.ramificationIdx R) * a := by
  set e := Q.ramificationIdx R
  have hm : IsLocalRing.maximalIdeal R = Ideal.span {π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  have hinj : Function.Injective (algebraMap R A) := FaithfulSMul.algebraMap_injective R A
  have hπA : algebraMap R A π ≠ 0 := fun h => hπ.ne_zero (hinj (by rw [h, map_zero]))
  have hmap : (IsLocalRing.maximalIdeal R).map (algebraMap R A) = Ideal.span {algebraMap R A π} := by
    rw [hm, Ideal.map_span, Set.image_singleton]
  have hmap0 : (IsLocalRing.maximalIdeal R).map (algebraMap R A) ≠ ⊥ := by
    rw [hmap, Ne, Ideal.span_singleton_eq_bot]; exact hπA
  have hQ0 : Q ≠ ⊥ := by
    intro h
    have h1 : (IsLocalRing.maximalIdeal R) = Q.under R := Q.over_def _
    rw [h] at h1
    change _ = Ideal.comap _ ⊥ at h1
    rw [Ideal.comap_bot_of_injective _ hinj, hm, Ideal.span_singleton_eq_bot] at h1
    exact hπ.ne_zero h1
  have hQ1 : Q ≠ ⊤ := Ideal.IsPrime.ne_top ‹_›
  have hQirr : Irreducible Q := (Ideal.prime_of_isPrime hQ0 ‹_›).irreducible
  -- `count_Q (π) = e`
  have hcount : (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {algebraMap R A π})).count Q = e := by
    rw [← hmap]
    exact (Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count _ Q hmap0).symm
  have hle : Ideal.span {algebraMap R A π} ≤ Q ^ e := by
    have h1 := Ideal.le_pow_ramificationIdx' (p := IsLocalRing.maximalIdeal R) (P := Q)
    have hm0 : IsLocalRing.maximalIdeal R ≠ ⊥ := by
      rw [hm, Ne, Ideal.span_singleton_eq_bot]; exact hπ.ne_zero
    rwa [Ideal.ramificationIdx'_eq_ramificationIdx _ Q hm0, hmap] at h1
  have hnle : ¬ Ideal.span {algebraMap R A π} ≤ Q ^ (e + 1) := by
    intro h
    have hd : Q ^ (e + 1) ∣ Ideal.span {algebraMap R A π} := Ideal.dvd_iff_le.mpr h
    rw [UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors
      (pow_ne_zero _ hQ0) (by rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot])] at hd
    have := Multiset.count_le_of_le Q hd
    rw [UniqueFactorizationMonoid.normalizedFactors_pow,
      UniqueFactorizationMonoid.normalizedFactors_irreducible hQirr, normalize_eq,
      Multiset.count_nsmul, Multiset.count_singleton_self, hcount] at this
    omega
  -- a local uniformizer `ϖ ∈ Q \ Q²`
  obtain ⟨ϖ, hϖQ, hϖQ2⟩ := Ideal.exists_mem_pow_notMem_pow_succ Q hQ0 hQ1 1
  rw [pow_one] at hϖQ
  have hϖ0 : ϖ ≠ 0 := fun h => hϖQ2 (h ▸ Ideal.zero_mem _)
  obtain ⟨J2, hJ2⟩ : Q ∣ Ideal.span {ϖ} := Ideal.dvd_iff_le.mpr
    ((Ideal.span_singleton_le_iff_mem _).mpr hϖQ)
  have hJ2Q : ¬ J2 ≤ Q := by
    intro h
    apply hϖQ2
    have : Ideal.span {ϖ} ≤ Q ^ (1 + 1) := by
      rw [hJ2, pow_two]; exact Ideal.mul_mono_right h
    exact (Ideal.span_singleton_le_iff_mem _).mp this
  have hJ2eQ : ¬ J2 ^ e ≤ Q := fun h => hJ2Q (Ideal.IsPrime.le_of_pow_le h)
  obtain ⟨b, hbJ, hbQ⟩ := IsConcreteLE.not_le_iff_exists.mp hJ2eQ
  obtain ⟨J1, hJ1⟩ : Q ^ e ∣ Ideal.span {algebraMap R A π} := Ideal.dvd_iff_le.mpr hle
  have hmem : b * algebraMap R A π ∈ Ideal.span {ϖ ^ e} := by
    have h1 : b * algebraMap R A π ∈ J2 ^ e * Ideal.span {algebraMap R A π} :=
      Ideal.mul_mem_mul hbJ (Ideal.mem_span_singleton_self _)
    have h2 : J2 ^ e * Ideal.span {algebraMap R A π} = Ideal.span {ϖ ^ e} * J1 := by
      rw [hJ1, ← Ideal.span_singleton_pow, hJ2, mul_pow]; ring
    rw [h2] at h1
    exact (Ideal.mul_le_left : Ideal.span {ϖ ^ e} * J1 ≤ Ideal.span {ϖ ^ e}) h1
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hmem
  refine ⟨ϖ, b, a, hϖ0, hbQ, ?_, by rw [← ha, mul_comm]⟩
  intro haQ
  apply hnle
  rw [Ideal.span_singleton_le_iff_mem]
  have h3 : b * algebraMap R A π ∈ Q ^ (e + 1) := by
    rw [← ha, pow_succ']
    exact Ideal.mul_mem_mul haQ (Ideal.pow_mem_pow hϖQ e)
  rcases Ideal.IsPrime.mul_mem_pow Q h3 with h | h
  · exact absurd h hbQ
  · exact h

/-- Residue separability is transitive along a tower of primes. -/
lemma isSeparable_quotient_trans {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    (p : Ideal R) (q : Ideal A) (P : Ideal B) [p.IsMaximal] [q.IsMaximal] [P.IsMaximal]
    [q.LiesOver p] [P.LiesOver q] [P.LiesOver p]
    (h1 : Algebra.IsSeparable (R ⧸ p) (A ⧸ q)) (h2 : Algebra.IsSeparable (A ⧸ q) (B ⧸ P)) :
    Algebra.IsSeparable (R ⧸ p) (B ⧸ P) := by
  letI : Field (R ⧸ p) := Ideal.Quotient.field _
  letI : Field (A ⧸ q) := Ideal.Quotient.field _
  letI : Field (B ⧸ P) := Ideal.Quotient.field _
  haveI : IsScalarTower (R ⧸ p) (A ⧸ q) (B ⧸ P) := IsScalarTower.of_algebraMap_eq <| by
    rintro ⟨x⟩
    change algebraMap R (B ⧸ P) x = algebraMap (A ⧸ q) (B ⧸ P) (algebraMap R (A ⧸ q) x)
    rw [IsScalarTower.algebraMap_apply R A (B ⧸ P) x,
      IsScalarTower.algebraMap_apply R A (A ⧸ q) x, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.algebraMap_mk_of_liesOver]
    rfl
  exact Algebra.IsSeparable.trans _ (A ⧸ q) _

/-- Inertia degree one gives a (trivially) separable residue extension. -/
lemma isSeparable_quotient_of_inertiaDeg_eq_one {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (P : Ideal A) (Q : Ideal B) [P.IsMaximal] [Q.IsMaximal] [Q.LiesOver P]
    (hF : Q.inertiaDeg A = 1) : Algebra.IsSeparable (A ⧸ P) (B ⧸ Q) := by
  letI : Field (A ⧸ P) := Ideal.Quotient.field _
  letI : Field (B ⧸ Q) := Ideal.Quotient.field _
  rw [Ideal.inertiaDeg_eq_of_isMaximal P Q] at hF
  haveI : Module.Free (A ⧸ P) (B ⧸ Q) := Module.Free.of_divisionRing _ _
  have hbot := (Subalgebra.bot_eq_top_iff_finrank_eq_one (F := A ⧸ P) (E := B ⧸ Q)).mpr hF
  refine ⟨fun x => ?_⟩
  have hx : x ∈ (⊥ : Subalgebra (A ⧸ P) (B ⧸ Q)) := by rw [hbot]; trivial
  obtain ⟨y, rfl⟩ := Algebra.mem_bot.mp hx
  exact isSeparable_algebraMap y

theorem abhyankarDVR_main (R K L M : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Field M] [Algebra L M] [Algebra K M] [Algebra R M]
    [IsScalarTower K L M] [IsScalarTower R K M]
    (π : R) (hπ : Irreducible π) (n : ℕ) (hn0 : 0 < n) (hn : IsUnit (n : R))
    (htame : ∀ (Q : Ideal (integralClosure R L)) [Q.IsPrime]
      [Q.LiesOver (IsLocalRing.maximalIdeal R)],
      IsUnit ((Q.ramificationIdx R : ℕ) : R) ∧ Q.ramificationIdx R ∣ n ∧
      Algebra.IsSeparable (R ⧸ IsLocalRing.maximalIdeal R) (integralClosure R L ⧸ Q))
    (t : M) (ht : t ^ n = algebraMap R M π) (hM : IntermediateField.adjoin L {t} = ⊤)
    (Q' : Ideal (integralClosure R M)) [Q'.IsPrime]
    [Q'.LiesOver (IsLocalRing.maximalIdeal R)] :
    Q'.ramificationIdx R = n ∧
      Algebra.IsSeparable (R ⧸ IsLocalRing.maximalIdeal R) (integralClosure R M ⧸ Q') := by
  haveI := abhyankar_isScalarTower_RLM R K L M
  haveI : FiniteDimensional L M := abhyankar_finiteDimensional_L (K := K) hn0 ht hM
  haveI : FiniteDimensional K M := abhyankar_finiteDimensional (K := K) hn0 ht hM
  haveI : Algebra.IsSeparable K M := abhyankar_isSeparable (K := K) hπ hn ht hM
  haveI : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
  haveI : IsDedekindDomain (integralClosure R L) := integralClosure.isDedekindDomain R K L
  haveI : IsDedekindDomain (integralClosure R M) := integralClosure.isDedekindDomain R K M
  haveI : IsFractionRing (integralClosure R L) L :=
    integralClosure.isFractionRing_of_finite_extension K L
  -- the inclusion `S_L → S_M`
  let ι13 : integralClosure R L →ₐ[R] integralClosure R M :=
    ((IsScalarTower.toAlgHom R L M).comp (integralClosure R L).val).codRestrict _
      (fun x => x.2.map (IsScalarTower.toAlgHom R L M))
  letI : Algebra (integralClosure R L) (integralClosure R M) := ι13.toAlgebra
  haveI : IsScalarTower R (integralClosure R L) (integralClosure R M) := IsScalarTower.of_algHom ι13
  let Q : Ideal (integralClosure R L) := Q'.under (integralClosure R L)
  haveI : Q.LiesOver (IsLocalRing.maximalIdeal R) :=
    Ideal.LiesOver.tower_bot Q' Q (IsLocalRing.maximalIdeal R)
  obtain ⟨heU, ⟨m, hm⟩, hsepQ⟩ := htame Q
  set e := Q.ramificationIdx R with he_def
  have he0 : 0 < e := Ideal.ramificationIdx_pos R Q
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, mul_zero] at hm; omega
    · exact h
  haveI : Module.IsTorsionFree R (integralClosure R L) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    intro a b hab
    apply (IsFractionRing.injective R K)
    apply (algebraMap K L).injective
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    exact congrArg Subtype.val hab
  obtain ⟨ϖ, b, a, hϖ0, hbQ, haQ, hba⟩ := exists_pow_mul_eq R (integralClosure R L) π hπ Q
  rw [← he_def] at hba
  set u : integralClosure R L := b ^ (e - 1) * a with hu_def
  have huQ : u ∉ Q := by
    intro h
    rcases Ideal.IsPrime.mem_or_mem (inferInstance : Q.IsPrime) h with h | h
    · exact hbQ (Ideal.IsPrime.mem_of_pow_mem (inferInstance : Q.IsPrime) _ h)
    · exact haQ h
  -- `w = b t^m / ϖ`, with `wᵉ = u`
  let ϖM : M := algebraMap L M ((ϖ : integralClosure R L) : L)
  let bM : M := algebraMap L M ((b : integralClosure R L) : L)
  let aM : M := algebraMap L M ((a : integralClosure R L) : L)
  have hϖM : ϖM ≠ 0 := by
    simp only [ϖM, ne_eq, map_eq_zero]
    exact fun h => hϖ0 (Subtype.ext h)
  have hbM : bM ≠ 0 := by
    simp only [bM, ne_eq, map_eq_zero]
    intro h
    apply hbQ
    have : b = 0 := Subtype.ext h
    rw [this]; exact Q.zero_mem
  have h1 : bM * algebraMap R M π = ϖM ^ e * aM := by
    have := congrArg (fun x : integralClosure R L => algebraMap L M (x : L)) hba
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow] at this
    rw [IsScalarTower.algebraMap_apply R L M]
    exact this
  let w : M := bM * t ^ m / ϖM
  have hw : w ^ e = algebraMap L M ((u : integralClosure R L) : L) := by
    rw [hu_def]
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow]
    change (bM * t ^ m / ϖM) ^ e = bM ^ (e - 1) * aM
    rw [div_pow, mul_pow, ← pow_mul, mul_comm m e, ← hm, ht, div_eq_iff (pow_ne_zero _ hϖM)]
    obtain ⟨k, hk⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel]
    rw [hk] at h1
    linear_combination bM ^ k * h1
  -- `L₁ = L(w)` and `A₂ = integral closure of A₁ in L₁`
  have hwint : IsIntegral L w := ⟨X ^ e - C ((u : integralClosure R L) : L),
    monic_X_pow_sub_C _ he0.ne', by
      rw [← aeval_def, map_sub, map_pow, aeval_X, aeval_C, hw, sub_self]⟩
  let L1 : IntermediateField L M := L⟮w⟯
  haveI : FiniteDimensional L L1 := IntermediateField.adjoin.finiteDimensional hwint
  haveI : Algebra.IsSeparable L L1 := Algebra.isSeparable_tower_bot_of_isSeparable L L1 M
  haveI : IsScalarTower (integralClosure R L) L L1 := inferInstance
  haveI : IsDedekindDomain (integralClosure (integralClosure R L) L1) :=
    integralClosure.isDedekindDomain (integralClosure R L) L L1
  haveI : IsFractionRing (integralClosure (integralClosure R L) L1) L1 :=
    integralClosure.isFractionRing_of_finite_extension L L1
  haveI : Module.Finite (integralClosure R L) (integralClosure (integralClosure R L) L1) :=
    IsIntegralClosure.finite (integralClosure R L) L L1 _
  haveI : Module.IsTorsionFree (integralClosure R L) (integralClosure (integralClosure R L) L1) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    intro a b hab
    have h2 := congrArg (fun x => ((x : L1) : M)) (congrArg Subtype.val hab)
    apply Subtype.ext
    exact (algebraMap L M).injective h2
  -- `w` as an element of `A₂`
  let wL1 : L1 := ⟨w, IntermediateField.mem_adjoin_simple_self L w⟩
  have hwL1 : wL1 ^ e = algebraMap (integralClosure R L) L1 u := by
    apply Subtype.ext
    simp only [wL1, SubmonoidClass.coe_pow]
    exact hw
  have hw2int : IsIntegral (integralClosure R L) wL1 :=
    ⟨X ^ e - C u, monic_X_pow_sub_C _ he0.ne', by
      rw [← aeval_def, map_sub, map_pow, aeval_X, aeval_C, hwL1, sub_self]⟩
  let w2 : integralClosure (integralClosure R L) L1 := ⟨wL1, hw2int⟩
  have hw2 : w2 ^ e = algebraMap (integralClosure R L) _ u := Subtype.ext hwL1
  have hgen : Algebra.adjoin L {algebraMap (integralClosure (integralClosure R L) L1) L1 w2} = ⊤ :=
    algebra_adjoin_gen_eq_top hwint
  -- the map `A₂ → A₃` and the towers
  letI : Algebra R (integralClosure (integralClosure R L) L1) :=
    ((algebraMap (integralClosure R L) (integralClosure (integralClosure R L) L1)).comp
      (algebraMap R (integralClosure R L))).toAlgebra
  haveI : IsScalarTower R (integralClosure R L) (integralClosure (integralClosure R L) L1) :=
    IsScalarTower.of_algebraMap_eq (fun x => rfl)
  let f23 : integralClosure (integralClosure R L) L1 →+* M :=
    (L1.val.toRingHom).comp ((integralClosure (integralClosure R L) L1).val.toRingHom)
  have hf23 : ∀ x, f23 x ∈ integralClosure R M := by
    intro x
    have h1 : IsIntegral (integralClosure R L) ((x : L1) : M) :=
      x.2.map (L1.val.restrictScalars (integralClosure R L))
    exact isIntegral_trans (R := R) (A := integralClosure R L) _ h1
  let ι23 := f23.codRestrict (integralClosure R M) hf23
  letI : Algebra (integralClosure (integralClosure R L) L1) (integralClosure R M) := ι23.toAlgebra
  haveI : IsScalarTower (integralClosure R L) (integralClosure (integralClosure R L) L1)
      (integralClosure R M) := IsScalarTower.of_algebraMap_eq (fun x => Subtype.ext rfl)
  haveI : IsScalarTower R (integralClosure (integralClosure R L) L1) (integralClosure R M) :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      apply Subtype.ext
      change algebraMap R M x =
        ((algebraMap R (integralClosure (integralClosure R L) L1) x : L1) : M)
      rw [IsScalarTower.algebraMap_apply R L M x]
      rfl)
  let P : Ideal (integralClosure (integralClosure R L) L1) := Q'.under _
  haveI : P.LiesOver Q := Ideal.LiesOver.tower_bot Q' P Q
  have huP : algebraMap (integralClosure R L) _ u ∉ P := by
    intro h
    apply huQ
    rw [P.over_def Q]
    exact h
  have heA1 : IsUnit ((e : ℕ) : integralClosure R L) := by
    have := heU.map (algebraMap R (integralClosure R L))
    rwa [map_natCast] at this
  have hunr : Algebra.IsUnramifiedAt (integralClosure R L) P :=
    isUnramifiedAt_of_pow_eq (integralClosure R L) L L1 _ e he0 heA1 w2 u hw2 hgen P huP
  -- step (c): `A₂ → A₃`
  haveI : FiniteDimensional L1 M := FiniteDimensional.right L L1 M
  haveI : Algebra.IsSeparable L1 M := Algebra.isSeparable_tower_top_of_isSeparable L L1 M
  haveI : IsScalarTower (integralClosure (integralClosure R L) L1) (integralClosure R M) M :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower R (integralClosure (integralClosure R L) L1) M :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      rw [IsScalarTower.algebraMap_apply R L M x]
      rfl)
  haveI : Algebra.IsIntegral R (integralClosure (integralClosure R L) L1) :=
    Algebra.IsIntegral.trans (integralClosure R L)
  haveI : IsIntegralClosure (integralClosure R M) (integralClosure (integralClosure R L) L1) M := by
    refine ⟨Subtype.val_injective, fun {x} => ⟨fun hx => ?_, ?_⟩⟩
    · exact ⟨⟨x, isIntegral_trans (R := R) (A := integralClosure (integralClosure R L) L1) x hx⟩,
        rfl⟩
    · rintro ⟨y, rfl⟩
      exact (y.2 : IsIntegral R (y : M)).tower_top
  haveI : Module.Finite (integralClosure (integralClosure R L) L1) (integralClosure R M) :=
    IsIntegralClosure.finite (integralClosure (integralClosure R L) L1) L1 M _
  haveI : Module.IsTorsionFree (integralClosure (integralClosure R L) L1) (integralClosure R M) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    intro a b hab
    have h2 := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext h2)
  have hm_le : Module.finrank L1 M ≤ m := by
    have hc : w * ϖM / bM ∈ L1 := L1.div_mem (L1.mul_mem (IntermediateField.mem_adjoin_simple_self L w)
      (L1.algebraMap_mem _)) (L1.algebraMap_mem _)
    refine finrank_le_of_pow_eq_field (F := L1) hm0 (t := t) (c := ⟨w * ϖM / bM, hc⟩) ?_ ?_
    · change t ^ m = w * ϖM / bM
      simp only [w]
      field_simp
    · rw [← IntermediateField.restrictScalars_eq_top_iff (K := L),
        IntermediateField.restrictScalars_adjoin_eq_sup, hM, sup_top_eq]
  -- primes and ramification indices
  have hmax0 : IsLocalRing.maximalIdeal R ≠ ⊥ := by
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ, Ne,
      Ideal.span_singleton_eq_bot]
    exact hπ.ne_zero
  haveI : P.LiesOver (IsLocalRing.maximalIdeal R) :=
    Ideal.LiesOver.trans P Q (IsLocalRing.maximalIdeal R)
  have hP0 : P ≠ ⊥ := by
    intro h
    apply hmax0
    rw [(P.over_def (IsLocalRing.maximalIdeal R)), h]
    exact Ideal.comap_bot_of_injective _ (by
      intro a b hab
      apply IsFractionRing.injective R K
      apply (algebraMap K M).injective
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
      have h3 : algebraMap L M (algebraMap R L a) = algebraMap L M (algebraMap R L b) :=
        congrArg (fun x => ((x : L1) : M)) (congrArg Subtype.val hab)
      rw [IsScalarTower.algebraMap_apply R L M, IsScalarTower.algebraMap_apply R L M b]
      exact h3)
  haveI : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP0
  -- `e(Q'|P) · f(Q'|P) ≤ [M : L₁]`
  haveI : IsFractionRing (integralClosure R M) M :=
    integralClosure.isFractionRing_of_finite_extension K M
  have hsum := Ideal.sum_ramification_inertia (integralClosure R M) L1 M hP0
  have hQ'mem : Q' ∈ IsDedekindDomain.primesOverFinset P (integralClosure R M) :=
    (IsDedekindDomain.mem_primesOverFinset_iff hP0 _).mpr ⟨inferInstance, inferInstance⟩
  have hef : P.ramificationIdx' Q' * P.inertiaDeg' Q' ≤ m :=
    le_trans (Finset.single_le_sum (f := fun Q'' => P.ramificationIdx' Q'' * P.inertiaDeg' Q'')
      (fun _ _ => Nat.zero_le _) hQ'mem) (hsum.trans_le hm_le)
  haveI : Q'.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal Q' P
  rw [Ideal.ramificationIdx'_eq_ramificationIdx P Q' hP0,
    Ideal.inertiaDeg'_eq_inertiaDeg] at hef
  -- `n ∣ e(Q'|𝔪) = e · e(Q'|P)`
  have hdvd := abhyankar_dvd_ramificationIdx (K := K) (L := L) π hπ n hn0 hn t ht hM Q'
  have hPQ : P.ramificationIdx (integralClosure R L) = 1 := Ideal.ramificationIdx_eq_one P _
  have htow1 : Q'.ramificationIdx R =
      P.ramificationIdx R * Q'.ramificationIdx (integralClosure (integralClosure R L) L1) :=
    Ideal.ramificationIdx_tower (R := R) P Q'
  have htow2 : P.ramificationIdx R = Q.ramificationIdx R * P.ramificationIdx (integralClosure R L) :=
    Ideal.ramificationIdx_tower (R := R) Q P
  rw [htow2, hPQ, mul_one, ← he_def] at htow1
  have hE0 : 0 < Q'.ramificationIdx (integralClosure (integralClosure R L) L1) :=
    Ideal.ramificationIdx_pos _ Q'
  have hF0 : 0 < Q'.inertiaDeg (integralClosure (integralClosure R L) L1) :=
    Ideal.inertiaDeg_pos Q' _
  rw [htow1, hm] at hdvd
  have hmE : m ∣ Q'.ramificationIdx (integralClosure (integralClosure R L) L1) :=
    Nat.dvd_of_mul_dvd_mul_left he0 hdvd
  have hmE' := Nat.le_of_dvd hE0 hmE
  have hE : Q'.ramificationIdx (integralClosure (integralClosure R L) L1) = m := by nlinarith
  have hF : Q'.inertiaDeg (integralClosure (integralClosure R L) L1) = 1 := by nlinarith
  refine ⟨by rw [htow1, hE, hm], ?_⟩
  -- residue fields: `k → κ(Q) → κ(P) → κ(Q')`
  haveI : Q.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal Q (IsLocalRing.maximalIdeal R)
  have hQ0 : Q ≠ ⊥ := by
    intro h
    apply hmax0
    rw [Q.over_def (IsLocalRing.maximalIdeal R), h]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective R _)
  haveI : Algebra.IsSeparable (FractionRing (integralClosure R L))
      (FractionRing (integralClosure (integralClosure R L) L1)) := by
    refine Algebra.IsSeparable.of_equiv_equiv
      (FractionRing.algEquiv (integralClosure R L) L).symm.toRingEquiv
      (FractionRing.algEquiv (integralClosure (integralClosure R L) L1) L1).symm.toRingEquiv ?_
    ext _
    exact IsFractionRing.algEquiv_commutes (FractionRing.algEquiv (integralClosure R L) L).symm
      (FractionRing.algEquiv (integralClosure (integralClosure R L) L1) L1).symm _
  have hsep12 : Algebra.IsSeparable (integralClosure R L ⧸ Q)
      (integralClosure (integralClosure R L) L1 ⧸ P) := by
    by_contra H
    exact (dvd_differentIdeal_iff.mp
      (dvd_differentIdeal_of_not_isSeparable (integralClosure R L) hQ0 P H)) hunr
  have hsep23 := isSeparable_quotient_of_inertiaDeg_eq_one P Q' hF
  have hsep02 := isSeparable_quotient_trans (IsLocalRing.maximalIdeal R) Q P hsepQ hsep12
  exact isSeparable_quotient_trans (IsLocalRing.maximalIdeal R) P Q' hsep02 hsep23

end Assembly

end TBrauerPurity

universe u_lf

/-- **Leaf T2 (`PkgI2.AbhyankarDVR`), proved** (t-brauer-purity, `T2Full.lean`). -/
theorem TBrauerPurity.abhyankarDVR : PkgI2.AbhyankarDVR.{u_lf} := by
  intro R K L M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ π hπ n hn0 hn htame t ht hM Q _ _
  exact TBrauerPurity.abhyankarDVR_main R K L M π hπ n hn0 hn htame t ht hM Q

end LeafFoldT2


/-! ## leaf-fold (2026-11-13): the closed leaves folded in, three statement repairs, the open bundles

Since leaf-fold the whole file lives in `namespace HDec`, so that it can import the closed proofs of
`ZInQKernel/Contrib/`. Those proofs are stated over `ZInQKernel/HDecomp/`, the kernel port of this
file, which declares the same names at the root (`PkgI6.LocalH2CardC`, …). Inside `HDec` every
name of this file resolves to this file's copy (innermost namespace first), and a Contrib theorem
about the root copy is converted to this file's copy by `exact` (definitional unfolding). In
addition, `#hdec_same HDec.X` checks *syntactically* that `HDec.X` and the root `X`, and every
`HDec` constant they mention, have the same type and the same body after deleting the prefix
`HDec.`, up to the auto-generated names of proofs (proof irrelevance). -/

section LeafFoldCheckSec

open Lean Elab Command Meta

/-- `t` is a proposition (failures count as no). -/
def LeafFoldCheck.isProofType (t : Expr) : MetaM Bool := do
  try Meta.isProp t catch _ => pure false

/-- Normal form for `#hdec_same`: every constant whose type is a proposition (a theorem, an
auxiliary `_proof_n`, a `Fact` instance, …) is replaced by `proofOf T` with `T` its normalized
type (proof irrelevance: two proofs of one proposition are interchangeable, and their
auto-generated names differ between files); every other constant `c` is renamed to `stripN c`. -/
partial def LeafFoldCheck.norm (stripN : Name → Name) (fuel : Nat) (e : Expr) : MetaM Expr := do
  let env ← getEnv
  let mut m : Std.HashMap Name Expr := {}
  for c in e.getUsedConstants do
    if let some ci := env.find? c then
      let isPf ← LeafFoldCheck.isProofType ci.type
      if isPf then
        let t ← if fuel = 0 then pure (mkConst `LeafFoldCheck.deep)
          else LeafFoldCheck.norm stripN (fuel - 1) ci.type
        m := m.insert c (mkApp (mkConst `LeafFoldCheck.proofOf) t)
  return e.replace fun
    | .const c us => some ((m.get? c).getD (.const (stripN c) us))
    | _ => none

/-- The comparison behind `#hdec_same`: `n` (an `HDec.` name) against `top`; a nested `HDec.Z`
against `P.Z` if that exists, else against `Z`. -/
def LeafFoldCheck.run (n top P : Name) : TermElabM Unit := do
  let env ← getEnv
  let strip : Name → Name := fun c =>
    if c == n then top
    else if (`HDec).isPrefixOf c then
      let z := c.replacePrefix `HDec .anonymous
      if !P.isAnonymous && env.contains (P ++ z) then P ++ z else z
    else c
  let mut todo : Array Name := #[n]
  let mut seen : NameSet := {}
  let mut bad : Array String := #[]
  let mut count : Nat := 0
  while todo.size > 0 do
    let c := todo.back!
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    let some ci := env.find? c | bad := bad.push s!"{c}: not found"
    -- proofs are compared through their types only (where they occur)
    if (← LeafFoldCheck.isProofType ci.type) && c != n then continue
    count := count + 1
    let some ri := env.find? (strip c) | bad := bad.push s!"{c}: no root counterpart"
    if (← LeafFoldCheck.norm strip 8 ci.type) != (← LeafFoldCheck.norm id 8 ri.type) then
      bad := bad.push s!"{c}: types differ"
    let isThm := match ci with | .thmInfo _ => true | _ => false
    let mut used := ci.type.getUsedConstants
    if !isThm then
      match ci.value?, ri.value? with
      | some v, some w =>
        if (← LeafFoldCheck.norm strip 8 v) != (← LeafFoldCheck.norm id 8 w) then
          bad := bad.push s!"{c}: bodies differ"
        used := used ++ v.getUsedConstants
      | none, none => pure ()
      | _, _ => bad := bad.push s!"{c}: kinds differ"
    match ci with
    | .inductInfo v => used := used ++ v.ctors.toArray
    | _ => pure ()
    for u in used do
      if (`HDec).isPrefixOf u && !seen.contains u then todo := todo.push u
  if bad.isEmpty then
    logInfo m!"{n}: {count} HDec constants compared; each is its root counterpart verbatim \
      (up to the prefix and the names of proofs)"
  else
    logInfo m!"{n}: {count} HDec constants compared; differences:\n\
      {String.intercalate "\n" bad.toList}"

/-- `#hdec_same HDec.X`: compare `HDec.X` with the root `X`, recursively through every `HDec.`
constant that the types and (for definitions) the bodies mention: the types and bodies must agree
after deleting the prefix `HDec.`, up to the names of proofs (`LeafFoldCheck.norm`). Reports the
number of constants compared and every difference. -/
elab "#hdec_same " a:ident : command => liftTermElabM do
  LeafFoldCheck.run a.getId (a.getId.replacePrefix `HDec .anonymous) .anonymous

/-- `#hdec_same_as HDec.X Y P`: compare `HDec.X` with `Y`, and a nested `HDec.Z` with `P.Z` if that
exists, else with `Z` (for a Contrib file that restates `X` and some of the definitions it uses
inside a namespace `P`). -/
elab "#hdec_same_as " a:ident b:ident c:ident : command => liftTermElabM do
  LeafFoldCheck.run a.getId b.getId c.getId

end LeafFoldCheckSec

noncomputable section

/-! ### Statement repair: R14 with its published determinant clause (g0-mod-galois)

Copied verbatim from `scratch/g0-mod-galois/part_det.lean` (`toRingEquivQ`, `cycQ`, `R14Det`). -/

namespace G0Galois

-- op-dedupe was: open PkgI4 (GaloisRep GaloisChar)
open _root_.PkgI4 (GaloisRep GaloisChar) -- op-dedupe

/-- `σ ↦ σ` as ring automorphisms of `ℚ̄`. -/
def toRingEquivQ : PkgI4.GQ →* (PkgI4.Qbar ≃+* PkgI4.Qbar) where
  toFun σ := σ.toRingEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The `ℓ`-adic cyclotomic character `χ_ℓ : G_ℚ → ℤ_ℓ^× ⊆ ℚ̄_ℓ^×` (Mathlib's
`cyclotomicCharacter` on `ℚ̄`, as `PkgI4.cyc` on `G_{ℚ_p}`). -/
def cycQ (ℓ : ℕ) [Fact ℓ.Prime] : PkgI4.GQ →* (PadicAlgCl ℓ)ˣ :=
  (Units.map ((algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)).comp PadicInt.Coe.ringHom).toMonoidHom).comp
    ((cyclotomicCharacter PkgI4.Qbar ℓ).comp toRingEquivQ)

/-- **R14 with its published determinant clause (leaf; Shimura 1971 Thm 7.14 for `k = 2`,
Deligne 1971 for `k ≥ 2`, Deligne–Serre 1974 for `k = 1`; locators UNVERIFIED).** For a normalized
eigenform `g` of weight `k ≥ 1` with nebentypus, there is a semisimple `ρ_g` attached to `g` with
`det ρ_g = ε · χ_ℓ^{k−1}`, `ε` of finite image (the nebentypus as a Galois character). This is
`HSyn.EigenformRepExists` plus the determinant, which the published statements contain. -/
def R14Det : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : PkgI4.CF N k),
    0 < N → 1 ≤ k → PkgI4.IsNormalizedEigenform g χ →
    ∃ ρ : GaloisRep ℓ 2, ρ.IsSemisimple ∧ ρ.AttachedTo ιC ιL g ∧
      ∃ ε : PkgI4.GQ →* (PadicAlgCl ℓ)ˣ, (Set.range ε).Finite ∧
        ∀ σ, (ρ.mat σ).det = ((ε σ * cycQ ℓ σ ^ (k - 1) : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ)

/-! ### Statement repair: G10 with concrete hypotheses (g10-odd)

g0-mod-galois's glue Prop `G10Glue` (oddness of `r_ℓ`, inside the glue piece
`GluePieces.modularConstituent`) assumed the `opaque` placeholders `HSyn.T11_RiemannGAGA`,
`HSyn.T12_ArtinComparison` (inert: nothing follows from them). g10-odd's corrected statement
`G10GlueConcrete` assumes the concrete leaves T11(a), T11(b), T35, T5, T26 and R9(b) instead, and
g10-odd proves `G10GlueConcrete` from the smaller glue Prop `ConjTwistNontrivial` (a statement
about `A` alone). The objects `resQ`, `Vb`, `tate`, `Intertwines` are copied verbatim from
g0-mod-galois (`ZInQKernel/Contrib/G9/Statement.lean` has the same copies), `G10Out`,
`G10GlueConcrete`, `ConjTwistNontrivial` verbatim from `scratch/g10-odd/G10Odd.lean` (with the
namespace `ZInQ.LeafPush2` written out). Neither is a hypothesis of `sixContactMin_of_open`: both
are parts of the glue piece `modularConstituent`. -/

/-- The restriction map `G_K → G_ℚ` for a number field `K` (Mathlib's
`Field.absoluteGaloisGroup.map` along `ℚ → K`). -/
def resQ (K : Type) [Field K] [NumberField K] : Field.absoluteGaloisGroup K →* PkgI4.GQ :=
  (Field.absoluteGaloisGroup.map (algebraMap ℚ K) :
    Field.absoluteGaloisGroup K →* Field.absoluteGaloisGroup ℚ)

/-- `ℚ̄_ℓ ⊗_{ℚ_ℓ} V_ℓ(A)`. -/
abbrev Vb {K : Type} [Field K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] : Type :=
  TensorProduct ℚ_[ℓ] (PadicAlgCl ℓ) (A.V ℓ)

/-- The Tate action of `G_K` on `ℚ̄_ℓ ⊗ V_ℓ(A)`. -/
def tate {K : Type} [Field K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] :
    Representation (PadicAlgCl ℓ) (Field.absoluteGaloisGroup K) (Vb A ℓ) :=
  GlueI3.repBaseChange (PadicAlgCl ℓ) (A.galRep ℓ)

/-- `e` intertwines the operators `f g` on `V` with `r(g) ⊕ r(g)` on `ℚ̄_ℓ² × ℚ̄_ℓ²`. -/
def Intertwines {ℓ : ℕ} [Fact ℓ.Prime] {G V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    (f : G → Module.End (PadicAlgCl ℓ) V) (m : G → Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ))
    (e : V ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ)) : Prop :=
  ∀ g v, e (f g v) = ((m g).mulVec (e v).1, (m g).mulVec (e v).2)

/-- Output of G10: `r` is odd. -/
def G10Out {ℓ : ℕ} [Fact ℓ.Prime] (r : GaloisRep ℓ 2) : Prop := r.IsOdd

/-- **G10, corrected statement (GLUE; g10-odd).** `G10Glue` with the inert placeholders replaced
by the concrete leaves its proof uses: T11(a) `T11a_RiemannEnd`, T11(b) `T11b_Rigidity`, T35
`UniformizationExists`, T5 `PkgI2.TorsionStructure`, T26 `PkgI3.TateModuleFree`, R9(b)
`PkgI3.FaltingsTate`. Conclusion unchanged. -/
def G10GlueConcrete : Prop :=
  ZInQ.LeafPush2.T11a_RiemannEnd → ZInQ.LeafPush2.T11b_Rigidity →
  ZInQ.LeafPush2.UniformizationExists → PkgI2.TorsionStructure.{0} →
  PkgI3.TateModuleFree → PkgI3.FaltingsTate →
  ∀ (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] (A : PkgI3.AbVar K) (ℓ : ℕ)
    [Fact ℓ.Prime] (r : GaloisRep ℓ 2)
    (e : Vb A ℓ ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ)),
    A.dim = 2 → Module.finrank ℤ (PkgI3.AbVar.End A) = 4 → PkgI3.EndDivision A →
    (∃ x y : PkgI3.AbVar.End A, x * y ≠ y * x) →
    Intertwines (tate A ℓ) (fun σ => r.mat (resQ K σ)) e → G10Out r

/-- **The core of G10 (GLUE; g10-odd, which proves `ConjTwistNontrivial → G10Glue` and
`ConjTwistFromLeaves → G10GlueConcrete`).** Complex conjugation does not act trivially by
conjugation on the image of `G_K` in `GL(V_ℓ(A))`. -/
def ConjTwistNontrivial : Prop :=
  PkgI3.FaltingsTate →
  ∀ (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] (A : PkgI3.AbVar K) (ℓ : ℕ)
    [Fact ℓ.Prime], A.dim = 2 → ∀ c : PkgI4.GQ, PkgI4.IsComplexConj c →
    ¬ ∀ σ τ : Field.absoluteGaloisGroup K, resQ K τ = c * resQ K σ * c⁻¹ →
      A.galRep ℓ τ = A.galRep ℓ σ

end G0Galois

/-! ### Statement repair: R10 with its multiplicity-0 clause (g9-derham, finding F1)

`PkgI4.DeRhamComparison` (field `r10`) gives the Hodge–Tate multiplicities `g` at `0` and `−1`
but not `0` at every other weight, which G9's output `HasHTWeights p ρ {0, −1}` needs (g9-derham
F1). The published theorem contains it: the Hodge–Tate decomposition
`ℂ_p ⊗ V_p(A) ≅ ℂ_p^g ⊕ ℂ_p(1)^g` (Tate 1967 for good reduction, Faltings 1988 in general;
UNVERIFIED locators) with Tate's `ℂ_p(j)^{G_F} = 0` for `j ≠ 0`. `R10Weights` is g9-derham's
`G9Bridge.R10Weights` (verbatim; `ZInQKernel/Contrib/G9/Reduction.lean`); the corrected leaf is
`DeRhamComparisonHT`, R10 with the clause, used as the field `r10` of `OpenResearchLeaves`. -/

namespace PkgI4

/-- g9-derham's missing clause of R10: every Hodge–Tate weight other than `0`, `−1` of `V_p(A)`
has multiplicity `0`. -/
def R10Weights : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : PkgI4.I3.AbVar F) (w : ℤ), w ≠ 0 → w ≠ -1 → PkgI4.htMultOver p (A.galRep p) w = 0

/-- **I4-L0 corrected (R10 with the multiplicity-0 clause; leaf).** For an abelian variety `A`
of dimension `g` over a finite extension `F` of `ℚ_p`, `V_p(A)` is de Rham, with Hodge–Tate
weights `0` and `−1` each of multiplicity `g`, and multiplicity `0` at every other weight
(`DeRhamComparison` and `R10Weights` in one statement; references as for `DeRhamComparison`, plus
the Hodge–Tate decomposition, Tate 1967, Faltings 1988, UNVERIFIED locators). -/
def DeRhamComparisonHT : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : PkgI4.I3.AbVar F),
    (∀ g : ℕ, A.dim = (g : WithBot ℕ∞) →
      IsDeRhamOver p (A.galRep p) ∧ htMultOver p (A.galRep p) 0 = g ∧
        htMultOver p (A.galRep p) (-1) = g) ∧
    ∀ w : ℤ, w ≠ 0 → w ≠ -1 → htMultOver p (A.galRep p) w = 0

theorem deRhamComparison_of_HT (h : DeRhamComparisonHT) : DeRhamComparison := by
  intro p _ F _ _ _ A g hg
  exact (h p F A).1 g hg

theorem r10Weights_of_HT (h : DeRhamComparisonHT) : R10Weights := by
  intro p _ F _ _ _ A w h0 h1
  exact (h p F A).2 w h0 h1

/-- The corrected R10 is the conjunction of the old field and the missing clause. -/
theorem deRhamComparisonHT_iff : DeRhamComparisonHT ↔ DeRhamComparison ∧ R10Weights := by
  refine ⟨fun h => ⟨deRhamComparison_of_HT h, r10Weights_of_HT h⟩, fun ⟨h, hw⟩ => ?_⟩
  intro p _ F _ _ _ A
  exact ⟨fun g hg => h p F A g hg, fun w h0 h1 => hw p F A w h0 h1⟩

end PkgI4

namespace HSyn

/-! ### The closed leaves (leaf-fold)

Each bundle field below is now a theorem, from a closed proof in `ZInQKernel/Contrib/` (or, for
T2, t-brauer-purity's proof copied above). The `#hdec_same` lines after the bundles check that
the field's Prop is the Contrib theorem's Prop verbatim. -/

/-- T2, Abhyankar's lemma, DVR form (t-brauer-purity; proof copied above). -/
theorem t2_proved : PkgI2.AbhyankarDVR.{0} := TBrauerPurity.abhyankarDVR

/-- T15, `#H²(G_{ℚ_p}, ℤ/2) = #H²(G_ℝ, ℤ/2) = 2` on cochains (t1415-tc, from Tau Ceti). -/
theorem t15_proved : PkgI6.LocalH2CardC := ZInQ.Contrib.BrauerT14T15.localH2CardC

/-- T16(a), local Kronecker–Weber for `ℚ_p` (lkw, from Tau Ceti's local class field theory). -/
theorem t16a_proved : ∀ (p : ℕ) [Fact p.Prime], PkgI6.LocalKroneckerWeber p :=
  ZInQ.Contrib.localKroneckerWeber

/-- T17, Kronecker–Weber for cyclic `L/ℚ` (kw-new, from Tau Ceti's `kroneckerWeber`). -/
theorem t17_proved : TSkolemKW.KW.KroneckerWeberCyclic :=
  ZInQ.Contrib.KroneckerWeber.kroneckerWeberCyclic

/-- T17 in its original (pre-leaf-adopt3) form `HSyn.KroneckerWeber` (kw-new restates it
verbatim as `ZInQ.Contrib.KroneckerWeber.HSynKroneckerWeber`). -/
theorem kroneckerWeber_proved : KroneckerWeber := ZInQ.Contrib.KroneckerWeber.hSynKroneckerWeber

/-- T18, Chebotarev, existence form (cheb-bridge, from Tau Ceti's Chebotarev density theorem). -/
theorem t18_proved : PkgI6.ChebotarevExists := ZInQ.Contrib.chebotarevExists

/-- T18 in its density form `HSyn.FrobeniusDense` (cheb-bridge restates it verbatim, with the
`HSyn` definitions it uses, as `ZInQ.Contrib.ChebFD.HSyn.FrobeniusDense`). -/
theorem frobeniusDense_proved : FrobeniusDense := ZInQ.Contrib.frobeniusDense

/-- T20, Hilbert's different formula, global form (diff-bridge, from Tau Ceti). -/
theorem t20_proved : GlueConductor.HilbertDifferentFormula :=
  ZInQ.Contrib.Different.hilbertDifferentFormula

/-- T21, Serre's different bound, global form (diff-bridge, from Tau Ceti's wild bound). -/
theorem t21_proved : GlueConductor.SerreDifferentBound := ZInQ.Contrib.Different.serreDifferentBound

/-- T25, a normalized eigenform has the eigenvalues of a newform (t25-newform, from Tau Ceti). -/
theorem t25_proved : PkgI4.NewformOfEigenform := T25.newformOfEigenform_leaf

/-- T30, the local square-root criterion (lkw: from T16(a); the file's own derivation
`T30.leafSqrtCrit_of_t16a` gives the same). -/
theorem t30_proved : GlueDescent.B2Q.LeafSqrtCrit := ZInQ.Contrib.leafSqrtCrit

/-- T30 by this file's own derivation from T16(a). -/
theorem t30_proved' : GlueDescent.B2Q.LeafSqrtCrit := T30.leafSqrtCrit_of_t16a t16a_proved

/-- T31, unramified outside the primes of a finite set (t31-unram, from Tau Ceti). -/
theorem t31_proved : GlueDescent.B2Q.LeafUnramified := ZInQ.Contrib.T31.leafUnramified

/-- T14(a′), T14(b′) from the Kummer case of the second inequality of global class field theory
(t1415-tc: `KummerIndexBound`, over Tau Ceti's idele class groups; Milne, *Class Field Theory*,
VII §6). Not used below: T14(a′), T14(b′) stay open leaves; this is the reduction t1415-tc found. -/
theorem t14_of_kummerIndexBound (h : ZInQ.Contrib.BrauerT14T15.KummerIndexBound) :
    PkgI6.BrauerHasse2C ∧ PkgI6.BrauerReciprocity2C :=
  ⟨ZInQ.Contrib.BrauerT14T15.brauerHasse2C_of_kummerIndexBound h,
    ZInQ.Contrib.BrauerT14T15.brauerReciprocity2C_of_kummerIndexBound h⟩

/-- R14 from its corrected form `G0Galois.R14Det` (drop the determinant clause). -/
theorem eigenformRepExists_of_r14Det (h : G0Galois.R14Det) : EigenformRepExists := by
  intro ℓ _ ιC ιL N k χ g hN hk hg
  obtain ⟨ρ, hss, hatt, -⟩ := h ℓ ιC ιL N k χ g hN hk hg
  exact ⟨⟨ρ.toHom, ρ.continuous_toHom⟩, hss, hatt⟩

/-- **The research-level leaves still open** (leaf-fold, 2026-11-13): the 26 fields of
`ResearchLeaves` (the note's 23 research-level leaves; none is proved), with two fields replaced by the published, corrected statements:
* `r10 : PkgI4.DeRhamComparisonHT`: R10 with the multiplicity-0 clause (g9-derham F1);
* `r14 : G0Galois.R14Det`: R14 with the determinant `det ρ_g = ε χ_ℓ^{k−1}` (g0-mod-galois).
Both imply the old fields (`PkgI4.deRhamComparison_of_HT`, `eigenformRepExists_of_r14Det`).
Still `opaque` placeholders: `r1an` (R1(b)) and `r17` (R17). -/
structure OpenResearchLeaves : Prop where
  r1r2 : LeafAdopt.R1R2fpRep
  r1an : R01b_ComplexUniformization
  r1rec : LeafQM.AV.R1rec
  r3 : ZInQ.LeafPush2.R03_LinYang
  r4 : PkgI1.ThetaModularity
  r5 : LeafQM.AV.R5fp
  r5count : LeafQM.AV.R5fpCount
  r6 : PkgI2.RaynaudCriterion.{0}
  r7a : PkgI2.NeronOggShafarevich.{0}
  r7b : PkgI2.SerreTatePotentialGood.{0}
  r8 : PkgI2.GrothendieckMonodromy.{0}
  r9a : PkgI3.FaltingsSemisimple
  r9b : PkgI3.FaltingsTate
  /-- R10 corrected: with multiplicity `0` at every weight other than `0`, `−1` (g9-derham). -/
  r10 : PkgI4.DeRhamComparisonHT
  r11r12 : PkgI4.PanBerger
  r13 : PkgI4.EigenformHT
  /-- R14 corrected: with the determinant clause (g0-mod-galois's `R14Det`). -/
  r14 : G0Galois.R14Det
  r15 : DeligneSerreConseq
  r16 : LeafModCurves.R16_EichlerShimuraJ1'
  r17 : R17_Carayol
  r18 : ZInQ.LeafPush2.R18_Javanpeykar
  r19 : ZInQ.DefFaltings.R19_GaudronRemond
  r20 : ZInQ.DefFaltings.R20_FaltingsLemma5
  r21 : ZInQ.DefFaltings.R21_Bost
  r22 : ZInQ.LeafPush2.R22_Pazuki
  h5 : LeafAdopt.H5

/-- **The textbook leaves still open** (leaf-fold, 2026-11-13): `TextbookLeaves` without the nine
fields now proved (`t2`, `t15`, `t16a`, `t17`, `t18`, `t20`, `t21`, `t25`, `t31`). -/
structure OpenTextbookLeaves : Prop where
  t1 : PkgI2.PurityBranchLocus.{0}
  t3 : PkgI2.NeronMappingAbelianScheme.{0}
  t4 : PkgI2.ReductionTorsionBijective.{0}
  t5 : PkgI2.TorsionStructure.{0}
  t6 : PkgI3.HomFreeFinite
  t7 : PkgI3.CharPolyIndepOfEll
  t8 : PkgI3.PoincareReducibility
  t9 : LeafPush.T09_WeilPairing.{0}
  t10 : T10Etale.T10_TateDuality
  t11a : ZInQ.LeafPush2.T11a_RiemannEnd
  t11b : ZInQ.LeafPush2.T11b_Rigidity
  t14a : PkgI6.BrauerHasse2C
  t14b : PkgI6.BrauerReciprocity2C
  t16b : PkgI6.LocalReciprocityUpper
  t23 : ∀ (p : ℕ) [Fact p.Prime], PkgI4.T23_FontaineClosure p
  t24 : EigenformTwist
  t26 : PkgI3.TateModuleFree
  t27 : PkgI3.QMDichotomyYu
  t28 : PkgI1.IgusaClebschSeparation
  t29a : ∀ (p : ℕ) [Fact p.Prime], LeafPush.T29a_DivisionNormalizer p
  t29b : ∀ (p : ℕ) [Fact p.Prime], LeafPush.T29b_SplitNormalizer p
  t33 : LeafModCurves.JacobianExists ℚ
  t34 : LeafModCurves.DimJ1Genus
  t35 : ZInQ.LeafPush2.UniformizationExists
  x1 : X1Belyi.X1Leaves
  t41 : ZInQ.H5Neron.NeronModelExists

theorem researchLeaves_of_open (r : OpenResearchLeaves) : ResearchLeaves where
  r1r2 := r.r1r2
  r1an := r.r1an
  r1rec := r.r1rec
  r3 := r.r3
  r4 := r.r4
  r5 := r.r5
  r5count := r.r5count
  r6 := r.r6
  r7a := r.r7a
  r7b := r.r7b
  r8 := r.r8
  r9a := r.r9a
  r9b := r.r9b
  r10 := PkgI4.deRhamComparison_of_HT r.r10
  r11r12 := r.r11r12
  r13 := r.r13
  r14 := eigenformRepExists_of_r14Det r.r14
  r15 := r.r15
  r16 := r.r16
  r17 := r.r17
  r18 := r.r18
  r19 := r.r19
  r20 := r.r20
  r21 := r.r21
  r22 := r.r22
  h5 := r.h5

theorem textbookLeaves_of_open (t : OpenTextbookLeaves) : TextbookLeaves where
  t5 := t.t5
  t6 := t.t6
  t7 := t.t7
  t8 := t.t8
  t9 := t.t9
  t10 := t.t10
  t11a := t.t11a
  t11b := t.t11b
  t14a := t.t14a
  t14b := t.t14b
  t15 := t15_proved
  t16a := t16a_proved
  t17 := t17_proved
  t18 := t18_proved
  t23 := t.t23
  t24 := t.t24
  t25 := t25_proved
  t26 := t.t26
  t27 := t.t27
  t31 := t31_proved
  t33 := t.t33
  t34 := t.t34
  t35 := t.t35
  x1 := t.x1
  t41 := t.t41

/-- **G0 with only the open leaves** (leaf-fold, 2026-11-13; no `sorry`, standard axioms).
`SixContactMin` follows from the open leaves and the ten glue pieces.

Open research-level leaves (all 23 of the note's R1-R22 and H5, in 26 fields; none is proved):
R1(a,c,d)+R2+R5-on-`X₆` (`r1r2`), R1(b) (`r1an`, opaque), R1(d) reciprocity (`r1rec`), R3, R4,
R5(ii) (`r5`), R5(i) (`r5count`), R6, R7(a), R7(b), R8, R9(a), R9(b), **R10 corrected**
(`PkgI4.DeRhamComparisonHT`), R11+R12 (`r11r12`), R13, **R14 corrected** (`G0Galois.R14Det`), R15,
R16, R17 (opaque), R18, R19, R20, R21, R22, H5.

Open textbook leaves (26 fields; `x1` bundles T36-T40): T1, T3, T4, T5, T6, T7, T8,
T9, T10, T11(a), T11(b), T14(a′), T14(b′), T16(b), T23, T24, T26, T27, T28, T29(a), T29(b), T33,
T34, T35, T36-T40 (`x1`), T41.

Proved (no longer hypotheses): T2 (`t2_proved`), T13, T15 (`t15_proved`), T16(a)
(`t16a_proved`), T17 (`t17_proved`), T18 (`t18_proved`), T19, T20 and T21 in global form
(`t20_proved`, `t21_proved`), T22, T25 (`t25_proved`), T30, T31 (`t31_proved`). -/
theorem sixContactMin_of_open (r : OpenResearchLeaves) (t : OpenTextbookLeaves)
    (gp : GluePieces) : ZInQ.SixContactMin :=
  sixContactMin_of_leaves (researchLeaves_of_open r) (textbookLeaves_of_open t) gp

end HSyn

end

/-! ### Verbatim checks: each closed field against its Contrib Prop (leaf-fold)

`HDec.X` is this file's statement, `X` the one the Contrib theorem proves (in
`ZInQKernel/HDecomp/`). -/

-- op-dedupe: `HDec.PkgI6.LocalH2CardC` removed; the bundle field is the kernel's `PkgI6.LocalH2CardC` itself
-- op-dedupe: `HDec.PkgI6.LocalKroneckerWeber` removed; the bundle field is the kernel's `PkgI6.LocalKroneckerWeber` itself
-- op-dedupe: `HDec.TSkolemKW.KW.KroneckerWeberCyclic` removed; the bundle field is the kernel's `TSkolemKW.KW.KroneckerWeberCyclic` itself
-- op-dedupe: `HDec.PkgI6.ChebotarevExists` removed; the bundle field is the kernel's `PkgI6.ChebotarevExists` itself
-- op-dedupe: `HDec.GlueConductor.HilbertDifferentFormula` removed; the bundle field is the kernel's `GlueConductor.HilbertDifferentFormula` itself
-- op-dedupe: `HDec.GlueConductor.SerreDifferentBound` removed; the bundle field is the kernel's `GlueConductor.SerreDifferentBound` itself
-- op-dedupe: `HDec.PkgI4.NewformOfEigenform` removed; the bundle field is the kernel's `PkgI4.NewformOfEigenform` itself
-- op-dedupe: `HDec.GlueDescent.B2Q.LeafSqrtCrit` removed; the bundle field is the kernel's `GlueDescent.B2Q.LeafSqrtCrit` itself
-- op-dedupe: `HDec.GlueDescent.B2Q.LeafUnramified` removed; the bundle field is the kernel's `GlueDescent.B2Q.LeafUnramified` itself
-- op-dedupe: `HDec.PkgI6.BrauerHasse2C` removed; the bundle field is the kernel's `PkgI6.BrauerHasse2C` itself
-- op-dedupe: `HDec.PkgI6.BrauerReciprocity2C` removed; the bundle field is the kernel's `PkgI6.BrauerReciprocity2C` itself
-- op-dedupe: `HDec.PkgI2.AbhyankarDVR` removed; the bundle field is the kernel's `PkgI2.AbhyankarDVR` itself
#hdec_same_as HDec.HSyn.FrobeniusDense ZInQ.Contrib.ChebFD.HSyn.FrobeniusDense ZInQ.Contrib.ChebFD
#hdec_same_as HDec.HSyn.KroneckerWeber ZInQ.Contrib.KroneckerWeber.HSynKroneckerWeber
  ZInQ.Contrib.KroneckerWeber

#print axioms HSyn.weight_match
#print axioms PkgI2.inertiaTrivial_of_goodReduction
#print axioms PkgI2.D2_fixed_of_raynaud
#print axioms GlueConductor.D1_genuine
#print axioms GlueConductor.level_le
#print axioms GlueConductor.fourth_pow_mem
#print axioms HSyn.sixContactMin_of_glueOutputs
#print axioms PkgI1.f1_algebra
#print axioms PkgI1.equiv_of_lyVec
#print axioms PkgI3.exists_hom_ne_zero_of_equivariant
#print axioms PkgI3.finrank_equivEnd
#print axioms PkgI6.eq_of_same_finite_support
#print axioms GlueAssembly.twist_finite
#print axioms GlueAssembly.index_Gamma1_le
#print axioms GlueAssembly.mulHeight_le_mulHeightL2
#print axioms GlueAssembly.invariants_ne_bot_of_baseChange
#print axioms GlueDescent.B3Q.b3_degree_le_QM
#print axioms GlueRepo.PR.inertia_orders_eq_one_iff
#print axioms GlueRepo.PR.fibre_free
#print axioms HSyn.sq_principalUnits_proved
#print axioms HSyn.sixContactMin_of_leaves
-- hsyn-fix: theorems adopted from rv-a6-route, glue-I6-rest and glue-I3-linalg
#print axioms PkgI2.goodReduction_of_QM_rational3
#print axioms PkgI6.artinConductor_le_of_upper
#print axioms PkgI6.sq_principalUnits
#print axioms PkgI3.C2_absolutelyIrreducible
#print axioms PkgI3.E1_exists_hom_ne_zero
#print axioms GlueI3.equivariantDescent
#print axioms GlueI3.absolutelyIrreducible_of_finrank_commOf_prod_le_four
-- hsyn-fix: further theorems the note calls proved (rv-hsyn §B checked them in a copy)
#print axioms PkgI1.gram_det
#print axioms PkgI1.cm4
#print axioms PkgI1.cm24
#print axioms PkgI1.G6_sub_F2
#print axioms PkgI1.Ju_ne_branch
#print axioms PkgI1.elkies_t
#print axioms PkgI1.elkies_t_sub_one
#print axioms PkgI1.thetaRatio_invariant
#print axioms GlueAssembly.logHeight_Phi_le
#print axioms GlueAssembly.transfer_of_level
#print axioms GlueAssembly.weight_match_coh
#print axioms GlueAssembly.sixContactMinAt_of_glueOutputs
#print axioms GlueAssembly.pazuki_numerics
#print axioms PkgI3.range_tateHomZl_subset
#print axioms GlueDescent.B2Q.b2_of_leaves
#print axioms GlueConductor.exists_sq_eq_one_add
#print axioms PkgI6.cob_of_same_finite_support
-- hsyn-fold: theorems adopted from glue-a6-alg, glue-c10 and glue-d1-local
#print axioms GlueA6Alg.Alg.core
#print axioms GlueA6Alg.Alg.exists_valuationSubring_comap_eq
#print axioms PkgI2.quatUnipotentTrivial
#print axioms PkgI2.goodReduction_of_QM_rational3_of_alg
#print axioms PkgI2.goodReduction_of_QM_rational3'
#print axioms PkgI3.trace_indep_of_ell
#print axioms PkgI3.trace_eq_trace_of_ell
#print axioms GlueC10.iso_of_trace_eq_frob_finite
#print axioms GlueC10.frobDense_of_chebotarev
#print axioms GlueC10.eq_of_eq_on_frob
#print axioms GlueC10.iso_of_trace_eq_on_frob
#print axioms GlueC10.iso_three_of_five
#print axioms GlueC10.semisimple_of_le
#print axioms GlueC10.trace_half
#print axioms GlueC10.frobLift
#print axioms GlueC10.frobDense
#print axioms GlueC10.c10
#print axioms GlueD1Local.ramificationIdx_le_factorial_local
#print axioms GlueD1Local.D1_local
#print axioms GlueD1Local.index_localSub
#print axioms GlueD1Local.D1_local'
#print axioms GlueD1Local.ramificationIdx_le_factorial_of_unique
#print axioms GlueD1Local.D1_krasner
#print axioms GlueD1Local.D1_krasner'
-- hsyn-fold: obj-bridge
#print axioms ObjBridge.homEquiv
#print axioms ObjBridge.endMulEquiv
#print axioms ObjBridge.homRankBound_iff
#print axioms ObjBridge.charpolyIndependentOfEll_iff
#print axioms ObjBridge.neronOggShafarevich_iff
#print axioms ObjBridge.i3Leaves_iff
#print axioms ObjBridge.charPolyIndepOfEll_iff_grp
#print axioms ObjBridge.exists_hom_ne_one_of_equivariant
#print axioms ObjBridge.finrank_equivEnd
#print axioms ObjBridge.ofGrp_baseChange
#print axioms ObjBridge.homT_comp
#print axioms ObjBridge.homT_id
-- leaf-adopt: theorems adopted from glue-t32a, leaf-qm-fp, leaf-modcurves, def-faltings, and new
#print axioms HSyn.t32a_glue
#print axioms HSyn.t32b_glue
#print axioms HSyn.leafB3a_glue
#print axioms GlueB3Unram.unramified_outside_noLeaf
#print axioms LeafQM.AV.R1fp_of_R1R2fp
#print axioms LeafQM.AV.R5fpWeak_of_R5fp
#print axioms LeafQM.AV.conj_iso_of_rational
#print axioms LeafQM.AV.cm_of_val
#print axioms LeafQM.AV.Level3.onto
#print axioms LeafQM.AV.Level3.torsor
#print axioms LeafQM.AV.QML3.goodReduction
#print axioms LeafQM.AV.residue_unramified_over_branch
#print axioms LeafQM.AV.exists_fibre_object
#print axioms LeafQM.AV.fibre_conjugates_isomorphic
#print axioms LeafQM.AV.leaves_on_one_witness
#print axioms LeafModCurves.genus_Gamma1_le
#print axioms LeafModCurves.IsJacobian.unique
#print axioms LeafModCurves.dim_J1_le
#print axioms LeafModCurves.exists_J1_dim_le
#print axioms LeafModCurves.exists_J1_quotient
#print axioms LeafModCurves.rhoF_traces
#print axioms LeafModCurves.g13_constituent
#print axioms LeafModCurves.rhoF_attached
#print axioms ZInQ.DefFaltings.stableFaltingsHeight
#print axioms ZInQ.DefFaltings.MetrizedModel.modelHeight_eq_of_model_eq
#print axioms ZInQ.DefFaltings.stableFaltingsHeight_eq_iInf_height
#print axioms ZInQ.DefFaltings.stableFaltingsHeightDeligne_eq
#print axioms ZInQ.DefFaltings.stableFaltingsHeight_ne_bot_of_R21
#print axioms LeafAdopt.r2X6PropsIff_of
#print axioms LeafAdopt.cmExists_of_iff
#print axioms LeafAdopt.R1R2fp_of_rep
#print axioms LeafAdopt.R5fp_iff_R5fpStrong
#print axioms LeafAdopt.abVarEquiv_dim
#print axioms ZInQ.LeafPush2.stableFaltingsHeight
#print axioms ZInQ.LeafPush2.R18_real
#print axioms ZInQ.LeafPush2.javanpeykarBound_pos
#print axioms ZInQ.LeafPush2.javanpeykarBound_mono
#print axioms ZInQ.LeafPush2.R22_plus3
#print axioms ZInQ.LeafPush2.isSiegel_I
#print axioms ZInQ.LeafPush2.linYangTuple_onQMLocus
#print axioms ZInQ.LeafPush2.onQMLocus_of_linYangTuple
#print axioms ZInQ.LeafPush2.linYang_j_eq
#print axioms ZInQ.LeafPush2.R03_of_algClosed
#print axioms ZInQ.LeafPush2.exists_isComplexConj
#print axioms ZInQ.LeafPush2.T10_groupIso
#print axioms ZInQ.LeafPush2.R03_LinYang
#print axioms ZInQ.LeafPush2.R22_Pazuki
#print axioms ZInQ.LeafPush2.R18_Javanpeykar
#print axioms HSyn.isComplexConj_leafPush2_iff
-- leaf-adopt3: g0-split's proof of glueOutputs_of_leaves
#print axioms HSyn.glueOutputs_of_leaves
#print axioms HSyn.G0Split.transfer_core
#print axioms HSyn.G0Split.javanpeykarJ1
#print axioms HSyn.G0Split.thetaPazuki
#print axioms HSyn.G0Split.isogenousProduct
#print axioms HSyn.G0Split.semisimpleBaseChange
-- leaf-adopt3: wave-25 folds and the new bundle consequences
#print axioms HSyn.G0Split.r18Concrete_of
#print axioms HSyn.G0Split.r22Concrete_of
#print axioms HSyn.G0Split.heightAdditivity_of_h5neron
#print axioms HSyn.G0Split.hodgeLatticeTheorem_of_dimBaseChange
#print axioms HSyn.t13_proved
#print axioms HSyn.t19_proved
#print axioms HSyn.t22a_proved
#print axioms HSyn.t22b_proved
#print axioms HSyn.t20_local_proved
#print axioms HSyn.t21_local_proved
#print axioms HSyn.TextbookLeaves.frobeniusDense
#print axioms HSyn.TextbookLeaves.leafSqrtCrit
#print axioms HSyn.TextbookLeaves.t10_groupIso
#print axioms HSyn.TextbookLeaves.x1ModelExists
#print axioms HSyn.TextbookLeaves.belyiX1
#print axioms HSyn.TextbookLeaves.exists_J1
#print axioms HSyn.modCurveLeaves_of_bundles
#print axioms TSkolemKW.glueDescent_leafSkolemNoether
#print axioms TSkolemKW.pkgI6_brauerNesbittChar0
#print axioms TSkolemKW.hsyn_dirichletCharacter_of_kroneckerWeberCyclic
#print axioms TSkolemKW.C10.c10_of_chebotarev
#print axioms Pi0X6.leafAdopt_r1pi0Props_of_bundle
#print axioms Pi0X6.leafAdopt_r1pi0Props_of_X6Props
#print axioms ZInQ.DefFaltings.HodgeLattice.hodgeLatticeTheorem_of_tangent
#print axioms ZInQ.DefFaltings.HodgeLattice.hodgeLatticeTheorem_of_abVarFacts
#print axioms ZInQ.H5Neron.stableFaltingsHeight_eq_neron_all
#print axioms ZInQ.H5Neron.stableFaltingsHeight_add_le'
#print axioms X1Belyi.belyiX1_of_leaves
#print axioms X1Belyi.x1ModelExists_of_leaves
#print axioms E1Sub.vSurjOfSurjective
#print axioms C9Rhof.rhoF_semisimple
#print axioms C9Rhof.rhoF_continuous
#print axioms C9Rhof.c9
#print axioms C9Rhof.c9_R14
#print axioms C9Rhof.c9_r5
#print axioms C9Rhof.c10_via_c9
#print axioms C9Rhof.c9_hsyn
#print axioms HSyn.G0Split.x1BelyiOnModel_of_belyiX1
-- pin-apply: qm-pin comparison
#print axioms LeafQM.AV.Pin.r1fpPin_relabel_iff
#print axioms LeafQM.AV.Pin.r1fpPin_aut
#print axioms LeafQM.AV.Pin.r2fp_aut
#print axioms LeafQM.AV.Pin.phi_part
#print axioms LeafQM.AV.Pin.relabel_is_morphism
#print axioms LeafQM.AV.Pin.sameTripleMor_of_mobius
#print axioms LeafQM.AV.Pin.pointwise_of_witness_mor
#print axioms LeafQM.AV.Pin.cm_objects_of_R1R2fp
#print axioms HSyn.G0Split.fibreSimple_iff_at
#print axioms HSyn.G0Split.thetaPointOfFibre_iff_at
#print axioms HSyn.G0Split.modularConstituent_iff_at
#print axioms HSyn.G0Split.qmPieces_iff_w
#print axioms HSyn.gluePieces_of_pin
#print axioms HSyn.gluePiecesPin_of
#print axioms HSyn.sixContactMin_of_leaves_pin

-- leaf-fold: the closed leaves, the repairs and the open bundles
#print axioms HDec.TBrauerPurity.abhyankarDVR
#print axioms HSyn.t2_proved
#print axioms HSyn.t15_proved
#print axioms HSyn.t16a_proved
#print axioms HSyn.t17_proved
#print axioms HSyn.kroneckerWeber_proved
#print axioms HSyn.t18_proved
#print axioms HSyn.frobeniusDense_proved
#print axioms HSyn.t20_proved
#print axioms HSyn.t21_proved
#print axioms HSyn.t25_proved
#print axioms HSyn.t30_proved
#print axioms HSyn.t30_proved'
#print axioms HSyn.t31_proved
#print axioms HSyn.t14_of_kummerIndexBound
#print axioms HSyn.eigenformRepExists_of_r14Det
#print axioms PkgI4.deRhamComparisonHT_iff
#print axioms HSyn.researchLeaves_of_open
#print axioms HSyn.textbookLeaves_of_open
#print axioms HSyn.sixContactMin_of_open

end HDec
