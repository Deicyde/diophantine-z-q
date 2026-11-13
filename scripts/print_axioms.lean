import ZInQKernel

/-!
Prints the axioms of the main theorems, their variants, and the theorems that replace former
hypotheses. From the repository root, after `lake build ZInQKernel`:

    lake env lean scripts/print_axioms.lean

Each declaration should depend on `[propext, Classical.choice, Quot.sound]` only.
-/

-- The main theorems: two hypotheses (`MainGreenTao.lean`) and three hypotheses (`Main.lean`).
#print axioms ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRank
#print axioms ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankSel
#print axioms ZInQ.exists_bounded_integer_polynomial_defining_integers_of

-- Variants.
#print axioms ZInQ.exists_bounded_integer_polynomial_defining_integers_of_goodPrimeDensity
#print axioms ZInQ.exists_bounded_integer_polynomial_defining_integers_of_certifiedRankSel_goodPrimeDensity
#print axioms ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactEstimate
#print axioms ZInQ.exists_bounded_integer_polynomial_defining_integers_of_twoSlopePattern
#print axioms ZInQ.exists_bounded_integer_polynomial_defining_integers_of_poleCompleteness
#print axioms ZInQ.exists_bounded_integer_polynomial_defining_integers_of_addMulBound
#print axioms ZInQ.exists_bounded_integer_polynomial_defining_integers_of_nodeCheck
#print axioms ZInQ.exists_bounded_integer_polynomial_defining_integers_of_certifiedRankSel
#print axioms ZInQ.exists_bounded_integer_polynomial_defining_integers_of_goodPrimeAP
#print axioms ZInQ.exists_bounded_integer_polynomial_defining_integers_of_greenTaoDense
#print axioms ZInQ.exists_bounded_integer_polynomial_defining_integers_of_certifiedRankSel_greenTaoDense
#print axioms ZInQ.exists_bounded_integer_polynomial_defining_integers_of_certifiedRank5b
#print axioms ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRank5b
#print axioms ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZ
#print axioms ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZCl
#print axioms ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankRk
#print axioms ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZRk
#print axioms ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZClRk
#print axioms ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankDLRk
#print axioms ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankDLAdmRk
#print axioms ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankInf
#print axioms ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZInf
#print axioms ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZClInf
#print axioms ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankDLInf

-- Variants with the literature forms of the hypotheses (`MainLiterature.lean`).
#print axioms ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_tyzThm35ReadingA_heckeContinuation_functionalEquation5_grossZagier
#print axioms ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_tyzRow5b_functionalEquation5_grossZagier
#print axioms ZInQ.exists_bounded_integer_polynomial_defining_integers_of_jHeightBound_certifiedRankTYZClRk
#print axioms ZInQ.exists_bounded_integer_polynomial_defining_integers_of_jHeightBound_tyzRow5b_functionalEquation5_grossZagier
#print axioms ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_tyzInputs_functionalEquation5_grossZagier

-- Theorems that replace former hypotheses, and the vendored Green–Tao theorem.
#print axioms ZInQ.greenTaoDense
#print axioms ZInQ.Density.goodPrimeDensity
#print axioms ZInQ.greenTao_primes
#print axioms Submission.green_tao
#print axioms ZInQ.RouteK.Selmer.certifiedRank_of_certifiedRankSel
#print axioms ZInQ.RouteK.Rank5b.certifiedRankSel_of_certifiedRank5b
#print axioms ZInQ.RouteK.Rank5b.det_M5b_eq_T5b
#print axioms ZInQ.RouteK.Rank5b.certifiedRank5b_of_certifiedRankTYZ
#print axioms ZInQ.RouteK.Rank5b.certifiedRankTYZ_iff_of_redeiFormula
#print axioms ZInQ.RouteK.Redei.oddGClStatement
#print axioms ZInQ.RouteK.Redei.redeiFormula
#print axioms ZInQ.RouteK.Redei.certifiedRankTYZ_iff'
#print axioms ZInQ.RouteK.Redei.certifiedRankTYZRk_of_certifiedRankTYZClRk
#print axioms ZInQ.RouteK.Rank.fg_points
#print axioms ZInQ.RouteK.Rank.twoTorsion_card
#print axioms ZInQ.RouteK.Rank.loc_of_mem_sel2_of_infinite_order
#print axioms ZInQ.RouteK.Rank.certifiedRank_of_certifiedRankRk'
#print axioms ZInQ.RouteK.Rank.certifiedRankTYZ_of_certifiedRankTYZRk'
#print axioms ZInQ.RouteK.Rank.certifiedRankTYZCl_of_certifiedRankTYZClRk'
#print axioms ZInQ.RouteK.Rank.certifiedRankRk_of_certifiedRankTYZRk
#print axioms ZInQ.RouteK.Rank.sel_of_selmerCertified
#print axioms ZInQ.RouteK.Rank.certifiedRankDLRk_of_certifiedRankTYZRk
#print axioms ZInQ.RouteK.Rank.certifiedRankDLRk_of_certifiedRankRk
#print axioms ZInQ.RouteK.Rank.poleCompleteness_of_certifiedRankDLRk
#print axioms ZInQ.RouteK.Rank.poleCompleteness_of_certifiedRankDLAdmRk
#print axioms ZInQ.RouteK.Rank.certifiedRankDLAdmRk_of_certifiedRankDLRk
#print axioms ZInQ.RouteK.Rank.exists_infinite_order_iff_infinitelyManyPoints
#print axioms ZInQ.RouteK.Rank.certifiedRankInf_iff_certifiedRankRk
#print axioms ZInQ.RouteK.Rank.certifiedRankTYZInf_iff_certifiedRankTYZRk
#print axioms ZInQ.RouteK.Rank.certifiedRankTYZClInf_iff_certifiedRankTYZClRk
#print axioms ZInQ.RouteK.Rank.certifiedRankDLInf_iff_certifiedRankDLRk
#print axioms ZInQ.poleCompleteness_of_certifiedRank
#print axioms ZInQ.mordellWeilE
#print axioms ZInQ.catalogueBound8

-- Reductions of the hypotheses to their literature forms (`Hypotheses/CR3Literature.lean`,
-- `Hypotheses/JHeight.lean`).
#print axioms ZInQ.Literature.certifiedRankTYZClRk_of_literature
#print axioms ZInQ.Literature.rootNumberVanishing_of_functionalEquation
#print axioms ZInQ.Literature.tyzRow5b_of_readingA
#print axioms ZInQ.Literature.IsLContinuation.eq
#print axioms ZInQ.JHeight.sixContactMin_of_jHeightBound

-- Mathlib's L-function of `C_d` (`RouteK/Rank/LFunctionCd.lean`).
#print axioms ZInQ.Literature.isMinimal_cdLocal
#print axioms ZInQ.Literature.hasGoodReduction_cdLocal
#print axioms ZInQ.Literature.hasAdditiveReduction_cdLocal
#print axioms ZInQ.Literature.localPolynomial_cdLocal_of_not_dvd
#print axioms ZInQ.Literature.localPolynomial_cdLocal_of_dvd
#print axioms ZInQ.Literature.LFunction_cd_apply_prime
#print axioms ZInQ.Literature.LFunction_cd_apply_prime_eq_sub_card
#print axioms ZInQ.Literature.LFunction_cd_apply_prime_pow
#print axioms ZInQ.Literature.LFunction_cd_apply
#print axioms ZInQ.Literature.LSeries_cd_eq
#print axioms ZInQ.Literature.LSeries_cd_eq_of_mod_eight

-- Proposition N from the Tian–Yuan–Zhang inputs (`Hypotheses/TYZInputs.lean`, `RouteK/PropN.lean`).
#print axioms ZInQ.PropN.tyzRow5b_of_tyzInputs
#print axioms ZInQ.PropN.tyzThm35ReadingA_of_tyzInputs
#print axioms ZInQ.PropN.lemmaN1_core
#print axioms ZInQ.PropN.lemmaN2
#print axioms ZInQ.PropN.finalStep
#print axioms ZInQ.PropN.matching
#print axioms ZInQ.PropN.Witness.genusData_nonempty
#print axioms ZInQ.PropN.Witness.genusData_nonempty_iff_parities
#print axioms ZInQ.PropN.Witness.genusData_nonempty_of_parities
#print axioms ZInQ.PropN.Witness.Pw_congr

/-! The glue of the H decomposition (`docs/research/h-decomposition.md`), adopted by task
hdec-adopt into `ZInQKernel/HDecomp/`; the literature leaves are hypotheses of these theorems. -/
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
#print axioms ObjBridge.pkgI2_homRankBound_of_pkgI3_homFreeFinite
#print axioms GlueAssembly.sixContactMinAt_of_glueOutputs
#print axioms GlueAssembly.jHeightBound_of_glueOutputs
#print axioms GlueAssembly.sixContactMinAt_of_jHeightBound
#print axioms GlueAssembly.logHeight₁_algebraMap_rat
#print axioms GlueAssembly.logHeight_Phi_le
#print axioms GlueDescent.MatrixUnits2.splitEquiv_intertwines
#print axioms GlueDescent.rho_map_mul
#print axioms GlueDescent.sign_normalization
#print axioms GlueDescent.commute_adjoin
#print axioms GlueDescent.B6_inner
#print axioms GlueDescent.B6_isSimpleRing
#print axioms GlueDescent.B6_commute_i_j
#print axioms GlueDescent.exists_chi
#print axioms GlueDescent.B2Q.b2_of_leaves
#print axioms GlueDescent.B3Q.b3_of_leaves
#print axioms GlueDescent.B3Q.b3_degree_le_QM
#print axioms GlueConductor.upper_break_le
#print axioms GlueConductor.D1_genuine
#print axioms GlueConductor.card_GL4_F5
#print axioms GlueConductor.exists_fourth_root
#print axioms GlueConductor.fourth_pow_mem
#print axioms GlueConductor.level_le
#print axioms PkgI6.eq_of_same_finite_support
#print axioms PkgI6.skolemNoether_aut
#print axioms PkgI6.lowerRam_tower
#print axioms PkgI6.cob_of_same_finite_support
#print axioms PkgI6.sq_principalUnits
#print axioms PkgI6.finrank_splittingField_le_factorial
#print axioms PkgI6.ramificationIdx_le_factorial
#print axioms PkgI6.upperRam_phi_nat
#print axioms PkgI6.sum_hInt_le
#print axioms PkgI6.artinConductor_le_of_upper
#print axioms GlueI6Rest.inflation_two_eq_coboundary
#print axioms GlueI6Rest.exists_half_iff
#print axioms GlueD1Local.ramificationIdx_le_factorial_local
#print axioms GlueD1Local.D1_local
#print axioms GlueD1Local.index_localSub
#print axioms GlueD1Local.D1_local'
#print axioms GlueD1Local.ramificationIdx_le_factorial_of_unique
#print axioms GlueD1Local.D1_krasner
#print axioms GlueD1Local.D1_krasner'
#print axioms GlueA6Alg.quatUnipotentTrivial
#print axioms GlueA6Alg.goodReduction_of_QM_rational3
#print axioms GlueA6Alg.goodReduction_of_QM_rational3'
#print axioms GlueA6Alg.exists_valuationSubring_algebraicClosure
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
#print axioms PkgI3.trace_indep_of_ell
#print axioms PkgI3.trace_eq_trace_of_ell
#print axioms GlueRepo.A1.trd_mul_ros_pos
#print axioms GlueRepo.A1.det_gram_E
#print axioms GlueRepo.A1.E_ros
#print axioms GlueRepo.A1.det_trace_form
#print axioms GlueRepo.A1.half_one_add_mem
#print axioms GlueRepo.A1.no_trd_zero_nrd_two
#print axioms GlueRepo.A1.nrd_mul
#print axioms GlueRepo.A1.card_units_mod3
#print axioms GlueRepo.A1.module_eq_zero
#print axioms GlueRepo.Numerics.splitting_degree_le
#print axioms GlueRepo.Numerics.a8_field
#print axioms GlueRepo.PR.inertia_trivial_iff_not_dvd
#print axioms GlueRepo.PR.J_ne_branch
#print axioms GlueRepo.PR.t_sub_one
#print axioms GlueRepo.PR.fibre_free
#print axioms GlueRepo.PR.inertia_orders_eq_one_iff
#print axioms GlueRepo.TorsionFree.card_le_three_pow
#print axioms GlueRepo.TorsionFree.padic_subgroup_trivial
