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
