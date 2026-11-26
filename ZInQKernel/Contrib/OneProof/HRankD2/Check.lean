import ZInQKernel.Contrib.OneProof.HRankD2.LSeriesHasseWeil
import ZInQKernel.Contrib.OneProof.HRankD2.EulerProduct
import ZInQKernel.Contrib.OneProof.HRankD2.NodeSlopes

/-!
# Kernel dependencies of the D2 bridge

`#print axioms` for every theorem of `HRankD2`. Each should depend only on `propext`,
`Classical.choice` and `Quot.sound`.
-/

#print axioms ZInQ.Manuscript.RankModel.hwEulerPoly_coeff_zero
#print axioms ZInQ.Manuscript.RankModel.map_tangentPolynomial'
#print axioms ZInQ.Manuscript.RankModel.splits_tangentPolynomial_map_ringEquiv
#print axioms ZInQ.Manuscript.RankModel.localData_of_minimal_change'
#print axioms ZInQ.Manuscript.RankModel.localPolynomial_of_hasMultiplicativeReduction
#print axioms ZInQ.Manuscript.RankModel.baseChange_baseChange_eq
#print axioms ZInQ.Manuscript.RankModel.baseChange_completion_Δ
#print axioms ZInQ.Manuscript.RankModel.baseChange_completion_c₄
#print axioms ZInQ.Manuscript.RankModel.baseChange_completion_Δ_ne_zero
#print axioms ZInQ.Manuscript.RankModel.valuation_intCast_lt_one_iff
#print axioms ZInQ.Manuscript.RankModel.valuation_intCast_eq_one_iff
#print axioms ZInQ.Manuscript.RankModel.integralModel_completion_eq
#print axioms ZInQ.Manuscript.RankModel.reduction_completion_map
#print axioms ZInQ.Manuscript.RankModel.localPolynomial_eq_hwEulerPoly
#print axioms ZInQ.Manuscript.RankModel.LFunction_apply_prime_pow_of_localPolynomial
#print axioms ZInQ.Manuscript.RankModel.LFunction_apply_eq_hwCoeff
#print axioms ZInQ.Manuscript.RankModel.LSeries_eq_hasseWeil
#print axioms ZInQ.Manuscript.RankModel.LSeries_eq_hasseWeil_of_isGlobalMinimalQ
#print axioms ZInQ.Manuscript.RankModel.hwLocalFactor_good
#print axioms ZInQ.Manuscript.RankModel.hwLocalFactor_split
#print axioms ZInQ.Manuscript.RankModel.hwLocalFactor_nonsplit
#print axioms ZInQ.Manuscript.RankModel.hwLocalFactor_additive
#print axioms ZInQ.Manuscript.RankModel.tsum_invOfUnit_eq_inv
#print axioms ZInQ.Manuscript.RankModel.hwCoeff_prime_pow
#print axioms ZInQ.Manuscript.RankModel.hasProd_LSeries_hasseWeil
#print axioms ZInQ.Manuscript.RankModel.taylor_of_singular
#print axioms ZInQ.Manuscript.RankModel.c₄_mul_x_of_singular
#print axioms ZInQ.Manuscript.RankModel.tangentPolynomial_eq_of_singular
#print axioms ZInQ.Manuscript.RankModel.degree_nodeSlopePolynomial
#print axioms ZInQ.Manuscript.RankModel.splits_nodeSlopePolynomial_iff
#print axioms ZInQ.Manuscript.RankModel.splits_tangentPolynomial_iff_exists_slope
#print axioms ZInQ.Manuscript.RankModel.c₄_reduction_ne_zero
#print axioms ZInQ.Manuscript.RankModel.hasSplitMultiplicativeReduction_iff_slope
#print axioms ZInQ.Manuscript.RankModel.hwSplit_iff_exists_slope
