/-
Copyright 2026 Anthropic, PBC. Released under Apache License 2.0.
Source: https://github.com/anthropics/fermats-last-theorem
Revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.lean; source lines 5757-6257.
Modification notice (CloudB3 Worker16 curve support, 2026-11-16):
Factored at balanced source section boundaries. Relocated imports with the canonical main-port reuse map; expanded P2M
namespace/open/export command helpers to ordinary Lean commands, removed metadata
reactivation commands, and resolved metadata aliases directly. Expanded local notation
literally. Promoted source-private helpers into the original P2MW module namespace
so proofs can cross factoring-file boundaries without new root-name collisions.
Kept mathematical proof bodies and all public solution signatures; no new mathematical
assumptions. Lean 4.35 compatibility edits are recorded in the accompanying manifest.
Complete original LICENSE, NOTICE, and attribution are in this vendor root; a local
copy is supplied in RRSplit for independent distribution of this support patch.
-/
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.RRSplit.functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed_Part04

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 6400000
set_option maxHeartbeats 12800000

namespace P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed

-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.ord_nonneg_of_mem :=
  @_root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.ord_nonneg_of_mem
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.mem_of_ord_nonneg :=
  @_root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.mem_of_ord_nonneg
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.mem_iff_ord_nonneg :=
  @_root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.mem_iff_ord_nonneg
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.comap_algebraMap_ne_top :=
  @_root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.comap_algebraMap_ne_top
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.exists_ord_algebraMap_pos :=
  @_root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.exists_ord_algebraMap_pos
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.uniformizerSubring :=
  @_root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.uniformizerSubring
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.coe_uniformizerSubring :=
  @_root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.coe_uniformizerSubring
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.irreducible_uniformizerSubring :=
  @_root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.irreducible_uniformizerSubring
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.uniformizerSubring_mem_maximalIdeal :=
  @_root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.uniformizerSubring_mem_maximalIdeal
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.uniformizer_mem :=
  @_root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.uniformizer_mem
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.simplePoleSubmodule :=
  @_root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.simplePoleSubmodule
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.mem_simplePoleSubmodule_of_mem :=
  @_root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.mem_simplePoleSubmodule_of_mem
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.simplePoleMulUniformizer :=
  @_root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.simplePoleMulUniformizer
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.simplePoleResidueAux :=
  @_root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.simplePoleResidueAux
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.simplePoleResidueAux_eq_zero_of_mem :=
  @_root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.simplePoleResidueAux_eq_zero_of_mem
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.localResidueExtend :=
  @_root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.localResidueExtend
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.localResidueExtend_apply_of_mem :=
  @_root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.localResidueExtend_apply_of_mem
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.isUnit_mk_of_ord_eq_zero :=
  @_root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.isUnit_mk_of_ord_eq_zero
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.residue_ne_zero_of_ord_eq_zero :=
  @_root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.residue_ne_zero_of_ord_eq_zero
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.IsRational :=
  @_root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.IsRational
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.residueInv :=
  @_root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.residueInv
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.algebraMap_residueInv :=
  @_root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.algebraMap_residueInv
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.evalAt :=
  @_root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.evalAt
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.evalAt_of_mem :=
  @_root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.evalAt_of_mem
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.algebraMap_evalAt :=
  @_root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.algebraMap_evalAt
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.evalAt_ne_zero :=
  @_root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.evalAt_ne_zero
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.poleSubmodule :=
  @_root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.poleSubmodule
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.uniformizer_pow_ne_zero :=
  @_root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.uniformizer_pow_ne_zero
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.ord_uniformizer_pow :=
  @_root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.ord_uniformizer_pow
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.poleSubmodule_one :=
  @_root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.poleSubmodule_one
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.mem_poleSubmodule_iff_ord :=
  @_root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.mem_poleSubmodule_iff_ord
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.poleSubmodule_mono :=
  @_root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.poleSubmodule_mono
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.ord_sub_evalAt_pos :=
  @_root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.ord_sub_evalAt_pos
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.isRational_of_deg_eq_one :=
  @_root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.isRational_of_deg_eq_one
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.mk_mem_maximalIdeal_iff :=
  @_root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.mk_mem_maximalIdeal_iff
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.RiemannGenusReachedAt.eq_of_ge :=
  @_root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RiemannGenusReachedAt.eq_of_ge
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.uniformizer_pow_inv_mem_poleSubmodule_self :=
  @_root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.uniformizer_pow_inv_mem_poleSubmodule_self
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.higherPoleMonomial_sum_mem_poleSubmodule :=
  @_root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.higherPoleMonomial_sum_mem_poleSubmodule
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.higherPoleMonomial_coeff_eq_zero_of_mem :=
  @_root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.higherPoleMonomial_coeff_eq_zero_of_mem
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.linearIndependent_higherPoleMonomial_mkQ :=
  @_root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.linearIndependent_higherPoleMonomial_mkQ
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.higherPoleCorrectionAux :=
  @_root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.higherPoleCorrectionAux
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.higherPoleCorrection :=
  @_root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.higherPoleCorrection
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.higherPoleCorrection_apply_of_mem :=
  @_root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.higherPoleCorrection_apply_of_mem
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.higherPoleCorrection_uniformizer_pow_inv :=
  @_root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.higherPoleCorrection_uniformizer_pow_inv
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.canonicalLocalResidueDataKOfExtend :=
  @_root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.canonicalLocalResidueDataKOfExtend
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.exists_trace_residue_ne_zero :=
  @_root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.exists_trace_residue_ne_zero
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.mem_of_isIntegral :=
  @_root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.mem_of_isIntegral
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.mem_of_isIntegral_of_algebraMap_mem :=
  @_root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.mem_of_isIntegral_of_algebraMap_mem
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.mem_of_isIntegral_of_restrict :=
  @_root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.mem_of_isIntegral_of_restrict
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.ord_nonneg_of_isIntegral_of_restrict :=
  @_root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.ord_nonneg_of_isIntegral_of_restrict


section
section
set_option autoImplicit false
noncomputable section
open _root_.Module
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module
open _root_.Polynomial
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Polynomial
open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain
namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic)

open _root_.AlgebraicCurve
namespace RationalFunctionField

export _root_.AlgebraicCurve.RationalFunctionField (algebraMap_mem_ofHeightOneSpectrum)

open _root_.AlgebraicCurve.RationalFunctionField
variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable (F : Type*) [Field F] [Algebra K F] [Algebra (RatFunc K) F]
  [IsScalarTower K (RatFunc K) F]
section LyingOver
variable [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable (RatFunc K) F]
attribute [local instance 0] Place.valuationSubringAlgebra
omit [DecidableEq (RatFunc K)] [Algebra K F] [IsScalarTower K (RatFunc K) F]
  [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable (RatFunc K) F] in

theorem not_isField_integralClosureAt' (v : Place K (RatFunc K)) :
    ¬IsField (Place.integralClosureAt F v) := fun hf =>
  ValuationSubring.not_isField_of_ne_top _ v.ne_top'
    ((Algebra.IsIntegral.isField_iff_isField
      (R := v.toValuationSubring) (S := Place.integralClosureAt F v)
      (Place.algebraMap_integralClosureAt_injective v)).mpr hf)
end LyingOver

end RationalFunctionField

end AlgebraicCurve

end


set_option autoImplicit false
noncomputable section
open _root_.Module
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module
open _root_.Polynomial
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Polynomial
open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain
namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic)

open _root_.AlgebraicCurve
namespace RationalFunctionField

export _root_.AlgebraicCurve.RationalFunctionField (algebraMap_mem_ofHeightOneSpectrum)

open _root_.AlgebraicCurve.RationalFunctionField
variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable (F : Type*) [Field F] [Algebra K F] [Algebra (RatFunc K) F]
  [IsScalarTower K (RatFunc K) F]
section LyingOver
variable [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable (RatFunc K) F]
attribute [local instance 0] Place.valuationSubringAlgebra
omit [DecidableEq (RatFunc K)] in

theorem exists_restrict_eq (v : Place K (RatFunc K)) :
    ∃ w : Place K F, w.restrict (RatFunc K) = v := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (Place.integralClosureAt F v)
  haveI := hM
  exact ⟨Place.placeOfPrime (v := v)
      ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM
        (not_isField_integralClosureAt' K F v)⟩,
    Place.restrict_placeOfPrime _⟩
end LyingOver

end RationalFunctionField

end AlgebraicCurve

end


set_option autoImplicit false
noncomputable section
open _root_.Module
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module
open _root_.Polynomial
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Polynomial
open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain
namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic)

open _root_.AlgebraicCurve
namespace RationalFunctionField

export _root_.AlgebraicCurve.RationalFunctionField (algebraMap_mem_ofHeightOneSpectrum)

open _root_.AlgebraicCurve.RationalFunctionField
variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable (F : Type*) [Field F] [Algebra K F] [Algebra (RatFunc K) F]
  [IsScalarTower K (RatFunc K) F]
section LyingOver
variable [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable (RatFunc K) F]
attribute [local instance 0] Place.valuationSubringAlgebra

theorem nonempty_place_of_ratFunc_tower : Nonempty (Place K F) :=
  (exists_restrict_eq K F (placeInfty K)).nonempty
end LyingOver

end RationalFunctionField

end AlgebraicCurve

end


set_option autoImplicit false
noncomputable section
open _root_.Module
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module
open _root_.Polynomial
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Polynomial
open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain
namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic)

open _root_.AlgebraicCurve
namespace RationalFunctionField

export _root_.AlgebraicCurve.RationalFunctionField (algebraMap_mem_ofHeightOneSpectrum)

open _root_.AlgebraicCurve.RationalFunctionField
variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable (F : Type*) [Field F] [Algebra K F] [Algebra (RatFunc K) F]
  [IsScalarTower K (RatFunc K) F]
omit [DecidableEq (RatFunc K)] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] in

theorem finiteDimensional_lSpace_zero_of_constantsAreBase (hC : ConstantsAreBase K F) :
    FiniteDimensional K (LSpace (0 : Divisor K F)) := by
  rw [show LSpace (0 : Divisor K F) = LinearMap.range (Algebra.linearMap K F) from hC]
  exact LinearMap.finiteDimensional_range _
end RationalFunctionField

end AlgebraicCurve

end


set_option autoImplicit false
noncomputable section
open _root_.Module
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module
open _root_.Polynomial
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Polynomial
open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain
namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic)

open _root_.AlgebraicCurve
namespace RationalFunctionField

export _root_.AlgebraicCurve.RationalFunctionField (algebraMap_mem_ofHeightOneSpectrum)

open _root_.AlgebraicCurve.RationalFunctionField
variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable (F : Type*) [Field F] [Algebra K F] [Algebra (RatFunc K) F]
  [IsScalarTower K (RatFunc K) F]
variable [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable (RatFunc K) F]
variable [IsCurveOver K F]

theorem stichtenothGenusExists (hC : ConstantsAreBase K F) :
    StichtenothGenusExists K F :=
  haveI := nonempty_place_of_ratFunc_tower K F
  haveI := finiteDimensional_lSpace_zero_of_constantsAreBase K F hC
  stichtenothGenusExists_of_ratFunc_tower K F
end RationalFunctionField

end AlgebraicCurve

end


end


end


section
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
noncomputable section
open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve
namespace ModularCurve

open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsLocalRing
section AlgClosedEngine
variable (K F : Type*) [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [DecidableEq (RatFunc K)]
variable [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
variable [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable (RatFunc K) F]
variable [IsAlgClosed K] [IsCurveOver K F]

theorem p0n20_rr_constantsAreBase_of_isAlgClosed : ConstantsAreBase K F := by
  obtain ⟨v⟩ := RationalFunctionField.nonempty_place_of_ratFunc_tower K F
  exact constantsAreBase_of_deg_eq_one v (IsCurveOver.deg_eq_one_of_isAlgClosed v)
end AlgClosedEngine

end ModularCurve

end


end


end


section
section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

set_option linter.unusedSectionVars false

noncomputable section

open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero
open _root_.Module
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsLocalRing
open _root_.Module.IsLocalRing

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve

namespace ModularCurve



section CanonicalProbe

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]

open scoped _root_.Classical _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Classical in

theorem p0n25_wkc_kaehlerResidueTermKFam_single_of_ne
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK) (ω : Ω[F⁄K])
    {v : Place K F} (g : F) {w : Place K F} (hw : w ≠ v) :
    kaehlerResidueTermKFam Rfam ω (Pi.single v g) w = 0 := by
  rw [kaehlerResidueTermKFam_apply, Pi.single_eq_of_ne hw, zero_mul, _root_.map_zero, _root_.map_zero]

theorem p0n25_wkc_localResidueData_res_mul_uniformizer_inv
    {v : Place K F} (R : v.LocalResidueData) (c : v.toValuationSubring) :
    R.res ((c : F) * v.uniformizer⁻¹) = IsLocalRing.residue _ c := by
  have hmul : v.uniformizer * ((c : F) * v.uniformizer⁻¹) = (c : F) := by
    rw [mul_comm (c : F), ← mul_assoc, mul_inv_cancel₀ v.uniformizer_ne_zero, one_mul]
  have hmem : v.uniformizer * ((c : F) * v.uniformizer⁻¹) ∈ v.toValuationSubring := by
    rw [hmul]; exact c.2
  rw [R.res_simplePole _ hmem]
  congr 1
  exact Subtype.ext hmul

variable [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]

open scoped _root_.Classical _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Classical in

theorem p0n25_wkc_weilOfKaehlerK_single
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK)
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) (v : Place K F) (g : F) :
    weilOfKaehlerK Rfam hω (adeleSingle v g)
      = Algebra.trace K v.ResidueField ((Rfam v).res (g * v.differentialCoeff ω)) := by
  rw [weilOfKaehlerK_apply, adeleSingle_coe]
  refine (finsum_eq_single _ v
    fun w hw => p0n25_wkc_kaehlerResidueTermKFam_single_of_ne Rfam ω g hw).trans ?_
  rw [kaehlerResidueTermKFam_apply, Pi.single_eq_same]

theorem p0n25_wkc_weilOfKaehlerK_simplePoleProbe
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK)
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) (v : Place K F) (c : v.toValuationSubring) :
    weilOfKaehlerK Rfam hω (simplePoleProbe hω v c)
      = Algebra.trace K v.ResidueField (IsLocalRing.residue _ c) := by
  unfold simplePoleProbe
  rw [p0n25_wkc_weilOfKaehlerK_single Rfam hω,
    mul_assoc, inv_mul_cancel₀ (v.differentialCoeff_ne_zero hω), mul_one,
    p0n25_wkc_localResidueData_res_mul_uniformizer_inv (Rfam v).toLocalResidueData c]

end CanonicalProbe


section CanonicalNonvanishingMaximality

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]

theorem p0n25_wkc_weilOfKaehlerK_ne_zero [HasSeparableResidue K F] [Nonempty (Place K F)]
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK)
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) : weilOfKaehlerK Rfam hω ≠ 0 := by
  obtain ⟨v⟩ := ‹Nonempty (Place K F)›
  obtain ⟨c, hc⟩ := v.exists_trace_residue_ne_zero
  intro h
  apply hc
  rw [← p0n25_wkc_weilOfKaehlerK_simplePoleProbe Rfam hω v c, h, LinearMap.zero_apply]

theorem p0n25_wkc_trace_eq_zero_of_weilOfKaehlerK_mem
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK)
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) {D : Divisor K F}
    (hD : weilOfKaehlerK Rfam hω ∈ omegaSpace D)
    {v : Place K F} (hDv : canonicalDivisorOf hω v < D v) :
    (Algebra.trace K v.ResidueField : _ →ₗ[K] K) = 0 := by
  ext x
  obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective x
  rw [LinearMap.zero_apply, ← p0n25_wkc_weilOfKaehlerK_simplePoleProbe Rfam hω v c]
  exact omegaSpace_vanishBdd hD (simplePoleProbe_mem_adeleBdd hω v c hDv)

theorem p0n25_wkc_weilOfKaehlerK_omegaSpace_le_canonical [HasSeparableResidue K F]
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK)
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) {D : Divisor K F}
    (hD : weilOfKaehlerK Rfam hω ∈ omegaSpace D) :
    D ≤ canonicalDivisorOf hω := by
  intro v
  rcases le_or_gt (D v) (canonicalDivisorOf hω v) with h | h
  · exact h
  · exact absurd (p0n25_wkc_trace_eq_zero_of_weilOfKaehlerK_mem Rfam hω hD h)
      (HasSeparableResidue.trace_ne_zero v)

end CanonicalNonvanishingMaximality


section CanonicalSupply

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]

theorem p0n25_wkc_exists_weilMax_of_residueTheoremK
    [HasSeparableResidue K F] [Nonempty (Place K F)] [HasPrincipalDivisors K F]
    (hRTK : ResidueTheoremK K F) {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    ∃ φ : Module.Dual K (adeleSpace K F), φ ≠ 0 ∧
      φ ∈ omegaSpace (canonicalDivisorOf hω) ∧
      ∀ D : Divisor K F, φ ∈ omegaSpace D → D ≤ canonicalDivisorOf hω :=
  ⟨weilOfKaehlerK (fun v => v.canonicalLocalResidueDataKOfExtend) hω,
    p0n25_wkc_weilOfKaehlerK_ne_zero _ hω,
    weilOfKaehlerK_mem_omegaSpace_of_residueTheoremK hRTK _ hω,
    fun _ hD => p0n25_wkc_weilOfKaehlerK_omegaSpace_le_canonical _ hω hD⟩

end CanonicalSupply


section MirrorIdentification

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
variable [∀ v : Place K F, v.DCoordGenerates]
variable [Nonempty (Place K F)] [FiniteDimensional K (LSpace (0 : Divisor K F))]

theorem p0n25_wkc_finrank_omegaSpace_eq_ell_of_genusReached_of_weilMax
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    {ω : Ω[F⁄K]} (hω : ω ≠ 0)
    {φ : Module.Dual K (adeleSpace K F)} (hne : φ ≠ 0)
    (hmem : φ ∈ omegaSpace (canonicalDivisorOf hω))
    (hmax : ∀ D : Divisor K F, φ ∈ omegaSpace D → D ≤ canonicalDivisorOf hω)
    (D : Divisor K F) :
    Module.finrank K (omegaSpace (K := K) (F := F) D) = ell (canonicalDivisorOf hω - D) := by
  have hinj := residuePairing_injective (canonicalDivisorOf hω) D hmem hne
  have hsurj := residuePairing_surjective_of_rankOne_max
    (weilDifferentialRankOne_of_genusReached h) hmem hne hmax D
  exact (LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩).finrank_eq.symm

theorem p0n25_wkc_ell_canonicalDivisor_eq_gamma_of_weilMax
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    (hsup : ∀ {ω : Ω[F⁄K]} (hω : ω ≠ 0), ∃ φ : Module.Dual K (adeleSpace K F),
      φ ≠ 0 ∧ φ ∈ omegaSpace (canonicalDivisorOf hω) ∧
      ∀ D : Divisor K F, φ ∈ omegaSpace D → D ≤ canonicalDivisorOf hω)
    (hC : ConstantsAreBase K F) {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    (ell (canonicalDivisorOf hω) : ℤ) = γ := by
  obtain ⟨φ, hne, hmem, hmax⟩ := hsup hω
  have hΩ0 := p0n25_wkc_finrank_omegaSpace_eq_ell_of_genusReached_of_weilMax
    h hω hne hmem hmax 0
  rw [sub_zero] at hΩ0
  have hi0 := (indexOfSpecialty_eq_of_genusReached h 0).2
  rw [← finrank_omegaSpace_eq_indexOfSpecialty, hΩ0, _root_.map_zero,
    ell_zero_eq_one_of_constantsAreBase hC] at hi0
  push_cast at hi0
  linarith

theorem p0n25_wkc_degree_canonicalDivisor_eq_of_weilMax
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    (hsup : ∀ {ω : Ω[F⁄K]} (hω : ω ≠ 0), ∃ φ : Module.Dual K (adeleSpace K F),
      φ ≠ 0 ∧ φ ∈ omegaSpace (canonicalDivisorOf hω) ∧
      ∀ D : Divisor K F, φ ∈ omegaSpace D → D ≤ canonicalDivisorOf hω)
    (hC : ConstantsAreBase K F) {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    Divisor.degree (canonicalDivisorOf hω) = 2 * γ - 2 := by
  obtain ⟨φ, hne, hmem, hmax⟩ := hsup hω
  have hΩW := p0n25_wkc_finrank_omegaSpace_eq_ell_of_genusReached_of_weilMax
    h hω hne hmem hmax (canonicalDivisorOf hω)
  rw [sub_self] at hΩW
  have hiW := (indexOfSpecialty_eq_of_genusReached h (canonicalDivisorOf hω)).2
  rw [← finrank_omegaSpace_eq_indexOfSpecialty, hΩW,
    ell_zero_eq_one_of_constantsAreBase hC] at hiW
  have hℓW := p0n25_wkc_ell_canonicalDivisor_eq_gamma_of_weilMax h hsup hC hω
  push_cast at hiW
  linarith

theorem p0n25_wkc_stichtenothGenus_eq_genus_of_weilMax
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    (hsup : ∀ {ω : Ω[F⁄K]} (hω : ω ≠ 0), ∃ φ : Module.Dual K (adeleSpace K F),
      φ ≠ 0 ∧ φ ∈ omegaSpace (canonicalDivisorOf hω) ∧
      ∀ D : Divisor K F, φ ∈ omegaSpace D → D ≤ canonicalDivisorOf hω)
    (hC : ConstantsAreBase K F) :
    γ = (genus K F : ℤ) := by
  obtain ⟨ω₀, hω₀, hgen⟩ := genus_eq_degree_div (K := K) (F := F)
  have hdeg := p0n25_wkc_degree_canonicalDivisor_eq_of_weilMax h hsup hC hω₀
  have hγ0 := stichtenothGenus_nonneg h hC
  rw [hgen, hdeg]
  have h2 : (2 * γ - 2 + 2).toNat / 2 = γ.toNat := by omega
  rw [h2]
  exact (Int.toNat_of_nonneg hγ0).symm

end MirrorIdentification


section MirrorAssembly

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable (F : Type*) [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F] [Algebra (RatFunc K) F]
  [IsScalarTower K (RatFunc K) F]
variable [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable (RatFunc K) F]
variable [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
variable [∀ v : Place K F, v.DCoordGenerates]

theorem p0n25_wkc_riemannGenusReached_of_weilMax
    (hsup : ∀ {ω : Ω[F⁄K]} (hω : ω ≠ 0), ∃ φ : Module.Dual K (adeleSpace K F),
      φ ≠ 0 ∧ φ ∈ omegaSpace (canonicalDivisorOf hω) ∧
      ∀ D : Divisor K F, φ ∈ omegaSpace D → D ≤ canonicalDivisorOf hω)
    (hC : ConstantsAreBase K F) :
    RiemannGenusReached K F (genus K F) := by
  obtain ⟨hne, hL0, γ, D₀, hD₀⟩ := RationalFunctionField.stichtenothGenusExists K F hC
  haveI := hne
  haveI := hL0
  have hγeq := p0n25_wkc_stichtenothGenus_eq_genus_of_weilMax hD₀ hsup hC
  exact ⟨hne, hL0, D₀, hγeq ▸ hD₀⟩

theorem p0n25_wkc_riemannIndexFormula_of_weilMax
    (hsup : ∀ {ω : Ω[F⁄K]} (hω : ω ≠ 0), ∃ φ : Module.Dual K (adeleSpace K F),
      φ ≠ 0 ∧ φ ∈ omegaSpace (canonicalDivisorOf hω) ∧
      ∀ D : Divisor K F, φ ∈ omegaSpace D → D ≤ canonicalDivisorOf hω)
    (hC : ConstantsAreBase K F) :
    RiemannIndexFormula K F := by
  refine riemannIndexFormula_of_genusReached ?_
  intro _ _
  exact p0n25_wkc_riemannGenusReached_of_weilMax K F hsup hC

theorem p0n25_wkc_weilOmegaEllAgrees_of_weilMax [Nonempty (Place K F)]
    (hRI : RiemannIndexFormula K F)
    (hsup : ∀ {ω : Ω[F⁄K]} (hω : ω ≠ 0), ∃ φ : Module.Dual K (adeleSpace K F),
      φ ≠ 0 ∧ φ ∈ omegaSpace (canonicalDivisorOf hω) ∧
      ∀ D : Divisor K F, φ ∈ omegaSpace D → D ≤ canonicalDivisorOf hω) :
    WeilOmegaEllAgrees K F := by
  have hSurj : ResiduePairingSurjective K F :=
    residuePairingSurjective_of_riemannIndexFormula hRI
  intro _ _ _ ω hω D
  obtain ⟨φ, hne, hmem, hmax⟩ := hsup hω
  have hinj := residuePairing_injective (canonicalDivisorOf hω) D hmem hne
  have hsurj := hSurj (canonicalDivisorOf hω) D hmem hne hmax
  exact_mod_cast (LinearEquiv.ofBijective
    (residuePairing K F (canonicalDivisorOf hω) D hmem) ⟨hinj, hsurj⟩).finrank_eq.symm

theorem p0n25_wkc_functionFieldRiemannRoch_of_weilMax_of_constantsAreBase
    (hsup : ∀ {ω : Ω[F⁄K]} (hω : ω ≠ 0), ∃ φ : Module.Dual K (adeleSpace K F),
      φ ≠ 0 ∧ φ ∈ omegaSpace (canonicalDivisorOf hω) ∧
      ∀ D : Divisor K F, φ ∈ omegaSpace D → D ≤ canonicalDivisorOf hω)
    (hC : ConstantsAreBase K F) :
    FunctionFieldRiemannRoch K F := by
  have hRI : RiemannIndexFormula K F :=
    p0n25_wkc_riemannIndexFormula_of_weilMax K F hsup hC
  haveI := RationalFunctionField.nonempty_place_of_ratFunc_tower K F
  have hΩℓ : WeilOmegaEllAgrees K F :=
    p0n25_wkc_weilOmegaEllAgrees_of_weilMax K F hRI hsup
  have hWDA : WeilDualityAdelic K F := weilDualityAdelic_of_residueRows K F hΩℓ
  have hWD : WeilDuality K F := weilDuality_of_riemannIndex_of_adelic K F hRI hWDA
  intro _ _ _ ω hω D
  exact functionFieldRiemannRoch_of_riemann_and_duality K F hWD hω D

theorem p0n25_wkc_functionFieldRiemannRoch_of_residueTheoremK
    [HasSeparableResidue K F]
    (hRTK : ResidueTheoremK K F) (hC : ConstantsAreBase K F) :
    FunctionFieldRiemannRoch K F := by
  haveI := RationalFunctionField.nonempty_place_of_ratFunc_tower K F
  intro _ _ _ ω hω D
  exact p0n25_wkc_functionFieldRiemannRoch_of_weilMax_of_constantsAreBase K F
    (fun {ω'} hω' => p0n25_wkc_exists_weilMax_of_residueTheoremK hRTK hω') hC hω D

end MirrorAssembly


section TrivialTowerLanding

end TrivialTowerLanding


end ModularCurve


end


end


end


theorem solution
    {K F : Type*} [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)]
    [Field F] [Algebra K F]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    [∀ w : AlgebraicCurve.Place K F, w.DCoordGenerates]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Algebra.IsIntegral (RatFunc K) F] [Module.Finite (RatFunc K) F]
    [AlgebraicCurve.HasLocalResidue K F]
    [∀ w : AlgebraicCurve.Place K F, w.FiniteResidue]
    [Nontrivial Ω[F⁄K]]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.IsCurveOver K (RatFunc K)]
    [∀ u : AlgebraicCurve.Place K (RatFunc K), u.FiniteResidue]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar K F]
    [AlgebraicCurve.HasPrincipalDivisors K F] [Algebra.IsSeparable (RatFunc K) F]
    [Nontrivial Ω[(RatFunc K)⁄K]] [∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates]
    [FiniteDimensional (RatFunc K) F] [AlgebraicCurve.HasSeparableResidue K F]
    (hRTK : AlgebraicCurve.ResidueTheoremK K F) :
    AlgebraicCurve.FunctionFieldRiemannRoch K F := by
  intro _ _ _
  exact ModularCurve.p0n25_wkc_functionFieldRiemannRoch_of_residueTheoremK K F
    (hRTK := hRTK) (hC := ModularCurve.p0n20_rr_constantsAreBase_of_isAlgClosed K F)

end P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed
