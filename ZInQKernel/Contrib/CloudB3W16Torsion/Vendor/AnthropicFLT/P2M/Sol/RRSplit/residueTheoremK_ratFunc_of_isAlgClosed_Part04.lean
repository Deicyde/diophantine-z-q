/-
Copyright 2026 Anthropic, PBC. Released under Apache License 2.0.
Source: https://github.com/anthropics/fermats-last-theorem
Revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.lean; source lines 5659-7758.
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
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.RRSplit.residueTheoremK_ratFunc_of_isAlgClosed_Part03

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 6400000
set_option maxHeartbeats 12800000

namespace P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed

-- RRSplit attribute-prefixed source-private field bridge.
private noncomputable abbrev _root_.AlgebraicCurve.Place.polynomialAlgebra :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.polynomialAlgebra
-- RRSplit attribute-prefixed source-private field bridge.
private noncomputable abbrev _root_.AlgebraicCurve.Place.polynomialIsScalarTower :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.polynomialIsScalarTower


-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.ord_add_eq_min :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.ord_add_eq_min
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.ord_nonneg_of_mem :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.ord_nonneg_of_mem
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.mem_of_ord_nonneg :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.mem_of_ord_nonneg
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.mem_iff_ord_nonneg :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.mem_iff_ord_nonneg
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.algebraMap_ne_zero :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.algebraMap_ne_zero
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.comap_algebraMap_ne_top :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.comap_algebraMap_ne_top
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.exists_ord_algebraMap_pos :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.exists_ord_algebraMap_pos
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.ord_add_eq_left :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.ord_add_eq_left
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.uniformizerSubring' :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.uniformizerSubring'
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.kaehlerMap_subring_D_uniformizer :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.kaehlerMap_subring_D_uniformizer
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.uniformizerSubring :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.uniformizerSubring
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.coe_uniformizerSubring :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.coe_uniformizerSubring
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.irreducible_uniformizerSubring :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.irreducible_uniformizerSubring
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.uniformizerSubring_mem_maximalIdeal :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.uniformizerSubring_mem_maximalIdeal
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.uniformizer_mem :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.uniformizer_mem
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.simplePoleSubmodule :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.simplePoleSubmodule
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.mem_simplePoleSubmodule_of_mem :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.mem_simplePoleSubmodule_of_mem
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.simplePoleMulUniformizer :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.simplePoleMulUniformizer
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.simplePoleResidueAux :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.simplePoleResidueAux
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.simplePoleResidueAux_eq_zero_of_mem :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.simplePoleResidueAux_eq_zero_of_mem
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.localResidueExtend :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.localResidueExtend
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.localResidueExtend_apply_of_mem :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.localResidueExtend_apply_of_mem
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.localResidueDataOfExtend :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.localResidueDataOfExtend
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.ModularCurve.MilneAvAg9bRd14CubeRowCartierSliceStart.ag9b14c_res_uniformizer_zpow_eq_zero_of_ne_neg_one :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve.MilneAvAg9bRd14CubeRowCartierSliceStart.ag9b14c_res_uniformizer_zpow_eq_zero_of_ne_neg_one
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.aeval_mem :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.aeval_mem
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.exists_coeff_ord_ne_zero :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.exists_coeff_ord_ne_zero
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.uniformizerSubring'' :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.uniformizerSubring''
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.polynomialAlgebra_algebraMap_X :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.polynomialAlgebra_algebraMap_X
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.range_mapBaseChange_le_span_D_uniformizer :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.range_mapBaseChange_le_span_D_uniformizer
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.range_mapBaseChange_eq_top_of_subsingleton :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.range_mapBaseChange_eq_top_of_subsingleton
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.span_D_uniformizer_eq_top_of_subsingleton :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.span_D_uniformizer_eq_top_of_subsingleton
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.poleSubmodule :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.poleSubmodule
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.mem_poleSubmodule :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.mem_poleSubmodule
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.uniformizer_pow_ne_zero :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.uniformizer_pow_ne_zero
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.ord_uniformizer_pow :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.ord_uniformizer_pow
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.coe_poleSubmodule_zero :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.coe_poleSubmodule_zero
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.poleSubmodule_one :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.poleSubmodule_one
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.mem_poleSubmodule_iff_ord :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.mem_poleSubmodule_iff_ord
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.poleSubmodule_mono :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.poleSubmodule_mono
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.poleMulUniformizerPow :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.poleMulUniformizerPow
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.laurentTailCoeff :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.laurentTailCoeff
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.laurentTail_remainder_mem_poleSubmodule :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.laurentTail_remainder_mem_poleSubmodule
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.localResidueData_res_eq_simplePoleResidueAux :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.localResidueData_res_eq_simplePoleResidueAux
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.isUnit_algebraMap :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.isUnit_algebraMap
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.adicValuation_algebraMap :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.adicValuation_algebraMap
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.ord_algebraMap :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.ord_algebraMap
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.ord_eq_neg_log_of_valuationSubring_eq :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.ord_eq_neg_log_of_valuationSubring_eq
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.uniformizerSubring''' :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.uniformizerSubring'''
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.irreducible_uniformizerSubring''' :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.irreducible_uniformizerSubring'''
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.maximalIdeal_eq_span_uniformizer :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.maximalIdeal_eq_span_uniformizer
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.D_polynomialAlgebra_uniformizer :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.D_polynomialAlgebra_uniformizer
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.ker_algebraMap_residueField_eq_span :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.ker_algebraMap_residueField_eq_span
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.formallyUnramified_polynomial_residueField_of_isSeparable :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.formallyUnramified_polynomial_residueField_of_isSeparable
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.subsingleton_residueKaehler_of_isSeparable :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.subsingleton_residueKaehler_of_isSeparable
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.subsingleton_residueTensor_polynomialKaehler_of_isSeparable :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.subsingleton_residueTensor_polynomialKaehler_of_isSeparable
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.finite_polynomialKaehler_of_finite_kaehler :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.finite_polynomialKaehler_of_finite_kaehler
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.subsingleton_polynomialKaehler_of_isSeparable_of_finite :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.subsingleton_polynomialKaehler_of_isSeparable_of_finite
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.isSeparable_residueField_of_charZero_of_finiteResidue :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.isSeparable_residueField_of_charZero_of_finiteResidue
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.subsingleton_polynomialKaehler_of_charZero_of_finite :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.subsingleton_polynomialKaehler_of_charZero_of_finite
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.exists_mem_poleSubmodule :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.exists_mem_poleSubmodule
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.uniformizer_pow_inv_mem_poleSubmodule_self :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.uniformizer_pow_inv_mem_poleSubmodule_self
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.higherPoleMonomial_sum_mem_poleSubmodule :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.higherPoleMonomial_sum_mem_poleSubmodule
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.higherPoleMonomial_coeff_eq_zero_of_mem :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.higherPoleMonomial_coeff_eq_zero_of_mem
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.linearIndependent_higherPoleMonomial_mkQ :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.linearIndependent_higherPoleMonomial_mkQ
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.higherPoleCorrectionAux :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.higherPoleCorrectionAux
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.higherPoleCorrection :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.higherPoleCorrection
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.higherPoleCorrection_apply_of_mem :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.higherPoleCorrection_apply_of_mem
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.higherPoleCorrection_uniformizer_pow_inv :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.higherPoleCorrection_uniformizer_pow_inv
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.canonicalLocalResidueDataKOfExtend :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.canonicalLocalResidueDataKOfExtend
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.CanonicalLocalResidueDataK.res_algebraMap_mul_uniformizer_pow_inv :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.CanonicalLocalResidueDataK.res_algebraMap_mul_uniformizer_pow_inv
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.ModularCurve.MilneAvAg9bRd15UnitNormalFormLaurentSeed.ag9b15u_eq_zero_or_one_le_ord_of_residue_eq_zero :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve.MilneAvAg9bRd15UnitNormalFormLaurentSeed.ag9b15u_eq_zero_or_one_le_ord_of_residue_eq_zero
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.ModularCurve.MilneAvAg9bRd15UnitNormalFormLaurentSeed.ag9b15u_exists_unit_normal_form_of_surj :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve.MilneAvAg9bRd15UnitNormalFormLaurentSeed.ag9b15u_exists_unit_normal_form_of_surj
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.ModularCurve.MilneAvAg9bRd15UnitNormalFormLaurentSeed.ag9b15u_exists_K_truncation_of_mem_poleSubmodule :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve.MilneAvAg9bRd15UnitNormalFormLaurentSeed.ag9b15u_exists_K_truncation_of_mem_poleSubmodule
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.ModularCurve.MilneAvAg9bRd15UnitNormalFormLaurentSeed.ag9b15u_differentialCoeff_D_unit_mul_uniformizer :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve.MilneAvAg9bRd15UnitNormalFormLaurentSeed.ag9b15u_differentialCoeff_D_unit_mul_uniformizer
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.ord_prod :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.ord_prod


section
section

noncomputable section

open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.WithZero
open _root_.Module
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Module
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsLocalRing
open _root_.Module.IsLocalRing

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq)

open _root_.AlgebraicCurve

open scoped _root_.Polynomial _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial
open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

section SurjectivePlaceInfty

variable (K) [DecidableEq (RatFunc K)]

theorem surjective_algebraMap_residueField_placeInfty :
    Function.Surjective (algebraMap K (placeInfty K).ResidueField) := by
  intro z
  obtain ⟨c, hc⟩ :=
    (finrank_eq_one_iff_of_nonzero' (1 : (placeInfty K).ResidueField) one_ne_zero).mp
      (show Module.finrank K (placeInfty K).ResidueField = 1 from deg_placeInfty K) z
  exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one]; exact hc⟩

end SurjectivePlaceInfty


section NamedRow

variable (K F)
variable [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

def CanonicalLocalResidueKDifferentialCoordIndep : Prop :=
  ∀ (v : Place K F) (π' : F), v.ord π' = 1 →
    ∀ (R : v.CanonicalLocalResidueDataK) (n : ℕ), 1 ≤ n →
      R.res (v.differentialCoeff (KaehlerDifferential.D K F π') * ((π') ^ (n + 1))⁻¹) = 0

end NamedRow


section SATGate

variable [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

end SATGate


section XInvCoordinate

variable (K) [DecidableEq (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

omit [DecidableEq (RatFunc K)]
  [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]] in

theorem ratFuncX_inv_pow_inv (m : ℕ) :
    (((RatFunc.X : RatFunc K)⁻¹) ^ m)⁻¹ = (RatFunc.X : RatFunc K) ^ m := by
  rw [inv_pow, inv_inv]

theorem X_pow_mul_differentialCoeff_D_X_eq_neg (n : ℕ) :
    (RatFunc.X : RatFunc K) ^ n
        * (placeInfty K).differentialCoeff (KaehlerDifferential.D K (RatFunc K) RatFunc.X)
      = -((placeInfty K).differentialCoeff
            (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)⁻¹)
          * (((RatFunc.X : RatFunc K)⁻¹) ^ (n + 2))⁻¹) := by
  rw [ratFuncX_inv_pow_inv, differentialCoeff_placeInfty_D_X_eq K]
  ring

end XInvCoordinate


section Bridge

variable (K) [DecidableEq (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

theorem canonicalLocalResidueDataK_res_X_pow_mul_D_X_of_coordIndep
    (hcoord : CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K))
    (R : (placeInfty K).CanonicalLocalResidueDataK) (n : ℕ) :
    R.res ((RatFunc.X : RatFunc K) ^ n
        * (placeInfty K).differentialCoeff
            (KaehlerDifferential.D K (RatFunc K) RatFunc.X)) = 0 := by
  rw [X_pow_mul_differentialCoeff_D_X_eq_neg K n, _root_.map_neg, neg_eq_zero]
  exact hcoord (placeInfty K) (RatFunc.X : RatFunc K)⁻¹ (ord_placeInfty_X_inv K) R (n + 1)
    (by omega)

theorem canonicalLocalResidueDataK_kaehlerResidueTerm_X_pow_of_coordIndep
    (_hwd : OrdDifferentialWellDefined K (RatFunc K))
    (hcoord : CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K))
    (R : (placeInfty K).CanonicalLocalResidueDataK) (n : ℕ) :
    Algebra.trace K (placeInfty K).ResidueField
        (R.res (diagonalHom K (RatFunc K) ((RatFunc.X : RatFunc K) ^ n) (placeInfty K)
          * (placeInfty K).differentialCoeff
              (KaehlerDifferential.D K (RatFunc K) RatFunc.X))) = 0 := by
  rw [diagonalHom_apply,
    canonicalLocalResidueDataK_res_X_pow_mul_D_X_of_coordIndep K hcoord R n, _root_.map_zero]

end Bridge


section IntegralRecursion

namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_ne_zero adicValuation_coe_eq_one_iff adicValuation_coe_irreducible ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ord_smul ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring mk.injEq rec ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk adicValuation_valuationSubring mem_iff_adicValuation_le_one isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one isEquiv_adicValuation_ofHeightOneSpectrum ord_ofHeightOneSpectrum_ne_zero_iff dCoord DCoordGenerates dCoord_ne_zero differentialCoeff differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_dCoord differentialCoeff_zero differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg deg_restrict_mul_inertiaDeg ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq)

open _root_.AlgebraicCurve.Place

variable (v : Place K F)

end Place


end IntegralRecursion


end AlgebraicCurve


section AxiomAudit

end AxiomAudit


end


end


end


section
section

open _root_.CongruenceSubgroup
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.CongruenceSubgroup
open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.WithZero
open _root_.Polynomial
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsLocalRing

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq)

open _root_.AlgebraicCurve

namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_ne_zero adicValuation_coe_eq_one_iff adicValuation_coe_irreducible ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ord_smul ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring mk.injEq rec ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk adicValuation_valuationSubring mem_iff_adicValuation_le_one isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one isEquiv_adicValuation_ofHeightOneSpectrum ord_ofHeightOneSpectrum_ne_zero_iff dCoord DCoordGenerates dCoord_ne_zero differentialCoeff differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_dCoord differentialCoeff_zero differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg deg_restrict_mul_inertiaDeg ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq)

open _root_.AlgebraicCurve.Place

section EftEngine

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.finite_kaehler_of_essFiniteType [Algebra.EssFiniteType K v.toValuationSubring] :
    Module.Finite v.toValuationSubring Ω[v.toValuationSubring⁄K] :=
  KaehlerDifferential.finite K v.toValuationSubring




-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.finite_kaehler_of_essFiniteType :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.finite_kaehler_of_essFiniteType
end EftEngine


end Place


variable (K F : Type*) [Field K] [Field F] [Algebra K F]

def ValSubringEssFiniteType : Prop :=
  ∀ v : Place K F, Algebra.EssFiniteType K v.toValuationSubring

variable {K F}

theorem valSubringKaehlerFinite_of_essFiniteType
    (heft : ValSubringEssFiniteType K F) :
    ValSubringKaehlerFinite K F := fun v =>
  haveI := heft v
  v.finite_kaehler_of_essFiniteType

end AlgebraicCurve


namespace ModularCurve

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve

variable (N : ℕ) [NeZero N]

end ModularCurve


namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq)

open _root_.AlgebraicCurve

end AlgebraicCurve


namespace ModularCurve

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve

end ModularCurve


end


end


section
section

set_option maxHeartbeats 6400000

open _root_.Polynomial
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsLocalRing
open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve
open ModularCurve.Lg37 ModularCurve.Mp72a102T3 Mp72a103T2 Mp72a102T1
open ModularCurve.KwNo6Section

namespace ModularCurve
namespace KwNo6Pin

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem aCoeff_zero (v : Place K F) (S : Lg37CompletionSection v)
    (x : lg37_completion v) :
    aCoeff v S 0 x = lg37_residueHat v x := by
  have ha := Classical.choose_spec (mp72a102_t3_sigma_taylor_expansion v S 1 x)
  set a := Classical.choose (mp72a102_t3_sigma_taylor_expansion v S 1 x) with ha_def
  rw [Finset.sum_range_one, pow_zero, mul_one] at ha
  have hres : lg37_residueHat v (x - S.lift (a 0)) = lg37_residueHat v 0 :=
    mp72a102_t3_residueHat_congr_of_depth_one v (by rw [ha, _root_.map_zero])
  rw [map_sub, S.residueHat_lift, _root_.map_zero, sub_eq_zero] at hres
  simp only [aCoeff, ← ha_def]
  exact hres.symm

theorem aCoeff_add (v : Place K F) (S : Lg37CompletionSection v) (m : ℕ)
    (x y : lg37_completion v) :
    aCoeff v S m (x + y) = aCoeff v S m x + aCoeff v S m y := by
  have hx := Classical.choose_spec (mp72a102_t3_sigma_taylor_expansion v S (m + 1) x)
  have hy := Classical.choose_spec (mp72a102_t3_sigma_taylor_expansion v S (m + 1) y)
  have hxy := Classical.choose_spec (mp72a102_t3_sigma_taylor_expansion v S (m + 1) (x + y))
  set ax := Classical.choose (mp72a102_t3_sigma_taylor_expansion v S (m + 1) x) with hax_def
  set ay := Classical.choose (mp72a102_t3_sigma_taylor_expansion v S (m + 1) y) with hay_def
  set axy := Classical.choose (mp72a102_t3_sigma_taylor_expansion v S (m + 1) (x + y))
    with haxy_def
  have hsum : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (m + 1)
      ((x + y) - ∑ i ∈ Finset.range (m + 1), S.lift ((fun i => ax i + ay i) i)
        * algebraMap v.toValuationSubring (lg37_completion v)
            v.uniformizerSubring ^ i) = 0 := by
    have e : (x + y) - ∑ i ∈ Finset.range (m + 1), S.lift (ax i + ay i)
          * algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ i
        = (x - ∑ i ∈ Finset.range (m + 1), S.lift (ax i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i)
          + (y - ∑ i ∈ Finset.range (m + 1), S.lift (ay i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i) := by
      rw [Finset.sum_congr rfl (fun i _ => by rw [map_add, add_mul]),
        Finset.sum_add_distrib]
      ring
    rw [e, mp72a102_t3_evalDepth_add, hx, hy, add_zero]
  have key : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (m + 1)
      (∑ i ∈ Finset.range (m + 1), S.lift ((fun i => (ax i + ay i) - axy i) i)
        * algebraMap v.toValuationSubring (lg37_completion v)
            v.uniformizerSubring ^ i) = 0 := by
    have e1 : (∑ i ∈ Finset.range (m + 1), S.lift ((ax i + ay i) - axy i)
          * algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ i)
        = ((x + y) - ∑ i ∈ Finset.range (m + 1), S.lift (axy i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i)
          - ((x + y) - ∑ i ∈ Finset.range (m + 1), S.lift (ax i + ay i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i) := by
      rw [Finset.sum_congr rfl (fun i _ => by rw [map_sub, sub_mul]),
        Finset.sum_sub_distrib]
      ring
    rw [e1, map_sub, hxy, hsum, sub_zero]
  have hzero := mp72a103_t2_taylor_coeff_eq_zero_of_depth v S (m + 1)
    (fun i => (ax i + ay i) - axy i) key m (Nat.lt_succ_self m)
  have han : axy m = ax m + ay m := (sub_eq_zero.mp hzero).symm
  simp only [aCoeff, ← hax_def, ← hay_def, ← haxy_def]
  exact han

theorem aCoeff_smul (v : Place K F) (S : Lg37CompletionSection v) (m : ℕ) (c : K)
    (x : lg37_completion v) :
    aCoeff v S m (algebraMap K (lg37_completion v) c * x)
      = algebraMap K v.ResidueField c * aCoeff v S m x := by
  have hx := Classical.choose_spec (mp72a102_t3_sigma_taylor_expansion v S (m + 1) x)
  have hcx := Classical.choose_spec (mp72a102_t3_sigma_taylor_expansion v S (m + 1)
    (algebraMap K (lg37_completion v) c * x))
  set ax := Classical.choose (mp72a102_t3_sigma_taylor_expansion v S (m + 1) x) with hax_def
  set acx := Classical.choose (mp72a102_t3_sigma_taylor_expansion v S (m + 1)
    (algebraMap K (lg37_completion v) c * x)) with hacx_def
  have hsmul : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (m + 1)
      ((algebraMap K (lg37_completion v) c * x)
        - ∑ i ∈ Finset.range (m + 1),
            S.lift ((fun i => algebraMap K v.ResidueField c * ax i) i)
          * algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ i) = 0 := by
    have e : (algebraMap K (lg37_completion v) c * x)
          - ∑ i ∈ Finset.range (m + 1), S.lift (algebraMap K v.ResidueField c * ax i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i
        = algebraMap K (lg37_completion v) c
          * (x - ∑ i ∈ Finset.range (m + 1), S.lift (ax i)
              * algebraMap v.toValuationSubring (lg37_completion v)
                  v.uniformizerSubring ^ i) := by
      rw [mul_sub, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hlift : S.lift (algebraMap K v.ResidueField c * ax i)
          = algebraMap K (lg37_completion v) c * S.lift (ax i) := by
        rw [← Algebra.smul_def c (ax i), map_smul, Algebra.smul_def]
      rw [hlift, mul_assoc]
    rw [e, mp72a102_t3_evalDepth_mul, hx, mul_zero]
  have key : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (m + 1)
      (∑ i ∈ Finset.range (m + 1),
          S.lift ((fun i => algebraMap K v.ResidueField c * ax i - acx i) i)
        * algebraMap v.toValuationSubring (lg37_completion v)
            v.uniformizerSubring ^ i) = 0 := by
    have e1 : (∑ i ∈ Finset.range (m + 1),
            S.lift (algebraMap K v.ResidueField c * ax i - acx i)
          * algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ i)
        = ((algebraMap K (lg37_completion v) c * x)
            - ∑ i ∈ Finset.range (m + 1), S.lift (acx i)
              * algebraMap v.toValuationSubring (lg37_completion v)
                  v.uniformizerSubring ^ i)
          - ((algebraMap K (lg37_completion v) c * x)
            - ∑ i ∈ Finset.range (m + 1), S.lift (algebraMap K v.ResidueField c * ax i)
              * algebraMap v.toValuationSubring (lg37_completion v)
                  v.uniformizerSubring ^ i) := by
      rw [Finset.sum_congr rfl (fun i _ => by rw [map_sub, sub_mul]),
        Finset.sum_sub_distrib]
      ring
    rw [e1, map_sub, hcx, hsmul, sub_zero]
  have hzero := mp72a103_t2_taylor_coeff_eq_zero_of_depth v S (m + 1)
    (fun i => algebraMap K v.ResidueField c * ax i - acx i) key m (Nat.lt_succ_self m)
  have han : acx m = algebraMap K v.ResidueField c * ax m := (sub_eq_zero.mp hzero).symm
  simp only [aCoeff, ← hax_def, ← hacx_def]
  exact han

theorem aCoeff_shift (v : Place K F) (S : Lg37CompletionSection v) (n : ℕ)
    (x : lg37_completion v) :
    aCoeff v S (n + 1)
        (algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring * x)
      = aCoeff v S n x := by
  have ha := Classical.choose_spec (mp72a102_t3_sigma_taylor_expansion v S (n + 1) x)
  have hpx := Classical.choose_spec (mp72a102_t3_sigma_taylor_expansion v S (n + 2)
    (algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring * x))
  set a := Classical.choose (mp72a102_t3_sigma_taylor_expansion v S (n + 1) x) with ha_def
  set b := Classical.choose (mp72a102_t3_sigma_taylor_expansion v S (n + 2)
    (algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring * x))
    with hb_def

  set c : ℕ → v.ResidueField :=
    fun i => Nat.rec (motive := fun _ => v.ResidueField) 0 (fun j _ => a j) i with hc_def

  have hshift : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (n + 2)
      ((algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring * x)
        - ∑ i ∈ Finset.range (n + 2), S.lift (c i)
          * algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ i) = 0 := by
    have hmul := mp72a102_t3_evalₐ_succ_mul_eq_zero (maximalIdeal v.toValuationSubring)
      v.uniformizerSubring_mem_maximalIdeal ha
    have e : (algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring * x)
          - ∑ i ∈ Finset.range (n + 2), S.lift (c i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i
        = algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring
          * (x - ∑ i ∈ Finset.range (n + 1), S.lift (a i)
              * algebraMap v.toValuationSubring (lg37_completion v)
                  v.uniformizerSubring ^ i) := by
      have hc0 : c 0 = 0 := rfl
      have hcs : ∀ i, c (i + 1) = a i := fun _ => rfl
      rw [Finset.sum_range_succ', hc0, _root_.map_zero, zero_mul, add_zero, mul_sub, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hcs i, pow_succ]
      ring
    rw [e]
    exact hmul

  have key : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (n + 2)
      (∑ i ∈ Finset.range (n + 2), S.lift ((fun i => c i - b i) i)
        * algebraMap v.toValuationSubring (lg37_completion v)
            v.uniformizerSubring ^ i) = 0 := by
    have e1 : (∑ i ∈ Finset.range (n + 2), S.lift (c i - b i)
          * algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ i)
        = ((algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring * x)
            - ∑ i ∈ Finset.range (n + 2), S.lift (b i)
              * algebraMap v.toValuationSubring (lg37_completion v)
                  v.uniformizerSubring ^ i)
          - ((algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring * x)
            - ∑ i ∈ Finset.range (n + 2), S.lift (c i)
              * algebraMap v.toValuationSubring (lg37_completion v)
                  v.uniformizerSubring ^ i) := by
      rw [Finset.sum_congr rfl (fun i _ => by rw [map_sub, sub_mul]),
        Finset.sum_sub_distrib]
      ring
    rw [e1, map_sub, hpx, hshift, sub_zero]
  have hzero := mp72a103_t2_taylor_coeff_eq_zero_of_depth v S (n + 2)
    (fun i => c i - b i) key (n + 1) (Nat.lt_succ_self (n + 1))
  have hcn : c (n + 1) = a n := rfl
  have hbn : b (n + 1) = a n := by
    have := sub_eq_zero.mp hzero
    rw [hcn] at this
    exact this.symm
  simp only [aCoeff, ← ha_def, ← hb_def]
  exact hbn

theorem aCoeff_shift_pow (v : Place K F) (S : Lg37CompletionSection v) (n k : ℕ)
    (x : lg37_completion v) :
    aCoeff v S (n + k)
        ((algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring) ^ k
          * x)
      = aCoeff v S n x := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep : (algebraMap v.toValuationSubring (lg37_completion v)
          v.uniformizerSubring) ^ (k + 1) * x
        = algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring
          * ((algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring) ^ k * x) := by
      rw [pow_succ]; ring
    rw [show n + (k + 1) = (n + k) + 1 from by omega, hstep, aCoeff_shift, ih]

theorem aCoeff_one_eq_zero (v : Place K F) (S : Lg37CompletionSection v)
    {n : ℕ} (hn : 1 ≤ n) : aCoeff v S n 1 = 0 := by
  have hc := Classical.choose_spec (mp72a102_t3_sigma_taylor_expansion v S (n + 1) 1)
  set cc := Classical.choose (mp72a102_t3_sigma_taylor_expansion v S (n + 1) 1) with hcc_def

  set e : ℕ → v.ResidueField := fun i => if i = 0 then 1 else 0 with he_def
  have hesum : (∑ i ∈ Finset.range (n + 1), S.lift (e i)
      * algebraMap v.toValuationSubring (lg37_completion v)
          v.uniformizerSubring ^ i) = 1 := by
    rw [Finset.sum_eq_single 0]
    · simp [he_def]
    · intro i _ hi; simp [he_def, hi]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  have hevalid : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (n + 1)
      ((1 : lg37_completion v) - ∑ i ∈ Finset.range (n + 1), S.lift (e i)
        * algebraMap v.toValuationSubring (lg37_completion v)
            v.uniformizerSubring ^ i) = 0 := by
    rw [hesum, sub_self, _root_.map_zero]
  have key : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (n + 1)
      (∑ i ∈ Finset.range (n + 1), S.lift ((fun i => e i - cc i) i)
        * algebraMap v.toValuationSubring (lg37_completion v)
            v.uniformizerSubring ^ i) = 0 := by
    have e1 : (∑ i ∈ Finset.range (n + 1), S.lift (e i - cc i)
          * algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ i)
        = ((1 : lg37_completion v) - ∑ i ∈ Finset.range (n + 1), S.lift (cc i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i)
          - ((1 : lg37_completion v) - ∑ i ∈ Finset.range (n + 1), S.lift (e i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i) := by
      rw [Finset.sum_congr rfl (fun i _ => by rw [map_sub, sub_mul]),
        Finset.sum_sub_distrib]
      ring
    rw [e1, map_sub, hc, hevalid, sub_zero]
  have hzero := mp72a103_t2_taylor_coeff_eq_zero_of_depth v S (n + 1)
    (fun i => e i - cc i) key n (Nat.lt_succ_self n)
  have hen : e n = 0 := by simp [he_def, Nat.one_le_iff_ne_zero.mp hn]
  have : e n - cc n = 0 := hzero
  rw [hen, zero_sub, neg_eq_zero] at this
  simp only [aCoeff, ← hcc_def]
  exact this

theorem clearPow_mem (v : Place K F) (f : F) {N : ℕ} (hN : (-v.ord f).toNat ≤ N) :
    v.uniformizer ^ (N + 1) * f ∈ v.toValuationSubring := by
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [mul_zero]; exact zero_mem _
  · refine (v.mem_iff_ord_nonneg (mul_ne_zero (v.uniformizer_pow_ne_zero _) hf0)).mpr ?_
    rw [v.ord_mul (v.uniformizer_pow_ne_zero _) hf0, v.ord_uniformizer_pow]
    have h := Int.self_le_toNat (-v.ord f)
    have hNc : ((-v.ord f).toNat : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
    omega

noncomputable def clearedHat (v : Place K F) (f : F) {N : ℕ} (hN : (-v.ord f).toNat ≤ N) :
    lg37_completion v :=
  algebraMap v.toValuationSubring (lg37_completion v)
    ⟨v.uniformizer ^ (N + 1) * f, clearPow_mem v f hN⟩

noncomputable def resStar (v : Place K F) (S : Lg37CompletionSection v) (f : F) :
    v.ResidueField :=
  aCoeff v S ((-v.ord f).toNat) (clearedHat v f (le_refl _))

theorem aCoeff_clearedHat_of_le (v : Place K F) (S : Lg37CompletionSection v) (f : F)
    {N : ℕ} (hN : (-v.ord f).toNat ≤ N) :
    aCoeff v S N (clearedHat v f hN) = resStar v S f := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  unfold clearedHat resStar
  have hfac : (⟨v.uniformizer ^ (((-v.ord f).toNat + k) + 1) * f,
        clearPow_mem v f hN⟩ : v.toValuationSubring)
      = v.uniformizerSubring ^ k
        * ⟨v.uniformizer ^ ((-v.ord f).toNat + 1) * f, clearPow_mem v f (le_refl _)⟩ := by
    apply Subtype.ext
    push_cast [v.coe_uniformizerSubring]
    ring
  rw [hfac, map_mul, map_pow]
  exact aCoeff_shift_pow v S ((-v.ord f).toNat) k _

theorem resStar_add (v : Place K F) (S : Lg37CompletionSection v) (f g : F) :
    resStar v S (f + g) = resStar v S f + resStar v S g := by
  set N := (-v.ord f).toNat ⊔ (-v.ord g).toNat ⊔ (-v.ord (f + g)).toNat with hN
  have hf : (-v.ord f).toNat ≤ N := le_trans le_sup_left le_sup_left
  have hg : (-v.ord g).toNat ≤ N := le_trans le_sup_right le_sup_left
  have hfg : (-v.ord (f + g)).toNat ≤ N := le_sup_right
  rw [← aCoeff_clearedHat_of_le v S f hf, ← aCoeff_clearedHat_of_le v S g hg,
    ← aCoeff_clearedHat_of_le v S (f + g) hfg, ← aCoeff_add]
  congr 1
  unfold clearedHat
  rw [← map_add]
  congr 1
  apply Subtype.ext
  push_cast
  ring

theorem resStar_smul (v : Place K F) (S : Lg37CompletionSection v) (c : K) (f : F) :
    resStar v S (c • f) = c • resStar v S f := by
  set N := (-v.ord (c • f)).toNat ⊔ (-v.ord f).toNat with hN
  have hcf : (-v.ord (c • f)).toNat ≤ N := le_sup_left
  have hf : (-v.ord f).toNat ≤ N := le_sup_right
  rw [← aCoeff_clearedHat_of_le v S (c • f) hcf, ← aCoeff_clearedHat_of_le v S f hf,
    Algebra.smul_def c (aCoeff v S N (clearedHat v f hf)), ← aCoeff_smul]
  congr 1
  unfold clearedHat
  rw [IsScalarTower.algebraMap_apply K v.toValuationSubring (lg37_completion v) c, ← map_mul]
  congr 1
  apply Subtype.ext
  push_cast [v.coe_algebraMap, Algebra.smul_def]
  ring

noncomputable def resStarₗ (v : Place K F) (S : Lg37CompletionSection v) :
    F →ₗ[K] v.ResidueField where
  toFun := resStar v S
  map_add' := resStar_add v S
  map_smul' c f := by rw [RingHom.id_apply]; exact resStar_smul v S c f

theorem resStar_simplePole (v : Place K F) (S : Lg37CompletionSection v) (f : F)
    (hf : v.uniformizer * f ∈ v.toValuationSubring) :
    resStar v S f = IsLocalRing.residue _ ⟨v.uniformizer * f, hf⟩ := by
  have hM : (-v.ord f).toNat ≤ 1 := by
    rcases eq_or_ne f 0 with rfl | hf0
    · rw [v.ord_zero]; simp
    · have hge : (0 : ℤ) ≤ v.ord (v.uniformizer * f) :=
        (v.mem_iff_ord_nonneg (mul_ne_zero v.uniformizer_ne_zero hf0)).mp hf
      rw [v.ord_mul v.uniformizer_ne_zero hf0, v.ord_uniformizer] at hge
      have := Int.self_le_toNat (-v.ord f)
      omega
  rw [← aCoeff_clearedHat_of_le v S f hM]
  unfold clearedHat
  have hfac : (⟨v.uniformizer ^ (1 + 1) * f, clearPow_mem v f hM⟩ : v.toValuationSubring)
      = v.uniformizerSubring * ⟨v.uniformizer * f, hf⟩ := by
    apply Subtype.ext
    push_cast [v.coe_uniformizerSubring]
    ring
  rw [hfac, map_mul, aCoeff_shift, aCoeff_zero, lg37_residueHat_algebraMap]

theorem resStar_of_mem (v : Place K F) (S : Lg37CompletionSection v) {f : F}
    (hf : f ∈ v.toValuationSubring) : resStar v S f = 0 := by
  rw [resStar_simplePole v S f (mul_mem v.uniformizer_mem hf), IsLocalRing.residue_eq_zero_iff]
  have : (⟨v.uniformizer * f, mul_mem v.uniformizer_mem hf⟩ : v.toValuationSubring)
      = v.uniformizerSubring * ⟨f, hf⟩ := Subtype.ext rfl
  rw [this]
  exact Ideal.mul_mem_right _ _ v.uniformizerSubring_mem_maximalIdeal

theorem resStar_higherPoleMonomial (v : Place K F) (S : Lg37CompletionSection v)
    {n : ℕ} (hn : 1 ≤ n) : resStar v S (v.uniformizer ^ (n + 1))⁻¹ = 0 := by
  have hord : v.ord (v.uniformizer ^ (n + 1))⁻¹ = -((n : ℤ) + 1) := by
    rw [v.ord_inv, v.ord_uniformizer_pow]; push_cast; ring
  have hM : (-v.ord (v.uniformizer ^ (n + 1))⁻¹).toNat = n + 1 := by
    rw [hord]; simp
  have hle : (-v.ord (v.uniformizer ^ (n + 1))⁻¹).toNat ≤ n + 1 := le_of_eq hM
  rw [← aCoeff_clearedHat_of_le v S (v.uniformizer ^ (n + 1))⁻¹ hle]
  unfold clearedHat
  have hfac : (⟨v.uniformizer ^ ((n + 1) + 1) * (v.uniformizer ^ (n + 1))⁻¹,
        clearPow_mem v (v.uniformizer ^ (n + 1))⁻¹ hle⟩ : v.toValuationSubring)
      = v.uniformizerSubring := by
    apply Subtype.ext
    push_cast [v.coe_uniformizerSubring]
    rw [pow_succ, mul_right_comm, mul_inv_cancel₀ (v.uniformizer_pow_ne_zero (n + 1)), one_mul]
  rw [hfac]
  have : algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring
      = algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring * 1 := by
    rw [mul_one]
  rw [this, aCoeff_shift, aCoeff_one_eq_zero v S hn]

noncomputable def canonicalLocalResidueDataKStar (v : Place K F)
    (S : Lg37CompletionSection v) : v.CanonicalLocalResidueDataK where
  res := resStarₗ v S
  res_of_mem _f hf := resStar_of_mem v S hf
  res_simplePole f hf := resStar_simplePole v S f hf
  res_higherPoleMonomial _n hn := resStar_higherPoleMonomial v S hn

section WitnessW
variable {v : Place K F} {ℓ : v.toValuationSubring}
  (hℓ : IsLocalRing.residue v.toValuationSubring ℓ ∉ Set.range (algebraMap K v.ResidueField))
include hℓ

end WitnessW


end ModularCurve.KwNo6Pin



end


end


section
section

noncomputable section

open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.WithZero
open _root_.Module
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Module
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsLocalRing
open _root_.Module.IsLocalRing
open _root_.KaehlerDifferential
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.KaehlerDifferential
open _root_.Polynomial
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq)

open _root_.AlgebraicCurve

open scoped _root_.Polynomial _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial

open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField

section WronskianBound

variable {K : Type*} [Field K]

theorem natDegree_numDenomWronskian_lt {n d : K[X]} (hn : n ≠ 0) (hd : d ≠ 0)
    (hW : n.derivative * d - n * d.derivative ≠ 0) :
    (n.derivative * d - n * d.derivative).natDegree < n.natDegree + d.natDegree := by
  have hdeg : (n.derivative * d - n * d.derivative).degree < (n * d).degree := by
    rw [Polynomial.degree_mul]
    refine lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt ?_ ?_)
    · refine lt_of_le_of_lt (Polynomial.degree_mul_le _ _) ?_
      rw [WithBot.add_lt_add_iff_right (Polynomial.degree_ne_bot.mpr hd)]
      exact Polynomial.degree_derivative_lt hn
    · refine lt_of_le_of_lt (Polynomial.degree_mul_le _ _) ?_
      rw [WithBot.add_lt_add_iff_left (Polynomial.degree_ne_bot.mpr hn)]
      exact Polynomial.degree_derivative_lt hd
  have h2 := Polynomial.natDegree_lt_natDegree hW hdeg
  rwa [Polynomial.natDegree_mul hn hd] at h2

end WronskianBound


section DXCoeff

variable (K : Type*) [Field K]

def ratFuncDXCoeff (f : RatFunc K) : RatFunc K :=
  algebraMap K[X] (RatFunc K) (f.num.derivative * f.denom - f.num * f.denom.derivative)
    / (algebraMap K[X] (RatFunc K) f.denom) ^ 2

theorem ratFuncDXCoeff_def (f : RatFunc K) :
    ratFuncDXCoeff K f
      = algebraMap K[X] (RatFunc K) (f.num.derivative * f.denom - f.num * f.denom.derivative)
        / (algebraMap K[X] (RatFunc K) f.denom) ^ 2 := rfl

theorem D_eq_ratFuncDXCoeff_smul_dX (f : RatFunc K) :
    KaehlerDifferential.D K (RatFunc K) f = ratFuncDXCoeff K f • dX K := by
  have hd : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero f.denom_ne_zero
  rw [ratFuncDXCoeff_def, div_eq_mul_inv, mul_comm, mul_smul, ← denom_sq_smul_D_eq K f,
    smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 hd), one_smul]

theorem wronskian_ne_zero_of_ratFuncDXCoeff_ne_zero {f : RatFunc K}
    (h : ratFuncDXCoeff K f ≠ 0) :
    f.num.derivative * f.denom - f.num * f.denom.derivative ≠ 0 := by
  intro h0
  exact h (by rw [ratFuncDXCoeff_def, h0, _root_.map_zero, zero_div])

end DXCoeff


section FinitePlaces

variable {K : Type*} [Field K]
variable {w : HeightOneSpectrum K[X]}



theorem ord_algebraMap_denom_eq_zero_of_ord_eq_one {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) {f : RatFunc K}
    (hf : f ≠ 0) (hord : ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord f = 1) :
    ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord (algebraMap K[X] (RatFunc K) f.denom) = 0 := by
  by_contra hne

  have hpd : p ∣ f.denom := by
    rw [← Ideal.mem_span_singleton, ← hwp]
    exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
      f.denom_ne_zero).mp hne
  have hpn : ¬ p ∣ f.num := fun hpn =>
    hp.not_isUnit (f.isCoprime_num_denom.isUnit_of_dvd' hpn hpd)
  have hordn : ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord (algebraMap K[X] (RatFunc K) f.num) = 0 := by
    by_contra h
    exact hpn (by
      rw [← Ideal.mem_span_singleton, ← hwp]
      exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
        (RatFunc.num_ne_zero hf)).mp h)
  have hordd : 0 < ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord (algebraMap K[X] (RatFunc K) f.denom) :=
    lt_of_le_of_ne (((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord_nonneg_of_mem (algebraMap_mem_ofHeightOneSpectrum K w _))
      (Ne.symm hne)

  have hnum0 : algebraMap K[X] (RatFunc K) f.num ≠ 0 :=
    RatFunc.algebraMap_ne_zero (RatFunc.num_ne_zero hf)
  have hden0 : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero f.denom_ne_zero
  rw [← f.num_div_denom, div_eq_mul_inv, ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord_mul hnum0 (inv_ne_zero hden0),
    ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord_inv, hordn] at hord
  omega

theorem ord_algebraMap_num_eq_one_of_ord_eq_one {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) {f : RatFunc K}
    (hf : f ≠ 0) (hord : ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord f = 1) :
    ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord (algebraMap K[X] (RatFunc K) f.num) = 1 := by
  have hnum0 : algebraMap K[X] (RatFunc K) f.num ≠ 0 :=
    RatFunc.algebraMap_ne_zero (RatFunc.num_ne_zero hf)
  have hden0 : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero f.denom_ne_zero
  have h := hord
  rw [← f.num_div_denom, div_eq_mul_inv, ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord_mul hnum0 (inv_ne_zero hden0),
    ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord_inv, ord_algebraMap_denom_eq_zero_of_ord_eq_one hp hwp hf hord] at h
  omega

theorem not_dvd_wronskian_of_ord_eq_one {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) (hsep : p.Separable)
    {f : RatFunc K} (hf : f ≠ 0) (hord : ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord f = 1) :
    ¬ p ∣ (f.num.derivative * f.denom - f.num * f.denom.derivative) := by
  have hpn' : ¬ p ∣ f.num.derivative :=
    not_dvd_derivative_of_ord_eq_one hp hwp hsep (RatFunc.num_ne_zero hf)
      (ord_algebraMap_num_eq_one_of_ord_eq_one hp hwp hf hord)
  have hpd : ¬ p ∣ f.denom := fun hpd => by
    have h0 := ord_algebraMap_denom_eq_zero_of_ord_eq_one hp hwp hf hord
    rw [← Ideal.mem_span_singleton, ← hwp] at hpd
    exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
      f.denom_ne_zero).mpr hpd h0
  have hpn : p ∣ f.num := by
    rw [← Ideal.mem_span_singleton, ← hwp]
    refine (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
      (RatFunc.num_ne_zero hf)).mp ?_
    rw [ord_algebraMap_num_eq_one_of_ord_eq_one hp hwp hf hord]
    exact one_ne_zero
  intro hdvd

  have hpnd' : p ∣ f.num * f.denom.derivative := hpn.mul_right _
  have hpn'd : p ∣ f.num.derivative * f.denom := by
    have h1 := dvd_add hdvd hpnd'
    rwa [sub_add_cancel] at h1
  rcases hp.prime.dvd_mul.mp hpn'd with h | h
  · exact hpn' h
  · exact hpd h

theorem ratFuncDXCoeff_ne_zero_and_ord_eq_zero_of_ord_eq_one {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) (hsep : p.Separable)
    {f : RatFunc K} (hf : f ≠ 0) (hord : ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord f = 1) :
    ratFuncDXCoeff K f ≠ 0 ∧ ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord (ratFuncDXCoeff K f) = 0 := by
  have hW : ¬ p ∣ (f.num.derivative * f.denom - f.num * f.denom.derivative) :=
    not_dvd_wronskian_of_ord_eq_one hp hwp hsep hf hord
  have hξ0 : f.num.derivative * f.denom - f.num * f.denom.derivative ≠ 0 := fun h =>
    hW (h ▸ dvd_zero p)
  have hd0 : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero f.denom_ne_zero
  have hξ0' : algebraMap K[X] (RatFunc K)
      (f.num.derivative * f.denom - f.num * f.denom.derivative) ≠ 0 :=
    RatFunc.algebraMap_ne_zero hξ0

  have hordξ : ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord (algebraMap K[X] (RatFunc K)
      (f.num.derivative * f.denom - f.num * f.denom.derivative)) = 0 := by
    by_contra h
    refine hW ?_
    rw [← Ideal.mem_span_singleton, ← hwp]
    exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w hξ0).mp h
  refine ⟨div_ne_zero hξ0' (pow_ne_zero 2 hd0), ?_⟩
  rw [ratFuncDXCoeff_def, div_eq_mul_inv,
    ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord_mul hξ0' (inv_ne_zero (pow_ne_zero 2 hd0)), ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord_inv, hordξ,
    ← zpow_natCast, ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord_zpow,
    ord_algebraMap_denom_eq_zero_of_ord_eq_one hp hwp hf hord]
  ring

end FinitePlaces


section PlaceInftySide

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]

theorem ord_placeInfty_ratFuncDXCoeff_ge {g : RatFunc K} (hg : g ≠ 0)
    (hW : g.num.derivative * g.denom - g.num * g.denom.derivative ≠ 0) :
    (placeInfty K).ord g + 1 ≤ (placeInfty K).ord (ratFuncDXCoeff K g) := by
  have hn0 : g.num ≠ 0 := RatFunc.num_ne_zero hg
  have hd0 : g.denom ≠ 0 := g.denom_ne_zero
  have hW' : algebraMap K[X] (RatFunc K)
      (g.num.derivative * g.denom - g.num * g.denom.derivative) ≠ 0 :=
    RatFunc.algebraMap_ne_zero hW
  have hd' : algebraMap K[X] (RatFunc K) g.denom ≠ 0 := RatFunc.algebraMap_ne_zero hd0

  have hdeg : (g.num.derivative * g.denom - g.num * g.denom.derivative).natDegree
      < g.num.natDegree + g.denom.natDegree :=
    natDegree_numDenomWronskian_lt hn0 hd0 hW

  have hcoeff : (placeInfty K).ord (ratFuncDXCoeff K g)
      = 2 * (g.denom.natDegree : ℤ)
        - (g.num.derivative * g.denom - g.num * g.denom.derivative).natDegree := by
    rw [ratFuncDXCoeff_def, ord_placeInfty (div_ne_zero hW' (pow_ne_zero 2 hd')),
      RatFunc.intDegree_div hW' (pow_ne_zero 2 hd'), RatFunc.intDegree_polynomial,
      ← map_pow, RatFunc.intDegree_polynomial, Polynomial.natDegree_pow]
    push_cast
    ring

  have hgord : (placeInfty K).ord g = (g.denom.natDegree : ℤ) - g.num.natDegree := by
    rw [ord_placeInfty hg, RatFunc.intDegree]
    ring
  rw [hcoeff, hgord]
  omega

theorem exists_dXCoeff_ord_ge_two_of_ord_placeInfty_eq_zero {g : RatFunc K}
    (hg : g ≠ 0) (hord : (placeInfty K).ord g = 0) :
    ∃ e : RatFunc K, (e = 0 ∨ 2 ≤ (placeInfty K).ord e) ∧
      KaehlerDifferential.D K (RatFunc K) g = e • dX K := by

  have hmem : RatFunc.inftyValuation K g ≤ 1 := by
    have h1 : g ∈ (placeInfty K).toValuationSubring :=
      (placeInfty K).mem_of_ord_nonneg hg hord.symm.le
    rwa [placeInfty_toValuationSubring, Valuation.mem_valuationSubring_iff] at h1

  obtain ⟨c, hc⟩ := exists_sub_algebraMap_intDegree_neg K hmem

  have hDg : KaehlerDifferential.D K (RatFunc K) g
      = KaehlerDifferential.D K (RatFunc K) (g - algebraMap K (RatFunc K) c) := by
    rw [map_sub, Derivation.map_algebraMap (KaehlerDifferential.D K (RatFunc K)) c, sub_zero]
  rcases hc with hc0 | hcneg
  ·
    exact ⟨0, Or.inl rfl, by rw [hDg, hc0, _root_.map_zero, zero_smul]⟩
  ·
    have hg₁0 : g - algebraMap K (RatFunc K) c ≠ 0 := by
      intro h0
      rw [h0] at hcneg
      simp at hcneg
    refine ⟨ratFuncDXCoeff K (g - algebraMap K (RatFunc K) c), ?_,
      by rw [hDg, D_eq_ratFuncDXCoeff_smul_dX]⟩
    rcases eq_or_ne (ratFuncDXCoeff K (g - algebraMap K (RatFunc K) c)) 0 with h0 | h0
    · exact Or.inl h0
    · refine Or.inr ?_
      have hW := wronskian_ne_zero_of_ratFuncDXCoeff_ne_zero K h0
      have hge := ord_placeInfty_ratFuncDXCoeff_ge hg₁0 hW
      have hord₁ : 1 ≤ (placeInfty K).ord (g - algebraMap K (RatFunc K) c) := by
        rw [ord_placeInfty hg₁0]
        omega
      omega

theorem exists_unit_dXCoeff_of_ord_placeInfty_eq_neg_one {h : RatFunc K}
    (hh : h ≠ 0) (hord : (placeInfty K).ord h = -1) :
    ∃ b : RatFunc K, b ≠ 0 ∧ (placeInfty K).ord b = 0 ∧
      KaehlerDifferential.D K (RatFunc K) h = b • dX K := by
  have hX : (RatFunc.X : RatFunc K) ≠ 0 := RatFunc.X_ne_zero
  have hXinv : (RatFunc.X : RatFunc K)⁻¹ ≠ 0 := inv_ne_zero hX

  have hg0 : h * (RatFunc.X : RatFunc K)⁻¹ ≠ 0 := mul_ne_zero hh hXinv
  have hordg : (placeInfty K).ord (h * (RatFunc.X : RatFunc K)⁻¹) = 0 := by
    rw [(placeInfty K).ord_mul hh hXinv, (placeInfty K).ord_inv, ord_placeInfty_X, hord]
    ring
  obtain ⟨e, he, hDe⟩ := exists_dXCoeff_ord_ge_two_of_ord_placeInfty_eq_zero hg0 hordg

  have hh_eq : h = h * (RatFunc.X : RatFunc K)⁻¹ * RatFunc.X := by
    rw [mul_assoc, inv_mul_cancel₀ hX, mul_one]
  have hDh : KaehlerDifferential.D K (RatFunc K) h
      = (h * (RatFunc.X : RatFunc K)⁻¹ + RatFunc.X * e) • dX K := by
    conv_lhs => rw [hh_eq]
    rw [Derivation.leibniz, hDe, smul_smul,
      show KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K) = dX K from rfl,
      ← add_smul]
  rcases he with rfl | he2
  ·
    refine ⟨h * (RatFunc.X : RatFunc K)⁻¹ + RatFunc.X * 0, ?_, ?_, hDh⟩
    · rw [mul_zero, add_zero]
      exact hg0
    · rw [mul_zero, add_zero]
      exact hordg
  ·
    have he0 : e ≠ 0 := by
      intro h0
      rw [h0, (placeInfty K).ord_zero] at he2
      omega
    have hXe0 : (RatFunc.X : RatFunc K) * e ≠ 0 := mul_ne_zero hX he0
    have hlt : (placeInfty K).ord (h * (RatFunc.X : RatFunc K)⁻¹)
        < (placeInfty K).ord ((RatFunc.X : RatFunc K) * e) := by
      rw [hordg, (placeInfty K).ord_mul hX he0, ord_placeInfty_X]
      omega
    refine ⟨h * (RatFunc.X : RatFunc K)⁻¹ + RatFunc.X * e, ?_, ?_, hDh⟩
    ·
      intro hsum
      have hXe_eq : (RatFunc.X : RatFunc K) * e = -(h * (RatFunc.X : RatFunc K)⁻¹) := by
        linear_combination hsum
      rw [hXe_eq, (placeInfty K).ord_neg] at hlt
      exact lt_irrefl _ hlt
    · rw [(placeInfty K).ord_add_eq_left hg0 hXe0 hlt]
      exact hordg

theorem exists_dXCoeff_ord_two_of_ord_placeInfty_eq_one {f : RatFunc K}
    (hf : f ≠ 0) (hord : (placeInfty K).ord f = 1) :
    ∃ e : RatFunc K, e ≠ 0 ∧ (placeInfty K).ord e = 2 ∧
      KaehlerDifferential.D K (RatFunc K) f = e • dX K := by

  have hf' : f⁻¹ ≠ 0 := inv_ne_zero hf
  have hord' : (placeInfty K).ord f⁻¹ = -1 := by
    rw [(placeInfty K).ord_inv, hord]
  obtain ⟨b, hb0, hbord, hDb⟩ := exists_unit_dXCoeff_of_ord_placeInfty_eq_neg_one hf' hord'
  refine ⟨-(f ^ 2 * b), neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero 2 hf) hb0), ?_, ?_⟩
  · rw [(placeInfty K).ord_neg, (placeInfty K).ord_mul (pow_ne_zero 2 hf) hb0, hbord,
      add_zero, ← zpow_natCast, (placeInfty K).ord_zpow, hord]
    norm_num
  ·
    conv_lhs => rw [← inv_inv f]
    rw [(KaehlerDifferential.D K (RatFunc K)).leibniz_inv f⁻¹, hDb, inv_inv, smul_smul,
      neg_mul]

end PlaceInftySide


section Glue

variable {K : Type*} [Field K]

theorem exists_ord_zero_smul_of_smul_dX_eq {v : Place K (RatFunc K)} {π π' c c' : RatFunc K}
    (hc : c ≠ 0) (hc' : c' ≠ 0) (hord : v.ord c' = v.ord c)
    (hD : KaehlerDifferential.D K (RatFunc K) π = c • dX K)
    (hD' : KaehlerDifferential.D K (RatFunc K) π' = c' • dX K) :
    ∃ u : RatFunc K, v.ord u = 0 ∧
      KaehlerDifferential.D K (RatFunc K) π' = u • KaehlerDifferential.D K (RatFunc K) π := by
  refine ⟨c' / c, ?_, ?_⟩
  · rw [div_eq_mul_inv, v.ord_mul hc' (inv_ne_zero hc), v.ord_inv, hord]
    ring
  · rw [hD, hD', smul_smul, div_mul_cancel₀ _ hc]

end Glue


theorem ordDifferentialWellDefined_ratFunc (K : Type*) [Field K] [CharZero K] :
    OrdDifferentialWellDefined K (RatFunc K) := by
  classical
  intro v π π' hπ hπ'

  have hπ0 : π ≠ 0 := by
    intro h
    rw [h, v.ord_zero] at hπ
    exact zero_ne_one hπ
  have hπ'0 : π' ≠ 0 := by
    intro h
    rw [h, v.ord_zero] at hπ'
    exact zero_ne_one hπ'

  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
  ·
    obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
    obtain ⟨h1ne, h1ord⟩ :=
      ratFuncDXCoeff_ne_zero_and_ord_eq_zero_of_ord_eq_one hp hwp hp.separable hπ0 hπ
    obtain ⟨h2ne, h2ord⟩ :=
      ratFuncDXCoeff_ne_zero_and_ord_eq_zero_of_ord_eq_one hp hwp hp.separable hπ'0 hπ'
    exact exists_ord_zero_smul_of_smul_dX_eq h1ne h2ne (h2ord.trans h1ord.symm)
      (D_eq_ratFuncDXCoeff_smul_dX K π) (D_eq_ratFuncDXCoeff_smul_dX K π')
  ·
    obtain ⟨e, he0, heord, hDe⟩ := exists_dXCoeff_ord_two_of_ord_placeInfty_eq_one hπ0 hπ
    obtain ⟨e', he'0, he'ord, hDe'⟩ := exists_dXCoeff_ord_two_of_ord_placeInfty_eq_one hπ'0 hπ'
    exact exists_ord_zero_smul_of_smul_dX_eq he0 he'0 (he'ord.trans heord.symm) hDe hDe'

section ConsumerGates

variable (K : Type*) [Field K] [CharZero K] [DecidableEq (RatFunc K)]
variable [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

end ConsumerGates


section NonVacuity

variable (K : Type*) [Field K]

end NonVacuity


end AlgebraicCurve


section AxiomAudit

end AxiomAudit


end

end


end


section
section

noncomputable section

open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.WithZero
open _root_.Module
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Module
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsLocalRing
open _root_.Module.IsLocalRing

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq)

open _root_.AlgebraicCurve

open scoped _root_.Polynomial _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial

open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]

variable (K)

theorem two_le_ord_placeInfty_p1PrincipalPartAtom
    {p : K[X]} (hp : Irreducible p) {c : K[X]} (hc : c ≠ 0) {m : ℕ}
    (hdeg : c.degree < p.degree) (hm : 2 ≤ m) :
    2 ≤ (placeInfty K).ord (p1PrincipalPartAtom K p c m) := by
  rw [ord_placeInfty_p1PrincipalPartAtom K hp.ne_zero hc]
  have hndeg : c.natDegree < p.natDegree :=
    Polynomial.natDegree_lt_natDegree hc hdeg
  have hpdeg : 1 ≤ (p.natDegree : ℤ) := by exact_mod_cast hp.natDegree_pos
  have hm' : 2 ≤ (m : ℤ) := by exact_mod_cast hm
  nlinarith

section InftyVanish

variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]

end InftyVanish


omit [DecidableEq (RatFunc K)] in

theorem not_dvd_of_degree_lt {p c : K[X]} (hc : c ≠ 0)
    (hdeg : c.degree < p.degree) : ¬ p ∣ c :=
  fun hdvd => not_lt.mpr (Polynomial.degree_le_of_dvd hdvd hc) hdeg

omit [DecidableEq (RatFunc K)] in

theorem ord_finitePlace_of_degree_lt {p : K[X]} (hp : Irreducible p) {c : K[X]} (hc : c ≠ 0)
    (hdeg : c.degree < p.degree) :
    (finitePlace K hp).ord (algebraMap K[X] (RatFunc K) c) = 0 :=
  not_ne_iff.mp fun h =>
    not_dvd_of_degree_lt K hc hdeg ((ord_finitePlace_ne_zero_iff K hp hc).mp h)

omit [DecidableEq (RatFunc K)] in

theorem ord_finitePlace_p1PrincipalPartAtom {p : K[X]} (hp : Irreducible p)
    {c : K[X]} (hc : c ≠ 0) (hdeg : c.degree < p.degree) (m : ℕ) :
    (finitePlace K hp).ord (p1PrincipalPartAtom K p c m) = -(m : ℤ) := by
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  have hp' : algebraMap K[X] (RatFunc K) p ≠ 0 := (map_ne_zero_iff _ hinj).mpr hp.ne_zero
  have hc' : algebraMap K[X] (RatFunc K) c ≠ 0 := (map_ne_zero_iff _ hinj).mpr hc
  unfold p1PrincipalPartAtom
  rw [div_eq_mul_inv, (finitePlace K hp).ord_mul hc' (inv_ne_zero (pow_ne_zero m hp')),
    (finitePlace K hp).ord_inv, ← zpow_natCast, (finitePlace K hp).ord_zpow,
    ord_finitePlace_of_degree_lt K hp hc hdeg, ord_finitePlace_self K hp]
  ring

section NamedSubrow

variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]

end NamedSubrow


section MOneReduction

variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]

variable {K}

end MOneReduction


section ComposedEngine

variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]

variable {K}

end ComposedEngine


section UnitFinite

variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]

def P1DifferentialCoeffUnitFinite {ω₀ : Ω[(RatFunc K)⁄K]} (_hω₀ : ω₀ ≠ 0) : Prop :=
  ∀ v : Place K (RatFunc K), v ≠ placeInfty K → v.ord (v.differentialCoeff ω₀) = 0

variable {K}

omit [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
  [Nontrivial Ω[(RatFunc K)⁄K]] [HasPrincipalDivisors K (RatFunc K)] in

theorem p1DifferentialCoeffRegularFinite_of_unitFinite
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0)
    (hunit : P1DifferentialCoeffUnitFinite K hω₀) :
    P1DifferentialCoeffRegularFinite K hω₀ :=
  fun v hv => v.mem_of_ord_nonneg (v.differentialCoeff_ne_zero hω₀) (hunit v hv).ge

end UnitFinite


end AlgebraicCurve


section AxiomAudit

end AxiomAudit


end


end


end


section
section

noncomputable section

open _root_.IntermediateField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IntermediateField
open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve
open _root_.Polynomial
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial
open _root_.TensorProduct
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.TensorProduct
open _root_.Module
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Module

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq)

open _root_.AlgebraicCurve

variable (K : Type*) [Field K]

def kaehlerPolynomialBasis : Basis Unit K[X] Ω[K[X]⁄K] :=
  (Basis.singleton Unit K[X]).map (KaehlerDifferential.polynomialEquiv K).symm

scoped instance instFormallyEtalePolynomialRatFunc : Algebra.FormallyEtale K[X] (RatFunc K) :=
  Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors K[X])

def kaehlerRatFuncBasis : Basis Unit (RatFunc K) Ω[(RatFunc K)⁄K] :=
  ((kaehlerPolynomialBasis K).baseChange (RatFunc K)).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K K[X] (RatFunc K))

theorem kaehlerRankOne_ratFunc : KaehlerRankOne K (RatFunc K) :=
  ⟨Module.Free.of_basis (kaehlerRatFuncBasis K),
    (Module.finrank_eq_card_basis (kaehlerRatFuncBasis K)).trans (by simp)⟩

scoped instance instIsCurveOverRatFunc : IsCurveOver K (RatFunc K) :=
  RationalFunctionField.isCurveOver_of_kaehlerRankOne K (kaehlerRankOne_ratFunc K)

variable {F : Type*} [Field F] [Algebra K F]

variable {K}

variable (K F)

variable {K F}

end AlgebraicCurve


namespace ModularCurve

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]

end ModularCurve


end

end


end


section
section

@[expose] public section

noncomputable section

open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.WithZero
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsLocalRing

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq)

open _root_.AlgebraicCurve

namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_ne_zero adicValuation_coe_eq_one_iff adicValuation_coe_irreducible ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ord_smul ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring mk.injEq rec ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk adicValuation_valuationSubring mem_iff_adicValuation_le_one isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one isEquiv_adicValuation_ofHeightOneSpectrum ord_ofHeightOneSpectrum_ne_zero_iff dCoord DCoordGenerates dCoord_ne_zero differentialCoeff differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_dCoord differentialCoeff_zero differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg deg_restrict_mul_inertiaDeg ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq)

open _root_.AlgebraicCurve.Place

attribute [local instance 0] valuationSubringAlgebra

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

theorem sum_ramificationIndex_mul_inertiaDeg_of_forall_mem_iff
    (v : Place K F) (s : Finset (Place K F'))
    (hs : ∀ w : Place K F', w ∈ s ↔ w.restrict F = v) :
    ∑ w ∈ s, (w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ)
      = (Module.finrank F F' : ℤ) := by
  classical
  have hkey := Ideal.sum_ramification_inertia (integralClosureAt F' v) F F'
    (p := IsLocalRing.maximalIdeal v.toValuationSubring) (maximalIdeal_ne_bot v)
  rw [← hkey]
  push_cast
  refine Finset.sum_bij
    (fun w hw => (fiberCenter F' v ((hs w).mp hw)).asIdeal) ?_ ?_ ?_ ?_
  ·
    intro w hw
    rw [IsDedekindDomain.mem_primesOverFinset_iff (maximalIdeal_ne_bot v)]
    exact ⟨(fiberCenter F' v ((hs w).mp hw)).isPrime,
      fiberCenter_liesOver ((hs w).mp hw)⟩
  ·
    intro w hw w' hw' h
    exact eq_of_fiberCenter_eq ((hs w).mp hw) ((hs w').mp hw')
      (HeightOneSpectrum.ext h)
  ·
    intro P hP
    rw [IsDedekindDomain.mem_primesOverFinset_iff (maximalIdeal_ne_bot v)] at hP
    obtain ⟨hP1, hP2⟩ := hP
    have hPne : P ≠ ⊥ := by
      intro h
      apply maximalIdeal_ne_bot v
      have h2 := hP2.over
      rw [h, Ideal.under_def, Ideal.comap_bot_of_injective _
        (algebraMap_integralClosureAt_injective v)] at h2
      exact h2
    refine ⟨placeOfPrime ⟨P, hP1, hPne⟩,
      (hs _).mpr (restrict_placeOfPrime ⟨P, hP1, hPne⟩), ?_⟩
    exact congrArg HeightOneSpectrum.asIdeal
      (fiberCenter_placeOfPrime (⟨P, hP1, hPne⟩ :
        HeightOneSpectrum (integralClosureAt F' v)))
  ·
    intro w hw
    rw [ramificationIndex_eq_ramificationIdx_fiberCenter ((hs w).mp hw),
      inertiaDeg_eq_inertiaDeg_fiberCenter ((hs w).mp hw)]

theorem sum_ramificationIndex_mul_deg_of_forall_mem_iff
    (v : Place K F) (s : Finset (Place K F'))
    (hs : ∀ w : Place K F', w ∈ s ↔ w.restrict F = v) :
    ∑ w ∈ s, (w.ramificationIndex F : ℤ) * (w.deg : ℤ)
      = (Module.finrank F F' : ℤ) * (v.deg : ℤ) := by
  have hsum := sum_ramificationIndex_mul_inertiaDeg_of_forall_mem_iff v s hs
  calc ∑ w ∈ s, (w.ramificationIndex F : ℤ) * (w.deg : ℤ)
      = ∑ w ∈ s, (v.deg : ℤ) * ((w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ)) := by
        refine Finset.sum_congr rfl fun w hw => ?_
        have hdeg : (w.restrict F).deg * w.inertiaDeg F = w.deg :=
          deg_restrict_mul_inertiaDeg (K := K) (F := F) (w := w)
        rw [(hs w).mp hw] at hdeg
        rw [← hdeg]
        push_cast
        ring
    _ = (v.deg : ℤ) * ∑ w ∈ s, (w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ) := by
        rw [Finset.mul_sum]
    _ = (Module.finrank F F' : ℤ) * (v.deg : ℤ) := by rw [hsum]; ring

end Place


theorem ramificationInertiaIdentity_of_finiteDimensional
    (K F F' : Type*) [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F'] :
    RamificationInertiaIdentity K F F' := fun v s hs =>
  Place.sum_ramificationIndex_mul_deg_of_forall_mem_iff v s hs

namespace RationalFunctionField

export _root_.AlgebraicCurve.RationalFunctionField (heightOneSpectrumOfIrreducible heightOneSpectrumOfIrreducible_asIdeal exists_irreducible_span finitePlace finitePlace_def algebraMap_mem_ofHeightOneSpectrum residueFieldEquivOfHeightOneSpectrum deg_ofHeightOneSpectrum deg_finitePlace)

open _root_.AlgebraicCurve.RationalFunctionField

variable {K : Type*} [Field K] {F' : Type*} [Field F'] [Algebra K F']
  [Algebra (RatFunc K) F'] [IsScalarTower K (RatFunc K) F']
  [FiniteDimensional (RatFunc K) F'] [Algebra.IsSeparable (RatFunc K) F']

scoped instance (priority := 50) instHasPrincipalDivisorsOfIsGalois [IsGalois (RatFunc K) F'] :
    HasPrincipalDivisors K F' :=
  hasPrincipalDivisors_of_isGalois
    (ramificationInertiaIdentity_of_finiteDimensional K (RatFunc K) F')

section GaloisClosure

variable (F'' : Type*) [Field F''] [Algebra K F''] [Algebra (RatFunc K) F'']
  [Algebra F' F''] [IsScalarTower K (RatFunc K) F''] [IsScalarTower K F' F'']
  [FiniteDimensional (RatFunc K) F''] [Algebra.IsSeparable (RatFunc K) F'']
  [IsGalois (RatFunc K) F''] [FiniteDimensional F' F'']

end GaloisClosure


end RationalFunctionField


end AlgebraicCurve


end

end


end


section
section

noncomputable section

open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.WithZero
open _root_.Module
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Module
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsLocalRing
open _root_.Module.IsLocalRing
open _root_.Polynomial
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq)

open _root_.AlgebraicCurve

open scoped _root_.Polynomial _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial
open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)]

section SurjectiveDegOne

end SurjectiveDegOne


section PCoordinateIdentity

variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

omit [DecidableEq (RatFunc K)]
  [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]] in

theorem derivative_monic_natDegree_one_eq_one {p : K[X]} (hpmon : p.Monic)
    (hdeg : p.natDegree = 1) : derivative p = 1 := by
  rw [hpmon.eq_X_add_C hdeg, derivative_add, derivative_X, derivative_C, add_zero]

omit [DecidableEq (RatFunc K)]
  [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]] in

theorem D_algebraMap_polynomial_degOne {p : K[X]} (hpmon : p.Monic) (hdeg : p.natDegree = 1) :
    KaehlerDifferential.D K (RatFunc K) (algebraMap K[X] (RatFunc K) p) = dX K := by
  rw [D_algebraMap_polynomial K p, derivative_monic_natDegree_one_eq_one K hpmon hdeg, map_one,
    one_smul]

omit [DecidableEq (RatFunc K)]
  [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]] in

theorem eq_C_coeff_zero_of_degree_lt_degOne {p c : K[X]} (hpirr : Irreducible p)
    (hdeg : p.natDegree = 1) (hcdeg : c.degree < p.degree) : c = C (c.coeff 0) := by
  have hpdeg : p.degree = (1 : ℕ) := by
    rw [degree_eq_natDegree hpirr.ne_zero, hdeg]
  rw [hpdeg, Nat.cast_one] at hcdeg
  exact eq_C_of_degree_le_zero (Nat.WithBot.lt_one_iff_le_zero.mp hcdeg)

omit [DecidableEq (RatFunc K)]
  [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]] in

theorem p1PrincipalPartAtom_mul_differentialCoeff_dX_degOne
    {p c : K[X]} (hpmon : p.Monic) (hpirr : Irreducible p) (hdeg : p.natDegree = 1)
    (hcdeg : c.degree < p.degree) (m : ℕ) :
    p1PrincipalPartAtom K p c m * (finitePlace K hpirr).differentialCoeff (dX K)
      = c.coeff 0 • ((finitePlace K hpirr).differentialCoeff
            (KaehlerDifferential.D K (RatFunc K) (algebraMap K[X] (RatFunc K) p))
          * ((algebraMap K[X] (RatFunc K) p) ^ m)⁻¹) := by
  have hc : algebraMap K[X] (RatFunc K) c = algebraMap K (RatFunc K) (c.coeff 0) := by
    conv_lhs => rw [eq_C_coeff_zero_of_degree_lt_degOne K hpirr hdeg hcdeg]
    rw [C_eq_algebraMap, ← IsScalarTower.algebraMap_apply K K[X] (RatFunc K)]
  rw [D_algebraMap_polynomial_degOne K hpmon hdeg, Algebra.smul_def,
    show p1PrincipalPartAtom K p c m
      = algebraMap K[X] (RatFunc K) c / (algebraMap K[X] (RatFunc K) p) ^ m from rfl, hc]
  ring

end PCoordinateIdentity


section NamedHigherDeg

variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

def P1FinitePlaceCanonicalResidueAtomMGeTwoHigherDeg : Prop :=
  ∀ (p c : K[X]) (m : ℕ) (_ : p.Monic) (hpirr : Irreducible p),
    c.degree < p.degree → 2 ≤ m → 2 ≤ p.natDegree →
    ∀ R : (finitePlace K hpirr).CanonicalLocalResidueDataK,
      R.res (p1PrincipalPartAtom K p c m * (finitePlace K hpirr).differentialCoeff (dX K)) = 0

end NamedHigherDeg


section DegOneDischarge

variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

omit [DecidableEq (RatFunc K)]
  [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]] in

theorem p1FinitePlaceCanonicalResidueAtom_of_coordIndep_degOne
    (hcoord : CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K))
    {p c : K[X]} {m : ℕ} (hpmon : p.Monic) (hpirr : Irreducible p)
    (hcdeg : c.degree < p.degree) (hm : 2 ≤ m) (hdeg : p.natDegree = 1)
    (R : (finitePlace K hpirr).CanonicalLocalResidueDataK) :
    R.res (p1PrincipalPartAtom K p c m * (finitePlace K hpirr).differentialCoeff (dX K)) = 0 := by
  rw [p1PrincipalPartAtom_mul_differentialCoeff_dX_degOne K hpmon hpirr hdeg hcdeg m, map_smul,
    show m = (m - 1) + 1 from (Nat.sub_add_cancel (by omega)).symm,
    hcoord (finitePlace K hpirr) (algebraMap K[X] (RatFunc K) p) (ord_finitePlace_self K hpirr)
      R (m - 1) (by omega),
    smul_zero]

end DegOneDischarge


section ComposedEngine

variable [CharZero K]
variable [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

end ComposedEngine


section AlgClosed

variable [IsAlgClosed K]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

omit [DecidableEq (RatFunc K)]
  [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]] in

theorem p1FinitePlaceCanonicalResidueAtomMGeTwoHigherDeg_of_algClosed :
    P1FinitePlaceCanonicalResidueAtomMGeTwoHigherDeg K := by
  intro p c m _ hpirr _ _ hdeg
  have h1 : p.natDegree = 1 := by
    have h := IsAlgClosed.degree_eq_one_of_irreducible K hpirr
    rw [degree_eq_natDegree hpirr.ne_zero] at h
    exact_mod_cast h
  omega

end AlgClosed


end AlgebraicCurve


section AxiomAudit

end AxiomAudit


end


end


end


section
section

open _root_.CongruenceSubgroup
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.CongruenceSubgroup
open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.WithZero
open _root_.Polynomial
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsLocalRing

namespace ValuationSubring

export _root_.ValuationSubring (comap idealOfLE mem_comap neg_mem prime_idealOfLE toSubring algebraMap_apply ext zero_mem ofPrime_top rec mem_nonunits_iff ofPrime mk mem_or_inv_mem' mem_top instIsDomainSubtypeMem toSubring_injective mul_mem one_mem mem_or_inv_mem mk.injEq add_mem eq_top_iff valuation inclusion ofPrime_idealOfLE ofPrime_bot)

open _root_.ValuationSubring

variable {F : Type*} [Field F]

theorem ofPrime_congr {R : ValuationSubring F} {P Q : Ideal R}
    [P.IsPrime] [Q.IsPrime] (h : P = Q) : R.ofPrime P = R.ofPrime Q := by
  subst h; congr

theorem eq_top_of_idealOfLE_eq_bot {R S : ValuationSubring F} (h : R ≤ S)
    (hbot : idealOfLE R S h = ⊥) : S = ⊤ := by
  haveI : IsDomain R := Subring.instIsDomainSubtypeMem R.toSubring
  rw [← ofPrime_idealOfLE R S h, ofPrime_congr hbot, ofPrime_bot]

theorem idealOfLE_ne_bot_of_ne_top {R S : ValuationSubring F} (h : R ≤ S)
    (hS : S ≠ ⊤) : idealOfLE R S h ≠ ⊥ :=
  fun hbot => hS (eq_top_of_idealOfLE_eq_bot h hbot)

theorem eq_of_isDiscreteValuationRing_of_le {R S : ValuationSubring F}
    [IsDiscreteValuationRing R] (h : R ≤ S) (hS : S ≠ ⊤) : R = S := by

  haveI : IsDomain R := Subring.instIsDomainSubtypeMem R.toSubring
  haveI : IsDedekindDomain R := IsPrincipalIdealRing.isDedekindDomain R

  have hne : idealOfLE R S h ≠ ⊥ := idealOfLE_ne_bot_of_ne_top h hS
  have hmax : (idealOfLE R S h).IsMaximal := (prime_idealOfLE R S h).isMaximal hne
  have heq : idealOfLE R S h = IsLocalRing.maximalIdeal R := IsLocalRing.eq_maximalIdeal hmax
  rw [← ofPrime_idealOfLE R S h, ofPrime_congr heq, ofPrime_top]

end ValuationSubring


namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq)

open _root_.AlgebraicCurve

namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_ne_zero adicValuation_coe_eq_one_iff adicValuation_coe_irreducible ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ord_smul ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring mk.injEq rec ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk adicValuation_valuationSubring mem_iff_adicValuation_le_one isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one isEquiv_adicValuation_ofHeightOneSpectrum ord_ofHeightOneSpectrum_ne_zero_iff dCoord DCoordGenerates dCoord_ne_zero differentialCoeff differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_dCoord differentialCoeff_zero differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg deg_restrict_mul_inertiaDeg ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq)

open _root_.AlgebraicCurve.Place

section CenterIdeal

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

variable (A : Subalgebra K F) (hA : (A : Set F) ⊆ (v.toValuationSubring : Set F))

@[reducible] noncomputable def _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.modelInclusion : A →+* v.toValuationSubring :=
  (Subring.inclusion (show A.toSubring ≤ v.toValuationSubring.toSubring from hA))


-- RRSplit attribute-prefixed source-private field bridge.
private noncomputable abbrev _root_.AlgebraicCurve.Place.modelInclusion :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.modelInclusion


@[scoped simp] theorem coe_modelInclusion (a : A) :
    ((v.modelInclusion A hA a : v.toValuationSubring) : F) = (a : F) := rfl

@[reducible] noncomputable def _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.modelAlgebra : Algebra A v.toValuationSubring :=
  (v.modelInclusion A hA).toAlgebra


-- RRSplit attribute-prefixed source-private field bridge.
private noncomputable abbrev _root_.AlgebraicCurve.Place.modelAlgebra :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.modelAlgebra


@[reducible] noncomputable def _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.centerIdeal : Ideal A :=
  letI := v.modelAlgebra A hA
  (IsLocalRing.maximalIdeal v.toValuationSubring).comap (algebraMap A v.toValuationSubring)


-- RRSplit attribute-prefixed source-private field bridge.
private noncomputable abbrev _root_.AlgebraicCurve.Place.centerIdeal :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.centerIdeal


scoped instance centerIdeal_isPrime : (v.centerIdeal A hA).IsPrime :=
  letI := v.modelAlgebra A hA
  Ideal.comap_isPrime _ _

theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.isUnit_modelInclusion_of_not_mem_centerIdeal {s : A}
    (hs : s ∉ v.centerIdeal A hA) :
    IsUnit (v.modelInclusion A hA s) := by
  letI := v.modelAlgebra A hA

  change s ∉ _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.centerIdeal v A hA at hs
  unfold _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.centerIdeal at hs
  rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    not_not] at hs
  exact hs




-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.isUnit_modelInclusion_of_not_mem_centerIdeal :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.isUnit_modelInclusion_of_not_mem_centerIdeal
theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.isUnit_modelInclusion_of_mem_primeCompl (s : (v.centerIdeal A hA).primeCompl) :
    IsUnit (v.modelInclusion A hA (s : A)) :=
  v.isUnit_modelInclusion_of_not_mem_centerIdeal A hA s.2




-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.isUnit_modelInclusion_of_mem_primeCompl :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.isUnit_modelInclusion_of_mem_primeCompl
theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.modelAlgebra_isScalarTower :
    letI := v.modelAlgebra A hA
    IsScalarTower K A v.toValuationSubring := by
  letI := v.modelAlgebra A hA
  refine IsScalarTower.of_algebraMap_eq fun c => ?_
  apply Subtype.ext
  simp only [coe_modelInclusion, RingHom.algebraMap_toAlgebra]
  rfl




-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.modelAlgebra_isScalarTower :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.modelAlgebra_isScalarTower
theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.essFiniteType_of_finiteType_isLocalization_centerIdeal
    [Algebra.FiniteType K A]
    (hloc : letI := v.modelAlgebra A hA
            IsLocalization.AtPrime v.toValuationSubring (v.centerIdeal A hA)) :
    Algebra.EssFiniteType K v.toValuationSubring := by
  letI := v.modelAlgebra A hA
  haveI := v.modelAlgebra_isScalarTower A hA
  haveI : Algebra.EssFiniteType A v.toValuationSubring :=
    Algebra.EssFiniteType.of_isLocalization _ (v.centerIdeal A hA).primeCompl
  exact Algebra.EssFiniteType.comp K A v.toValuationSubring




-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.essFiniteType_of_finiteType_isLocalization_centerIdeal :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.essFiniteType_of_finiteType_isLocalization_centerIdeal
end CenterIdeal


end Place


variable (K F : Type*) [Field K] [Field F] [Algebra K F]

def ValSubringDedekindModel : Prop :=
  ∀ v : Place K F,
    ∃ (A : Subalgebra K F) (hA : (A : Set F) ⊆ (v.toValuationSubring : Set F)),
      Algebra.FiniteType K A ∧
      (letI := v.modelAlgebra A hA
       IsLocalization.AtPrime v.toValuationSubring (v.centerIdeal A hA))

variable {K F}

theorem valSubringEssFiniteType_of_dedekindModel
    (hmodel : ValSubringDedekindModel K F) :
    ValSubringEssFiniteType K F := fun v => by
  obtain ⟨A, hA, hft, hloc⟩ := hmodel v
  exact v.essFiniteType_of_finiteType_isLocalization_centerIdeal A hA hloc

theorem valSubringKaehlerFinite_of_dedekindModel
    (hmodel : ValSubringDedekindModel K F) :
    ValSubringKaehlerFinite K F :=
  valSubringKaehlerFinite_of_essFiniteType
    (valSubringEssFiniteType_of_dedekindModel hmodel)

end AlgebraicCurve


namespace ModularCurve

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve

variable (N : ℕ) [NeZero N]

end ModularCurve


namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq)

open _root_.AlgebraicCurve

end AlgebraicCurve


namespace ModularCurve

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve

end ModularCurve


end


end


section
section

set_option maxHeartbeats 6400000

open _root_.Polynomial
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsLocalRing
open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve
open ModularCurve.Lg37 ModularCurve.KwNo6Section ModularCurve.KwNo6Pin
open Mp72a102T1

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq)

open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem completionSection_nonempty_generic (v : Place K F)
    [FiniteDimensional K v.ResidueField] [Algebra.IsSeparable K v.ResidueField] :
    Nonempty (Lg37CompletionSection v) := by
  obtain ⟨ᾱ, htop⟩ := Field.exists_primitive_element K v.ResidueField
  have hint : _root_.IsIntegral K ᾱ := Algebra.IsIntegral.isIntegral ᾱ
  have hmon : (minpoly K ᾱ).Monic := minpoly.monic hint
  have hsep : (minpoly K ᾱ).Separable := Algebra.IsSeparable.isSeparable K ᾱ
  have haevalbar : (aeval ᾱ) (minpoly K ᾱ) = 0 := minpoly.aeval K ᾱ
  obtain ⟨αhat, hαroot, hαres⟩ :=
    mp72a102_t1_exists_completion_root_of_residue_root v hmon hsep haevalbar
  exact ⟨sectionOfPrimitiveRoot v hint htop αhat hαroot hαres⟩

variable (K F) in

noncomputable scoped instance instHasCanonicalLocalResidueKStar [IsCurveOver K F] [PerfectField K] :
    HasCanonicalLocalResidueKStar K F where
  dataKStar v :=
    haveI : FiniteDimensional K v.ResidueField := Place.FiniteResidue.finite
    haveI : Algebra.IsSeparable K v.ResidueField :=
      Algebra.IsAlgebraic.isSeparable_of_perfectField
    canonicalLocalResidueDataKStar v
      (Classical.choice (completionSection_nonempty_generic v))

end AlgebraicCurve


end


end


section
section

noncomputable section

open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.WithZero
open _root_.Module
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Module
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsLocalRing
open _root_.Module.IsLocalRing
open _root_.KaehlerDifferential
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.KaehlerDifferential
open _root_.Polynomial
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq)

open _root_.AlgebraicCurve

open scoped _root_.Polynomial _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial

open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField

theorem ordDifferentialWellDefined_ratFunc_of_perfectField (K : Type*) [Field K]
    [PerfectField K] :
    OrdDifferentialWellDefined K (RatFunc K) := by
  classical
  intro v π π' hπ hπ'

  have hπ0 : π ≠ 0 := by
    intro h
    rw [h, v.ord_zero] at hπ
    exact zero_ne_one hπ
  have hπ'0 : π' ≠ 0 := by
    intro h
    rw [h, v.ord_zero] at hπ'
    exact zero_ne_one hπ'

  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
  ·

    obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
    obtain ⟨h1ne, h1ord⟩ :=
      ratFuncDXCoeff_ne_zero_and_ord_eq_zero_of_ord_eq_one hp hwp
        (PerfectField.separable_of_irreducible hp) hπ0 hπ
    obtain ⟨h2ne, h2ord⟩ :=
      ratFuncDXCoeff_ne_zero_and_ord_eq_zero_of_ord_eq_one hp hwp
        (PerfectField.separable_of_irreducible hp) hπ'0 hπ'
    exact exists_ord_zero_smul_of_smul_dX_eq h1ne h2ne (h2ord.trans h1ord.symm)
      (D_eq_ratFuncDXCoeff_smul_dX K π) (D_eq_ratFuncDXCoeff_smul_dX K π')
  ·
    obtain ⟨e, he0, heord, hDe⟩ := exists_dXCoeff_ord_two_of_ord_placeInfty_eq_one hπ0 hπ
    obtain ⟨e', he'0, he'ord, hDe'⟩ := exists_dXCoeff_ord_two_of_ord_placeInfty_eq_one hπ'0 hπ'
    exact exists_ord_zero_smul_of_smul_dX_eq he0 he'0 (he'ord.trans heord.symm) hDe hDe'

section ConsumerGates

variable (K : Type*) [Field K] [CharZero K] [DecidableEq (RatFunc K)]
variable [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

end ConsumerGates


end AlgebraicCurve


section AxiomAudit

end AxiomAudit


end

end


end


section
section

noncomputable section

open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.WithZero
open _root_.Module
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Module
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsLocalRing
open _root_.Module.IsLocalRing
open _root_.Polynomial
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq)

open _root_.AlgebraicCurve

open scoped _root_.Polynomial _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial
open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]

section Defect

variable [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]

end Defect


section CorrectedCarrier

variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

end CorrectedCarrier


section CorrectedBridge

variable [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

end CorrectedBridge


section UnitFinite

variable [CharZero K]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

theorem p1DifferentialCoeffUnitFinite_dX :
    P1DifferentialCoeffUnitFinite K (dX_ne_zero K) := by
  intro v hvinf
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
  · obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
    exact ord_differentialCoeff_dX_ofHeightOneSpectrum hp hwp hp.separable
  · exact absurd rfl hvinf

end UnitFinite


section CorrectedEngine

variable [CharZero K]
variable [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

end CorrectedEngine


end AlgebraicCurve


section AxiomAudit

end AxiomAudit


end


end


end


section
section

noncomputable section

open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.WithZero
open _root_.Module
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Module
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsLocalRing
open _root_.Module.IsLocalRing

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq)

open _root_.AlgebraicCurve

open scoped _root_.Polynomial _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial
open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]

section Defect

variable (K)
variable [DecidableEq (RatFunc K)] [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]

end Defect


section CanonicityRow

variable (K F)
variable [HasLocalResidue K F] [HasCanonicalLocalResidueKStar K F]

variable {K F}

end CanonicityRow


section MOneSimplePoleBounds

variable (K)
variable [DecidableEq (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates]

theorem ord_finitePlace_mOneAtom_mul_differentialCoeff
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0)
    (hunit : ∀ v : Place K (RatFunc K), v ≠ placeInfty K → v.ord (v.differentialCoeff ω₀) = 0)
    {p : K[X]} (hp : Irreducible p) {c : K[X]} (hc : c ≠ 0)
    (hdeg : c.degree < p.degree) :
    (finitePlace K hp).ord
        (p1PrincipalPartAtom K p c 1 * (finitePlace K hp).differentialCoeff ω₀) = -1 := by
  have hatom0 : p1PrincipalPartAtom K p c 1 ≠ 0 := by
    simp only [p1PrincipalPartAtom, ne_eq, div_eq_zero_iff, not_or]
    exact ⟨(map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hc,
      pow_ne_zero _ ((map_ne_zero_iff _
        (IsFractionRing.injective K[X] (RatFunc K))).mpr hp.ne_zero)⟩
  rw [(finitePlace K hp).ord_mul hatom0 ((finitePlace K hp).differentialCoeff_ne_zero hω₀),
    ord_finitePlace_p1PrincipalPartAtom K hp hc hdeg 1,
    hunit (finitePlace K hp) (finitePlace_ne_placeInfty hp)]
  norm_num

theorem ord_placeInfty_mOneAtom_mul_differentialCoeff_ge_neg_one
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0)
    (hInfty : (placeInfty K).ordDifferential ω₀ = -2)
    {p : K[X]} (hp : Irreducible p) {c : K[X]} (hc : c ≠ 0)
    (hdeg : c.degree < p.degree) :
    -1 ≤ (placeInfty K).ord
        (p1PrincipalPartAtom K p c 1 * (placeInfty K).differentialCoeff ω₀) := by
  have hatom0 : p1PrincipalPartAtom K p c 1 ≠ 0 := by
    simp only [p1PrincipalPartAtom, ne_eq, div_eq_zero_iff, not_or]
    exact ⟨(map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hc,
      pow_ne_zero _ ((map_ne_zero_iff _
        (IsFractionRing.injective K[X] (RatFunc K))).mpr hp.ne_zero)⟩
  rw [(placeInfty K).ord_mul hatom0 ((placeInfty K).differentialCoeff_ne_zero hω₀)]
  have h1 : 1 ≤ (placeInfty K).ord (p1PrincipalPartAtom K p c 1) :=
    one_le_ord_placeInfty_p1PrincipalPartAtom K hp hc hdeg le_rfl
  have hordD : (placeInfty K).ord ((placeInfty K).differentialCoeff ω₀) = -2 := hInfty
  omega

theorem p1MOneAtom_mul_differentialCoeff_mem_simplePole_finitePlace
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0)
    (hunit : ∀ v : Place K (RatFunc K), v ≠ placeInfty K → v.ord (v.differentialCoeff ω₀) = 0)
    {p : K[X]} (hp : Irreducible p) (c : K[X]) (hdeg : c.degree < p.degree) :
    p1PrincipalPartAtom K p c 1 * (finitePlace K hp).differentialCoeff ω₀
      ∈ (finitePlace K hp).simplePoleSubmodule := by
  rcases eq_or_ne c 0 with rfl | hc
  · show algebraMap K[X] (RatFunc K) 0 / (algebraMap K[X] (RatFunc K) p) ^ 1
        * (finitePlace K hp).differentialCoeff ω₀ ∈ _
    rw [_root_.map_zero, zero_div, zero_mul]; exact zero_mem _
  · have hatom0 : p1PrincipalPartAtom K p c 1 ≠ 0 := by
      simp only [p1PrincipalPartAtom, ne_eq, div_eq_zero_iff, not_or]
      exact ⟨(map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hc,
        pow_ne_zero _ ((map_ne_zero_iff _
          (IsFractionRing.injective K[X] (RatFunc K))).mpr hp.ne_zero)⟩
    have hEq : (finitePlace K hp).poleSubmodule 1 = (finitePlace K hp).simplePoleSubmodule :=
      (finitePlace K hp).poleSubmodule_one
    rw [← hEq, Place.mem_poleSubmodule, pow_one]
    refine (finitePlace K hp).mem_of_ord_nonneg
      (mul_ne_zero (finitePlace K hp).uniformizer_ne_zero
        (mul_ne_zero hatom0 ((finitePlace K hp).differentialCoeff_ne_zero hω₀))) ?_
    rw [(finitePlace K hp).ord_mul (finitePlace K hp).uniformizer_ne_zero
        (mul_ne_zero hatom0 ((finitePlace K hp).differentialCoeff_ne_zero hω₀)),
      (finitePlace K hp).ord_uniformizer,
      ord_finitePlace_mOneAtom_mul_differentialCoeff K hω₀ hunit hp hc hdeg]
    omega

theorem p1MOneAtom_mul_differentialCoeff_mem_simplePole_placeInfty
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0)
    (hInfty : (placeInfty K).ordDifferential ω₀ = -2)
    {p : K[X]} (hp : Irreducible p) (c : K[X]) (hdeg : c.degree < p.degree) :
    p1PrincipalPartAtom K p c 1 * (placeInfty K).differentialCoeff ω₀
      ∈ (placeInfty K).simplePoleSubmodule := by
  rcases eq_or_ne c 0 with rfl | hc
  · show algebraMap K[X] (RatFunc K) 0 / (algebraMap K[X] (RatFunc K) p) ^ 1
        * (placeInfty K).differentialCoeff ω₀ ∈ _
    rw [_root_.map_zero, zero_div, zero_mul]; exact zero_mem _
  · have hatom0 : p1PrincipalPartAtom K p c 1 ≠ 0 := by
      simp only [p1PrincipalPartAtom, ne_eq, div_eq_zero_iff, not_or]
      exact ⟨(map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hc,
        pow_ne_zero _ ((map_ne_zero_iff _
          (IsFractionRing.injective K[X] (RatFunc K))).mpr hp.ne_zero)⟩
    have hEq : (placeInfty K).poleSubmodule 1 = (placeInfty K).simplePoleSubmodule :=
      (placeInfty K).poleSubmodule_one
    rw [← hEq, Place.mem_poleSubmodule, pow_one]
    refine (placeInfty K).mem_of_ord_nonneg
      (mul_ne_zero (placeInfty K).uniformizer_ne_zero
        (mul_ne_zero hatom0 ((placeInfty K).differentialCoeff_ne_zero hω₀))) ?_
    rw [(placeInfty K).ord_mul (placeInfty K).uniformizer_ne_zero
        (mul_ne_zero hatom0 ((placeInfty K).differentialCoeff_ne_zero hω₀)),
      (placeInfty K).ord_uniformizer]
    have h := ord_placeInfty_mOneAtom_mul_differentialCoeff_ge_neg_one K hω₀ hInfty hp hc hdeg
    omega

end MOneSimplePoleBounds


section MOneSimplePoleRow

variable (K)
variable [DecidableEq (RatFunc K)]
variable [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates]

def P1PrincipalPartMOneSimplePoleCancel {ω₀ : Ω[(RatFunc K)⁄K]} (_hω₀ : ω₀ ≠ 0) : Prop :=
  ∀ (p c : K[X]) (_ : p.Monic) (hpirr : Irreducible p), c.degree < p.degree →
    ∀ (hfmem : p1PrincipalPartAtom K p c 1 * (finitePlace K hpirr).differentialCoeff ω₀
        ∈ (finitePlace K hpirr).simplePoleSubmodule)
      (himem : p1PrincipalPartAtom K p c 1 * (placeInfty K).differentialCoeff ω₀
        ∈ (placeInfty K).simplePoleSubmodule),
    Algebra.trace K (finitePlace K hpirr).ResidueField
        ((finitePlace K hpirr).simplePoleResidueAux ⟨_, hfmem⟩)
      + Algebra.trace K (placeInfty K).ResidueField
          ((placeInfty K).simplePoleResidueAux ⟨_, himem⟩)
      = 0

variable {K}

end MOneSimplePoleRow


section CorrectedSubrow2

variable (K)
variable [DecidableEq (RatFunc K)]
variable [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

variable {K}

end CorrectedSubrow2


section NearClose

variable (K)
variable [DecidableEq (RatFunc K)]
variable [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

end NearClose


end AlgebraicCurve


section AxiomAudit

end AxiomAudit


end


end


end


section
section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

open _root_.Polynomial
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial
open _root_.IntermediateField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IntermediateField
open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq)

open _root_.AlgebraicCurve

variable {K : Type*} [Field K]

end AlgebraicCurve


namespace ModularCurve

section Engine

variable {K : Type*} [Field K] {N : ℕ} [NeZero N]

end Engine


section Corollaries

variable (K : Type*) [Field K]

scoped instance instHasPrincipalDivisorsRatFuncSelf : HasPrincipalDivisors K (RatFunc K) :=
  RationalFunctionField.instHasPrincipalDivisorsOfIsGalois

end Corollaries


end ModularCurve


end


end


end

end
end P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed
