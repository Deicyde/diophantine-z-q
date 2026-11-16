/-
Copyright 2026 Anthropic, PBC. Released under Apache License 2.0.
Source: https://github.com/anthropics/fermats-last-theorem
Revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.lean; source lines 7759-9808.
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
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.RRSplit.residueTheoremK_ratFunc_of_isAlgClosed_Part04

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
-- RRSplit attribute-prefixed source-private field bridge.
private noncomputable abbrev _root_.AlgebraicCurve.Place.modelInclusion :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.modelInclusion
-- RRSplit attribute-prefixed source-private field bridge.
private noncomputable abbrev _root_.AlgebraicCurve.Place.modelAlgebra :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.modelAlgebra
-- RRSplit attribute-prefixed source-private field bridge.
private noncomputable abbrev _root_.AlgebraicCurve.Place.centerIdeal :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.centerIdeal


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
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.finite_kaehler_of_essFiniteType :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.finite_kaehler_of_essFiniteType
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.isUnit_modelInclusion_of_not_mem_centerIdeal :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.isUnit_modelInclusion_of_not_mem_centerIdeal
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.isUnit_modelInclusion_of_mem_primeCompl :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.isUnit_modelInclusion_of_mem_primeCompl
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.modelAlgebra_isScalarTower :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.modelAlgebra_isScalarTower
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.essFiniteType_of_finiteType_isLocalization_centerIdeal :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.essFiniteType_of_finiteType_isLocalization_centerIdeal


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

section TraceRow

variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

def P1FinitePlaceCanonicalResidueAtomMGeTwoTrace : Prop :=
  ∀ (p c : K[X]) (m : ℕ) (_ : p.Monic) (hpirr : Irreducible p), c.degree < p.degree → 2 ≤ m →
    ∀ R : (finitePlace K hpirr).CanonicalLocalResidueDataK,
      Algebra.trace K (finitePlace K hpirr).ResidueField
          (R.res (p1PrincipalPartAtom K p c m
            * (finitePlace K hpirr).differentialCoeff (dX K))) = 0

def P1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg : Prop :=
  ∀ (p c : K[X]) (m : ℕ) (_ : p.Monic) (hpirr : Irreducible p),
    c.degree < p.degree → 2 ≤ m → 2 ≤ p.natDegree →
    ∀ R : (finitePlace K hpirr).CanonicalLocalResidueDataK,
      Algebra.trace K (finitePlace K hpirr).ResidueField
          (R.res (p1PrincipalPartAtom K p c m
            * (finitePlace K hpirr).differentialCoeff (dX K))) = 0

end TraceRow


section Monotonicity

variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

omit [DecidableEq (RatFunc K)]
  [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]] in

theorem p1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg_of_higherDeg
    (h : P1FinitePlaceCanonicalResidueAtomMGeTwoHigherDeg K) :
    P1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg K :=
  fun p c m hpmon hpirr hdeg hm hpdeg R => by
    rw [h p c m hpmon hpirr hdeg hm hpdeg R, _root_.map_zero]

end Monotonicity


section DegOneDischarge

variable [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

omit [DecidableEq (RatFunc K)]
  [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]] in

theorem p1FinitePlaceCanonicalResidueAtomTrace_of_coordIndep_degOne
    (hcoord : CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K))
    {p c : K[X]} {m : ℕ} (hpmon : p.Monic) (hpirr : Irreducible p)
    (hcdeg : c.degree < p.degree) (hm : 2 ≤ m) (hdeg : p.natDegree = 1)
    (R : (finitePlace K hpirr).CanonicalLocalResidueDataK) :
    Algebra.trace K (finitePlace K hpirr).ResidueField
        (R.res (p1PrincipalPartAtom K p c m
          * (finitePlace K hpirr).differentialCoeff (dX K))) = 0 := by
  rw [p1FinitePlaceCanonicalResidueAtom_of_coordIndep_degOne K hcoord hpmon hpirr hcdeg hm
    hdeg R, _root_.map_zero]

omit [DecidableEq (RatFunc K)]
  [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]] in

theorem p1FinitePlaceCanonicalResidueAtomMGeTwoTrace_of_coordIndep_higherDeg
    (hcoord : CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K))
    (hHigh : P1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg K) :
    P1FinitePlaceCanonicalResidueAtomMGeTwoTrace K := by
  intro p c m hpmon hpirr hcdeg hm R
  have hpos := hpirr.natDegree_pos
  rcases Nat.lt_or_ge p.natDegree 2 with hdeg | hdeg
  · exact p1FinitePlaceCanonicalResidueAtomTrace_of_coordIndep_degOne K hcoord hpmon hpirr
      hcdeg hm (by omega) R
  · exact hHigh p c m hpmon hpirr hcdeg hm hdeg R

end DegOneDischarge


section TraceBridge

variable [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

end TraceBridge


section ComposedEngine

variable [CharZero K]
variable [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

end ComposedEngine


section AlgClosed

variable [IsAlgClosed K] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

omit [DecidableEq (RatFunc K)]
  [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]] in

theorem p1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg_of_algClosed :
    P1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg K :=
  p1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg_of_higherDeg K
    (p1FinitePlaceCanonicalResidueAtomMGeTwoHigherDeg_of_algClosed K)

end AlgClosed


end AlgebraicCurve


section AxiomAudit

end AxiomAudit


end


end


end


section
section

open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsLocalRing

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq)

open _root_.AlgebraicCurve

namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_ne_zero adicValuation_coe_eq_one_iff adicValuation_coe_irreducible ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ord_smul ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring mk.injEq rec ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk adicValuation_valuationSubring mem_iff_adicValuation_le_one isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one isEquiv_adicValuation_ofHeightOneSpectrum ord_ofHeightOneSpectrum_ne_zero_iff dCoord DCoordGenerates dCoord_ne_zero differentialCoeff differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_dCoord differentialCoeff_zero differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg deg_restrict_mul_inertiaDeg ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq)

open _root_.AlgebraicCurve.Place

section CenterNonzero

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
  (A : Subalgebra K F) (hA : (A : Set F) ⊆ (v.toValuationSubring : Set F))

theorem inv_mem_of_not_mem_centerIdeal {a : A} (ha : a ∉ v.centerIdeal A hA) :
    ((a : F))⁻¹ ∈ v.toValuationSubring := by
  obtain ⟨u, hu⟩ := v.isUnit_modelInclusion_of_not_mem_centerIdeal A hA ha
  have huF : ((u : v.toValuationSubring) : F) = (a : F) :=
    congrArg (Subtype.val : v.toValuationSubring → F) hu
  have huinvF : ((u⁻¹ : v.toValuationSubringˣ).1 : F) * (a : F) = 1 := by
    have h1 : ((u⁻¹ : v.toValuationSubringˣ).1 : F) * ((u : v.toValuationSubring) : F)
        = ((1 : v.toValuationSubring) : F) :=
      congrArg (Subtype.val : v.toValuationSubring → F) u.inv_mul
    rw [huF] at h1; exact h1
  have : ((u⁻¹ : v.toValuationSubringˣ).1 : F) = (a : F)⁻¹ :=
    eq_inv_of_mul_eq_one_left huinvF
  exact this ▸ ((u⁻¹ : v.toValuationSubringˣ).1 : v.toValuationSubring).2

theorem div_mem_of_not_mem_centerIdeal (r : A) {a : A}
    (ha : a ∉ v.centerIdeal A hA) :
    (r : F) / (a : F) ∈ v.toValuationSubring := by
  rw [div_eq_mul_inv]
  exact v.toValuationSubring.toSubring.mul_mem (hA r.2)
    (inv_mem_of_not_mem_centerIdeal v A hA ha)

theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.centerIdeal_ne_bot_of_isFractionRing [IsFractionRing A F] :
    v.centerIdeal A hA ≠ ⊥ := by

  obtain ⟨f, hf⟩ : ∃ f : F, f ∉ v.toValuationSubring := by
    by_contra h; push Not at h
    exact v.ne_top' (ValuationSubring.toSubring_injective (top_le_iff.mp fun x _ => h x))
  obtain ⟨r, s, hs, hfrs⟩ := IsFractionRing.div_surjective (A := A) f

  have hsP : s ∈ v.centerIdeal A hA := by
    by_contra hsP
    apply hf
    have : algebraMap A F r / algebraMap A F s ∈ v.toValuationSubring :=
      div_mem_of_not_mem_centerIdeal v A hA r hsP
    rwa [hfrs] at this

  intro hbot
  exact (nonZeroDivisors.ne_zero hs) (Ideal.mem_bot.mp (hbot ▸ hsP))




-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.centerIdeal_ne_bot_of_isFractionRing :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.centerIdeal_ne_bot_of_isFractionRing
end CenterNonzero


section LocalizationSubalgebra

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
  (A : Subalgebra K F) (hA : (A : Set F) ⊆ (v.toValuationSubring : Set F))

@[reducible] noncomputable def _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.centerLocalizationSubalgebra [IsFractionRing A F] :
    Subalgebra A F :=
  Localization.subalgebra.ofField F (v.centerIdeal A hA).primeCompl
    (v.centerIdeal A hA).primeCompl_le_nonZeroDivisors


-- RRSplit attribute-prefixed source-private field bridge.
private noncomputable abbrev _root_.AlgebraicCurve.Place.centerLocalizationSubalgebra :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.centerLocalizationSubalgebra


scoped instance centerLocalizationSubalgebra_isLocalization [IsFractionRing A F] :
    IsLocalization.AtPrime (v.centerLocalizationSubalgebra A hA) (v.centerIdeal A hA) :=
  Localization.subalgebra.isLocalization_ofField F _ _

scoped instance centerLocalizationSubalgebra_isDomain [IsFractionRing A F] :
    IsDomain (v.centerLocalizationSubalgebra A hA) :=
  inferInstanceAs (IsDomain (_ : Subalgebra A F))

theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.centerLocalizationSubalgebra_isDiscreteValuationRing
    [IsDedekindDomain A] [IsFractionRing A F] :
    IsDiscreteValuationRing (v.centerLocalizationSubalgebra A hA) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A
    (v.centerIdeal_ne_bot_of_isFractionRing A hA) _




-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.centerLocalizationSubalgebra_isDiscreteValuationRing :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.centerLocalizationSubalgebra_isDiscreteValuationRing
scoped instance centerLocalizationSubalgebra_isFractionRing [IsFractionRing A F] :
    IsFractionRing (v.centerLocalizationSubalgebra A hA) F :=
  inferInstanceAs (IsFractionRing (Localization.subalgebra.ofField F _ _) F)

theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.centerLocalizationSubalgebra_subset [IsFractionRing A F] :
    ((v.centerLocalizationSubalgebra A hA : Subalgebra A F) : Set F)
      ⊆ (v.toValuationSubring : Set F) := by
  intro x hx

  obtain ⟨a, s, hs, rfl⟩ := hx

  rw [← div_eq_mul_inv]
  exact div_mem_of_not_mem_centerIdeal v A hA a hs




-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.centerLocalizationSubalgebra_subset :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.centerLocalizationSubalgebra_subset
noncomputable def _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.centerLocalizationValuationSubring
    [IsDedekindDomain A] [IsFractionRing A F] : ValuationSubring F where
  toSubring := (v.centerLocalizationSubalgebra A hA).toSubring
  mem_or_inv_mem' x := by
    haveI := v.centerLocalizationSubalgebra_isDiscreteValuationRing A hA
    rcases ValuationRing.isInteger_or_isInteger (v.centerLocalizationSubalgebra A hA) x with
      ⟨a, ha⟩ | ⟨a, ha⟩
    · exact Or.inl (ha ▸ a.2)
    · exact Or.inr (ha ▸ a.2)




-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.centerLocalizationValuationSubring :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.centerLocalizationValuationSubring
theorem coe_centerLocalizationValuationSubring [IsDedekindDomain A] [IsFractionRing A F] :
    ((v.centerLocalizationValuationSubring A hA : ValuationSubring F) : Set F)
      = ((v.centerLocalizationSubalgebra A hA : Subalgebra A F) : Set F) := rfl

scoped instance centerLocalizationValuationSubring_isDiscreteValuationRing
    [IsDedekindDomain A] [IsFractionRing A F] :
    IsDiscreteValuationRing (v.centerLocalizationValuationSubring A hA) :=
  v.centerLocalizationSubalgebra_isDiscreteValuationRing A hA

theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.centerLocalizationValuationSubring_le [IsDedekindDomain A] [IsFractionRing A F] :
    v.centerLocalizationValuationSubring A hA ≤ v.toValuationSubring :=
  v.centerLocalizationSubalgebra_subset A hA




-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.centerLocalizationValuationSubring_le :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.centerLocalizationValuationSubring_le
theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.centerLocalizationValuationSubring_eq [IsDedekindDomain A] [IsFractionRing A F] :
    v.centerLocalizationValuationSubring A hA = v.toValuationSubring :=
  ValuationSubring.eq_of_isDiscreteValuationRing_of_le
    (v.centerLocalizationValuationSubring_le A hA) v.ne_top'




-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.centerLocalizationValuationSubring_eq :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.centerLocalizationValuationSubring_eq
theorem coe_centerLocalizationSubalgebra_eq [IsDedekindDomain A] [IsFractionRing A F] :
    ((v.centerLocalizationSubalgebra A hA : Subalgebra A F) : Set F)
      = (v.toValuationSubring : Set F) := by
  rw [← coe_centerLocalizationValuationSubring]
  exact congrArg (SetLike.coe) (v.centerLocalizationValuationSubring_eq A hA)

theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.mem_centerLocalizationSubalgebra_of_mem [IsDedekindDomain A] [IsFractionRing A F]
    (x : F) (hx : x ∈ v.toValuationSubring) :
    x ∈ (v.centerLocalizationSubalgebra A hA : Subalgebra A F) := by
  rw [← SetLike.mem_coe, coe_centerLocalizationSubalgebra_eq]; exact hx




-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.mem_centerLocalizationSubalgebra_of_mem :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.mem_centerLocalizationSubalgebra_of_mem
theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.isLocalization_centerIdeal_of_isDedekindDomain
    [IsDedekindDomain A] [IsFractionRing A F] :
    letI := v.modelAlgebra A hA
    IsLocalization.AtPrime v.toValuationSubring (v.centerIdeal A hA) := by
  letI := v.modelAlgebra A hA
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  ·
    exact v.isUnit_modelInclusion_of_mem_primeCompl A hA
  ·

    intro x
    have hxP : (x : F) ∈ (v.centerLocalizationSubalgebra A hA : Subalgebra A F) :=
      v.mem_centerLocalizationSubalgebra_of_mem A hA (x : F) x.2
    obtain ⟨a, s, hs, hxeq⟩ := hxP

    refine ⟨⟨a, ⟨s, hs⟩⟩, Subtype.ext ?_⟩
    show (x : F) * ((s : A) : F) = ((a : A) : F)
    have halg_s : algebraMap A F s = ((s : A) : F) := rfl
    have halg_a : algebraMap A F a = ((a : A) : F) := rfl
    have hs0 : algebraMap A F s ≠ 0 := by
      intro hF
      have hsne : s ≠ 0 := fun h => (h ▸ hs) (Ideal.zero_mem _)
      exact hsne (Subtype.ext (p := (· ∈ A)) (halg_s ▸ hF))
    rw [← halg_s, ← halg_a, hxeq, mul_assoc, inv_mul_cancel₀ hs0, mul_one]
  ·
    intro a₁ a₂ h
    have hF : (a₁ : F) = (a₂ : F) :=
      congrArg (Subtype.val : v.toValuationSubring → F) h
    exact ⟨1, by rw [show a₁ = a₂ from Subtype.ext hF]⟩




-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.isLocalization_centerIdeal_of_isDedekindDomain :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.isLocalization_centerIdeal_of_isDedekindDomain
end LocalizationSubalgebra


end Place


variable (K F : Type*) [Field K] [Field F] [Algebra K F]

def ValSubringDedekindFractionModel : Prop :=
  ∀ v : Place K F,
    ∃ (A : Subalgebra K F) (_ : (A : Set F) ⊆ (v.toValuationSubring : Set F)),
      Algebra.FiniteType K A ∧ IsDedekindDomain A ∧ IsFractionRing A F

variable {K F}

theorem valSubringDedekindModel_of_dedekindFractionModel
    (hfrac : ValSubringDedekindFractionModel K F) :
    ValSubringDedekindModel K F := fun v => by
  obtain ⟨A, hA, hft, hded, hfracA⟩ := hfrac v
  exact ⟨A, hA, hft, v.isLocalization_centerIdeal_of_isDedekindDomain A hA⟩

theorem valSubringKaehlerFinite_of_dedekindFractionModel
    (hfrac : ValSubringDedekindFractionModel K F) :
    ValSubringKaehlerFinite K F :=
  valSubringKaehlerFinite_of_dedekindModel
    (valSubringDedekindModel_of_dedekindFractionModel hfrac)

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

set_option linter.unusedSectionVars false

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

section EulerGeneral

variable [CharZero K] {p : K[X]} [Fact (Irreducible p)]

theorem aeval_root_eq_sum_range {c : K[X]} {d : ℕ} (hd : c.natDegree < d) :
    (aeval (AdjoinRoot.root p) c : AdjoinRoot p)
      = ∑ k ∈ Finset.range d, c.coeff k • AdjoinRoot.root p ^ k := by
  rw [aeval_def, eval₂_eq_sum_range' (algebraMap K (AdjoinRoot p)) hd]
  exact Finset.sum_congr rfl fun k _ => (Algebra.smul_def _ _).symm

theorem trace_adjoinRoot_mk_div_mk_derivative_of_degree_lt (hpmon : p.Monic)
    {c : K[X]} (hdeg : c.degree < p.degree) :
    Algebra.trace K (AdjoinRoot p)
        (AdjoinRoot.mk p c / AdjoinRoot.mk p (derivative p))
      = c.coeff (p.natDegree - 1) := by
  haveI : FiniteDimensional K (AdjoinRoot p) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hpmon.ne_zero).basis

  have hpd : 0 < p.natDegree := (Fact.out : Irreducible p).natDegree_pos
  have hcd : c.natDegree < p.natDegree := by
    rcases eq_or_ne c 0 with rfl | hc
    · simpa using hpd
    · exact natDegree_lt_natDegree hc hdeg
  rw [← AdjoinRoot.aeval_eq, ← AdjoinRoot.aeval_eq,
    aeval_root_eq_sum_range K hcd, Finset.sum_div, map_sum]

  trans ∑ k ∈ Finset.range p.natDegree,
      c.coeff k * Algebra.trace K (AdjoinRoot p)
        (AdjoinRoot.root p ^ k / aeval (AdjoinRoot.root p) (derivative p))
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, mul_div_assoc, ← Algebra.smul_def, map_smul, smul_eq_mul]

  rw [Finset.sum_eq_single (p.natDegree - 1)]
  ·
    rw [FLT.EulerDualBasis.trace_root_pow_div_derivative_self hpmon hpd, mul_one]
  ·
    intro k hk hkne
    have hk' : k < p.natDegree - 1 :=
      lt_of_le_of_ne (Nat.le_sub_one_of_lt (Finset.mem_range.mp hk)) hkne
    rw [FLT.EulerDualBasis.trace_root_pow_div_derivative_of_lt hpmon hk', mul_zero]
  ·
    intro h
    exact absurd (Finset.mem_range.mpr (Nat.sub_lt hpd one_pos)) h

end EulerGeneral


section AlgEquiv

variable {p : K[X]} (hpirr : Irreducible p)

def finitePlaceResidueFieldAlgEquivAdjoinRoot :
    AdjoinRoot p ≃ₐ[K] (finitePlace K hpirr).ResidueField :=
  residueFieldEquivOfHeightOneSpectrum K (heightOneSpectrumOfIrreducible K hpirr)

theorem finitePlaceResidueFieldAlgEquivAdjoinRoot_mk (q : K[X]) :
    finitePlaceResidueFieldAlgEquivAdjoinRoot K hpirr (AdjoinRoot.mk p q)
      = IsLocalRing.residue _ ⟨algebraMap K[X] (RatFunc K) q,
          algebraMap_mem_ofHeightOneSpectrum K _ q⟩ :=
  rfl

end AlgEquiv


section TraceTransport

variable {p : K[X]} (hpirr : Irreducible p)

theorem trace_finitePlace_residueField_eq_trace_adjoinRoot
    (y : (finitePlace K hpirr).ResidueField) :
    Algebra.trace K (finitePlace K hpirr).ResidueField y
      = Algebra.trace K (AdjoinRoot p)
          ((finitePlaceResidueFieldAlgEquivAdjoinRoot K hpirr).symm y) := by
  conv_lhs => rw [← (finitePlaceResidueFieldAlgEquivAdjoinRoot K hpirr).apply_symm_apply y]
  exact Algebra.trace_eq_of_algEquiv _ _

end TraceTransport


section BridgeRows

variable [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates]

def P1FinitePlaceSimplePoleResidueAdjoinRootValue : Prop :=
  ∀ (p c : K[X]) (_ : p.Monic) (hpirr : Irreducible p), c.degree < p.degree →
    letI : Fact (Irreducible p) := ⟨hpirr⟩
    ∀ (hfmem : p1PrincipalPartAtom K p c 1 * (finitePlace K hpirr).differentialCoeff (dX K)
        ∈ (finitePlace K hpirr).simplePoleSubmodule),
    (finitePlaceResidueFieldAlgEquivAdjoinRoot K hpirr).symm
        ((finitePlace K hpirr).simplePoleResidueAux ⟨_, hfmem⟩)
      = AdjoinRoot.mk p c / AdjoinRoot.mk p (derivative p)

def P1PlaceInftySimplePoleResidueEulerValue : Prop :=
  ∀ (p c : K[X]) (_ : p.Monic) (_ : Irreducible p), c.degree < p.degree →
    ∀ (himem : p1PrincipalPartAtom K p c 1 * (placeInfty K).differentialCoeff (dX K)
        ∈ (placeInfty K).simplePoleSubmodule),
    Algebra.trace K (placeInfty K).ResidueField
        ((placeInfty K).simplePoleResidueAux ⟨_, himem⟩)
      = -(c.coeff (p.natDegree - 1))

end BridgeRows


section FinitePlaceTrace

variable [CharZero K]
variable [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates]

theorem trace_finitePlace_simplePoleResidue_of_adjoinRootValue
    (hbridge : P1FinitePlaceSimplePoleResidueAdjoinRootValue K)
    {p c : K[X]} (hpmon : p.Monic) (hpirr : Irreducible p) (hdeg : c.degree < p.degree)
    (hfmem : p1PrincipalPartAtom K p c 1 * (finitePlace K hpirr).differentialCoeff (dX K)
        ∈ (finitePlace K hpirr).simplePoleSubmodule) :
    Algebra.trace K (finitePlace K hpirr).ResidueField
        ((finitePlace K hpirr).simplePoleResidueAux ⟨_, hfmem⟩)
      = c.coeff (p.natDegree - 1) := by
  haveI : Fact (Irreducible p) := ⟨hpirr⟩
  have hval := hbridge p c hpmon hpirr hdeg
  rw [trace_finitePlace_residueField_eq_trace_adjoinRoot K hpirr, hval hfmem,
    trace_adjoinRoot_mk_div_mk_derivative_of_degree_lt K hpmon hdeg]

end FinitePlaceTrace


section HigherDegReduction

variable [CharZero K]
variable [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

theorem p1PrincipalPartMOneSimplePoleCancel_of_eulerBridge
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0) (heq : ω₀ = dX K)
    (hfin : P1FinitePlaceSimplePoleResidueAdjoinRootValue K)
    (hinf : P1PlaceInftySimplePoleResidueEulerValue K) :
    P1PrincipalPartMOneSimplePoleCancel K hω₀ := by
  subst heq
  intro p c hpmon hpirr hdeg hfmem himem
  rw [trace_finitePlace_simplePoleResidue_of_adjoinRootValue K hfin hpmon hpirr hdeg hfmem,
    hinf p c hpmon hpirr hdeg himem, add_neg_cancel]

end HigherDegReduction


section ComposedEngine

variable [CharZero K] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

end ComposedEngine


end AlgebraicCurve


section AxiomAudits

end AxiomAudits


end

end


end


section
section

open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsLocalRing

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq)

open _root_.AlgebraicCurve

namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_ne_zero adicValuation_coe_eq_one_iff adicValuation_coe_irreducible ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ord_smul ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring mk.injEq rec ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk adicValuation_valuationSubring mem_iff_adicValuation_le_one isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one isEquiv_adicValuation_ofHeightOneSpectrum ord_ofHeightOneSpectrum_ne_zero_iff dCoord DCoordGenerates dCoord_ne_zero differentialCoeff differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_dCoord differentialCoeff_zero differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg deg_restrict_mul_inertiaDeg ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq)

open _root_.AlgebraicCurve.Place

section IntegrallyClosed

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.isIntegrallyClosed_toValuationSubring :
    IsIntegrallyClosed v.toValuationSubring := inferInstance




-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.isIntegrallyClosed_toValuationSubring :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.isIntegrallyClosed_toValuationSubring
theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.mem_valuationSubring_of_isIntegral {x : F}
    (hx : _root_.IsIntegral v.toValuationSubring x) :
    x ∈ v.toValuationSubring := by
  obtain ⟨y, hy⟩ := (isIntegrallyClosed_iff F).mp (v.isIntegrallyClosed_toValuationSubring) hx
  exact hy ▸ y.2




-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.mem_valuationSubring_of_isIntegral :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.mem_valuationSubring_of_isIntegral
variable (B : Subalgebra K F) (hB : (B : Set F) ⊆ (v.toValuationSubring : Set F))

include hB in

theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.modelAlgebra_isScalarTower_top :
    letI := v.modelAlgebra B hB
    IsScalarTower B v.toValuationSubring F := by
  letI := v.modelAlgebra B hB
  refine IsScalarTower.of_algebraMap_eq fun b => ?_
  rfl




-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.modelAlgebra_isScalarTower_top :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.modelAlgebra_isScalarTower_top
include hB in

theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.mem_valuationSubring_of_isIntegral_subalgebra {x : F}
    (hx : _root_.IsIntegral B x) :
    x ∈ v.toValuationSubring := by
  letI := v.modelAlgebra B hB
  haveI := v.modelAlgebra_isScalarTower_top B hB
  exact v.mem_valuationSubring_of_isIntegral (hx.tower_top (A := v.toValuationSubring))




-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.mem_valuationSubring_of_isIntegral_subalgebra :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.mem_valuationSubring_of_isIntegral_subalgebra
include hB in

theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.integralClosure_subset_valuationSubring :
    ((integralClosure B F : Subalgebra B F) : Set F)
      ⊆ (v.toValuationSubring : Set F) := fun _ hx =>
  v.mem_valuationSubring_of_isIntegral_subalgebra B hB hx




-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.integralClosure_subset_valuationSubring :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.integralClosure_subset_valuationSubring
end IntegrallyClosed


end Place


section TwoCharts

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

def IsAffineChart (A : Subalgebra K F) : Prop :=
  Algebra.FiniteType K A ∧ IsDedekindDomain A ∧ IsFractionRing A F

def ValSubringTwoAffineCharts : Prop :=
  ∃ A₀ A₁ : Subalgebra K F, IsAffineChart K F A₀ ∧ IsAffineChart K F A₁
    ∧ ∀ v : Place K F, (A₀ : Set F) ⊆ (v.toValuationSubring : Set F)
        ∨ (A₁ : Set F) ⊆ (v.toValuationSubring : Set F)

variable {K F}

theorem valSubringDedekindFractionModel_of_twoAffineCharts
    (h : ValSubringTwoAffineCharts K F) :
    ValSubringDedekindFractionModel K F := fun v => by
  obtain ⟨A₀, A₁, ⟨hft₀, hded₀, hfrac₀⟩, ⟨hft₁, hded₁, hfrac₁⟩, hcover⟩ := h
  rcases hcover v with h₀ | h₁
  · exact ⟨A₀, h₀, hft₀, hded₀, hfrac₀⟩
  · exact ⟨A₁, h₁, hft₁, hded₁, hfrac₁⟩

theorem valSubringKaehlerFinite_of_twoAffineCharts
    (h : ValSubringTwoAffineCharts K F) :
    ValSubringKaehlerFinite K F :=
  valSubringKaehlerFinite_of_dedekindFractionModel
    (valSubringDedekindFractionModel_of_twoAffineCharts h)

end TwoCharts


end AlgebraicCurve


namespace ModularCurve

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve

variable (N : ℕ) [NeZero N]

end ModularCurve


namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq)

open _root_.AlgebraicCurve

section Gates

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place
export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_ne_zero adicValuation_coe_eq_one_iff adicValuation_coe_irreducible ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ord_smul ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring mk.injEq rec ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk adicValuation_valuationSubring mem_iff_adicValuation_le_one isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one isEquiv_adicValuation_ofHeightOneSpectrum ord_ofHeightOneSpectrum_ne_zero_iff dCoord DCoordGenerates dCoord_ne_zero differentialCoeff differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_dCoord differentialCoeff_zero differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg deg_restrict_mul_inertiaDeg ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq)
end Place
namespace Place
open scoped _root_.AlgebraicCurve.Place in
@[reducible] noncomputable def _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.toKSubalgebra (v : Place K F) : Subalgebra K F where
  __ := v.toValuationSubring.toSubring
  algebraMap_mem' c := v.algebraMap_mem' c

-- RRSplit attribute-prefixed source-private field bridge.
private noncomputable abbrev _root_.AlgebraicCurve.Place.toKSubalgebra :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.toKSubalgebra
end Place



namespace Place
open scoped _root_.AlgebraicCurve.Place in
theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.coe_toKSubalgebra (v : Place K F) :
    (v.toKSubalgebra : Set F) = (v.toValuationSubring : Set F) := rfl

-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.coe_toKSubalgebra :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.coe_toKSubalgebra
end Place



theorem gate_adjoin_subset_valuationSubring_of_mem (v : Place K F) {t : F}
    (ht : t ∈ v.toValuationSubring) :
    ((Algebra.adjoin K {t} : Subalgebra K F) : Set F)
      ⊆ (v.toValuationSubring : Set F) := by
  rw [← v.coe_toKSubalgebra]
  exact Algebra.adjoin_le (Set.singleton_subset_iff.mpr ht)

end Gates


end AlgebraicCurve


section AxiomAudits

end AxiomAudits


end


end


section
section

set_option linter.unusedSectionVars false

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

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]

namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_ne_zero adicValuation_coe_eq_one_iff adicValuation_coe_irreducible ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ord_smul ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring mk.injEq rec ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk adicValuation_valuationSubring mem_iff_adicValuation_le_one isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one isEquiv_adicValuation_ofHeightOneSpectrum ord_ofHeightOneSpectrum_ne_zero_iff dCoord DCoordGenerates dCoord_ne_zero differentialCoeff differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_dCoord differentialCoeff_zero differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg deg_restrict_mul_inertiaDeg ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq)

open _root_.AlgebraicCurve.Place

variable (v : Place K F)

theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.simplePoleResidueAux_mul_of_mem {a : F} (ha : a ∈ v.toValuationSubring)
    {f : F} (hf : f ∈ v.simplePoleSubmodule)
    (haf : a * f ∈ v.simplePoleSubmodule) :
    v.simplePoleResidueAux ⟨a * f, haf⟩
      = IsLocalRing.residue _ ⟨a, ha⟩ * v.simplePoleResidueAux ⟨f, hf⟩ := by
  rw [simplePoleResidueAux_apply, simplePoleResidueAux_apply, ← map_mul]
  exact congrArg (IsLocalRing.residue _) (Subtype.ext (mul_left_comm _ _ _))




-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.simplePoleResidueAux_mul_of_mem :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.simplePoleResidueAux_mul_of_mem
theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.mul_mem_simplePoleSubmodule_of_mem {a : F} (ha : a ∈ v.toValuationSubring)
    {f : F} (hf : f ∈ v.simplePoleSubmodule) :
    a * f ∈ v.simplePoleSubmodule := by
  rw [mem_simplePoleSubmodule, mul_left_comm]
  exact mul_mem ha hf




-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.mul_mem_simplePoleSubmodule_of_mem :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.mul_mem_simplePoleSubmodule_of_mem
end Place


section DerivativeRegular

variable (K)
variable [DecidableEq (RatFunc K)]

theorem denom_notMem_of_mem_ofHeightOneSpectrum (w : HeightOneSpectrum K[X]) {f : RatFunc K}
    (hf : f ∈ (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).toValuationSubring) :
    f.denom ∉ w.asIdeal := by
  intro hd
  have hxval : w.valuation (RatFunc K) f ≤ 1 :=
    (Place.isEquiv_adicValuation_ofHeightOneSpectrum (K := K)
      (F := RatFunc K) w).le_one_iff_le_one.mpr ((Place.mem_iff_adicValuation_le_one _).mp hf)
  have hden_ne : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr f.denom_ne_zero
  have hmul : f * algebraMap K[X] (RatFunc K) f.denom = algebraMap K[X] (RatFunc K) f.num :=
    ((div_eq_iff hden_ne).mp f.num_div_denom).symm
  have hnum : f.num ∉ w.asIdeal := by
    intro hn
    refine w.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr ?_)
    obtain ⟨a, b, hab⟩ := RatFunc.isCoprime_num_denom f
    exact hab ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ hn) (Ideal.mul_mem_left _ _ hd)
  have h1 : w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) f.num) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem w).mpr hnum
  refine absurd h1 (ne_of_lt ?_)
  calc w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) f.num)
      = w.valuation (RatFunc K) f
          * w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) f.denom) := by
        rw [← map_mul, hmul]
    _ ≤ w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) f.denom) :=
        mul_le_of_le_one_left' hxval
    _ < 1 := (HeightOneSpectrum.valuation_lt_one_iff_mem w f.denom).mpr hd

variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

theorem differentialCoeff_add' (v : Place K (RatFunc K)) (ω₁ ω₂ : Ω[(RatFunc K)⁄K]) :
    v.differentialCoeff (ω₁ + ω₂) = v.differentialCoeff ω₁ + v.differentialCoeff ω₂ :=
  v.differentialCoeff_unique
    (by rw [add_smul, v.differentialCoeff_smul_dCoord, v.differentialCoeff_smul_dCoord])

theorem differentialCoeff_D_algebraMap_polynomial (v : Place K (RatFunc K)) (q : K[X]) :
    v.differentialCoeff (D K (RatFunc K) (algebraMap K[X] (RatFunc K) q))
      = algebraMap K[X] (RatFunc K) q.derivative * v.differentialCoeff (dX K) := by
  rw [D_algebraMap_polynomial K q, v.differentialCoeff_smul]

theorem differentialCoeff_D_mem_finitePlace [CharZero K] {p : K[X]} (hpirr : Irreducible p)
    {f : RatFunc K} (hf : f ∈ (finitePlace K hpirr).toValuationSubring) :
    (finitePlace K hpirr).differentialCoeff (D K (RatFunc K) f)
      ∈ (finitePlace K hpirr).toValuationSubring := by
  set v := finitePlace K hpirr

  set ξ : K[X] := f.num.derivative * f.denom - f.num * f.denom.derivative
  have hd0 : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr f.denom_ne_zero
  have hcoeff : v.differentialCoeff (D K (RatFunc K) f)
      = algebraMap K[X] (RatFunc K) ξ * ((algebraMap K[X] (RatFunc K) f.denom) ^ 2)⁻¹
          * v.differentialCoeff (dX K) := by
    have hkey := denom_sq_smul_D_eq K f
    refine v.differentialCoeff_unique ?_
    rw [mul_smul, v.differentialCoeff_smul_dCoord, mul_comm, mul_smul, ← hkey, smul_smul,
      inv_mul_cancel₀ (pow_ne_zero 2 hd0), one_smul]
  rw [hcoeff]

  refine mul_mem (mul_mem ?_ ?_) ?_
  · exact algebraMap_mem_ofHeightOneSpectrum K _ ξ
  ·
    have hden_notmem : f.denom ∉ (heightOneSpectrumOfIrreducible K hpirr).asIdeal :=
      denom_notMem_of_mem_ofHeightOneSpectrum K _ hf
    have hordd : v.ord (algebraMap K[X] (RatFunc K) f.denom) = 0 := by
      by_contra h
      exact hden_notmem ((Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K)
        (F := RatFunc K) _ f.denom_ne_zero).mp h)
    refine v.mem_of_ord_nonneg (inv_ne_zero (pow_ne_zero 2 hd0)) ?_
    rw [v.ord_inv, ← zpow_natCast, v.ord_zpow, hordd, mul_zero, _root_.neg_zero]
  · exact v.mem_of_ord_nonneg (v.differentialCoeff_ne_zero (dX_ne_zero K))
      (ord_differentialCoeff_dX_ofHeightOneSpectrum hpirr
        (heightOneSpectrumOfIrreducible_asIdeal K hpirr) hpirr.separable).ge

end DerivativeRegular


section LeibnizCore

variable (K)
variable [DecidableEq (RatFunc K)] [CharZero K]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

theorem uniformizer_div_mem_finitePlace {p : K[X]} (hpirr : Irreducible p) :
    (finitePlace K hpirr).uniformizer / algebraMap K[X] (RatFunc K) p
      ∈ (finitePlace K hpirr).toValuationSubring := by
  set v := finitePlace K hpirr
  have hp0 : algebraMap K[X] (RatFunc K) p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hpirr.ne_zero
  refine v.mem_of_ord_nonneg (div_ne_zero v.uniformizer_ne_zero hp0) ?_
  rw [div_eq_mul_inv, v.ord_mul v.uniformizer_ne_zero (inv_ne_zero hp0), v.ord_inv,
    v.ord_uniformizer, ord_finitePlace_self K hpirr]
  omega

theorem one_sub_uniformizer_div_mul_differentialCoeff_D
    {p : K[X]} (hpirr : Irreducible p) :
    (1 : RatFunc K) - (finitePlace K hpirr).uniformizer / algebraMap K[X] (RatFunc K) p
        * (finitePlace K hpirr).differentialCoeff
            (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p))
      = algebraMap K[X] (RatFunc K) p
          * (finitePlace K hpirr).differentialCoeff
              (D K (RatFunc K) ((finitePlace K hpirr).uniformizer
                / algebraMap K[X] (RatFunc K) p)) := by
  set v := finitePlace K hpirr
  have hp0 : algebraMap K[X] (RatFunc K) p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hpirr.ne_zero

  have hleib : D K (RatFunc K) v.uniformizer
      = (v.uniformizer / algebraMap K[X] (RatFunc K) p)
            • D K (RatFunc K) (algebraMap K[X] (RatFunc K) p)
        + algebraMap K[X] (RatFunc K) p
            • D K (RatFunc K) (v.uniformizer / algebraMap K[X] (RatFunc K) p) := by
    have h := (D K (RatFunc K)).leibniz (a := v.uniformizer / algebraMap K[X] (RatFunc K) p)
      (b := algebraMap K[X] (RatFunc K) p)
    rw [div_mul_cancel₀ _ hp0] at h
    exact h

  have h1 : (1 : RatFunc K)
      = (v.uniformizer / algebraMap K[X] (RatFunc K) p)
            * v.differentialCoeff (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p))
        + algebraMap K[X] (RatFunc K) p
            * v.differentialCoeff
                (D K (RatFunc K) (v.uniformizer / algebraMap K[X] (RatFunc K) p)) := by
    have hcoord : D K (RatFunc K) v.uniformizer = v.dCoord := rfl
    rw [← v.differentialCoeff_dCoord, ← hcoord, hleib, differentialCoeff_add' K,
      v.differentialCoeff_smul, v.differentialCoeff_smul]
  linear_combination h1

theorem uniformizer_div_mul_differentialCoeff_D_mem_finitePlace
    {p : K[X]} (hpirr : Irreducible p) :
    (finitePlace K hpirr).uniformizer / algebraMap K[X] (RatFunc K) p
        * (finitePlace K hpirr).differentialCoeff
            (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p))
      ∈ (finitePlace K hpirr).toValuationSubring := by
  set v := finitePlace K hpirr
  have hp0 : algebraMap K[X] (RatFunc K) p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hpirr.ne_zero
  refine mul_mem (uniformizer_div_mem_finitePlace K hpirr) ?_
  rw [differentialCoeff_D_algebraMap_polynomial K]
  exact mul_mem (algebraMap_mem_ofHeightOneSpectrum K _ p.derivative)
    (v.mem_of_ord_nonneg (v.differentialCoeff_ne_zero (dX_ne_zero K))
      (ord_differentialCoeff_dX_ofHeightOneSpectrum hpirr
        (heightOneSpectrumOfIrreducible_asIdeal K hpirr) hpirr.separable).ge)

theorem residue_uniformizer_div_mul_differentialCoeff_D_eq_one
    {p : K[X]} (hpirr : Irreducible p) :
    IsLocalRing.residue _ ⟨_, uniformizer_div_mul_differentialCoeff_D_mem_finitePlace K hpirr⟩
      = (1 : (finitePlace K hpirr).ResidueField) := by
  set v := finitePlace K hpirr
  rw [← sub_eq_zero, show (1 : v.ResidueField) = IsLocalRing.residue _ 1 by simp,
    ← map_sub, IsLocalRing.residue_eq_zero_iff]

  have hsubmem : (1 : RatFunc K) - (v.uniformizer / algebraMap K[X] (RatFunc K) p
      * v.differentialCoeff (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p)))
        ∈ v.toValuationSubring :=
    sub_mem (one_mem _) (uniformizer_div_mul_differentialCoeff_D_mem_finitePlace K hpirr)
  have hcoe : (⟨_, uniformizer_div_mul_differentialCoeff_D_mem_finitePlace K hpirr⟩
        - 1 : v.toValuationSubring)
      = -⟨_, hsubmem⟩ :=
    Subtype.ext (by push_cast; ring)
  rw [hcoe]
  refine neg_mem ?_

  have herr : (1 : RatFunc K) - (v.uniformizer / algebraMap K[X] (RatFunc K) p
      * v.differentialCoeff (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p)))
        = algebraMap K[X] (RatFunc K) p
          * v.differentialCoeff (D K (RatFunc K)
              (v.uniformizer / algebraMap K[X] (RatFunc K) p)) :=
    one_sub_uniformizer_div_mul_differentialCoeff_D K hpirr

  have hpmem : (⟨algebraMap K[X] (RatFunc K) p, algebraMap_mem_ofHeightOneSpectrum K _ p⟩
      : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
    rw [Place.mem_maximalIdeal_iff_adicValuation_lt_one]
    refine (Place.isEquiv_adicValuation_ofHeightOneSpectrum (K := K)
      (F := RatFunc K) (heightOneSpectrumOfIrreducible K hpirr)).lt_one_iff_lt_one.mp ?_
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem _ p).mpr
      (Ideal.mem_span_singleton_self p)
  have hregmem : v.differentialCoeff (D K (RatFunc K)
        (v.uniformizer / algebraMap K[X] (RatFunc K) p)) ∈ v.toValuationSubring :=
    differentialCoeff_D_mem_finitePlace K hpirr (uniformizer_div_mem_finitePlace K hpirr)
  have hprod : (⟨_, hsubmem⟩ : v.toValuationSubring)
      = ⟨_, algebraMap_mem_ofHeightOneSpectrum K _ p⟩ * ⟨_, hregmem⟩ :=
    Subtype.ext herr
  rw [hprod]
  exact Ideal.mul_mem_right _ _ hpmem

end LeibnizCore


section BridgeDischarge

variable (K)
variable [DecidableEq (RatFunc K)] [CharZero K]
variable [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

theorem residue_algebraMap_derivative_ne_zero {p : K[X]} (hpirr : Irreducible p) :
    IsLocalRing.residue _ ⟨algebraMap K[X] (RatFunc K) p.derivative,
        algebraMap_mem_ofHeightOneSpectrum K _ p.derivative⟩
      ≠ (0 : (finitePlace K hpirr).ResidueField) := by
  rw [ne_eq, IsLocalRing.residue_eq_zero_iff,
    Place.mem_maximalIdeal_iff_adicValuation_lt_one]
  intro hlt
  have hlt' := (Place.isEquiv_adicValuation_ofHeightOneSpectrum (K := K)
    (F := RatFunc K) (heightOneSpectrumOfIrreducible K hpirr)).lt_one_iff_lt_one.mpr hlt
  rw [HeightOneSpectrum.valuation_lt_one_iff_mem,
    heightOneSpectrumOfIrreducible_asIdeal K hpirr, Ideal.mem_span_singleton] at hlt'
  exact hpirr.not_isUnit (hpirr.separable.isUnit_of_dvd' dvd_rfl hlt')

theorem simplePoleResidueAux_finitePlace_p1PrincipalPartAtom_mOne
    {p c : K[X]} (hpirr : Irreducible p)
    (hfmem : p1PrincipalPartAtom K p c 1 * (finitePlace K hpirr).differentialCoeff (dX K)
        ∈ (finitePlace K hpirr).simplePoleSubmodule) :
    (finitePlace K hpirr).simplePoleResidueAux ⟨_, hfmem⟩
      = IsLocalRing.residue _ ⟨algebraMap K[X] (RatFunc K) c,
            algebraMap_mem_ofHeightOneSpectrum K _ c⟩
        / IsLocalRing.residue _ ⟨algebraMap K[X] (RatFunc K) p.derivative,
            algebraMap_mem_ofHeightOneSpectrum K _ p.derivative⟩ := by
  set v := finitePlace K hpirr
  have hp0 : algebraMap K[X] (RatFunc K) p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hpirr.ne_zero

  rw [Place.simplePoleResidueAux_apply, eq_div_iff (residue_algebraMap_derivative_ne_zero K hpirr)]

  have hkey : (v.uniformizer * (p1PrincipalPartAtom K p c 1 * v.differentialCoeff (dX K)))
        * algebraMap K[X] (RatFunc K) p.derivative
      = algebraMap K[X] (RatFunc K) c
        * (v.uniformizer / algebraMap K[X] (RatFunc K) p
            * v.differentialCoeff (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p))) := by
    rw [differentialCoeff_D_algebraMap_polynomial K]
    show v.uniformizer
        * (algebraMap K[X] (RatFunc K) c / algebraMap K[X] (RatFunc K) p ^ 1
            * v.differentialCoeff (dX K))
        * algebraMap K[X] (RatFunc K) (derivative p)
      = algebraMap K[X] (RatFunc K) c
        * (v.uniformizer / algebraMap K[X] (RatFunc K) p
            * (algebraMap K[X] (RatFunc K) (derivative p) * v.differentialCoeff (dX K)))
    rw [pow_one, div_mul_eq_mul_div, div_mul_eq_mul_div, mul_div_assoc, mul_div_assoc]
    ring_nf

  have hLHSmem : v.uniformizer * (p1PrincipalPartAtom K p c 1 * v.differentialCoeff (dX K))
      * algebraMap K[X] (RatFunc K) p.derivative ∈ v.toValuationSubring :=
    mul_mem hfmem (algebraMap_mem_ofHeightOneSpectrum K _ p.derivative)
  have hRHSmem : algebraMap K[X] (RatFunc K) c
      * (v.uniformizer / algebraMap K[X] (RatFunc K) p
          * v.differentialCoeff (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p)))
        ∈ v.toValuationSubring :=
    mul_mem (algebraMap_mem_ofHeightOneSpectrum K _ c)
      (uniformizer_div_mul_differentialCoeff_D_mem_finitePlace K hpirr)
  calc IsLocalRing.residue _ ⟨_, hfmem⟩ * IsLocalRing.residue _ ⟨_,
          algebraMap_mem_ofHeightOneSpectrum K _ p.derivative⟩
      = IsLocalRing.residue _ (⟨_, hfmem⟩ * ⟨_,
          algebraMap_mem_ofHeightOneSpectrum K _ p.derivative⟩) := (map_mul _ _ _).symm
    _ = IsLocalRing.residue _ ⟨_, hLHSmem⟩ :=
        congrArg (IsLocalRing.residue _) (Subtype.ext rfl)
    _ = IsLocalRing.residue _ ⟨_, hRHSmem⟩ :=
        congrArg (IsLocalRing.residue _) (Subtype.ext hkey)
    _ = IsLocalRing.residue _ (⟨_, algebraMap_mem_ofHeightOneSpectrum K _ c⟩
          * ⟨_, uniformizer_div_mul_differentialCoeff_D_mem_finitePlace K hpirr⟩) :=
        congrArg (IsLocalRing.residue _) (Subtype.ext rfl)
    _ = IsLocalRing.residue _ ⟨_, algebraMap_mem_ofHeightOneSpectrum K _ c⟩
          * IsLocalRing.residue _
              ⟨_, uniformizer_div_mul_differentialCoeff_D_mem_finitePlace K hpirr⟩ :=
        map_mul _ _ _
    _ = IsLocalRing.residue _ ⟨_, algebraMap_mem_ofHeightOneSpectrum K _ c⟩ := by
        rw [residue_uniformizer_div_mul_differentialCoeff_D_eq_one K hpirr, mul_one]

theorem p1FinitePlaceSimplePoleResidueAdjoinRootValue_dX :
    P1FinitePlaceSimplePoleResidueAdjoinRootValue K := by
  intro p c _ hpirr _
  letI : Fact (Irreducible p) := ⟨hpirr⟩
  intro hfmem
  rw [simplePoleResidueAux_finitePlace_p1PrincipalPartAtom_mOne K hpirr hfmem,
    AlgEquiv.symm_apply_eq, map_div₀,
    finitePlaceResidueFieldAlgEquivAdjoinRoot_mk K hpirr c,
    finitePlaceResidueFieldAlgEquivAdjoinRoot_mk K hpirr p.derivative]

end BridgeDischarge


section ComposedEngine

variable (K)
variable [DecidableEq (RatFunc K)] [CharZero K]
variable [HasCanonicalDivisor (K := K) (F := RatFunc K)] [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

theorem p1PrincipalPartMOneSimplePoleCancel_of_inftyBridge
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0) (heq : ω₀ = dX K)
    (hinf : P1PlaceInftySimplePoleResidueEulerValue K) :
    P1PrincipalPartMOneSimplePoleCancel K hω₀ :=
  p1PrincipalPartMOneSimplePoleCancel_of_eulerBridge K hω₀ heq
    (p1FinitePlaceSimplePoleResidueAdjoinRootValue_dX K) hinf

end ComposedEngine


end AlgebraicCurve


section AxiomAudits

end AxiomAudits


end

end


end


section
section

open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsLocalRing
open _root_.IntermediateField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IntermediateField
open _root_.IntermediateField.algebraAdjoinAdjoin
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IntermediateField.algebraAdjoinAdjoin

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq)

open _root_.AlgebraicCurve

section AdjoinRingProperties

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Transcendental.isPrincipalIdealRing_adjoin {t : F} (ht : Transcendental K t) :
    IsPrincipalIdealRing ↥(Algebra.adjoin K ({t} : Set F)) :=
  IsPrincipalIdealRing.of_surjective
    (Polynomial.algEquivOfTranscendental K t ht).toRingHom
    (Polynomial.algEquivOfTranscendental K t ht).surjective


-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.Transcendental.isPrincipalIdealRing_adjoin :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Transcendental.isPrincipalIdealRing_adjoin
theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Transcendental.isDedekindDomain_adjoin {t : F} (ht : Transcendental K t) :
    IsDedekindDomain ↥(Algebra.adjoin K ({t} : Set F)) :=
  haveI := ht.isPrincipalIdealRing_adjoin
  inferInstance


-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.Transcendental.isDedekindDomain_adjoin :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Transcendental.isDedekindDomain_adjoin
theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Transcendental.isIntegrallyClosed_adjoin {t : F} (ht : Transcendental K t) :
    IsIntegrallyClosed ↥(Algebra.adjoin K ({t} : Set F)) :=
  haveI := ht.isDedekindDomain_adjoin
  inferInstance


-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.Transcendental.isIntegrallyClosed_adjoin :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Transcendental.isIntegrallyClosed_adjoin
theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Transcendental.isNoetherianRing_adjoin {t : F} (ht : Transcendental K t) :
    IsNoetherianRing ↥(Algebra.adjoin K ({t} : Set F)) :=
  haveI := ht.isPrincipalIdealRing_adjoin
  inferInstance


-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.Transcendental.isNoetherianRing_adjoin :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Transcendental.isNoetherianRing_adjoin
theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Algebra.FiniteType.adjoin_singleton (t : F) :
    Algebra.FiniteType K ↥(Algebra.adjoin K ({t} : Set F)) :=
  Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton t)


-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.Algebra.FiniteType.adjoin_singleton :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Algebra.FiniteType.adjoin_singleton
theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Transcendental.inv {t : F} (ht : Transcendental K t) :
    Transcendental K t⁻¹ := by
  rw [Transcendental, IsAlgebraic.inv_iff]; exact ht


-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.Transcendental.inv :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Transcendental.inv
end AdjoinRingProperties


section TranscendentalChart

variable (K : Type*) {F : Type*} [Field K] [Field F] [Algebra K F]

@[reducible] noncomputable def transcendentalChart (t : F) : Subalgebra K F :=
  (integralClosure (Algebra.adjoin K ({t} : Set F)) F).restrictScalars K

theorem coe_transcendentalChart (t : F) :
    (transcendentalChart K t : Set F)
      = ((integralClosure (Algebra.adjoin K ({t} : Set F)) F : Subalgebra _ F) : Set F) :=
  rfl

variable {K}

theorem transcendentalChart_subset_valuationSubring_of_mem (v : Place K F)
    {t : F} (ht : t ∈ v.toValuationSubring) :
    (transcendentalChart K t : Set F) ⊆ (v.toValuationSubring : Set F) := by
  rw [coe_transcendentalChart]
  exact v.integralClosure_subset_valuationSubring _
    (gate_adjoin_subset_valuationSubring_of_mem v ht)

theorem transcendentalChart_subset_or_inv_subset (v : Place K F) (t : F) :
    (transcendentalChart K t : Set F) ⊆ (v.toValuationSubring : Set F)
      ∨ (transcendentalChart K t⁻¹ : Set F) ⊆ (v.toValuationSubring : Set F) :=
  (v.toValuationSubring.mem_or_inv_mem t).imp
    (transcendentalChart_subset_valuationSubring_of_mem v)
    (transcendentalChart_subset_valuationSubring_of_mem v)

end TranscendentalChart


section IsAffineChartEngine

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

section

variable (B : Subalgebra K F)

theorem isScalarTower_integralClosure_subalgebra :
    IsScalarTower K B ↥(integralClosure B F) := by
  refine IsScalarTower.of_algebraMap_eq fun c => ?_
  exact Subtype.ext rfl

theorem finiteType_integralClosure_of_moduleFinite (hft : Algebra.FiniteType K B)
    (hfin : Module.Finite B ↥(integralClosure B F)) :
    Algebra.FiniteType K ↥(integralClosure B F) :=
  haveI := isScalarTower_integralClosure_subalgebra B
  haveI := hfin
  Algebra.FiniteType.trans (S := B) hft inferInstance

end


theorem isDedekindDomain_integralClosure_adjoin {t : F} (ht : Transcendental K t)
    [FiniteDimensional K⟮t⟯ F] [Algebra.IsSeparable K⟮t⟯ F] :
    IsDedekindDomain ↥(integralClosure (Algebra.adjoin K ({t} : Set F)) F) := by
  haveI := ht.isDedekindDomain_adjoin
  exact integralClosure.isDedekindDomain ↥(Algebra.adjoin K ({t} : Set F)) ↥(K⟮t⟯) F

theorem isFractionRing_integralClosure_adjoin (t : F) [FiniteDimensional K⟮t⟯ F] :
    IsFractionRing ↥(integralClosure (Algebra.adjoin K ({t} : Set F)) F) F :=
  integralClosure.isFractionRing_of_finite_extension
    (A := ↥(Algebra.adjoin K ({t} : Set F))) ↥(K⟮t⟯) F

set_option synthInstance.maxHeartbeats 320000 in

theorem moduleFinite_integralClosure_adjoin {t : F} (ht : Transcendental K t)
    [FiniteDimensional K⟮t⟯ F] [Algebra.IsSeparable K⟮t⟯ F] :
    Module.Finite ↥(Algebra.adjoin K ({t} : Set F))
      ↥(integralClosure (Algebra.adjoin K ({t} : Set F)) F) := by
  haveI := ht.isIntegrallyClosed_adjoin
  haveI := ht.isNoetherianRing_adjoin
  exact IsIntegralClosure.finite (A := ↥(Algebra.adjoin K ({t} : Set F)))
    (K := ↥(K⟮t⟯)) (L := F) (integralClosure ↥(Algebra.adjoin K ({t} : Set F)) F)

theorem finiteType_integralClosure_adjoin {t : F} (ht : Transcendental K t)
    [FiniteDimensional K⟮t⟯ F] [Algebra.IsSeparable K⟮t⟯ F] :
    Algebra.FiniteType K ↥(integralClosure (Algebra.adjoin K ({t} : Set F)) F) :=
  finiteType_integralClosure_of_moduleFinite (Algebra.adjoin K {t})
    (Algebra.FiniteType.adjoin_singleton t) (moduleFinite_integralClosure_adjoin ht)

theorem isAffineChart_restrictScalars_integralClosure (B : Subalgebra K F)
    (hft : Algebra.FiniteType K ↥(integralClosure B F))
    (hded : IsDedekindDomain ↥(integralClosure B F))
    (hfrac : IsFractionRing ↥(integralClosure B F) F) :
    IsAffineChart K F ((integralClosure B F).restrictScalars K) :=
  ⟨hft, hded, hfrac⟩

theorem isAffineChart_transcendentalChart {t : F} (ht : Transcendental K t)
    [FiniteDimensional K⟮t⟯ F] [Algebra.IsSeparable K⟮t⟯ F] :
    IsAffineChart K F (transcendentalChart K t) :=
  isAffineChart_restrictScalars_integralClosure (Algebra.adjoin K {t})
    (finiteType_integralClosure_adjoin ht)
    (isDedekindDomain_integralClosure_adjoin ht)
    (isFractionRing_integralClosure_adjoin t)

end IsAffineChartEngine


section SeparatingTranscendental

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

def HasSeparatingTranscendental : Prop :=
  ∃ t : F, Transcendental K t
    ∧ FiniteDimensional K⟮t⟯ F ∧ Algebra.IsSeparable K⟮t⟯ F
    ∧ FiniteDimensional K⟮t⁻¹⟯ F ∧ Algebra.IsSeparable K⟮t⁻¹⟯ F

variable {K F}

theorem valSubringTwoAffineCharts_of_hasSeparatingTranscendental
    (h : HasSeparatingTranscendental K F) :
    ValSubringTwoAffineCharts K F := by
  obtain ⟨t, ht, hfin, hsep, hfin', hsep'⟩ := h
  exact ⟨transcendentalChart K t, transcendentalChart K t⁻¹,
    isAffineChart_transcendentalChart ht,
    isAffineChart_transcendentalChart ht.inv,
    fun v => transcendentalChart_subset_or_inv_subset v t⟩

theorem valSubringKaehlerFinite_of_hasSeparatingTranscendental
    (h : HasSeparatingTranscendental K F) :
    ValSubringKaehlerFinite K F :=
  valSubringKaehlerFinite_of_twoAffineCharts
    (valSubringTwoAffineCharts_of_hasSeparatingTranscendental h)

end SeparatingTranscendental


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


section AxiomAudits

end AxiomAudits


end


end


section
section

set_option linter.unusedSectionVars false

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

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]

section LowDegRegular

variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

theorem ord_placeInfty_mOneAtom_mul_differentialCoeff_dX
    (hInfty : (placeInfty K).ord ((placeInfty K).differentialCoeff (dX K)) = -2)
    {p c : K[X]} (hp : p ≠ 0) (hc : c ≠ 0) :
    (placeInfty K).ord
        (p1PrincipalPartAtom K p c 1 * (placeInfty K).differentialCoeff (dX K))
      = (p.natDegree : ℤ) - c.natDegree - 2 := by
  have hatom0 : p1PrincipalPartAtom K p c 1 ≠ 0 := by
    simp only [p1PrincipalPartAtom, ne_eq, div_eq_zero_iff, not_or]
    exact ⟨(map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hc,
      pow_ne_zero _ ((map_ne_zero_iff _
        (IsFractionRing.injective K[X] (RatFunc K))).mpr hp)⟩
  rw [(placeInfty K).ord_mul hatom0 ((placeInfty K).differentialCoeff_ne_zero (dX_ne_zero K)),
    ord_placeInfty_p1PrincipalPartAtom K hp hc 1, hInfty]
  push_cast; ring

theorem p1MOneAtom_mul_differentialCoeff_dX_mem_placeInfty
    (hInfty : (placeInfty K).ord ((placeInfty K).differentialCoeff (dX K)) = -2)
    {p c : K[X]} (hp : p ≠ 0) (hcdeg : c = 0 ∨ c.natDegree + 2 ≤ p.natDegree) :
    p1PrincipalPartAtom K p c 1 * (placeInfty K).differentialCoeff (dX K)
      ∈ (placeInfty K).toValuationSubring := by
  rcases hcdeg with rfl | hcdeg
  · show algebraMap K[X] (RatFunc K) 0 / (algebraMap K[X] (RatFunc K) p) ^ 1
        * (placeInfty K).differentialCoeff (dX K) ∈ _
    rw [_root_.map_zero, zero_div, zero_mul]; exact zero_mem _
  · rcases eq_or_ne c 0 with rfl | hc
    · show algebraMap K[X] (RatFunc K) 0 / (algebraMap K[X] (RatFunc K) p) ^ 1
          * (placeInfty K).differentialCoeff (dX K) ∈ _
      rw [_root_.map_zero, zero_div, zero_mul]; exact zero_mem _
    have hatom0 : p1PrincipalPartAtom K p c 1 ≠ 0 := by
      simp only [p1PrincipalPartAtom, ne_eq, div_eq_zero_iff, not_or]
      exact ⟨(map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hc,
        pow_ne_zero _ ((map_ne_zero_iff _
          (IsFractionRing.injective K[X] (RatFunc K))).mpr hp)⟩
    refine (placeInfty K).mem_of_ord_nonneg
      (mul_ne_zero hatom0 ((placeInfty K).differentialCoeff_ne_zero (dX_ne_zero K))) ?_
    rw [ord_placeInfty_mOneAtom_mul_differentialCoeff_dX K hInfty hp hc]
    omega

end LowDegRegular


section LowDegValue

variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

theorem trace_placeInfty_simplePoleResidue_mOne_of_lowDeg
    (hInfty : (placeInfty K).ord ((placeInfty K).differentialCoeff (dX K)) = -2)
    {p c : K[X]} (hpirr : Irreducible p)
    (hcdeg : c = 0 ∨ c.natDegree + 2 ≤ p.natDegree)
    (himem : p1PrincipalPartAtom K p c 1 * (placeInfty K).differentialCoeff (dX K)
        ∈ (placeInfty K).simplePoleSubmodule) :
    Algebra.trace K (placeInfty K).ResidueField
        ((placeInfty K).simplePoleResidueAux ⟨_, himem⟩)
      = -(c.coeff (p.natDegree - 1)) := by

  have hreg := p1MOneAtom_mul_differentialCoeff_dX_mem_placeInfty K hInfty hpirr.ne_zero hcdeg
  have hLHS : (placeInfty K).simplePoleResidueAux ⟨_, himem⟩ = 0 :=
    (placeInfty K).simplePoleResidueAux_eq_zero_of_mem hreg
  rw [hLHS, _root_.map_zero]

  rcases hcdeg with rfl | hcdeg
  · simp
  · rw [coeff_eq_zero_of_natDegree_lt (by omega : c.natDegree < p.natDegree - 1), _root_.neg_zero]

end LowDegValue


section NamedCarriers

variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

def P1PlaceInftySimplePoleResidueEulerValueTopDeg : Prop :=
  ∀ (p c : K[X]) (_ : p.Monic) (_ : Irreducible p), c ≠ 0 → c.natDegree + 1 = p.natDegree →
    ∀ (himem : p1PrincipalPartAtom K p c 1 * (placeInfty K).differentialCoeff (dX K)
        ∈ (placeInfty K).simplePoleSubmodule),
    Algebra.trace K (placeInfty K).ResidueField
        ((placeInfty K).simplePoleResidueAux ⟨_, himem⟩)
      = -(c.coeff (p.natDegree - 1))

def P1PlaceInftySimplePoleResidueEulerValueMonomial : Prop :=
  ∀ (p : K[X]) (_ : p.Monic) (_ : Irreducible p),
    ∀ (himem : p1PrincipalPartAtom K p (X ^ (p.natDegree - 1)) 1
          * (placeInfty K).differentialCoeff (dX K)
        ∈ (placeInfty K).simplePoleSubmodule),
    Algebra.trace K (placeInfty K).ResidueField
        ((placeInfty K).simplePoleResidueAux ⟨_, himem⟩)
      = -1

end NamedCarriers


section EraseLeadLinearity

variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

omit [DecidableEq (RatFunc K)] in

theorem p1PrincipalPartAtom_add_mul_differentialCoeff (p c₁ c₂ : K[X]) (m : ℕ)
    (v : Place K (RatFunc K)) (ω : Ω[(RatFunc K)⁄K]) :
    p1PrincipalPartAtom K p (c₁ + c₂) m * v.differentialCoeff ω
      = p1PrincipalPartAtom K p c₁ m * v.differentialCoeff ω
        + p1PrincipalPartAtom K p c₂ m * v.differentialCoeff ω := by
  show algebraMap K[X] (RatFunc K) (c₁ + c₂) / (algebraMap K[X] (RatFunc K) p) ^ m
        * v.differentialCoeff ω
    = algebraMap K[X] (RatFunc K) c₁ / (algebraMap K[X] (RatFunc K) p) ^ m * v.differentialCoeff ω
      + algebraMap K[X] (RatFunc K) c₂ / (algebraMap K[X] (RatFunc K) p) ^ m
        * v.differentialCoeff ω
  rw [map_add]; ring

omit [DecidableEq (RatFunc K)] in

theorem p1PrincipalPartAtom_C_mul_mul_differentialCoeff (p c : K[X]) (a : K) (m : ℕ)
    (v : Place K (RatFunc K)) (ω : Ω[(RatFunc K)⁄K]) :
    p1PrincipalPartAtom K p (C a * c) m * v.differentialCoeff ω
      = a • (p1PrincipalPartAtom K p c m * v.differentialCoeff ω) := by
  show algebraMap K[X] (RatFunc K) (C a * c) / (algebraMap K[X] (RatFunc K) p) ^ m
        * v.differentialCoeff ω
    = a • (algebraMap K[X] (RatFunc K) c / (algebraMap K[X] (RatFunc K) p) ^ m
        * v.differentialCoeff ω)
  rw [map_mul, C_eq_algebraMap, ← IsScalarTower.algebraMap_apply K K[X] (RatFunc K),
    Algebra.smul_def]
  ring

theorem trace_placeInfty_simplePoleResidueAux_mOne_add
    {p c₁ c₂ : K[X]} {ω : Ω[(RatFunc K)⁄K]}
    (h1 : p1PrincipalPartAtom K p c₁ 1 * (placeInfty K).differentialCoeff ω
        ∈ (placeInfty K).simplePoleSubmodule)
    (h2 : p1PrincipalPartAtom K p c₂ 1 * (placeInfty K).differentialCoeff ω
        ∈ (placeInfty K).simplePoleSubmodule)
    (h12 : p1PrincipalPartAtom K p (c₁ + c₂) 1 * (placeInfty K).differentialCoeff ω
        ∈ (placeInfty K).simplePoleSubmodule) :
    Algebra.trace K (placeInfty K).ResidueField
        ((placeInfty K).simplePoleResidueAux ⟨_, h12⟩)
      = Algebra.trace K (placeInfty K).ResidueField
          ((placeInfty K).simplePoleResidueAux ⟨_, h1⟩)
        + Algebra.trace K (placeInfty K).ResidueField
            ((placeInfty K).simplePoleResidueAux ⟨_, h2⟩) := by
  have heq : (⟨_, h12⟩ : (placeInfty K).simplePoleSubmodule)
      = (⟨_, h1⟩ : (placeInfty K).simplePoleSubmodule) + ⟨_, h2⟩ :=
    Subtype.ext (p1PrincipalPartAtom_add_mul_differentialCoeff K p c₁ c₂ 1 _ ω)
  rw [heq, map_add, map_add]

theorem trace_placeInfty_simplePoleResidueAux_mOne_C_mul
    {p c : K[X]} {a : K} {ω : Ω[(RatFunc K)⁄K]}
    (hc : p1PrincipalPartAtom K p c 1 * (placeInfty K).differentialCoeff ω
        ∈ (placeInfty K).simplePoleSubmodule)
    (hac : p1PrincipalPartAtom K p (C a * c) 1 * (placeInfty K).differentialCoeff ω
        ∈ (placeInfty K).simplePoleSubmodule) :
    Algebra.trace K (placeInfty K).ResidueField
        ((placeInfty K).simplePoleResidueAux ⟨_, hac⟩)
      = a * Algebra.trace K (placeInfty K).ResidueField
          ((placeInfty K).simplePoleResidueAux ⟨_, hc⟩) := by
  have heq : (⟨_, hac⟩ : (placeInfty K).simplePoleSubmodule)
      = a • (⟨_, hc⟩ : (placeInfty K).simplePoleSubmodule) :=
    Subtype.ext (p1PrincipalPartAtom_C_mul_mul_differentialCoeff K p c a 1 _ ω)
  rw [heq, map_smul, map_smul, smul_eq_mul]

theorem p1PlaceInftySimplePoleResidueEulerValue_of_topDeg
    (hInfty : (placeInfty K).ord ((placeInfty K).differentialCoeff (dX K)) = -2)
    (htop : P1PlaceInftySimplePoleResidueEulerValueTopDeg K) :
    P1PlaceInftySimplePoleResidueEulerValue K := by
  intro p c hpmon hpirr hcdeg himem
  rcases eq_or_ne c 0 with rfl | hc
  · exact trace_placeInfty_simplePoleResidue_mOne_of_lowDeg K hInfty hpirr (.inl rfl) himem
  have hndeg : c.natDegree < p.natDegree := natDegree_lt_natDegree hc hcdeg
  rcases (by omega : c.natDegree + 2 ≤ p.natDegree ∨ c.natDegree + 1 = p.natDegree) with h | h
  · exact trace_placeInfty_simplePoleResidue_mOne_of_lowDeg K hInfty hpirr (.inr h) himem
  · exact htop p c hpmon hpirr hc h himem

theorem p1PlaceInftySimplePoleResidueEulerValueTopDeg_of_monomial
    (hInfty : (placeInfty K).ord ((placeInfty K).differentialCoeff (dX K)) = -2)
    (hmono : P1PlaceInftySimplePoleResidueEulerValueMonomial K) :
    P1PlaceInftySimplePoleResidueEulerValueTopDeg K := by
  intro p c hpmon hpirr hc hcnd himem

  have hInfty' : (placeInfty K).ordDifferential (dX K) = -2 := hInfty
  have hXd : (X ^ (p.natDegree - 1) : K[X]).degree < p.degree := by
    rw [degree_X_pow, degree_eq_natDegree hpirr.ne_zero]
    exact_mod_cast (by omega : p.natDegree - 1 < p.natDegree)
  have hXmem := p1MOneAtom_mul_differentialCoeff_mem_simplePole_placeInfty K
    (dX_ne_zero K) hInfty' hpirr (X ^ (p.natDegree - 1)) hXd
  have hCXmem : p1PrincipalPartAtom K p (C c.leadingCoeff * X ^ (p.natDegree - 1)) 1
        * (placeInfty K).differentialCoeff (dX K)
      ∈ (placeInfty K).simplePoleSubmodule := by
    rw [p1PrincipalPartAtom_C_mul_mul_differentialCoeff K]
    exact (placeInfty K).simplePoleSubmodule.smul_mem _ hXmem
  have hELdeg : c.eraseLead = 0 ∨ c.eraseLead.natDegree + 2 ≤ p.natDegree := by
    rcases Polynomial.eraseLead_natDegree_lt_or_eraseLead_eq_zero c with h | h
    · exact .inr (by omega)
    · exact .inl h
  have hELmem : p1PrincipalPartAtom K p c.eraseLead 1 * (placeInfty K).differentialCoeff (dX K)
      ∈ (placeInfty K).simplePoleSubmodule :=
    (placeInfty K).mem_simplePoleSubmodule_of_mem
      (p1MOneAtom_mul_differentialCoeff_dX_mem_placeInfty K hInfty hpirr.ne_zero hELdeg)

  have hcnd' : c.natDegree = p.natDegree - 1 := by omega
  have hcdecomp : c = C c.leadingCoeff * X ^ (p.natDegree - 1) + c.eraseLead := by
    conv_lhs => rw [← Polynomial.eraseLead_add_C_mul_X_pow c, add_comm, hcnd']

  have h12mem : p1PrincipalPartAtom K p
        (C c.leadingCoeff * X ^ (p.natDegree - 1) + c.eraseLead) 1
          * (placeInfty K).differentialCoeff (dX K)
      ∈ (placeInfty K).simplePoleSubmodule := by
    rw [p1PrincipalPartAtom_add_mul_differentialCoeff K]; exact add_mem hCXmem hELmem
  have heq : (⟨_, himem⟩ : (placeInfty K).simplePoleSubmodule) = ⟨_, h12mem⟩ := by
    refine Subtype.ext ?_
    show algebraMap K[X] (RatFunc K) c / (algebraMap K[X] (RatFunc K) p) ^ 1
          * (placeInfty K).differentialCoeff (dX K)
      = algebraMap K[X] (RatFunc K) (C c.leadingCoeff * X ^ (p.natDegree - 1) + c.eraseLead)
          / (algebraMap K[X] (RatFunc K) p) ^ 1 * (placeInfty K).differentialCoeff (dX K)
    rw [← hcdecomp]

  have hELcoeff : c.eraseLead.coeff (p.natDegree - 1) = 0 := by
    rcases hELdeg with h | h
    · rw [h, coeff_zero]
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  have hLead : c.leadingCoeff = c.coeff (p.natDegree - 1) := by
    rw [leadingCoeff, hcnd']
  rw [heq, trace_placeInfty_simplePoleResidueAux_mOne_add K hCXmem hELmem,
    trace_placeInfty_simplePoleResidueAux_mOne_C_mul K hXmem,
    hmono p hpmon hpirr hXmem,
    trace_placeInfty_simplePoleResidue_mOne_of_lowDeg K hInfty hpirr hELdeg hELmem,
    hELcoeff, _root_.neg_zero, add_zero, hLead]
  ring

theorem p1PlaceInftySimplePoleResidueEulerValue_of_monomial
    (hInfty : (placeInfty K).ord ((placeInfty K).differentialCoeff (dX K)) = -2)
    (hmono : P1PlaceInftySimplePoleResidueEulerValueMonomial K) :
    P1PlaceInftySimplePoleResidueEulerValue K :=
  p1PlaceInftySimplePoleResidueEulerValue_of_topDeg K hInfty
    (p1PlaceInftySimplePoleResidueEulerValueTopDeg_of_monomial K hInfty hmono)

end EraseLeadLinearity


section ComposedEngine

variable [CharZero K]
variable [HasCanonicalDivisor (K := K) (F := RatFunc K)] [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

theorem p1PrincipalPartMOneSimplePoleCancel_of_inftyMonomial
    (hwd : OrdDifferentialWellDefined K (RatFunc K))
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0) (heq : ω₀ = dX K)
    (hmono : P1PlaceInftySimplePoleResidueEulerValueMonomial K) :
    P1PrincipalPartMOneSimplePoleCancel K hω₀ :=
  p1PrincipalPartMOneSimplePoleCancel_of_inftyBridge K hω₀ heq
    (p1PlaceInftySimplePoleResidueEulerValue_of_monomial K
      (ordDifferential_placeInfty_D_ratFuncX K hwd) hmono)

end ComposedEngine


end AlgebraicCurve


section AxiomAudits

end AxiomAudits


end

end


end


section
section

open _root_.IntermediateField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IntermediateField

namespace IntermediateField

export _root_.IntermediateField (charP toAlgebra map_le_iff_le_comap mk val isIntegral_iff topEquiv_apply lift_top lift AdjoinSimple.gen inclusion lift_injective lift_adjoin_simple ext adjoin_simple_le_iff charZero equivOfEq algebraMap_apply smul_def adjoin mk.injEq AdjoinSimple.algebraMap_gen comap topEquiv mem_top adjoinRootEquivAdjoin restrictScalars rec adjoinRootEquivAdjoin_apply_root coe_smul AdjoinSimple.coe_gen mem_bot mem_adjoin_simple_self adjoin_map smul_mem restrict map)

open _root_.IntermediateField

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem adjoin_simple_inv (t : F) : K⟮t⁻¹⟯ = K⟮t⟯ := by
  refine le_antisymm (adjoin_simple_le_iff.mpr ?_) (adjoin_simple_le_iff.mpr ?_)
  · exact inv_mem (mem_adjoin_simple_self K t)
  · have h : (t⁻¹)⁻¹ ∈ (K⟮t⁻¹⟯ : IntermediateField K F) :=
      inv_mem (mem_adjoin_simple_self K t⁻¹)
    rwa [inv_inv] at h

theorem algebraMap_comp_equivOfEq {S T : IntermediateField K F} (h : S = T) :
    (algebraMap T F).comp ((IntermediateField.equivOfEq h).toRingEquiv : S →+* T)
      = ((RingEquiv.refl F : F ≃+* F) : F →+* F).comp (algebraMap S F) := by
  ext x; rfl

theorem finiteDimensional_of_eq {S T : IntermediateField K F} (h : S = T)
    [FiniteDimensional ↥S F] : FiniteDimensional ↥T F :=
  Module.Finite.of_equiv_equiv (IntermediateField.equivOfEq h).toRingEquiv (RingEquiv.refl F)
    (algebraMap_comp_equivOfEq h)

theorem isSeparable_of_eq {S T : IntermediateField K F} (h : S = T)
    [Algebra.IsSeparable ↥S F] : Algebra.IsSeparable ↥T F :=
  Algebra.IsSeparable.of_equiv_equiv (IntermediateField.equivOfEq h).toRingEquiv
    (RingEquiv.refl F) (algebraMap_comp_equivOfEq h)

theorem finiteDimensional_adjoin_inv (t : F) [FiniteDimensional K⟮t⟯ F] :
    FiniteDimensional K⟮t⁻¹⟯ F :=
  finiteDimensional_of_eq (adjoin_simple_inv t).symm

theorem isSeparable_adjoin_inv (t : F) [Algebra.IsSeparable K⟮t⟯ F] :
    Algebra.IsSeparable K⟮t⁻¹⟯ F :=
  isSeparable_of_eq (adjoin_simple_inv t).symm

end IntermediateField


namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq)

open _root_.AlgebraicCurve

section CharZeroSeparable

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem isSeparable_of_charZero_of_finiteDimensional [CharZero K]
    (S : IntermediateField K F) [FiniteDimensional ↥S F] :
    Algebra.IsSeparable ↥S F :=
  haveI : CharZero ↥S := IntermediateField.charZero S
  Algebra.IsSeparable.of_integral ↥S F

theorem isSeparable_adjoin_of_charZero_of_finiteDimensional [CharZero K] (t : F)
    [FiniteDimensional K⟮t⟯ F] : Algebra.IsSeparable K⟮t⟯ F :=
  isSeparable_of_charZero_of_finiteDimensional K⟮t⟯

end CharZeroSeparable


section SeparatingTranscendentalCore

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

def HasSeparatingTranscendentalCore : Prop :=
  ∃ t : F, Transcendental K t ∧ FiniteDimensional K⟮t⟯ F

variable {K F}

theorem hasSeparatingTranscendental_of_core [CharZero K]
    (h : HasSeparatingTranscendentalCore K F) :
    HasSeparatingTranscendental K F := by
  obtain ⟨t, ht, hfin⟩ := h
  haveI : Algebra.IsSeparable K⟮t⟯ F :=
    isSeparable_adjoin_of_charZero_of_finiteDimensional t
  exact ⟨t, ht, hfin, ‹_›,
    IntermediateField.finiteDimensional_adjoin_inv t,
    IntermediateField.isSeparable_adjoin_inv t⟩

theorem valSubringKaehlerFinite_of_core [CharZero K]
    (h : HasSeparatingTranscendentalCore K F) :
    ValSubringKaehlerFinite K F :=
  valSubringKaehlerFinite_of_hasSeparatingTranscendental
    (hasSeparatingTranscendental_of_core h)

end SeparatingTranscendentalCore


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


section AxiomAudits

end AxiomAudits


end


end


section
section

set_option linter.unusedSectionVars false

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

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]

section MonicRatioResidue

theorem ord_placeInfty_X_pow_natDegree_div {p : K[X]} (hp : p ≠ 0) :
    (placeInfty K).ord
        (algebraMap K[X] (RatFunc K) (X ^ p.natDegree) / algebraMap K[X] (RatFunc K) p) = 0 := by
  have hp' : algebraMap K[X] (RatFunc K) p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hp
  have hXd : (X ^ p.natDegree : K[X]) ≠ 0 := pow_ne_zero _ X_ne_zero
  have hXd' : algebraMap K[X] (RatFunc K) (X ^ p.natDegree) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hXd
  rw [div_eq_mul_inv, (placeInfty K).ord_mul hXd' (inv_ne_zero hp'),
    (placeInfty K).ord_inv, ord_placeInfty_algebraMap' K hXd, ord_placeInfty_algebraMap' K hp,
    natDegree_X_pow]
  ring

theorem X_pow_natDegree_div_mem_placeInfty {p : K[X]} (hp : p ≠ 0) :
    algebraMap K[X] (RatFunc K) (X ^ p.natDegree) / algebraMap K[X] (RatFunc K) p
      ∈ (placeInfty K).toValuationSubring := by
  have hp' : algebraMap K[X] (RatFunc K) p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hp
  have hXd' : algebraMap K[X] (RatFunc K) (X ^ p.natDegree) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr
      (pow_ne_zero _ X_ne_zero)
  exact (placeInfty K).mem_of_ord_nonneg (div_ne_zero hXd' hp')
    (ord_placeInfty_X_pow_natDegree_div K hp).ge

theorem degree_X_pow_natDegree_sub_lt_of_monic {p : K[X]} (hpmon : p.Monic) :
    ((X : K[X]) ^ p.natDegree - p).degree < p.degree := by
  have hdeg : ((X : K[X]) ^ p.natDegree).degree = p.degree := by
    rw [degree_X_pow, degree_eq_natDegree hpmon.ne_zero]
  refine (Polynomial.degree_sub_lt hdeg (pow_ne_zero _ X_ne_zero) ?_).trans_le hdeg.le
  rw [Polynomial.leadingCoeff_X_pow, hpmon]

theorem residue_placeInfty_X_pow_natDegree_div_monic_eq_one {p : K[X]} (hpmon : p.Monic) :
    IsLocalRing.residue _ ⟨_, X_pow_natDegree_div_mem_placeInfty K hpmon.ne_zero⟩
      = (1 : (placeInfty K).ResidueField) := by
  rw [← sub_eq_zero, show (1 : (placeInfty K).ResidueField) = IsLocalRing.residue _ 1 from
      (map_one _).symm, ← map_sub, IsLocalRing.residue_eq_zero_iff]

  set d := p.natDegree
  have hp' : algebraMap K[X] (RatFunc K) p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hpmon.ne_zero

  have hsubmem : algebraMap K[X] (RatFunc K) (X ^ d - p) / algebraMap K[X] (RatFunc K) p
      ∈ (placeInfty K).toValuationSubring := by
    rcases eq_or_ne ((X : K[X]) ^ d - p) 0 with h0 | h0
    · simp only [h0, _root_.map_zero, zero_div]; exact zero_mem _
    have h0' : algebraMap K[X] (RatFunc K) (X ^ d - p) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr h0
    refine (placeInfty K).mem_of_ord_nonneg (div_ne_zero h0' hp') ?_
    rw [div_eq_mul_inv, (placeInfty K).ord_mul h0' (inv_ne_zero hp'),
      (placeInfty K).ord_inv, ord_placeInfty_algebraMap' K h0,
      ord_placeInfty_algebraMap' K hpmon.ne_zero]
    have hlt : ((X : K[X]) ^ d - p).natDegree < d :=
      Polynomial.natDegree_lt_natDegree h0 (degree_X_pow_natDegree_sub_lt_of_monic K hpmon)
    omega
  have hcoe : (⟨_, X_pow_natDegree_div_mem_placeInfty K hpmon.ne_zero⟩
        - 1 : (placeInfty K).toValuationSubring)
      = ⟨_, hsubmem⟩ := by
    refine Subtype.ext ?_
    show algebraMap K[X] (RatFunc K) (X ^ d) / algebraMap K[X] (RatFunc K) p - 1
      = algebraMap K[X] (RatFunc K) (X ^ d - p) / algebraMap K[X] (RatFunc K) p
    rw [map_sub, sub_div, div_self hp']
  rw [hcoe, Place.mk_mem_maximalIdeal_iff]
  rcases eq_or_ne ((X : K[X]) ^ d - p) 0 with h0 | h0
  · exact .inl (by simp [h0])
  · refine .inr ?_
    have h0' : algebraMap K[X] (RatFunc K) (X ^ d - p) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr h0
    rw [div_eq_mul_inv, (placeInfty K).ord_mul h0' (inv_ne_zero hp'),
      (placeInfty K).ord_inv, ord_placeInfty_algebraMap' K h0,
      ord_placeInfty_algebraMap' K hpmon.ne_zero]
    have hlt : ((X : K[X]) ^ d - p).natDegree < d :=
      Polynomial.natDegree_lt_natDegree h0 (degree_X_pow_natDegree_sub_lt_of_monic K hpmon)
    omega

end MonicRatioResidue


section NamedCarrier

variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

def P1PlaceInftySimplePoleResidueEulerValueX : Prop :=
  ∀ (himem : p1PrincipalPartAtom K (X : K[X]) 1 1 * (placeInfty K).differentialCoeff (dX K)
        ∈ (placeInfty K).simplePoleSubmodule),
    Algebra.trace K (placeInfty K).ResidueField
        ((placeInfty K).simplePoleResidueAux ⟨_, himem⟩)
      = -1

end NamedCarrier


section MonicRatioReduction

variable [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

theorem p1MonomialAtom_eq_monicRatio_mul {p : K[X]} (hpdeg : 1 ≤ p.natDegree) :
    p1PrincipalPartAtom K p (X ^ (p.natDegree - 1)) 1 * (placeInfty K).differentialCoeff (dX K)
      = (algebraMap K[X] (RatFunc K) (X ^ p.natDegree) / algebraMap K[X] (RatFunc K) p)
        * (p1PrincipalPartAtom K (X : K[X]) 1 1
            * (placeInfty K).differentialCoeff (dX K)) := by
  show algebraMap K[X] (RatFunc K) (X ^ (p.natDegree - 1)) / algebraMap K[X] (RatFunc K) p ^ 1
        * (placeInfty K).differentialCoeff (dX K)
    = algebraMap K[X] (RatFunc K) (X ^ p.natDegree) / algebraMap K[X] (RatFunc K) p
        * (algebraMap K[X] (RatFunc K) 1 / algebraMap K[X] (RatFunc K) X ^ 1
            * (placeInfty K).differentialCoeff (dX K))
  have hXd : algebraMap K[X] (RatFunc K) (X ^ p.natDegree)
      = algebraMap K[X] (RatFunc K) (X ^ (p.natDegree - 1)) * algebraMap K[X] (RatFunc K) X := by
    rw [← map_mul, ← pow_succ, Nat.sub_add_cancel hpdeg]
  have hX0 : algebraMap K[X] (RatFunc K) (X : K[X]) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr X_ne_zero
  rw [pow_one, pow_one, map_one, hXd, one_div]
  field_simp

theorem p1XInvAtom_mul_differentialCoeff_dX_mem_simplePole_placeInfty
    (hInfty : (placeInfty K).ordDifferential (dX K) = -2) :
    p1PrincipalPartAtom K (X : K[X]) 1 1 * (placeInfty K).differentialCoeff (dX K)
      ∈ (placeInfty K).simplePoleSubmodule :=
  p1MOneAtom_mul_differentialCoeff_mem_simplePole_placeInfty K (dX_ne_zero K) hInfty
    irreducible_X 1 (by rw [degree_one, degree_X]; decide)

theorem simplePoleResidueAux_placeInfty_monomial_eq_X
    (hInfty : (placeInfty K).ordDifferential (dX K) = -2)
    {p : K[X]} (hpmon : p.Monic) (hpirr : Irreducible p)
    (himem : p1PrincipalPartAtom K p (X ^ (p.natDegree - 1)) 1
          * (placeInfty K).differentialCoeff (dX K)
        ∈ (placeInfty K).simplePoleSubmodule) :
    (placeInfty K).simplePoleResidueAux ⟨_, himem⟩
      = (placeInfty K).simplePoleResidueAux
          ⟨_, p1XInvAtom_mul_differentialCoeff_dX_mem_simplePole_placeInfty K hInfty⟩ := by
  set hXmem := p1XInvAtom_mul_differentialCoeff_dX_mem_simplePole_placeInfty K hInfty

  have hfact := p1MonomialAtom_eq_monicRatio_mul K hpirr.natDegree_pos
  have hRatioMem := X_pow_natDegree_div_mem_placeInfty K hpmon.ne_zero
  have hprodmem : (algebraMap K[X] (RatFunc K) (X ^ p.natDegree)
          / algebraMap K[X] (RatFunc K) p)
        * (p1PrincipalPartAtom K (X : K[X]) 1 1 * (placeInfty K).differentialCoeff (dX K))
      ∈ (placeInfty K).simplePoleSubmodule :=
    (placeInfty K).mul_mem_simplePoleSubmodule_of_mem hRatioMem hXmem
  have heq : (⟨_, himem⟩ : (placeInfty K).simplePoleSubmodule) = ⟨_, hprodmem⟩ :=
    Subtype.ext hfact
  rw [heq, (placeInfty K).simplePoleResidueAux_mul_of_mem hRatioMem hXmem,
    residue_placeInfty_X_pow_natDegree_div_monic_eq_one K hpmon, one_mul]

theorem p1PlaceInftySimplePoleResidueEulerValueMonomial_of_X
    (hInfty : (placeInfty K).ordDifferential (dX K) = -2)
    (hX : P1PlaceInftySimplePoleResidueEulerValueX K) :
    P1PlaceInftySimplePoleResidueEulerValueMonomial K := by
  intro p hpmon hpirr himem
  rw [simplePoleResidueAux_placeInfty_monomial_eq_X K hInfty hpmon hpirr himem]
  exact hX _

end MonicRatioReduction


section ComposedEngine

variable [CharZero K]
variable [HasCanonicalDivisor (K := K) (F := RatFunc K)] [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

theorem p1PrincipalPartMOneSimplePoleCancel_of_inftyX
    (hwd : OrdDifferentialWellDefined K (RatFunc K))
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0) (heq : ω₀ = dX K)
    (hX : P1PlaceInftySimplePoleResidueEulerValueX K) :
    P1PrincipalPartMOneSimplePoleCancel K hω₀ :=
  p1PrincipalPartMOneSimplePoleCancel_of_inftyMonomial K hwd hω₀ heq
    (p1PlaceInftySimplePoleResidueEulerValueMonomial_of_X K
      (ordDifferential_placeInfty_D_ratFuncX K hwd) hX)

end ComposedEngine


section Monotonicity

variable [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

end Monotonicity


end AlgebraicCurve


section AxiomAudits

end AxiomAudits


end

end


end


section
section

open _root_.IntermediateField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IntermediateField

namespace IntermediateField

export _root_.IntermediateField (charP toAlgebra map_le_iff_le_comap mk val isIntegral_iff topEquiv_apply lift_top lift AdjoinSimple.gen inclusion lift_injective lift_adjoin_simple ext adjoin_simple_le_iff charZero equivOfEq algebraMap_apply smul_def adjoin mk.injEq AdjoinSimple.algebraMap_gen comap topEquiv mem_top adjoinRootEquivAdjoin restrictScalars rec adjoinRootEquivAdjoin_apply_root coe_smul AdjoinSimple.coe_gen mem_bot mem_adjoin_simple_self adjoin_map smul_mem restrict map)

open _root_.IntermediateField

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

theorem finiteDimensional_top : FiniteDimensional ↥(⊤ : IntermediateField K E) E :=
  Module.Finite.of_surjective (Algebra.linearMap (↥(⊤ : IntermediateField K E)) E)
    fun x => ⟨⟨x, mem_top⟩, rfl⟩

theorem adjoin_simple_gen_eq_top (α : E) :
    K⟮AdjoinSimple.gen K α⟯ = (⊤ : IntermediateField K ↥K⟮α⟯) :=
  (K⟮α⟯).lift_injective <| by
    rw [lift_adjoin_simple, AdjoinSimple.coe_gen, lift_top]

theorem transcendental_gen {α : E} (hα : Transcendental K α) :
    Transcendental K (AdjoinSimple.gen K α) := by
  rw [show α = algebraMap K⟮α⟯ E (AdjoinSimple.gen K α) from
    (AdjoinSimple.algebraMap_gen K α).symm] at hα
  exact (transcendental_algebraMap_iff (algebraMap K⟮α⟯ E).injective).mp hα

end IntermediateField


namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq)

open _root_.AlgebraicCurve

section PurelyTranscendentalSimple

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

def IsPurelyTranscendentalSimple : Prop :=
  ∃ t : F, Transcendental K t ∧ K⟮t⟯ = (⊤ : IntermediateField K F)

variable {K F}

theorem hasSeparatingTranscendentalCore_of_isPurelyTranscendentalSimple
    (h : IsPurelyTranscendentalSimple K F) :
    HasSeparatingTranscendentalCore K F := by
  obtain ⟨t, ht, htop⟩ := h
  haveI : FiniteDimensional ↥(⊤ : IntermediateField K F) F :=
    IntermediateField.finiteDimensional_top
  exact ⟨t, ht, IntermediateField.finiteDimensional_of_eq htop.symm⟩

end PurelyTranscendentalSimple


section SelfAdjoinInstance

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

theorem isPurelyTranscendentalSimple_adjoin_simple {α : E} (hα : Transcendental K α) :
    IsPurelyTranscendentalSimple K ↥K⟮α⟯ :=
  ⟨AdjoinSimple.gen K α, IntermediateField.transcendental_gen hα,
    IntermediateField.adjoin_simple_gen_eq_top α⟩

end SelfAdjoinInstance


section TowerComposites

variable {K F F' : Type*} [Field K] [Field F] [Field F']
variable [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']

end TowerComposites


section AdjoinTowerComposites

variable {K E F' : Type*} [Field K] [Field E] [Field F']
variable [Algebra K E] [Algebra K F']

end AdjoinTowerComposites


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


section AxiomAudits

end AxiomAudits


end


end

end P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed
