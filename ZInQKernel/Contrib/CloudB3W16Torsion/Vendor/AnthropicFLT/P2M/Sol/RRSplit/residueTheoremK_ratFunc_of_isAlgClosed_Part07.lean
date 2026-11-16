/-
Copyright 2026 Anthropic, PBC. Released under Apache License 2.0.
Source: https://github.com/anthropics/fermats-last-theorem
Revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.lean; source lines 11710-13170.
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
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.RRSplit.residueTheoremK_ratFunc_of_isAlgClosed_Part06

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
-- RRSplit attribute-prefixed source-private field bridge.
private noncomputable abbrev _root_.AlgebraicCurve.Place.centerLocalizationSubalgebra :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.centerLocalizationSubalgebra
-- RRSplit attribute-prefixed source-private field bridge.
private noncomputable abbrev _root_.AlgebraicCurve.Place.toKSubalgebra :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.toKSubalgebra


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
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.centerIdeal_ne_bot_of_isFractionRing :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.centerIdeal_ne_bot_of_isFractionRing
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.centerLocalizationSubalgebra_isDiscreteValuationRing :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.centerLocalizationSubalgebra_isDiscreteValuationRing
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.centerLocalizationSubalgebra_subset :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.centerLocalizationSubalgebra_subset
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.centerLocalizationValuationSubring :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.centerLocalizationValuationSubring
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.centerLocalizationValuationSubring_le :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.centerLocalizationValuationSubring_le
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.centerLocalizationValuationSubring_eq :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.centerLocalizationValuationSubring_eq
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.mem_centerLocalizationSubalgebra_of_mem :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.mem_centerLocalizationSubalgebra_of_mem
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.isLocalization_centerIdeal_of_isDedekindDomain :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.isLocalization_centerIdeal_of_isDedekindDomain
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.isIntegrallyClosed_toValuationSubring :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.isIntegrallyClosed_toValuationSubring
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.mem_valuationSubring_of_isIntegral :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.mem_valuationSubring_of_isIntegral
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.modelAlgebra_isScalarTower_top :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.modelAlgebra_isScalarTower_top
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.mem_valuationSubring_of_isIntegral_subalgebra :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.mem_valuationSubring_of_isIntegral_subalgebra
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.integralClosure_subset_valuationSubring :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.integralClosure_subset_valuationSubring
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.coe_toKSubalgebra :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.coe_toKSubalgebra
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.simplePoleResidueAux_mul_of_mem :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.simplePoleResidueAux_mul_of_mem
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.mul_mem_simplePoleSubmodule_of_mem :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.mul_mem_simplePoleSubmodule_of_mem
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.Transcendental.isPrincipalIdealRing_adjoin :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Transcendental.isPrincipalIdealRing_adjoin
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.Transcendental.isDedekindDomain_adjoin :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Transcendental.isDedekindDomain_adjoin
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.Transcendental.isIntegrallyClosed_adjoin :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Transcendental.isIntegrallyClosed_adjoin
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.Transcendental.isNoetherianRing_adjoin :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Transcendental.isNoetherianRing_adjoin
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.Algebra.FiniteType.adjoin_singleton :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Algebra.FiniteType.adjoin_singleton
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.Transcendental.inv :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Transcendental.inv
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.differentialCoeff_add'' :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.differentialCoeff_add''
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.differentialCoeff_D_uniformizer_pow_inv :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.differentialCoeff_D_uniformizer_pow_inv
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.ModularCurve.MilneAvAg9bRd13T2CoordIndepChar3.ag9b13t_res_differentialCoeff_D_mul_pow_inv_of_surj_of_natCast_ne_zero :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve.MilneAvAg9bRd13T2CoordIndepChar3.ag9b13t_res_differentialCoeff_D_mul_pow_inv_of_surj_of_natCast_ne_zero


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

section KernelEngine

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
variable [HasPrincipalDivisors K F]

def kaehlerResidueFunctionalK (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK)
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) : F →ₗ[K] K :=
  (weilOfKaehlerK Rfam hω).comp (principalAdele K F)

theorem kaehlerResidueFunctionalK_eq_finsum
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK) {ω : Ω[F⁄K]} (hω : ω ≠ 0) (f : F) :
    kaehlerResidueFunctionalK Rfam hω f
      = ∑ᶠ v, kaehlerResidueTermKFam Rfam ω (diagonalHom K F f) v := rfl

theorem kaehlerResidueFunctionalK_eq_zero_of_term_zero_compl
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK) {ω : Ω[F⁄K]} (hω : ω ≠ 0) {f : F}
    {T : Finset (Place K F)}
    (hcompl : ∀ v ∉ T, kaehlerResidueTermKFam Rfam ω (diagonalHom K F f) v = 0)
    (hsum : ∑ v ∈ T, kaehlerResidueTermKFam Rfam ω (diagonalHom K F f) v = 0) :
    kaehlerResidueFunctionalK Rfam hω f = 0 := by
  rw [kaehlerResidueFunctionalK_eq_finsum Rfam hω f,
    finsum_eq_finsetSum_of_support_subset _
      (fun v hv => by_contra fun hT => hv (hcompl v hT))]
  exact hsum

theorem kaehlerResidueFunctionalK_eq_zero_of_singleton
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK) {ω : Ω[F⁄K]} (hω : ω ≠ 0) {f : F}
    {v₀ : Place K F}
    (hcompl : ∀ v, v ≠ v₀ → kaehlerResidueTermKFam Rfam ω (diagonalHom K F f) v = 0)
    (hv₀ : kaehlerResidueTermKFam Rfam ω (diagonalHom K F f) v₀ = 0) :
    kaehlerResidueFunctionalK Rfam hω f = 0 := by
  classical
  refine kaehlerResidueFunctionalK_eq_zero_of_term_zero_compl Rfam hω (T := {v₀}) ?_ ?_
  · intro v hv
    exact hcompl v (by simpa using hv)
  · simpa using hv₀

theorem kaehlerResidueFunctionalK_eq_zero_of_pair
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK) {ω : Ω[F⁄K]} (hω : ω ≠ 0) {f : F}
    {v₀ v₁ : Place K F} (hne : v₀ ≠ v₁)
    (hcompl : ∀ v, v ≠ v₀ → v ≠ v₁ → kaehlerResidueTermKFam Rfam ω (diagonalHom K F f) v = 0)
    (hsum : kaehlerResidueTermKFam Rfam ω (diagonalHom K F f) v₀
      + kaehlerResidueTermKFam Rfam ω (diagonalHom K F f) v₁ = 0) :
    kaehlerResidueFunctionalK Rfam hω f = 0 := by
  classical
  refine kaehlerResidueFunctionalK_eq_zero_of_term_zero_compl Rfam hω (T := {v₀, v₁}) ?_ ?_
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv
    exact hcompl v hv.1 hv.2
  · rw [Finset.sum_pair hne]
    exact hsum

end KernelEngine


section SimplePoleSeam

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]

theorem kaehlerResidueTermKFam_eq_of_mem_simplePoleSubmodule
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK)
    {ω : Ω[F⁄K]} {f : F} {v : Place K F}
    (hmem : f * v.differentialCoeff ω ∈ v.simplePoleSubmodule) :
    kaehlerResidueTermKFam Rfam ω (diagonalHom K F f) v
      = Algebra.trace K v.ResidueField
          (v.simplePoleResidueAux ⟨f * v.differentialCoeff ω, hmem⟩) := by
  rw [kaehlerResidueTermKFam_apply, diagonalHom_apply,
    (Rfam v).res_simplePole (f * v.differentialCoeff ω) hmem]
  rfl

end SimplePoleSeam


section SmulReduction

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

theorem kaehlerResidueTermKFam_smul_diagonal
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK)
    (g : F) (ω : Ω[F⁄K]) (f : F) (v : Place K F) :
    kaehlerResidueTermKFam Rfam (g • ω) (diagonalHom K F f) v
      = kaehlerResidueTermKFam Rfam ω (diagonalHom K F (g * f)) v := by
  simp only [kaehlerResidueTermKFam_apply, diagonalHom_apply]
  rw [v.differentialCoeff_smul,
    show f * (g * v.differentialCoeff ω) = g * f * v.differentialCoeff ω by ring]

variable [HasCanonicalDivisor (K := K) (F := F)]

theorem weilOfKaehlerK_smul_diagonal [HasPrincipalDivisors K F]
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK) {g : F} {ω : Ω[F⁄K]}
    (hω : ω ≠ 0) (hgω : g • ω ≠ 0) (f : F) :
    weilOfKaehlerK Rfam hgω ⟨diagonalHom K F f, diagonal_mem_adeleSpace f⟩
      = weilOfKaehlerK Rfam hω
          ⟨diagonalHom K F (g * f), diagonal_mem_adeleSpace (g * f)⟩ := by
  rw [weilOfKaehlerK_apply, weilOfKaehlerK_apply]
  exact finsum_congr fun v => kaehlerResidueTermKFam_smul_diagonal Rfam g ω f v

end SmulReduction


section PerGenerator

variable {K : Type*} [Field K] [CharZero K] [DecidableEq (RatFunc K)]
variable [HasPrincipalDivisors K (RatFunc K)]

theorem kaehlerResidueFunctionalK_dX_X_pow
    (Rfam : ∀ v : Place K (RatFunc K), v.CanonicalLocalResidueDataK) (n : ℕ) :
    kaehlerResidueFunctionalK Rfam (dX_ne_zero K) ((RatFunc.X : RatFunc K) ^ n) = 0 := by
  refine kaehlerResidueFunctionalK_eq_zero_of_singleton Rfam (dX_ne_zero K)
    (v₀ := placeInfty K) ?_ ?_
  ·
    intro v hv
    refine kaehlerResidueTermKFam_eq_zero_of_ord_nonneg Rfam ?_
    rw [diagonalHom_apply]
    exact Or.inr (v.ord_nonneg_of_mem
      (pow_X_mul_mem_of_ne_placeInfty K hv n (p1DifferentialCoeffRegularFinite_dX K v hv)))
  ·
    exact residueTheoremK_placeInfty_clause_X_pow Rfam n

theorem kaehlerResidueTermKFam_atom_eq_zero_of_ne_of_ne
    (Rfam : ∀ v : Place K (RatFunc K), v.CanonicalLocalResidueDataK)
    {p : K[X]} (hpirr : Irreducible p) (c : K[X]) (m : ℕ) {v : Place K (RatFunc K)}
    (hvp : v ≠ finitePlace K hpirr) (hvinf : v ≠ placeInfty K) :
    kaehlerResidueTermKFam Rfam (dX K)
      (diagonalHom K (RatFunc K) (p1PrincipalPartAtom K p c m)) v = 0 := by
  refine kaehlerResidueTermKFam_eq_zero_of_ord_nonneg Rfam ?_
  rw [diagonalHom_apply]
  exact Or.inr (v.ord_nonneg_of_mem
    (mul_mem (p1PrincipalPartAtom_mem_of_ne_finitePlace K hpirr c m hvp hvinf)
      (p1DifferentialCoeffRegularFinite_dX K v hvinf)))

theorem kaehlerResidueTermKFam_atom_placeInfty_eq_zero_of_two_le
    (Rfam : ∀ v : Place K (RatFunc K), v.CanonicalLocalResidueDataK)
    (hwd : OrdDifferentialWellDefined K (RatFunc K))
    {p : K[X]} (hpirr : Irreducible p) (c : K[X]) {m : ℕ}
    (hdeg : c.degree < p.degree) (hm : 2 ≤ m) :
    kaehlerResidueTermKFam Rfam (dX K)
      (diagonalHom K (RatFunc K) (p1PrincipalPartAtom K p c m)) (placeInfty K) = 0 := by
  refine kaehlerResidueTermKFam_eq_zero_of_ord_nonneg Rfam ?_
  rw [diagonalHom_apply]
  rcases eq_or_ne c 0 with rfl | hc
  · left
    show algebraMap K[X] (RatFunc K) 0 / (algebraMap K[X] (RatFunc K) p) ^ m
        * (placeInfty K).differentialCoeff (dX K) = 0
    rw [_root_.map_zero, zero_div, zero_mul]
  · right
    have hatom0 : p1PrincipalPartAtom K p c m ≠ 0 :=
      p1PrincipalPartAtom_ne_zero K hpirr.ne_zero hc m
    have hd0 : (placeInfty K).differentialCoeff (dX K) ≠ 0 :=
      (placeInfty K).differentialCoeff_ne_zero (dX_ne_zero K)
    rw [(placeInfty K).ord_mul hatom0 hd0]
    have h2 : 2 ≤ (placeInfty K).ord (p1PrincipalPartAtom K p c m) :=
      two_le_ord_placeInfty_p1PrincipalPartAtom K hpirr hc hdeg hm
    have hordD : (placeInfty K).ord ((placeInfty K).differentialCoeff (dX K)) = -2 :=
      ordDifferential_placeInfty_D_ratFuncX K hwd
    omega

theorem kaehlerResidueTermKFam_atom_finitePlace_eq_zero_of_two_le
    (Rfam : ∀ v : Place K (RatFunc K), v.CanonicalLocalResidueDataK)
    (hcoord : CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K))
    (hHigh5 : P1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg K)
    {p c : K[X]} {m : ℕ} (hpmon : p.Monic) (hpirr : Irreducible p)
    (hdeg : c.degree < p.degree) (hm : 2 ≤ m) :
    kaehlerResidueTermKFam Rfam (dX K)
      (diagonalHom K (RatFunc K) (p1PrincipalPartAtom K p c m)) (finitePlace K hpirr) = 0 := by
  rw [kaehlerResidueTermKFam_apply, diagonalHom_apply]
  exact p1FinitePlaceCanonicalResidueAtomMGeTwoTrace_of_coordIndep_higherDeg K hcoord hHigh5
    p c m hpmon hpirr hdeg hm (Rfam (finitePlace K hpirr))

theorem kaehlerResidueTermKFam_atom_mOne_two_place_sum
    (Rfam : ∀ v : Place K (RatFunc K), v.CanonicalLocalResidueDataK)
    (hwd : OrdDifferentialWellDefined K (RatFunc K))
    (hsp : CanonicalLocalResidueKSimplePoleCoordIndep K (RatFunc K))
    {p c : K[X]} (hpmon : p.Monic) (hpirr : Irreducible p) (hdeg : c.degree < p.degree) :
    kaehlerResidueTermKFam Rfam (dX K)
        (diagonalHom K (RatFunc K) (p1PrincipalPartAtom K p c 1)) (finitePlace K hpirr)
      + kaehlerResidueTermKFam Rfam (dX K)
          (diagonalHom K (RatFunc K) (p1PrincipalPartAtom K p c 1)) (placeInfty K) = 0 := by

  have hfmem := p1MOneAtom_mul_differentialCoeff_mem_simplePole_finitePlace K
    (dX_ne_zero K) (p1DifferentialCoeffUnitFinite_dX K) hpirr c hdeg
  have himem := p1MOneAtom_mul_differentialCoeff_mem_simplePole_placeInfty K
    (dX_ne_zero K) (ordDifferential_placeInfty_D_ratFuncX K hwd) hpirr c hdeg

  rw [kaehlerResidueTermKFam_eq_of_mem_simplePoleSubmodule Rfam hfmem,
    kaehlerResidueTermKFam_eq_of_mem_simplePoleSubmodule Rfam himem]

  exact p1PrincipalPartMOneSimplePoleCancel_of_simplePoleCoordIndep K hwd
    (dX_ne_zero K) rfl hsp p c hpmon hpirr hdeg hfmem himem

theorem kaehlerResidueFunctionalK_dX_atom
    (Rfam : ∀ v : Place K (RatFunc K), v.CanonicalLocalResidueDataK)
    (hwd : OrdDifferentialWellDefined K (RatFunc K))
    (hcoord : CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K))
    (hsp : CanonicalLocalResidueKSimplePoleCoordIndep K (RatFunc K))
    (hHigh5 : P1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg K)
    {p c : K[X]} {m : ℕ} (hpmon : p.Monic) (hpirr : Irreducible p)
    (hdeg : c.degree < p.degree) (hm : 1 ≤ m) :
    kaehlerResidueFunctionalK Rfam (dX_ne_zero K) (p1PrincipalPartAtom K p c m) = 0 := by
  refine kaehlerResidueFunctionalK_eq_zero_of_pair Rfam (dX_ne_zero K)
    (finitePlace_ne_placeInfty hpirr)
    (fun v hvp hvinf => kaehlerResidueTermKFam_atom_eq_zero_of_ne_of_ne Rfam hpirr c m
      hvp hvinf) ?_

  rcases eq_or_lt_of_le hm with rfl | hm2
  ·
    exact kaehlerResidueTermKFam_atom_mOne_two_place_sum Rfam hwd hsp hpmon hpirr hdeg
  ·
    rw [kaehlerResidueTermKFam_atom_finitePlace_eq_zero_of_two_le Rfam hcoord hHigh5
        hpmon hpirr hdeg hm2,
      kaehlerResidueTermKFam_atom_placeInfty_eq_zero_of_two_le Rfam hwd hpirr c hdeg hm2,
      add_zero]

theorem kaehlerResidueFunctionalK_dX_eq_zero
    (Rfam : ∀ v : Place K (RatFunc K), v.CanonicalLocalResidueDataK)
    (hwd : OrdDifferentialWellDefined K (RatFunc K))
    (hcoord : CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K))
    (hsp : CanonicalLocalResidueKSimplePoleCoordIndep K (RatFunc K))
    (hHigh5 : P1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg K)
    (h : RatFunc K) :
    kaehlerResidueFunctionalK Rfam (dX_ne_zero K) h = 0 := by

  have hker : Submodule.span K (P1PartialFractionGenerators K)
      ≤ LinearMap.ker (kaehlerResidueFunctionalK Rfam (dX_ne_zero K)) := by
    rw [Submodule.span_le]
    rintro s hs
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    rcases hs with hpoly | hatom
    · obtain ⟨n, rfl⟩ := hpoly
      exact kaehlerResidueFunctionalK_dX_X_pow Rfam n
    · obtain ⟨p, c, m, hpmon, hpirr, hdeg, hm, rfl⟩ := hatom
      exact kaehlerResidueFunctionalK_dX_atom Rfam hwd hcoord hsp hHigh5 hpmon hpirr hdeg hm

  have hh : h ∈ LinearMap.ker (kaehlerResidueFunctionalK Rfam (dX_ne_zero K)) := by
    apply hker
    rw [p1PartialFractionSpan_eq_top]
    exact Submodule.mem_top
  exact LinearMap.mem_ker.mp hh

end PerGenerator


section Engine

variable {K : Type*} [Field K] [CharZero K] [DecidableEq (RatFunc K)]

theorem residueTheoremK_ratFunc_of_subrows
    (hwd : OrdDifferentialWellDefined K (RatFunc K))
    (hcoord : CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K))
    (hsp : CanonicalLocalResidueKSimplePoleCoordIndep K (RatFunc K))
    (hHigh5 : P1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg K) :
    ResidueTheoremK K (RatFunc K) := by
  intro Rfam instHPD ω hω f

  obtain ⟨g, hg, rfl⟩ := exists_smul_eq_of_ne_zero (placeInfty K) hω (dX_ne_zero K)
  calc weilOfKaehlerK Rfam hω
        ⟨diagonalHom K (RatFunc K) f, diagonal_mem_adeleSpace f⟩
      = weilOfKaehlerK Rfam (dX_ne_zero K)
          ⟨diagonalHom K (RatFunc K) (g * f), diagonal_mem_adeleSpace (g * f)⟩ :=
        weilOfKaehlerK_smul_diagonal Rfam (dX_ne_zero K) hω f
    _ = 0 := kaehlerResidueFunctionalK_dX_eq_zero Rfam hwd hcoord hsp hHigh5 (g * f)

end Engine


section AlgClosedDischarge

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] [DecidableEq (RatFunc K)]

theorem residueTheoremK_ratFunc_of_isAlgClosed_main : ResidueTheoremK K (RatFunc K) :=
  residueTheoremK_ratFunc_of_subrows
    (ordDifferentialWellDefined_ratFunc K)
    (canonicalLocalResidueKDifferentialCoordIndep_ratFunc_of_isAlgClosed K)
    (canonicalLocalResidueKSimplePoleCoordIndep_ratFunc K)
    (p1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg_of_algClosed K)

end AlgClosedDischarge


section BridgeCorollary

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] [DecidableEq (RatFunc K)]

end BridgeCorollary


end AlgebraicCurve


section AxiomAudit

end AxiomAudit


end


end


end


section
section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000
set_option synthInstance.maxSize 4096
set_option maxRecDepth 8000

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

section MOnePerfect

theorem p0n21_rtk_p1MOneSimplePoleCancel_dX_of_perfectField
    (K : Type*) [Field K] [PerfectField K] [DecidableEq (RatFunc K)] :
    P1PrincipalPartMOneSimplePoleCancel K (dX_ne_zero K) :=
  ag9b12c_p1MOneSimplePoleCancel_dX_of_inftyEulerValue_of_perfectField K
    (ag9b13e_p1PlaceInftySimplePoleResidueEulerValue_of_perfectField K)

end MOnePerfect


section PerGenerator

variable {K : Type*} [Field K] [PerfectField K] [DecidableEq (RatFunc K)]
variable [HasPrincipalDivisors K (RatFunc K)]

theorem p0n21_rtk_kaehlerResidueFunctionalK_dX_X_pow
    (Rfam : ∀ v : Place K (RatFunc K), v.CanonicalLocalResidueDataK)
    (hwd : OrdDifferentialWellDefined K (RatFunc K))
    (hcoord : CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K)) (n : ℕ) :
    kaehlerResidueFunctionalK Rfam (dX_ne_zero K) ((RatFunc.X : RatFunc K) ^ n) = 0 := by
  refine kaehlerResidueFunctionalK_eq_zero_of_singleton Rfam (dX_ne_zero K)
    (v₀ := placeInfty K) ?_ ?_
  ·
    intro v hv
    refine kaehlerResidueTermKFam_eq_zero_of_ord_nonneg Rfam ?_
    rw [diagonalHom_apply]
    exact Or.inr (v.ord_nonneg_of_mem
      (pow_X_mul_mem_of_ne_placeInfty K hv n
        (p1DifferentialCoeffRegularFinite_dX_of_perfectField K v hv)))
  ·
    rw [kaehlerResidueTermKFam_apply]
    exact canonicalLocalResidueDataK_kaehlerResidueTerm_X_pow_of_coordIndep K hwd hcoord
      (Rfam (placeInfty K)) n

theorem p0n21_rtk_kaehlerResidueTermKFam_atom_eq_zero_of_ne_of_ne
    (Rfam : ∀ v : Place K (RatFunc K), v.CanonicalLocalResidueDataK)
    {p : K[X]} (hpirr : Irreducible p) (c : K[X]) (m : ℕ) {v : Place K (RatFunc K)}
    (hvp : v ≠ finitePlace K hpirr) (hvinf : v ≠ placeInfty K) :
    kaehlerResidueTermKFam Rfam (dX K)
      (diagonalHom K (RatFunc K) (p1PrincipalPartAtom K p c m)) v = 0 := by
  refine kaehlerResidueTermKFam_eq_zero_of_ord_nonneg Rfam ?_
  rw [diagonalHom_apply]
  exact Or.inr (v.ord_nonneg_of_mem
    (mul_mem (p1PrincipalPartAtom_mem_of_ne_finitePlace K hpirr c m hvp hvinf)
      (p1DifferentialCoeffRegularFinite_dX_of_perfectField K v hvinf)))

theorem p0n21_rtk_kaehlerResidueTermKFam_atom_placeInfty_eq_zero_of_two_le
    (Rfam : ∀ v : Place K (RatFunc K), v.CanonicalLocalResidueDataK)
    (hwd : OrdDifferentialWellDefined K (RatFunc K))
    {p : K[X]} (hpirr : Irreducible p) (c : K[X]) {m : ℕ}
    (hdeg : c.degree < p.degree) (hm : 2 ≤ m) :
    kaehlerResidueTermKFam Rfam (dX K)
      (diagonalHom K (RatFunc K) (p1PrincipalPartAtom K p c m)) (placeInfty K) = 0 := by
  refine kaehlerResidueTermKFam_eq_zero_of_ord_nonneg Rfam ?_
  rw [diagonalHom_apply]
  rcases eq_or_ne c 0 with rfl | hc
  · left
    show algebraMap K[X] (RatFunc K) 0 / (algebraMap K[X] (RatFunc K) p) ^ m
        * (placeInfty K).differentialCoeff (dX K) = 0
    rw [_root_.map_zero, zero_div, zero_mul]
  · right
    have hatom0 : p1PrincipalPartAtom K p c m ≠ 0 :=
      p1PrincipalPartAtom_ne_zero K hpirr.ne_zero hc m
    have hd0 : (placeInfty K).differentialCoeff (dX K) ≠ 0 :=
      (placeInfty K).differentialCoeff_ne_zero (dX_ne_zero K)
    rw [(placeInfty K).ord_mul hatom0 hd0]
    have h2 : 2 ≤ (placeInfty K).ord (p1PrincipalPartAtom K p c m) :=
      two_le_ord_placeInfty_p1PrincipalPartAtom K hpirr hc hdeg hm
    have hordD : (placeInfty K).ord ((placeInfty K).differentialCoeff (dX K)) = -2 :=
      ordDifferential_placeInfty_D_ratFuncX K hwd
    omega

theorem p0n21_rtk_kaehlerResidueTermKFam_atom_finitePlace_eq_zero_of_two_le
    (Rfam : ∀ v : Place K (RatFunc K), v.CanonicalLocalResidueDataK)
    (hcoord : CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K))
    (hHigh5 : P1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg K)
    {p c : K[X]} {m : ℕ} (hpmon : p.Monic) (hpirr : Irreducible p)
    (hdeg : c.degree < p.degree) (hm : 2 ≤ m) :
    kaehlerResidueTermKFam Rfam (dX K)
      (diagonalHom K (RatFunc K) (p1PrincipalPartAtom K p c m)) (finitePlace K hpirr) = 0 := by
  rw [kaehlerResidueTermKFam_apply, diagonalHom_apply]
  exact p1FinitePlaceCanonicalResidueAtomMGeTwoTrace_of_coordIndep_higherDeg K hcoord hHigh5
    p c m hpmon hpirr hdeg hm (Rfam (finitePlace K hpirr))

theorem p0n21_rtk_kaehlerResidueTermKFam_atom_mOne_two_place_sum
    (Rfam : ∀ v : Place K (RatFunc K), v.CanonicalLocalResidueDataK)
    (hwd : OrdDifferentialWellDefined K (RatFunc K))
    {p c : K[X]} (hpmon : p.Monic) (hpirr : Irreducible p) (hdeg : c.degree < p.degree) :
    kaehlerResidueTermKFam Rfam (dX K)
        (diagonalHom K (RatFunc K) (p1PrincipalPartAtom K p c 1)) (finitePlace K hpirr)
      + kaehlerResidueTermKFam Rfam (dX K)
          (diagonalHom K (RatFunc K) (p1PrincipalPartAtom K p c 1)) (placeInfty K) = 0 := by
  have hfmem := p1MOneAtom_mul_differentialCoeff_mem_simplePole_finitePlace K
    (dX_ne_zero K) (p1DifferentialCoeffUnitFinite_dX_of_perfectField K) hpirr c hdeg
  have himem := p1MOneAtom_mul_differentialCoeff_mem_simplePole_placeInfty K
    (dX_ne_zero K) (ordDifferential_placeInfty_D_ratFuncX K hwd) hpirr c hdeg
  rw [kaehlerResidueTermKFam_eq_of_mem_simplePoleSubmodule Rfam hfmem,
    kaehlerResidueTermKFam_eq_of_mem_simplePoleSubmodule Rfam himem]
  exact p0n21_rtk_p1MOneSimplePoleCancel_dX_of_perfectField K p c hpmon hpirr hdeg hfmem himem

theorem p0n21_rtk_kaehlerResidueFunctionalK_dX_atom
    (Rfam : ∀ v : Place K (RatFunc K), v.CanonicalLocalResidueDataK)
    (hwd : OrdDifferentialWellDefined K (RatFunc K))
    (hcoord : CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K))
    (hHigh5 : P1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg K)
    {p c : K[X]} {m : ℕ} (hpmon : p.Monic) (hpirr : Irreducible p)
    (hdeg : c.degree < p.degree) (hm : 1 ≤ m) :
    kaehlerResidueFunctionalK Rfam (dX_ne_zero K) (p1PrincipalPartAtom K p c m) = 0 := by
  refine kaehlerResidueFunctionalK_eq_zero_of_pair Rfam (dX_ne_zero K)
    (finitePlace_ne_placeInfty hpirr)
    (fun v hvp hvinf => p0n21_rtk_kaehlerResidueTermKFam_atom_eq_zero_of_ne_of_ne Rfam hpirr
      c m hvp hvinf) ?_
  rcases eq_or_lt_of_le hm with rfl | hm2
  · exact p0n21_rtk_kaehlerResidueTermKFam_atom_mOne_two_place_sum Rfam hwd hpmon hpirr hdeg
  · rw [p0n21_rtk_kaehlerResidueTermKFam_atom_finitePlace_eq_zero_of_two_le Rfam hcoord hHigh5
        hpmon hpirr hdeg hm2,
      p0n21_rtk_kaehlerResidueTermKFam_atom_placeInfty_eq_zero_of_two_le Rfam hwd hpirr c
        hdeg hm2,
      add_zero]

theorem p0n21_rtk_kaehlerResidueFunctionalK_dX_eq_zero
    (Rfam : ∀ v : Place K (RatFunc K), v.CanonicalLocalResidueDataK)
    (hwd : OrdDifferentialWellDefined K (RatFunc K))
    (hcoord : CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K))
    (hHigh5 : P1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg K)
    (h : RatFunc K) :
    kaehlerResidueFunctionalK Rfam (dX_ne_zero K) h = 0 := by
  have hker : Submodule.span K (P1PartialFractionGenerators K)
      ≤ LinearMap.ker (kaehlerResidueFunctionalK Rfam (dX_ne_zero K)) := by
    rw [Submodule.span_le]
    rintro s hs
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    rcases hs with hpoly | hatom
    · obtain ⟨n, rfl⟩ := hpoly
      exact p0n21_rtk_kaehlerResidueFunctionalK_dX_X_pow Rfam hwd hcoord n
    · obtain ⟨p, c, m, hpmon, hpirr, hdeg, hm, rfl⟩ := hatom
      exact p0n21_rtk_kaehlerResidueFunctionalK_dX_atom Rfam hwd hcoord hHigh5 hpmon hpirr
        hdeg hm
  have hh : h ∈ LinearMap.ker (kaehlerResidueFunctionalK Rfam (dX_ne_zero K)) := by
    apply hker
    rw [p1PartialFractionSpan_eq_top]
    exact Submodule.mem_top
  exact LinearMap.mem_ker.mp hh

end PerGenerator


section EngineCharFree

variable {K : Type*} [Field K] [PerfectField K] [DecidableEq (RatFunc K)]

theorem p0n21_rtk_residueTheoremK_ratFunc_of_subrows_charFree
    (hwd : OrdDifferentialWellDefined K (RatFunc K))
    (hcoord : CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K))
    (hHigh5 : P1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg K) :
    ResidueTheoremK K (RatFunc K) := by
  intro Rfam instHPD ω hω f
  obtain ⟨g, hg, rfl⟩ := exists_smul_eq_of_ne_zero (placeInfty K) hω (dX_ne_zero K)
  calc weilOfKaehlerK Rfam hω
        ⟨diagonalHom K (RatFunc K) f, diagonal_mem_adeleSpace f⟩
      = weilOfKaehlerK Rfam (dX_ne_zero K)
          ⟨diagonalHom K (RatFunc K) (g * f), diagonal_mem_adeleSpace (g * f)⟩ :=
        weilOfKaehlerK_smul_diagonal Rfam (dX_ne_zero K) hω f
    _ = 0 := p0n21_rtk_kaehlerResidueFunctionalK_dX_eq_zero Rfam hwd hcoord hHigh5 (g * f)

theorem p0n21_rtk_residueTheoremK_ratFunc_of_coordIndep_higherDeg_of_perfectField
    (hcoord : CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K))
    (hHigh5 : P1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg K) :
    ResidueTheoremK K (RatFunc K) :=
  p0n21_rtk_residueTheoremK_ratFunc_of_subrows_charFree
    (ordDifferentialWellDefined_ratFunc_of_perfectField K) hcoord hHigh5

end EngineCharFree


section AlgClosedAnyChar

theorem p0n21_rtk_residueTheoremK_ratFunc_of_isAlgClosed_of_coordIndep
    (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)]
    (hcoord : CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K)) :
    ResidueTheoremK K (RatFunc K) :=
  p0n21_rtk_residueTheoremK_ratFunc_of_coordIndep_higherDeg_of_perfectField hcoord
    (p1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg_of_algClosed K)

end AlgClosedAnyChar


section Bc2Carrier



end Bc2Carrier


section ResidualLocation

theorem p0n21_rtk_surjective_algebraMap_residueField_of_deg_eq_one
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hdeg : v.deg = 1) :
    Function.Surjective (algebraMap K v.ResidueField) := by
  intro z
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : v.ResidueField) one_ne_zero).mp
    (show Module.finrank K v.ResidueField = 1 from hdeg) z
  exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one]; exact hc⟩

theorem p0n21_rtk_surjective_algebraMap_residueField_ratFunc_of_isAlgClosed
    (K : Type*) [Field K] [IsAlgClosed K] (v : Place K (RatFunc K)) :
    Function.Surjective (algebraMap K v.ResidueField) := by
  classical
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
  · obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
    refine p0n21_rtk_surjective_algebraMap_residueField_of_deg_eq_one _ ?_
    rw [deg_ofHeightOneSpectrum K hwp]
    have h := IsAlgClosed.degree_eq_one_of_irreducible K hp
    rw [degree_eq_natDegree hp.ne_zero] at h
    exact_mod_cast h
  · exact surjective_algebraMap_residueField_placeInfty K

end ResidualLocation


end AlgebraicCurve


end


end


end


section
section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000
set_option synthInstance.maxSize 4096
set_option maxRecDepth 8000

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

section CharFreeToolkit

variable {K : Type*} [Field K] [PerfectField K]

theorem p0n22_cpf_uniformizer_pow_mul_mem_cases
    (v : Place K (RatFunc K))
    {σ : RatFunc K} (hσ : σ ∈ v.toValuationSubring) {k : ℕ} (hk : 1 ≤ k) :
    v.uniformizer ^ k * σ = 0 ∨ 1 ≤ v.ord (v.uniformizer ^ k * σ) := by
  rcases eq_or_ne σ 0 with rfl | hσ0
  · exact Or.inl (mul_zero _)
  · right
    rw [v.ord_mul (v.uniformizer_pow_ne_zero k) hσ0, v.ord_uniformizer_pow]
    have := v.ord_nonneg_of_mem hσ
    omega

theorem p0n22_cpf_one_add_ne_zero
    (v : Place K (RatFunc K))
    {g : RatFunc K} (hg : g = 0 ∨ 1 ≤ v.ord g) :
    (1 : RatFunc K) + g ≠ 0 := by
  rcases hg with rfl | hord
  · simp
  · intro h
    rw [eq_neg_of_add_eq_zero_right h] at hord
    have hneg : v.ord (-1 : RatFunc K) = 0 := by
      have h2 : v.ord ((-1 : RatFunc K) * (-1)) = v.ord (-1 : RatFunc K)
          + v.ord (-1 : RatFunc K) :=
        v.ord_mul (neg_ne_zero.mpr one_ne_zero) (neg_ne_zero.mpr one_ne_zero)
      rw [neg_mul_neg, one_mul, v.ord_one] at h2
      omega
    omega

theorem p0n22_cpf_ord_one_add_eq_zero
    (v : Place K (RatFunc K))
    {g : RatFunc K} (hg : g = 0 ∨ 1 ≤ v.ord g) :
    v.ord ((1 : RatFunc K) + g) = 0 := by
  rcases hg with rfl | hord
  · rw [add_zero, v.ord_one]
  · have hg0 : g ≠ 0 := by
      intro h
      rw [h, v.ord_zero] at hord
      omega
    have h1 := v.ord_add_eq_min (f := (1 : RatFunc K)) (g := g) one_ne_zero hg0
      (by rw [v.ord_one]; omega)
    rw [v.ord_one] at h1
    omega

theorem p0n22_cpf_one_add_inv_mem
    (v : Place K (RatFunc K))
    {g : RatFunc K} (hg : g = 0 ∨ 1 ≤ v.ord g) :
    ((1 : RatFunc K) + g)⁻¹ ∈ v.toValuationSubring := by
  refine v.mem_of_ord_nonneg (inv_ne_zero (p0n22_cpf_one_add_ne_zero v hg)) ?_
  rw [v.ord_inv, p0n22_cpf_ord_one_add_eq_zero v hg, _root_.neg_zero]

theorem p0n22_cpf_logDeriv_mul
    (v : Place K (RatFunc K)) [v.DCoordGenerates]
    [Nontrivial Ω[(RatFunc K)⁄K]]
    {w₁ w₂ : RatFunc K} (h1 : w₁ ≠ 0) (h2 : w₂ ≠ 0) :
    v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) (w₁ * w₂))
        * (w₁ * w₂)⁻¹
      = v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) w₁) * w₁⁻¹
        + v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) w₂)
            * w₂⁻¹ := by
  rw [Derivation.leibniz, v.differentialCoeff_add'', v.differentialCoeff_smul,
    v.differentialCoeff_smul]
  have hc1 : w₁ * w₁⁻¹ = 1 := mul_inv_cancel₀ h1
  have hc2 : w₂ * w₂⁻¹ = 1 := mul_inv_cancel₀ h2
  linear_combination
    (v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) w₂) * w₂⁻¹)
      * hc1
    + (v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) w₁) * w₁⁻¹)
      * hc2

theorem p0n22_cpf_logDeriv_mem
    (v : Place K (RatFunc K)) [v.DCoordGenerates]
    [Nontrivial Ω[(RatFunc K)⁄K]]
    {w : RatFunc K} (hw0 : w ≠ 0) (hword : v.ord w = 0) :
    v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) w) * w⁻¹
      ∈ v.toValuationSubring := by
  have hwmem : w ∈ v.toValuationSubring := v.mem_of_ord_nonneg hw0 hword.ge
  have hwinv : w⁻¹ ∈ v.toValuationSubring := by
    refine v.mem_of_ord_nonneg (inv_ne_zero hw0) ?_
    rw [v.ord_inv, hword, _root_.neg_zero]
  exact mul_mem (ag9b13e_differentialCoeff_D_mem_of_mem_of_perfectField v hwmem) hwinv

theorem p0n22_cpf_differentialCoeff_D_one_add_algebraMap_mul_pow
    (v : Place K (RatFunc K)) [v.DCoordGenerates]
    [Nontrivial Ω[(RatFunc K)⁄K]] (a : K) (k : ℕ) :
    v.differentialCoeff (KaehlerDifferential.D K (RatFunc K)
        ((1 : RatFunc K)
          + algebraMap K (RatFunc K) a * v.uniformizer ^ k))
      = algebraMap K (RatFunc K) a
        * (((k : ℕ) : RatFunc K) * v.uniformizer ^ (k - 1)) := by
  refine v.differentialCoeff_unique ?_
  rw [map_add, Derivation.map_one_eq_zero, zero_add, Derivation.leibniz,
    Derivation.map_algebraMap, smul_zero, add_zero, Derivation.leibniz_pow,
    show KaehlerDifferential.D K (RatFunc K) v.uniformizer = v.dCoord from
      rfl,
    ← Nat.cast_smul_eq_nsmul (RatFunc K) k, smul_smul, smul_smul, mul_assoc]

theorem p0n22_cpf_differentialCoeff_D_one_add_pow_mul
    (v : Place K (RatFunc K)) [v.DCoordGenerates]
    [Nontrivial Ω[(RatFunc K)⁄K]] (σ : RatFunc K) (k : ℕ) :
    v.differentialCoeff (KaehlerDifferential.D K (RatFunc K)
        ((1 : RatFunc K) + v.uniformizer ^ k * σ))
      = v.uniformizer ^ k
          * v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) σ)
        + σ * (((k : ℕ) : RatFunc K) * v.uniformizer ^ (k - 1)) := by
  refine v.differentialCoeff_unique ?_
  conv_lhs => rw [map_add, Derivation.map_one_eq_zero, zero_add, Derivation.leibniz,
    Derivation.leibniz_pow,
    show KaehlerDifferential.D K (RatFunc K) v.uniformizer = v.dCoord from
      rfl,
    ← Nat.cast_smul_eq_nsmul (RatFunc K) k,
    ← v.differentialCoeff_smul_dCoord
      (KaehlerDifferential.D K (RatFunc K) σ),
    smul_smul, smul_smul, smul_smul, ← add_smul]
  exact congrArg (· • v.dCoord) (by ring)

theorem p0n22_cpf_exists_residue_lift_decomp
    (v : Place K (RatFunc K))
    (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    {r : RatFunc K} (hr : r ∈ v.toValuationSubring) :
    ∃ (d : K) (r' : RatFunc K), r' ∈ v.toValuationSubring ∧
      r = algebraMap K (RatFunc K) d + v.uniformizer * r' := by
  obtain ⟨d, hd⟩ := hsurj (IsLocalRing.residue _ (⟨r, hr⟩ : v.toValuationSubring))
  have hxmem : r - algebraMap K (RatFunc K) d ∈ v.toValuationSubring :=
    sub_mem hr (v.algebraMap_mem' d)
  have hres0 : IsLocalRing.residue _
      (⟨r - algebraMap K (RatFunc K) d, hxmem⟩ : v.toValuationSubring)
      = 0 := by
    have hfact : (⟨r - algebraMap K (RatFunc K) d, hxmem⟩
        : v.toValuationSubring)
        = ⟨r, hr⟩ - algebraMap K v.toValuationSubring d :=
      Subtype.ext (by push_cast [v.coe_algebraMap]; ring)
    have h2 : IsLocalRing.residue _ (algebraMap K v.toValuationSubring d)
        = IsLocalRing.residue _ (⟨r, hr⟩ : v.toValuationSubring) := by
      rw [← hd, IsScalarTower.algebraMap_apply K v.toValuationSubring
        v.ResidueField, IsLocalRing.ResidueField.algebraMap_eq]
    rw [hfact, map_sub, h2, sub_self]
  rcases _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve.MilneAvAg9bRd15UnitNormalFormLaurentSeed.ag9b15u_eq_zero_or_one_le_ord_of_residue_eq_zero
      v hxmem hres0 with hx0 | hxord
  · exact ⟨d, 0, zero_mem _, by rw [mul_zero, add_zero]; exact (sub_eq_zero.mp hx0)⟩
  · have hxne : r - algebraMap K (RatFunc K) d ≠ 0 := by
      intro h0
      rw [h0, v.ord_zero] at hxord
      omega
    refine ⟨d, v.uniformizer⁻¹ * (r - algebraMap K (RatFunc K) d), ?_, ?_⟩
    · refine v.mem_of_ord_nonneg
        (mul_ne_zero (inv_ne_zero v.uniformizer_ne_zero) hxne) ?_
      rw [v.ord_mul (inv_ne_zero v.uniformizer_ne_zero) hxne, v.ord_inv,
        v.ord_uniformizer]
      omega
    · rw [← mul_assoc, mul_inv_cancel₀ v.uniformizer_ne_zero, one_mul]
      ring

theorem p0n22_cpf_exists_elementary_peel
    (v : Place K (RatFunc K))
    (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    {k : ℕ} (hk : 1 ≤ k) {σ : RatFunc K} (hσ : σ ∈ v.toValuationSubring) :
    ∃ (a : K) (τ : RatFunc K), τ ∈ v.toValuationSubring ∧
      (1 : RatFunc K) + v.uniformizer ^ k * σ
        = ((1 : RatFunc K)
              + algebraMap K (RatFunc K) a * v.uniformizer ^ k)
          * ((1 : RatFunc K) + v.uniformizer ^ (k + 1) * τ) := by
  obtain ⟨a, σ', hσ', hdec⟩ := p0n22_cpf_exists_residue_lift_decomp v hsurj hσ
  have hgcase : algebraMap K (RatFunc K) a * v.uniformizer ^ k = 0
      ∨ 1 ≤ v.ord (algebraMap K (RatFunc K) a * v.uniformizer ^ k) := by
    rw [mul_comm]
    exact p0n22_cpf_uniformizer_pow_mul_mem_cases v (v.algebraMap_mem' a) hk
  have he0 : (1 : RatFunc K)
      + algebraMap K (RatFunc K) a * v.uniformizer ^ k ≠ 0 :=
    p0n22_cpf_one_add_ne_zero v hgcase
  have heinv : ((1 : RatFunc K)
      + algebraMap K (RatFunc K) a * v.uniformizer ^ k)⁻¹
      ∈ v.toValuationSubring :=
    p0n22_cpf_one_add_inv_mem v hgcase
  refine ⟨a, σ' * ((1 : RatFunc K)
    + algebraMap K (RatFunc K) a * v.uniformizer ^ k)⁻¹,
    mul_mem hσ' heinv, ?_⟩
  have hce : ((1 : RatFunc K)
      + algebraMap K (RatFunc K) a * v.uniformizer ^ k)
      * ((1 : RatFunc K)
          + algebraMap K (RatFunc K) a * v.uniformizer ^ k)⁻¹ = 1 :=
    mul_inv_cancel₀ he0
  rw [hdec]
  linear_combination (-(v.uniformizer ^ (k + 1) * σ')) * hce

theorem p0n22_cpf_exists_laurent_expansion_one
    (v : Place K (RatFunc K))
    (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    (f : RatFunc K) :
    ∃ (s : Finset ℤ) (c : ℤ → K) (r : RatFunc K),
      r ∈ v.toValuationSubring ∧
      f = (∑ j ∈ s, c j • v.uniformizer ^ j) + v.uniformizer * r := by
  obtain ⟨N, hN⟩ := v.exists_mem_poleSubmodule f
  obtain ⟨c0, hc0⟩ :=
    _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve.MilneAvAg9bRd15UnitNormalFormLaurentSeed.ag9b15u_exists_K_truncation_of_mem_poleSubmodule
      v hsurj N hN
  obtain ⟨d, r, hr, hdec⟩ := p0n22_cpf_exists_residue_lift_decomp v hsurj hc0
  refine ⟨insert (0 : ℤ) ((Finset.range N).image fun j : ℕ => -((j : ℤ) + 1)),
    fun t => if t = 0 then d else c0 (-(t + 1)).toNat, r, hr, ?_⟩
  have h0not : (0 : ℤ) ∉ (Finset.range N).image (fun j : ℕ => -((j : ℤ) + 1)) := by
    simp only [Finset.mem_image, Finset.mem_range]
    rintro ⟨j, _, hj⟩
    omega
  have hinj : ∀ x ∈ Finset.range N, ∀ y ∈ Finset.range N,
      -((x : ℤ) + 1) = -((y : ℤ) + 1) → x = y := fun x _ y _ h => by omega
  have himg : ∀ j ∈ Finset.range N,
      (if -((j : ℤ) + 1) = 0 then d else c0 (-(-((j : ℤ) + 1) + 1)).toNat)
          • v.uniformizer ^ (-((j : ℤ) + 1))
        = algebraMap K (RatFunc K) (c0 j)
            * (v.uniformizer ^ (j + 1))⁻¹ := by
    intro j _
    rw [if_neg (by omega : ¬(-((j : ℤ) + 1) = (0 : ℤ))),
      show (-(-((j : ℤ) + 1) + 1)).toNat = j from by omega,
      Algebra.smul_def, _root_.zpow_neg,
      show ((j : ℤ) + 1) = ((j + 1 : ℕ) : ℤ) from by push_cast; ring, zpow_natCast]
  rw [Finset.sum_insert h0not, Finset.sum_image hinj, Finset.sum_congr rfl himg,
    show ((fun t : ℤ => if t = 0 then d else c0 (-(t + 1)).toNat) 0) = d from by simp,
    zpow_zero, Algebra.smul_def, mul_one]
  linear_combination hdec

theorem p0n22_cpf_res_geom_core
    (v : Place K (RatFunc K)) (R : v.CanonicalLocalResidueDataK)
    (a : K) {k q : ℕ} (hk : 1 ≤ k) (hq : 1 ≤ q) :
    R.res (algebraMap K (RatFunc K) a * v.uniformizer ^ (k - 1)
        * ((1 : RatFunc K)
            + algebraMap K (RatFunc K) a * v.uniformizer ^ k)⁻¹
        * (v.uniformizer ^ q)⁻¹)
      = if k ∣ q
        then algebraMap K v.ResidueField (a * (-a) ^ (q / k - 1))
        else 0 := by
  have hπ0 : (v.uniformizer : RatFunc K) ≠ 0 := v.uniformizer_ne_zero
  have hgcase : algebraMap K (RatFunc K) a * v.uniformizer ^ k = 0
      ∨ 1 ≤ v.ord (algebraMap K (RatFunc K) a * v.uniformizer ^ k) := by
    rw [mul_comm]
    exact p0n22_cpf_uniformizer_pow_mul_mem_cases v (v.algebraMap_mem' a) hk
  have hu0 : (1 : RatFunc K)
      + algebraMap K (RatFunc K) a * v.uniformizer ^ k ≠ 0 :=
    p0n22_cpf_one_add_ne_zero v hgcase
  have huinv : ((1 : RatFunc K)
      + algebraMap K (RatFunc K) a * v.uniformizer ^ k)⁻¹
      ∈ v.toValuationSubring :=
    p0n22_cpf_one_add_inv_mem v hgcase
  have hgeom : ((1 : RatFunc K)
      + algebraMap K (RatFunc K) a * v.uniformizer ^ k)⁻¹
      = (∑ t ∈ Finset.range q,
          (-(algebraMap K (RatFunc K) a * v.uniformizer ^ k)) ^ t)
        + (-(algebraMap K (RatFunc K) a * v.uniformizer ^ k)) ^ q
          * ((1 : RatFunc K)
              + algebraMap K (RatFunc K) a * v.uniformizer ^ k)⁻¹ := by
    refine (eq_inv_of_mul_eq_one_left ?_).symm
    rw [add_mul, mul_assoc, inv_mul_cancel₀ hu0, mul_one]
    have hgs := geom_sum_mul
      (-(algebraMap K (RatFunc K) a * v.uniformizer ^ k)) q
    linear_combination -hgs
  rw [hgeom, mul_add, add_mul, map_add]
  have htail : R.res ((algebraMap K (RatFunc K) a * v.uniformizer ^ (k - 1)
      * ((-(algebraMap K (RatFunc K) a * v.uniformizer ^ k)) ^ q
          * ((1 : RatFunc K)
              + algebraMap K (RatFunc K) a * v.uniformizer ^ k)⁻¹))
      * (v.uniformizer ^ q)⁻¹) = 0 := by
    apply R.res_of_mem
    have hqle : q ≤ k * q := Nat.le_of_dvd (Nat.mul_pos hk hq) (dvd_mul_left q k)
    have hpowsplit : (v.uniformizer : RatFunc K) ^ (k * q)
        = v.uniformizer ^ (k * q - q) * v.uniformizer ^ q := by
      rw [← pow_add, Nat.sub_add_cancel hqle]
    have hxq : (-(algebraMap K (RatFunc K) a * v.uniformizer ^ k)) ^ q
        = algebraMap K (RatFunc K) ((-a) ^ q)
          * (v.uniformizer ^ (k * q - q) * v.uniformizer ^ q) := by
      rw [map_pow, _root_.map_neg,
        show -(algebraMap K (RatFunc K) a * v.uniformizer ^ k)
            = -algebraMap K (RatFunc K) a * v.uniformizer ^ k from
          (neg_mul _ _).symm,
        mul_pow, ← pow_mul, hpowsplit]
    have hcc : (v.uniformizer : RatFunc K) ^ q
        * ((v.uniformizer : RatFunc K) ^ q)⁻¹ = 1 :=
      mul_inv_cancel₀ (pow_ne_zero _ hπ0)
    have heq : (algebraMap K (RatFunc K) a * v.uniformizer ^ (k - 1)
        * ((-(algebraMap K (RatFunc K) a * v.uniformizer ^ k)) ^ q
            * ((1 : RatFunc K)
                + algebraMap K (RatFunc K) a * v.uniformizer ^ k)⁻¹))
        * (v.uniformizer ^ q)⁻¹
        = algebraMap K (RatFunc K) a * v.uniformizer ^ (k - 1)
          * (algebraMap K (RatFunc K) ((-a) ^ q)
              * v.uniformizer ^ (k * q - q)
              * ((1 : RatFunc K)
                  + algebraMap K (RatFunc K) a * v.uniformizer ^ k)⁻¹) := by
      rw [hxq]
      linear_combination (algebraMap K (RatFunc K) a
        * v.uniformizer ^ (k - 1)
        * (algebraMap K (RatFunc K) ((-a) ^ q)
            * v.uniformizer ^ (k * q - q)
            * ((1 : RatFunc K)
                + algebraMap K (RatFunc K) a * v.uniformizer ^ k)⁻¹)) * hcc
    rw [heq]
    exact mul_mem (mul_mem (v.algebraMap_mem' a) (pow_mem v.uniformizer_mem _))
      (mul_mem (mul_mem (v.algebraMap_mem' _) (pow_mem v.uniformizer_mem _)) huinv)
  have hterm : (algebraMap K (RatFunc K) a * v.uniformizer ^ (k - 1)
      * (∑ t ∈ Finset.range q,
          (-(algebraMap K (RatFunc K) a * v.uniformizer ^ k)) ^ t))
      * (v.uniformizer ^ q)⁻¹
      = ∑ t ∈ Finset.range q, (a * (-a) ^ t)
          • v.uniformizer ^ ((k : ℤ) * ((t : ℤ) + 1) - 1 - (q : ℤ)) := by
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    have hxt : (-(algebraMap K (RatFunc K) a * v.uniformizer ^ k)) ^ t
        = algebraMap K (RatFunc K) ((-a) ^ t)
          * v.uniformizer ^ (k * t) := by
      rw [map_pow, _root_.map_neg,
        show -(algebraMap K (RatFunc K) a * v.uniformizer ^ k)
            = -algebraMap K (RatFunc K) a * v.uniformizer ^ k from
          (neg_mul _ _).symm,
        mul_pow, ← pow_mul]
    rw [hxt, Algebra.smul_def, map_mul, map_pow, _root_.map_neg,
      show (k : ℤ) * ((t : ℤ) + 1) - 1 - (q : ℤ)
          = ((k - 1 : ℕ) : ℤ) + ((k * t : ℕ) : ℤ) + -((q : ℕ) : ℤ) from by
        push_cast [Nat.cast_sub hk]
        ring,
      zpow_add₀ hπ0, zpow_add₀ hπ0, zpow_natCast, zpow_natCast, _root_.zpow_neg, zpow_natCast]
    ring
  rw [hterm, map_sum]
  simp only [map_smul]
  by_cases hdvd : k ∣ q
  · rw [if_pos hdvd, htail, add_zero]
    obtain ⟨e, rfl⟩ := hdvd
    rcases Nat.eq_zero_or_pos e with rfl | he1
    · simp at hq
    · rw [Nat.mul_div_cancel_left e hk]
      have he_lt : e - 1 < k * e := by
        have h1 : e ≤ k * e := Nat.le_of_dvd (Nat.mul_pos hk he1) (dvd_mul_left e k)
        omega
      have hother : ∀ t ∈ Finset.range (k * e), t ≠ e - 1 →
          (a * (-a) ^ t) • R.res ((v.uniformizer : RatFunc K)
            ^ ((k : ℤ) * ((t : ℤ) + 1) - 1 - ((k * e : ℕ) : ℤ))) = 0 := by
        intro t _ htne
        have hne : (k : ℤ) * ((t : ℤ) + 1) - 1 - ((k * e : ℕ) : ℤ) ≠ -1 := by
          intro hcontra
          have h2 : (k : ℤ) * ((t : ℤ) + 1) = (k : ℤ) * (e : ℤ) := by
            push_cast at hcontra
            linarith
          have hk0 : (k : ℤ) ≠ 0 := by omega
          have h3 : (t : ℤ) + 1 = (e : ℤ) := mul_left_cancel₀ hk0 h2
          omega
        rw [_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve.MilneAvAg9bRd14CubeRowCartierSliceStart.ag9b14c_res_uniformizer_zpow_eq_zero_of_ne_neg_one
          v R hne, smul_zero]
      rw [Finset.sum_eq_single_of_mem (e - 1) (Finset.mem_range.mpr he_lt) hother,
        show (k : ℤ) * (((e - 1 : ℕ) : ℤ) + 1) - 1 - ((k * e : ℕ) : ℤ) = -1 from by
          push_cast [Nat.cast_sub he1]
          ring,
        _root_.zpow_neg, zpow_one, gate_canonicalLocalResidueDataK_uniformizer_inv v R,
        ← Algebra.algebraMap_eq_smul_one]
  · rw [if_neg hdvd, htail, add_zero]
    refine Finset.sum_eq_zero fun t _ => ?_
    have hne : (k : ℤ) * ((t : ℤ) + 1) - 1 - (q : ℤ) ≠ -1 := by
      intro hcontra
      have h2 : (k : ℤ) * ((t : ℤ) + 1) = (q : ℤ) := by linarith
      have h3 : k * (t + 1) = q := by exact_mod_cast h2
      exact hdvd ⟨t + 1, h3.symm⟩
    rw [_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve.MilneAvAg9bRd14CubeRowCartierSliceStart.ag9b14c_res_uniformizer_zpow_eq_zero_of_ne_neg_one
      v R hne, smul_zero]

theorem p0n22_cpf_res_logDeriv_elementary
    (v : Place K (RatFunc K)) [v.DCoordGenerates]
    [Nontrivial Ω[(RatFunc K)⁄K]]
    (R : v.CanonicalLocalResidueDataK) (a : K) {k q : ℕ} (hk : 1 ≤ k) (hq : 1 ≤ q) :
    R.res (v.differentialCoeff (KaehlerDifferential.D K (RatFunc K)
          ((1 : RatFunc K)
            + algebraMap K (RatFunc K) a * v.uniformizer ^ k))
        * ((1 : RatFunc K)
            + algebraMap K (RatFunc K) a * v.uniformizer ^ k)⁻¹
        * (v.uniformizer ^ q)⁻¹)
      = ((k : ℕ) : K) • (if k ∣ q
          then algebraMap K v.ResidueField (a * (-a) ^ (q / k - 1))
          else 0) := by
  rw [p0n22_cpf_differentialCoeff_D_one_add_algebraMap_mul_pow v a k]
  have hsplit : algebraMap K (RatFunc K) a
        * (((k : ℕ) : RatFunc K) * v.uniformizer ^ (k - 1))
        * ((1 : RatFunc K)
            + algebraMap K (RatFunc K) a * v.uniformizer ^ k)⁻¹
        * (v.uniformizer ^ q)⁻¹
      = ((k : ℕ) : K) • (algebraMap K (RatFunc K) a
          * v.uniformizer ^ (k - 1)
          * ((1 : RatFunc K)
              + algebraMap K (RatFunc K) a * v.uniformizer ^ k)⁻¹
          * (v.uniformizer ^ q)⁻¹) := by
    rw [Algebra.smul_def, map_natCast]
    ring
  rw [hsplit, map_smul, p0n22_cpf_res_geom_core v R a hk hq]

theorem p0n22_cpf_res_logDeriv_highLevel_vanish
    (v : Place K (RatFunc K)) [v.DCoordGenerates]
    [Nontrivial Ω[(RatFunc K)⁄K]]
    (R : v.CanonicalLocalResidueDataK)
    {σ : RatFunc K} (hσ : σ ∈ v.toValuationSubring)
    {k q : ℕ} (hbig : q + 1 ≤ k) :
    R.res (v.differentialCoeff (KaehlerDifferential.D K (RatFunc K)
          ((1 : RatFunc K) + v.uniformizer ^ k * σ))
        * ((1 : RatFunc K) + v.uniformizer ^ k * σ)⁻¹
        * (v.uniformizer ^ q)⁻¹) = 0 := by
  have hπ0 : (v.uniformizer : RatFunc K) ≠ 0 := v.uniformizer_ne_zero
  have hgcase := p0n22_cpf_uniformizer_pow_mul_mem_cases v hσ
    (show 1 ≤ k by omega)
  have huinv := p0n22_cpf_one_add_inv_mem v hgcase
  have hσ' : v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) σ)
      ∈ v.toValuationSubring :=
    ag9b13e_differentialCoeff_D_mem_of_mem_of_perfectField v hσ
  have hkF : ((k : ℕ) : RatFunc K) ∈ v.toValuationSubring := by
    rw [← map_natCast (algebraMap K (RatFunc K))]
    exact v.algebraMap_mem' _
  obtain ⟨e, rfl⟩ : ∃ e, k = q + 1 + e := ⟨k - (q + 1), by omega⟩
  apply R.res_of_mem
  rw [p0n22_cpf_differentialCoeff_D_one_add_pow_mul v σ (q + 1 + e)]
  have hcc : (v.uniformizer : RatFunc K) ^ q
      * ((v.uniformizer : RatFunc K) ^ q)⁻¹ = 1 :=
    mul_inv_cancel₀ (pow_ne_zero _ hπ0)
  have heq : (v.uniformizer ^ (q + 1 + e)
        * v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) σ)
        + σ * (((q + 1 + e : ℕ) : RatFunc K) * v.uniformizer ^ (q + 1 + e - 1)))
        * ((1 : RatFunc K) + v.uniformizer ^ (q + 1 + e) * σ)⁻¹
        * (v.uniformizer ^ q)⁻¹
      = (v.uniformizer ^ (1 + e)
          * v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) σ)
          + σ * (((q + 1 + e : ℕ) : RatFunc K) * v.uniformizer ^ e))
        * ((1 : RatFunc K) + v.uniformizer ^ (q + 1 + e) * σ)⁻¹ := by
    rw [show q + 1 + e - 1 = q + e from by omega]
    linear_combination ((v.uniformizer ^ (1 + e)
        * v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) σ)
        + σ * (((q + 1 + e : ℕ) : RatFunc K) * v.uniformizer ^ e))
      * ((1 : RatFunc K) + v.uniformizer ^ (q + 1 + e) * σ)⁻¹) * hcc
  rw [heq]
  exact mul_mem (add_mem (mul_mem (pow_mem v.uniformizer_mem _) hσ')
    (mul_mem hσ (mul_mem hkF (pow_mem v.uniformizer_mem _)))) huinv

theorem p0n22_cpf_row_integrand_eq_pow_mul_dlog
    (v : Place K (RatFunc K)) [v.DCoordGenerates]
    [Nontrivial Ω[(RatFunc K)⁄K]]
    {w : RatFunc K} (hw0 : w ≠ 0) (k : ℕ) :
    v.differentialCoeff (KaehlerDifferential.D K (RatFunc K)
        (w * v.uniformizer))
        * ((w * v.uniformizer) ^ (k + 1))⁻¹
      = (w ^ k * v.uniformizer ^ k)⁻¹
        * ((v.uniformizer)⁻¹
            + v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) w)
                * w⁻¹) := by
  rw [_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve.MilneAvAg9bRd15UnitNormalFormLaurentSeed.ag9b15u_differentialCoeff_D_unit_mul_uniformizer
    v w]
  have hπ0 : (v.uniformizer : RatFunc K) ≠ 0 := v.uniformizer_ne_zero
  have hcw : w * w⁻¹ = 1 := mul_inv_cancel₀ hw0
  have hcπ : (v.uniformizer : RatFunc K) * (v.uniformizer)⁻¹ = 1 :=
    mul_inv_cancel₀ hπ0
  linear_combination ((w ^ k)⁻¹ * (v.uniformizer ^ (k + 1))⁻¹) * hcw
    + (v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) w)
        * (w ^ (k + 1))⁻¹ * (v.uniformizer ^ k)⁻¹) * hcπ

end CharFreeToolkit


section CharPCartier

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [PerfectField K] [hKp : CharP K p]

theorem p0n22_cpf_res_logDeriv_elementary_cartier
    (v : Place K (RatFunc K)) [v.DCoordGenerates]
    [Nontrivial Ω[(RatFunc K)⁄K]]
    (R : v.CanonicalLocalResidueDataK) (a : K) {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) :
    R.res (v.differentialCoeff (KaehlerDifferential.D K (RatFunc K)
          ((1 : RatFunc K)
            + algebraMap K (RatFunc K) a * v.uniformizer ^ k))
        * ((1 : RatFunc K)
            + algebraMap K (RatFunc K) a * v.uniformizer ^ k)⁻¹
        * (v.uniformizer ^ (p * n))⁻¹)
      = (R.res (v.differentialCoeff (KaehlerDifferential.D K (RatFunc K)
          ((1 : RatFunc K)
            + algebraMap K (RatFunc K) a * v.uniformizer ^ k))
        * ((1 : RatFunc K)
            + algebraMap K (RatFunc K) a * v.uniformizer ^ k)⁻¹
        * (v.uniformizer ^ n)⁻¹)) ^ p := by
  haveI : CharP v.ResidueField p :=
    charP_of_injective_ringHom (algebraMap K v.ResidueField).injective p
  rw [p0n22_cpf_res_logDeriv_elementary v R a hk (Nat.mul_pos hp.out.pos hn),
    p0n22_cpf_res_logDeriv_elementary v R a hk hn]
  by_cases hdn : k ∣ n
  · rw [if_pos (hdn.mul_left p), if_pos hdn]
    obtain ⟨e, rfl⟩ := hdn
    rcases Nat.eq_zero_or_pos e with rfl | he1
    · simp at hn
    · rw [show p * (k * e) / k = p * e from by
          rw [show p * (k * e) = k * (p * e) from by ring, Nat.mul_div_cancel_left _ hk],
        Nat.mul_div_cancel_left e hk]
      have key : ∀ m : ℕ, 1 ≤ m → a * (-a) ^ (m - 1) = -((-a) ^ m) := by
        intro m hm
        obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_le hm
        rw [show 1 + m' - 1 = m' from by omega, show 1 + m' = m' + 1 from by omega,
          pow_succ]
        ring
      have hneg : (-((-a) ^ e) : K) ^ p = -(((-a) ^ e) ^ p) := by
        rw [neg_eq_neg_one_mul, mul_pow, neg_one_pow_char K p, neg_one_mul]
      have hxp : (a * (-a) ^ (e - 1)) ^ p = a * (-a) ^ (p * e - 1) := by
        rw [key e he1, key (p * e) (Nat.mul_pos hp.out.pos he1), hneg, ← pow_mul,
          mul_comm e p]
      have hfix : ((k : ℕ) : v.ResidueField) ^ p = ((k : ℕ) : v.ResidueField) := by
        have h := map_natCast (frobenius v.ResidueField p) k
        rwa [frobenius_def] at h
      rw [Algebra.smul_def, Algebra.smul_def, map_natCast (algebraMap K v.ResidueField) k,
        mul_pow, hfix, ← map_pow, hxp]
  · by_cases hdp : k ∣ p * n
    · have hpk : p ∣ k := by
        by_contra hpk
        exact hdn ((((hp.out.coprime_iff_not_dvd).mpr hpk).symm).dvd_mul_left.mp hdp)
      have hk0 : ((k : ℕ) : K) = 0 := (CharP.cast_eq_zero_iff K p k).mpr hpk
      rw [hk0, zero_smul, zero_smul, zero_pow hp.out.ne_zero]
    · rw [if_neg hdp, if_neg hdn, smul_zero, zero_pow hp.out.ne_zero]

theorem p0n22_cpf_res_logDeriv_principalUnit_cartier_aux
    (v : Place K (RatFunc K)) [v.DCoordGenerates]
    [Nontrivial Ω[(RatFunc K)⁄K]]
    (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    (R : v.CanonicalLocalResidueDataK) {n : ℕ} (hn : 1 ≤ n) :
    ∀ d k : ℕ, 1 ≤ k → p * n + 1 ≤ k + d →
      ∀ σ : RatFunc K, σ ∈ v.toValuationSubring →
        R.res (v.differentialCoeff (KaehlerDifferential.D K (RatFunc K)
              ((1 : RatFunc K) + v.uniformizer ^ k * σ))
            * ((1 : RatFunc K) + v.uniformizer ^ k * σ)⁻¹
            * (v.uniformizer ^ (p * n))⁻¹)
          = (R.res (v.differentialCoeff (KaehlerDifferential.D K (RatFunc K)
              ((1 : RatFunc K) + v.uniformizer ^ k * σ))
            * ((1 : RatFunc K) + v.uniformizer ^ k * σ)⁻¹
            * (v.uniformizer ^ n)⁻¹)) ^ p := by
  haveI : CharP v.ResidueField p :=
    charP_of_injective_ringHom (algebraMap K v.ResidueField).injective p
  intro d
  induction d with
  | zero =>
    intro k hk hbound σ hσ
    have hnp : n ≤ p * n := Nat.le_mul_of_pos_left n hp.out.pos
    rw [p0n22_cpf_res_logDeriv_highLevel_vanish v R hσ (show p * n + 1 ≤ k by omega),
      p0n22_cpf_res_logDeriv_highLevel_vanish v R hσ (show n + 1 ≤ k by omega),
      zero_pow hp.out.ne_zero]
  | succ d ihd =>
    intro k hk hbound σ hσ
    obtain ⟨a, τ, hτ, hfac⟩ := p0n22_cpf_exists_elementary_peel v hsurj hk hσ
    have hgcase1 : algebraMap K (RatFunc K) a * v.uniformizer ^ k = 0
        ∨ 1 ≤ v.ord (algebraMap K (RatFunc K) a * v.uniformizer ^ k) := by
      rw [mul_comm]
      exact p0n22_cpf_uniformizer_pow_mul_mem_cases v (v.algebraMap_mem' a) hk
    have h1 : (1 : RatFunc K)
        + algebraMap K (RatFunc K) a * v.uniformizer ^ k ≠ 0 :=
      p0n22_cpf_one_add_ne_zero v hgcase1
    have hgcase2 := p0n22_cpf_uniformizer_pow_mul_mem_cases v hτ
      (show 1 ≤ k + 1 by omega)
    have h2 : (1 : RatFunc K) + v.uniformizer ^ (k + 1) * τ ≠ 0 :=
      p0n22_cpf_one_add_ne_zero v hgcase2
    rw [hfac, p0n22_cpf_logDeriv_mul v h1 h2, add_mul, add_mul, LinearMap.map_add,
      LinearMap.map_add, p0n22_cpf_res_logDeriv_elementary_cartier v R a hk hn,
      ihd (k + 1) (by omega) (by omega) τ hτ, ← add_pow_char]

theorem p0n22_cpf_res_zpow_mul_logDeriv_cartier
    (v : Place K (RatFunc K)) [v.DCoordGenerates]
    [Nontrivial Ω[(RatFunc K)⁄K]]
    (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    (R : v.CanonicalLocalResidueDataK)
    {w : RatFunc K} (hw0 : w ≠ 0) (hword : v.ord w = 0) (j : ℤ) :
    R.res (v.uniformizer ^ ((p : ℤ) * j)
        * (v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) w)
            * w⁻¹))
      = (R.res (v.uniformizer ^ j
        * (v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) w)
            * w⁻¹))) ^ p := by
  have hπ0 : (v.uniformizer : RatFunc K) ≠ 0 := v.uniformizer_ne_zero
  have hL := p0n22_cpf_logDeriv_mem v hw0 hword
  rcases le_or_gt 0 j with hj | hj
  · have hmem : ∀ i : ℤ, 0 ≤ i → v.uniformizer ^ i
        * (v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) w)
            * w⁻¹) ∈ v.toValuationSubring := by
      intro i hi
      refine mul_mem ?_ hL
      refine v.mem_of_ord_nonneg (zpow_ne_zero i hπ0) ?_
      rw [v.ord_zpow, v.ord_uniformizer, mul_one]
      exact hi
    rw [R.res_of_mem _ (hmem _ (mul_nonneg (Int.natCast_nonneg p) hj)),
      R.res_of_mem _ (hmem _ hj), zero_pow hp.out.ne_zero]
  · obtain ⟨c, s, hc0, hs, hwfac⟩ :=
      _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve.MilneAvAg9bRd15UnitNormalFormLaurentSeed.ag9b15u_exists_unit_normal_form_of_surj
        v hsurj hw0 hword
    have hcF : algebraMap K (RatFunc K) c ≠ 0 := fun h =>
      hc0 ((algebraMap K (RatFunc K)).injective
        (h.trans (_root_.map_zero _).symm))
    have h1s : (1 : RatFunc K) + s ≠ 0 := by
      intro h0
      exact hw0 (by rw [hwfac, h0, mul_zero])
    have hLw : v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) w)
        * w⁻¹
        = v.differentialCoeff (KaehlerDifferential.D K (RatFunc K)
            ((1 : RatFunc K) + s)) * ((1 : RatFunc K) + s)⁻¹ := by
      rw [hwfac, p0n22_cpf_logDeriv_mul v hcF h1s, Derivation.map_algebraMap,
        v.differentialCoeff_zero, zero_mul, zero_add]
    rcases hs with rfl | hsord
    · rw [hLw, add_zero, Derivation.map_one_eq_zero, v.differentialCoeff_zero, zero_mul,
        mul_zero, mul_zero, _root_.map_zero, zero_pow hp.out.ne_zero]
    · have hs0 : s ≠ 0 := by
        intro h
        rw [h, v.ord_zero] at hsord
        omega
      have hσmem : v.uniformizer⁻¹ * s ∈ v.toValuationSubring := by
        refine v.mem_of_ord_nonneg (mul_ne_zero (inv_ne_zero hπ0) hs0) ?_
        rw [v.ord_mul (inv_ne_zero hπ0) hs0, v.ord_inv, v.ord_uniformizer]
        omega
      obtain ⟨n', rfl⟩ : ∃ n' : ℕ, j = -(n' : ℤ) := ⟨(-j).toNat, by omega⟩
      have hn1 : 1 ≤ n' := by omega
      rw [hLw, show (p : ℤ) * -(n' : ℤ) = -((p * n' : ℕ) : ℤ) from by push_cast; ring,
        _root_.zpow_neg, zpow_natCast, _root_.zpow_neg, zpow_natCast,
        show s = v.uniformizer ^ 1 * (v.uniformizer⁻¹ * s) from by
          rw [pow_one, ← mul_assoc, mul_inv_cancel₀ hπ0, one_mul],
        mul_comm ((v.uniformizer ^ (p * n') : RatFunc K)⁻¹) _,
        mul_comm ((v.uniformizer ^ n' : RatFunc K)⁻¹) _]
      exact p0n22_cpf_res_logDeriv_principalUnit_cartier_aux v hsurj R hn1 (p * n') 1
        le_rfl (by omega) _ hσmem

theorem p0n22_cpf_res_pow_mul_dlog_unit
    (v : Place K (RatFunc K)) [v.DCoordGenerates]
    [Nontrivial Ω[(RatFunc K)⁄K]]
    (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    (R : v.CanonicalLocalResidueDataK)
    {w : RatFunc K} (hw0 : w ≠ 0) (hword : v.ord w = 0) (f : RatFunc K) :
    R.res (f ^ p * ((v.uniformizer)⁻¹
        + v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) w)
            * w⁻¹))
      = (R.res (f * ((v.uniformizer)⁻¹
        + v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) w)
            * w⁻¹))) ^ p := by
  haveI : CharP (RatFunc K) p :=
    charP_of_injective_algebraMap (algebraMap K (RatFunc K)).injective p
  haveI : CharP v.ResidueField p :=
    charP_of_injective_ringHom (algebraMap K v.ResidueField).injective p
  have hπ0 : (v.uniformizer : RatFunc K) ≠ 0 := v.uniformizer_ne_zero
  have hL := p0n22_cpf_logDeriv_mem v hw0 hword
  obtain ⟨s, c, r, hr, hf⟩ := p0n22_cpf_exists_laurent_expansion_one v hsurj f
  have hππ : (v.uniformizer : RatFunc K) * (v.uniformizer)⁻¹ = 1 :=
    mul_inv_cancel₀ hπ0
  have hLHS : f ^ p * ((v.uniformizer)⁻¹
      + v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) w) * w⁻¹)
      = (∑ j ∈ s, c j • v.uniformizer ^ j) ^ p * (v.uniformizer)⁻¹
        + ((∑ j ∈ s, c j • v.uniformizer ^ j) ^ p
            * (v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) w)
                * w⁻¹)
          + (v.uniformizer ^ p * r ^ p * (v.uniformizer)⁻¹
            + v.uniformizer ^ p * r ^ p
                * (v.differentialCoeff
                    (KaehlerDifferential.D K (RatFunc K) w) * w⁻¹))) := by
    rw [hf, add_pow_char, mul_pow]
    ring
  have hRHS : f * ((v.uniformizer)⁻¹
      + v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) w) * w⁻¹)
      = (∑ j ∈ s, c j • v.uniformizer ^ j) * (v.uniformizer)⁻¹
        + ((∑ j ∈ s, c j • v.uniformizer ^ j)
            * (v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) w)
                * w⁻¹)
          + (r + v.uniformizer * r
              * (v.differentialCoeff
                  (KaehlerDifferential.D K (RatFunc K) w) * w⁻¹))) := by
    rw [hf]
    linear_combination r * hππ
  have hπp : (v.uniformizer : RatFunc K) ^ p
      = v.uniformizer ^ (p - 1) * v.uniformizer := by
    conv_lhs => rw [show p = (p - 1) + 1 from by have h2 := hp.out.two_le; omega]
    rw [pow_succ]
  have hm1 : v.uniformizer ^ p * r ^ p * (v.uniformizer)⁻¹ ∈ v.toValuationSubring := by
    have heq : v.uniformizer ^ p * r ^ p * (v.uniformizer)⁻¹
        = v.uniformizer ^ (p - 1) * r ^ p := by
      rw [hπp]
      linear_combination v.uniformizer ^ (p - 1) * r ^ p * hππ
    rw [heq]
    exact mul_mem (pow_mem v.uniformizer_mem _) (pow_mem hr _)
  have hm2 : v.uniformizer ^ p * r ^ p
      * (v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) w) * w⁻¹)
      ∈ v.toValuationSubring :=
    mul_mem (mul_mem (pow_mem v.uniformizer_mem _) (pow_mem hr _)) hL
  have hm3 : v.uniformizer * r
      * (v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) w) * w⁻¹)
      ∈ v.toValuationSubring :=
    mul_mem (mul_mem v.uniformizer_mem hr) hL
  have hpowp : ∀ j : ℤ, ((v.uniformizer : RatFunc K) ^ j) ^ p
      = v.uniformizer ^ ((p : ℤ) * j) := by
    intro j
    rw [← zpow_natCast ((v.uniformizer : RatFunc K) ^ j) p, ← zpow_mul,
      mul_comm j (p : ℤ)]
  have hPp : (∑ j ∈ s, c j • (v.uniformizer : RatFunc K) ^ j) ^ p
      = ∑ j ∈ s, (c j ^ p) • (v.uniformizer : RatFunc K) ^ ((p : ℤ) * j) := by
    rw [sum_pow_char]
    exact Finset.sum_congr rfl fun j _ => by rw [_root_.smul_pow, hpowp j]
  rw [hLHS, hRHS]
  simp only [map_add]
  rw [R.res_of_mem _ hm1, R.res_of_mem _ hm2, R.res_of_mem _ hr, R.res_of_mem _ hm3]
  simp only [add_zero]
  rw [add_pow_char]
  congr 1
  ·
    rw [hPp, Finset.sum_mul, Finset.sum_mul, map_sum, map_sum, sum_pow_char]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_assoc, smul_mul_assoc, map_smul, map_smul]
    rcases eq_or_ne j 0 with rfl | hj
    · rw [mul_zero, zpow_zero, one_mul,
        gate_canonicalLocalResidueDataK_uniformizer_inv v R,
        ← Algebra.algebraMap_eq_smul_one, ← Algebra.algebraMap_eq_smul_one, map_pow]
    · have hp0 : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hp.out.ne_zero
      have h1 : R.res ((v.uniformizer : RatFunc K) ^ ((p : ℤ) * j)
          * (v.uniformizer)⁻¹) = 0 := by
        rw [← zpow_sub_one₀ hπ0]
        refine _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve.MilneAvAg9bRd14CubeRowCartierSliceStart.ag9b14c_res_uniformizer_zpow_eq_zero_of_ne_neg_one
          v R ?_
        intro hcontra
        have hpj : (p : ℤ) * j = 0 := by linarith
        rcases mul_eq_zero.mp hpj with h | h
        · exact hp0 h
        · exact hj h
      have h2 : R.res ((v.uniformizer : RatFunc K) ^ j * (v.uniformizer)⁻¹) = 0 := by
        rw [← zpow_sub_one₀ hπ0]
        exact _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve.MilneAvAg9bRd14CubeRowCartierSliceStart.ag9b14c_res_uniformizer_zpow_eq_zero_of_ne_neg_one
          v R (by omega)
      rw [h1, h2, smul_zero, smul_zero, zero_pow hp.out.ne_zero]
  ·
    rw [hPp, Finset.sum_mul, Finset.sum_mul, map_sum, map_sum, sum_pow_char]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_assoc, smul_mul_assoc, map_smul, map_smul,
      p0n22_cpf_res_zpow_mul_logDeriv_cartier v hsurj R hw0 hword j,
      Algebra.smul_def, Algebra.smul_def, mul_pow, map_pow]

include hp hKp in

theorem p0n22_cpf_res_row_at_unit_mul_uniformizer
    (v : Place K (RatFunc K)) [v.DCoordGenerates]
    [Nontrivial Ω[(RatFunc K)⁄K]]
    (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    (R : v.CanonicalLocalResidueDataK)
    {w : RatFunc K} (hw0 : w ≠ 0) (hword : v.ord w = 0) :
    ∀ n : ℕ, 1 ≤ n →
      R.res (v.differentialCoeff (KaehlerDifferential.D K (RatFunc K)
          (w * v.uniformizer))
        * ((w * v.uniformizer) ^ (n + 1))⁻¹) = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hpn : p ∣ n
    · obtain ⟨m, rfl⟩ := hpn
      have hm1 : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with rfl | h
        · simp at hn
        · exact h
      have hmlt : m < p * m := by
        have h2m : 2 * m ≤ p * m := Nat.mul_le_mul_right m hp.out.two_le
        omega
      have hstep : R.res (v.differentialCoeff (KaehlerDifferential.D K
            (RatFunc K) (w * v.uniformizer))
            * ((w * v.uniformizer) ^ (p * m + 1))⁻¹)
          = (R.res (v.differentialCoeff (KaehlerDifferential.D K (RatFunc K)
              (w * v.uniformizer))
            * ((w * v.uniformizer) ^ (m + 1))⁻¹)) ^ p := by
        rw [p0n22_cpf_row_integrand_eq_pow_mul_dlog v hw0 (p * m),
          p0n22_cpf_row_integrand_eq_pow_mul_dlog v hw0 m]
        have hfp : ((w ^ m * v.uniformizer ^ m : RatFunc K)⁻¹) ^ p
            = (w ^ (p * m) * v.uniformizer ^ (p * m))⁻¹ := by
          rw [inv_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm m p]
        rw [← hfp]
        exact p0n22_cpf_res_pow_mul_dlog_unit v hsurj R hw0 hword
          ((w ^ m * v.uniformizer ^ m)⁻¹)
      rw [hstep, ih m hmlt hm1, zero_pow hp.out.ne_zero]
    · have hnK : ((n : ℕ) : K) ≠ 0 := fun h =>
        hpn ((CharP.cast_eq_zero_iff K p n).mp h)
      exact _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve.MilneAvAg9bRd13T2CoordIndepChar3.ag9b13t_res_differentialCoeff_D_mul_pow_inv_of_surj_of_natCast_ne_zero
        v hsurj
        (fun h hh => ag9b13e_differentialCoeff_D_mem_of_mem_of_perfectField v hh)
        R (w * v.uniformizer) hn hnK

include hp hKp in

theorem p0n22_cpf_res_differentialCoeff_D_mul_pow_inv_of_surj
    (v : Place K (RatFunc K)) [v.DCoordGenerates]
    [Nontrivial Ω[(RatFunc K)⁄K]]
    (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    (π' : RatFunc K) (hπ' : v.ord π' = 1)
    (R : v.CanonicalLocalResidueDataK) {n : ℕ} (hn : 1 ≤ n) :
    R.res (v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) π')
      * ((π') ^ (n + 1))⁻¹) = 0 := by
  have hπ'0 : π' ≠ 0 := by
    intro h0
    rw [h0, v.ord_zero] at hπ'
    omega
  have hw0 : π' * (v.uniformizer)⁻¹ ≠ 0 :=
    mul_ne_zero hπ'0 (inv_ne_zero v.uniformizer_ne_zero)
  have hword : v.ord (π' * (v.uniformizer)⁻¹) = 0 := by
    have h1 := v.ord_mul hπ'0 (inv_ne_zero v.uniformizer_ne_zero)
    rw [v.ord_inv, hπ', v.ord_uniformizer] at h1
    omega
  have hrec : π' * (v.uniformizer)⁻¹ * v.uniformizer = π' := by
    rw [mul_assoc, inv_mul_cancel₀ v.uniformizer_ne_zero, mul_one]
  have h := p0n22_cpf_res_row_at_unit_mul_uniformizer v hsurj R hw0 hword n hn
  rw [← hrec]
  exact h

end CharPCartier


section Headlines

theorem p0n22_cpf_canonicalLocalResidueKDifferentialCoordIndep_ratFunc_of_isAlgClosed
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p] :
    CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K) :=
  fun v π' hπ' R n hn =>
    p0n22_cpf_res_differentialCoeff_D_mul_pow_inv_of_surj (p := p) v
      (p0n21_rtk_surjective_algebraMap_residueField_ratFunc_of_isAlgClosed K v)
      π' hπ' R hn

theorem p0n22_cpf_residueTheoremK_ratFunc_of_isAlgClosed_of_charP
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    [DecidableEq (RatFunc K)] :
    ResidueTheoremK K (RatFunc K) :=
  p0n21_rtk_residueTheoremK_ratFunc_of_isAlgClosed_of_coordIndep K
    (p0n22_cpf_canonicalLocalResidueKDifferentialCoordIndep_ratFunc_of_isAlgClosed K p)

theorem p0n22_cpf_residueTheoremK_ratFunc_of_isAlgClosed_main
    (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)] :
    ResidueTheoremK K (RatFunc K) := by
  rcases CharP.char_is_prime_or_zero K (ringChar K) with hprime | hzero
  · haveI : Fact (ringChar K).Prime := ⟨hprime⟩
    exact p0n22_cpf_residueTheoremK_ratFunc_of_isAlgClosed_of_charP K (ringChar K)
  · haveI : CharP K 0 := hzero ▸ ringChar.charP K
    haveI : CharZero K := CharP.charP_to_charZero K
    exact residueTheoremK_ratFunc_of_isAlgClosed_main K

end Headlines


section Bc2Carrier



end Bc2Carrier


end AlgebraicCurve


end


end


end


theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar K (RatFunc K)]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := RatFunc K)]
    [∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates] :
    AlgebraicCurve.ResidueTheoremK K (RatFunc K) :=
  AlgebraicCurve.p0n22_cpf_residueTheoremK_ratFunc_of_isAlgClosed_main K

end P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed
