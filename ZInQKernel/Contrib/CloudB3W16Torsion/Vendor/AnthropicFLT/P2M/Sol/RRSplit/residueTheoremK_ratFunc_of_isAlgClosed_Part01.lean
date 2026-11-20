/-
Copyright 2026 Anthropic, PBC. Released under Apache License 2.0.
Source: https://github.com/anthropics/fermats-last-theorem
Revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.lean; source lines 1-1889.
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
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RatFuncPlaces
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_CanonicalDivisor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_CanonicalDivisorUniformizer
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CanonicalDivisor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_LocalResidue
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorPushPull
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlacesOverDVR
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 6400000
set_option maxHeartbeats 12800000

namespace P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed



namespace J1ThirteenPlaneModel
end J1ThirteenPlaneModel
namespace J1ThirteenPicZeroFibreDiamond
end J1ThirteenPicZeroFibreDiamond
namespace J1ThirteenPicZeroLiteralChordChain
end J1ThirteenPicZeroLiteralChordChain
namespace J1ThirteenPicZeroPlaceDictionary
end J1ThirteenPicZeroPlaceDictionary
namespace J1ThirteenPicZeroPlaceDictionary.PlaceConstruction
end J1ThirteenPicZeroPlaceDictionary.PlaceConstruction
namespace J1ThirteenPicZeroLitPic0Comparison
end J1ThirteenPicZeroLitPic0Comparison
namespace J1ThirteenX113RiemannRochRows
end J1ThirteenX113RiemannRochRows
namespace MazurTate1973Mt31b
end MazurTate1973Mt31b
namespace J1ThirteenX113PackageHeldRowOne
end J1ThirteenX113PackageHeldRowOne
namespace MilneAvAg9bRd9DictionaryHeld3Closure
end MilneAvAg9bRd9DictionaryHeld3Closure
namespace J1ThirteenX113OrdRowWellDefinedReduction
end J1ThirteenX113OrdRowWellDefinedReduction
namespace MilneAvAg9bRd10EllKFinUpperRow
end MilneAvAg9bRd10EllKFinUpperRow
namespace MilneAvAg9bRd11X113TowerPowerBasis
end MilneAvAg9bRd11X113TowerPowerBasis
namespace Ag9b11bX113HwdUnitDischarge
end Ag9b11bX113HwdUnitDischarge
namespace MilneAvAg9bRd11DictionaryBinderShrink
end MilneAvAg9bRd11DictionaryBinderShrink
namespace MilneAvAg9bRd12X113AssemblyRetirement
end MilneAvAg9bRd12X113AssemblyRetirement
namespace MilneAvAg9bRd12T1P1InftyResidue
end MilneAvAg9bRd12T1P1InftyResidue
namespace MilneAvAg9bRd12X113LocalDatumMint
end MilneAvAg9bRd12X113LocalDatumMint
namespace MilneAvAg9bRd12X113FiveRowUpgrade
end MilneAvAg9bRd12X113FiveRowUpgrade

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 6400000
set_option maxHeartbeats 12800000

namespace AdjoinRoot

export _root_.AdjoinRoot (powerBasis_gen lift powerBasis algebraMap_eq liftAlgHom_root mkₐ mk_surjective minpoly_powerBasis_gen_of_monic powerBasis_dim mk_eq_mk mk_eq_zero liftAlgHom algHom_ext aeval_eq root mk map)

open _root_.AdjoinRoot
end AdjoinRoot
namespace Ag9b11bX113HwdUnitDischarge
end Ag9b11bX113HwdUnitDischarge
namespace Algebra

export _root_.Algebra (algebraMap_eq_smul_one EssFiniteType IsAlgebraic.of_finite trace_eq_of_algEquiv ofId isIntegral_iff trace FormallyEtale.of_isLocalization FormallyUnramified.of_restrictScalars norm_ne_zero_iff mk algebraMap norm_eq_prod_automorphisms EssFiniteType.comp mem_top FormallyUnramified eq_top_iff adjoin_le finrank_eq_of_equiv_equiv norm IsIntegral.isIntegral FiniteType FormallyEtale FiniteType.adjoin_of_finite IsAlgebraic.isSeparable_of_perfectField algebraMap_self FormallyUnramified.of_isSeparable smul_def FiniteType.trans IsSeparable.of_integral IsSeparable.of_equiv_equiv adjoin IsSeparable.isSeparable rec mem_bot restrictScalars EssFiniteType.of_isLocalization commutes' trace_algebraMap FormallyUnramified.subsingleton_kaehlerDifferential to_smulCommClass)

open _root_.Algebra
end Algebra
namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq)

open _root_.AlgebraicCurve
end AlgebraicCurve
namespace CongruenceSubgroup
open _root_.CongruenceSubgroup
end CongruenceSubgroup
namespace CoordinateRing
end CoordinateRing
namespace IntermediateField

export _root_.IntermediateField (charP toAlgebra map_le_iff_le_comap mk val isIntegral_iff topEquiv_apply lift_top lift AdjoinSimple.gen inclusion lift_injective lift_adjoin_simple ext adjoin_simple_le_iff charZero equivOfEq algebraMap_apply smul_def adjoin mk.injEq AdjoinSimple.algebraMap_gen comap topEquiv mem_top adjoinRootEquivAdjoin restrictScalars rec adjoinRootEquivAdjoin_apply_root coe_smul AdjoinSimple.coe_gen mem_bot mem_adjoin_simple_self adjoin_map smul_mem restrict map)

open _root_.IntermediateField
end IntermediateField
namespace IntermediateField

export _root_.IntermediateField (charP toAlgebra map_le_iff_le_comap mk val isIntegral_iff topEquiv_apply lift_top lift AdjoinSimple.gen inclusion lift_injective lift_adjoin_simple ext adjoin_simple_le_iff charZero equivOfEq algebraMap_apply smul_def adjoin mk.injEq AdjoinSimple.algebraMap_gen comap topEquiv mem_top adjoinRootEquivAdjoin restrictScalars rec adjoinRootEquivAdjoin_apply_root coe_smul AdjoinSimple.coe_gen mem_bot mem_adjoin_simple_self adjoin_map smul_mem restrict map)

namespace algebraAdjoinAdjoin
open _root_.IntermediateField.algebraAdjoinAdjoin
open _root_.IntermediateField
end IntermediateField.algebraAdjoinAdjoin
namespace IsDedekindDomain

export _root_.IsDedekindDomain (mem_primesOverFinset_iff HeightOneSpectrum.valuationSubringAtPrime HeightOneSpectrum.valuation_of_algebraMap HeightOneSpectrum.intValuation_le_pow_iff_mem HeightOneSpectrum.valuation_lt_one_iff_mem HeightOneSpectrum.valuation_eq_one_iff_notMem HeightOneSpectrum.asIdeal rec HeightOneSpectrum.intValuation_ne_zero HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring HeightOneSpectrum.ext mk HeightOneSpectrum)

open _root_.IsDedekindDomain
end IsDedekindDomain
namespace IsLocalRing

export _root_.IsLocalRing (eq_maximalIdeal rec ResidueField ker_residue of_surjective maximalIdeal residue_eq_zero_iff mem_maximalIdeal ResidueField.mapEquiv residue_surjective subsingleton_tensorProduct ResidueField.algebraMap_eq residue)

open _root_.IsLocalRing
end IsLocalRing
namespace J1ThirteenPicZeroFibreDiamond
end J1ThirteenPicZeroFibreDiamond
namespace J1ThirteenPicZeroLitPic0Comparison
end J1ThirteenPicZeroLitPic0Comparison
namespace J1ThirteenPicZeroLiteralChordChain
end J1ThirteenPicZeroLiteralChordChain
namespace J1ThirteenPicZeroPlaceDictionary
end J1ThirteenPicZeroPlaceDictionary
namespace J1ThirteenPicZeroPlaceDictionary
namespace PlaceConstruction
end J1ThirteenPicZeroPlaceDictionary.PlaceConstruction
namespace J1ThirteenPlaneModel
end J1ThirteenPlaneModel
namespace J1ThirteenX113OrdRowWellDefinedReduction
end J1ThirteenX113OrdRowWellDefinedReduction
namespace J1ThirteenX113PackageHeldRowOne
end J1ThirteenX113PackageHeldRowOne
namespace J1ThirteenX113RiemannRochRows
end J1ThirteenX113RiemannRochRows
namespace KaehlerDifferential

export _root_.KaehlerDifferential (span_range_map_derivation_of_isLocalization tensorKaehlerEquivOfFormallyEtale finite exact_kerCotangentToTensor_mapBaseChange polynomialEquiv_symm polynomialEquiv mapBaseChange_tmul D span_range_derivation map_surjective range_mapBaseChange mapBaseChange map_D kerCotangentToTensor_toCotangent map)

open _root_.KaehlerDifferential
end KaehlerDifferential
namespace MazurTate1973Mt31b
end MazurTate1973Mt31b
namespace MilneAvAg9bRd10EllKFinUpperRow
end MilneAvAg9bRd10EllKFinUpperRow
namespace MilneAvAg9bRd11DictionaryBinderShrink
end MilneAvAg9bRd11DictionaryBinderShrink
namespace MilneAvAg9bRd11X113TowerPowerBasis
end MilneAvAg9bRd11X113TowerPowerBasis
namespace MilneAvAg9bRd12T1P1InftyResidue
end MilneAvAg9bRd12T1P1InftyResidue
namespace MilneAvAg9bRd12X113AssemblyRetirement
end MilneAvAg9bRd12X113AssemblyRetirement
namespace MilneAvAg9bRd12X113FiveRowUpgrade
end MilneAvAg9bRd12X113FiveRowUpgrade
namespace MilneAvAg9bRd12X113LocalDatumMint
end MilneAvAg9bRd12X113LocalDatumMint
namespace MilneAvAg9bRd9DictionaryHeld3Closure
end MilneAvAg9bRd9DictionaryHeld3Closure
namespace ModularCurve
namespace KwNo6Pin
end ModularCurve.KwNo6Pin
namespace ModularCurve
namespace KwNo6Section
end ModularCurve.KwNo6Section
namespace ModularCurve
namespace Ldgr35Cs
end ModularCurve.Ldgr35Cs
namespace ModularCurve
namespace Ldgr36Rc
end ModularCurve.Ldgr36Rc
namespace ModularCurve
namespace Ldgr36Si
end ModularCurve.Ldgr36Si
namespace ModularCurve
namespace Lg37
end ModularCurve.Lg37
namespace ModularCurve
namespace Ldgr37Ch
end ModularCurve.Ldgr37Ch
namespace ModularCurve
namespace Ldgr39Hf
end ModularCurve.Ldgr39Hf
namespace ModularCurve
namespace Mp72a102T3
end ModularCurve.Mp72a102T3
namespace Module

export _root_.Module (support Basis.span rec finrank_eq_card_basis Finite.of_basis Basis.singleton finrank Free mk finrank_self Free.of_basis Finite.of_equiv_equiv Basis.traceDual_powerBasis_eq restrictScalars Finite.of_surjective Basis.span_apply finrank_pos finite_of_finrank_pos mem_support_iff Basis)

open _root_.Module
end Module
namespace Mp72a101T2
end Mp72a101T2
namespace Mp72a102T1
end Mp72a102T1
namespace Mp72a102T2
end Mp72a102T2
namespace Mp72a103T2
end Mp72a103T2
namespace Pointwise
open _root_.Pointwise
end Pointwise
namespace Polynomial

export _root_.Polynomial (C smul_eq_C_mul X X_mul_divX_add coeff_natDegree support derivative_C degree_one derivative_map aeval_def natDegree_mul C_eq_algebraMap eval₂_eq_sum_range leadingCoeff eval₂_eq_sum_range' derivative_add coeff algebraMap_eq aeval_X_left_apply eraseLead_natDegree_lt_or_eraseLead_eq_zero algEquivOfTranscendental divX charZero aeval eraseLead_add_C_mul_X_pow irreducible_X not_dvd_of_degree_lt ext_iff map_surjective degree mapEquiv factor aeval_C toSubring degree_sub_le degree_derivative_lt map degree_C degree_ne_bot derivative_X Monic comp natDegree_X_pow natDegree_pow coe_mul algHom_ext sum charP derivative_mul coe_smul Separable coeff_zero leadingCoeff_C natDegree transcendental_X X_ne_zero rec degree_mul_le natDegree_lt_natDegree leadingCoeff_mul sum_C_mul_X_pow_eq mem_support_iff derivative degree_sub_lt smul_pow aeval_X degree_le_of_dvd algebraMap_apply degree_X coeff_divX coeff_eq_zero_of_natDegree_lt eval_map mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse degree_X_pow leadingCoeff_X_pow eraseLead ext degree_eq_natDegree eq_C_of_degree_le_zero isUnit_iff ring aeval_algHom_apply degree_mul aeval_algebraMap_apply leadingCoeff_ne_zero eval)

open _root_.Polynomial
end Polynomial
namespace Polynomial

export _root_.Polynomial (C smul_eq_C_mul X X_mul_divX_add coeff_natDegree support derivative_C degree_one derivative_map aeval_def natDegree_mul C_eq_algebraMap eval₂_eq_sum_range leadingCoeff eval₂_eq_sum_range' derivative_add coeff algebraMap_eq aeval_X_left_apply eraseLead_natDegree_lt_or_eraseLead_eq_zero algEquivOfTranscendental divX charZero aeval eraseLead_add_C_mul_X_pow irreducible_X not_dvd_of_degree_lt ext_iff map_surjective degree mapEquiv factor aeval_C toSubring degree_sub_le degree_derivative_lt map degree_C degree_ne_bot derivative_X Monic comp natDegree_X_pow natDegree_pow coe_mul algHom_ext sum charP derivative_mul coe_smul Separable coeff_zero leadingCoeff_C natDegree transcendental_X X_ne_zero rec degree_mul_le natDegree_lt_natDegree leadingCoeff_mul sum_C_mul_X_pow_eq mem_support_iff derivative degree_sub_lt smul_pow aeval_X degree_le_of_dvd algebraMap_apply degree_X coeff_divX coeff_eq_zero_of_natDegree_lt eval_map mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse degree_X_pow leadingCoeff_X_pow eraseLead ext degree_eq_natDegree eq_C_of_degree_le_zero isUnit_iff ring aeval_algHom_apply degree_mul aeval_algebraMap_apply leadingCoeff_ne_zero eval)

namespace Bivariate
open _root_.Polynomial.Bivariate
open _root_.Polynomial
end Polynomial.Bivariate
namespace RationalFunctionField
end RationalFunctionField
namespace TameRamificationConverseThree
end TameRamificationConverseThree
namespace TensorProduct

export _root_.TensorProduct (congr tmul_zero smul_tmul zero_tmul lift mk ext tmul map_surjective map Algebra.smul_def tmul_add mk_surjective tmul_smul)

open _root_.TensorProduct
end TensorProduct
namespace The
end The
namespace UniqueFactorizationMonoid

export _root_.UniqueFactorizationMonoid (normalizedFactors_eq_of_dvd rec induction_on_prime mk irreducible_of_normalized_factor mem_normalizedFactors_iff prod_normalizedFactors_eq normalizedFactors)

open _root_.UniqueFactorizationMonoid
end UniqueFactorizationMonoid
namespace WithZero

export _root_.WithZero (log_le_log map coe_mul exp_lt_exp log_zpow exp_neg coe log_exp exp_ne_zero log exp exp_zero log_mul lift le log_one exp_le_exp inv exp_log exp_injective)

open _root_.WithZero
end WithZero

section
section

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

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_ne_zero adicValuation_coe_eq_one_iff adicValuation_coe_irreducible ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ord_smul ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring mk.injEq rec ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk adicValuation_valuationSubring mem_iff_adicValuation_le_one isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one isEquiv_adicValuation_ofHeightOneSpectrum ord_ofHeightOneSpectrum_ne_zero_iff dCoord DCoordGenerates dCoord_ne_zero differentialCoeff differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_dCoord differentialCoeff_zero differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg deg_restrict_mul_inertiaDeg ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq)

open _root_.AlgebraicCurve.Place

variable {K F}

variable (v : Place K F)

end Place

namespace Divisor

export _root_.AlgebraicCurve.Divisor (degree degree_single principal smul_def smul_apply degree_smul)

open _root_.AlgebraicCurve.Divisor

variable {K F}

end Divisor

namespace Pic0

export _root_.AlgebraicCurve.Pic0 (mk mk_surjective)

open _root_.AlgebraicCurve.Pic0

variable {K F}

end Pic0

namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_ne_zero adicValuation_coe_eq_one_iff adicValuation_coe_irreducible ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ord_smul ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring mk.injEq rec ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk adicValuation_valuationSubring mem_iff_adicValuation_le_one isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one isEquiv_adicValuation_ofHeightOneSpectrum ord_ofHeightOneSpectrum_ne_zero_iff dCoord DCoordGenerates dCoord_ne_zero differentialCoeff differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_dCoord differentialCoeff_zero differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg deg_restrict_mul_inertiaDeg ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq)

open _root_.AlgebraicCurve.Place

open scoped _root_.Pointwise _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Pointwise

variable {K F}
variable (σ : F ≃ₐ[K] F)

variable (v : Place K F)

end Place

namespace Divisor

export _root_.AlgebraicCurve.Divisor (degree degree_single principal smul_def smul_apply degree_smul)

open _root_.AlgebraicCurve.Divisor

open scoped _root_.Pointwise _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Pointwise

variable {K F}

end Divisor

namespace Pic0

export _root_.AlgebraicCurve.Pic0 (mk mk_surjective)

open _root_.AlgebraicCurve.Pic0

open scoped _root_.Pointwise _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Pointwise

variable {K F}

end Pic0

namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_ne_zero adicValuation_coe_eq_one_iff adicValuation_coe_irreducible ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ord_smul ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring mk.injEq rec ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk adicValuation_valuationSubring mem_iff_adicValuation_le_one isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one isEquiv_adicValuation_ofHeightOneSpectrum ord_ofHeightOneSpectrum_ne_zero_iff dCoord DCoordGenerates dCoord_ne_zero differentialCoeff differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_dCoord differentialCoeff_zero differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg deg_restrict_mul_inertiaDeg ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq)

open _root_.AlgebraicCurve.Place

variable {K F}
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]

end Place

end AlgebraicCurve

end
end

end

section
section

open _root_.Polynomial
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial
open _root_.Module
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Module
open _root_.Algebra
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Algebra

namespace FLT
namespace EulerDualBasis

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]

omit [FiniteDimensional K L] [Algebra.IsSeparable K L] in

theorem coeff_minpolyDiv_dim_sub_one (pb : PowerBasis K L) :
    (minpolyDiv K pb.gen).coeff (pb.dim - 1) = 1 := by
  have h1 : (minpolyDiv K pb.gen).natDegree = pb.dim - 1 := by
    rw [natDegree_minpolyDiv, pb.natDegree_minpoly]
  rw [← h1]
  exact (minpolyDiv_monic pb.isIntegral_gen).coeff_natDegree

theorem traceDual_eq_one_div_of_val_eq (pb : PowerBasis K L) {j : Fin pb.dim}
    (hj : (j : ℕ) = pb.dim - 1) :
    pb.basis.traceDual j = 1 / aeval pb.gen (derivative (minpoly K pb.gen)) := by
  rw [Module.Basis.traceDual_powerBasis_eq]
  rw [hj, coeff_minpolyDiv_dim_sub_one]

theorem trace_pow_div_aeval_derivative_minpoly_of_lt (pb : PowerBasis K L) {k : ℕ}
    (hk : k < pb.dim - 1) :
    Algebra.trace K L
      (pb.gen ^ k / aeval pb.gen (derivative (minpoly K pb.gen))) = 0 := by
  have hd : 0 < pb.dim := by omega
  have hk' : k < pb.dim := by omega
  have hlt : pb.dim - 1 < pb.dim := by omega
  have key := pb.basis.trace_mul_traceDual ⟨k, hk'⟩ ⟨pb.dim - 1, hlt⟩
  rw [traceDual_eq_one_div_of_val_eq pb rfl, pb.basis_eq_pow, mul_one_div] at key
  rw [key, if_neg]
  simp only [Fin.mk.injEq]
  omega

theorem trace_pow_div_aeval_derivative_minpoly_self (pb : PowerBasis K L)
    (hd : 0 < pb.dim) :
    Algebra.trace K L
      (pb.gen ^ (pb.dim - 1) / aeval pb.gen (derivative (minpoly K pb.gen))) = 1 := by
  have hlt : pb.dim - 1 < pb.dim := by omega
  have key := pb.basis.trace_mul_traceDual ⟨pb.dim - 1, hlt⟩ ⟨pb.dim - 1, hlt⟩
  rw [traceDual_eq_one_div_of_val_eq pb rfl, pb.basis_eq_pow, mul_one_div] at key
  rw [key, if_pos rfl]

variable {F : Type*} [Field F] [CharZero F] {g : F[X]} [Fact (Irreducible g)]

theorem trace_root_pow_div_derivative_of_lt (hg : g.Monic) {k : ℕ}
    (hk : k < g.natDegree - 1) :
    Algebra.trace F (AdjoinRoot g)
      (AdjoinRoot.root g ^ k / aeval (AdjoinRoot.root g) (derivative g)) = 0 := by
  haveI : FiniteDimensional F (AdjoinRoot g) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hg.ne_zero).basis
  have hmin : minpoly F (AdjoinRoot.powerBasis hg.ne_zero).gen = g :=
    AdjoinRoot.minpoly_powerBasis_gen_of_monic hg
  have h := trace_pow_div_aeval_derivative_minpoly_of_lt
    (AdjoinRoot.powerBasis hg.ne_zero) (k := k)
    (by rwa [AdjoinRoot.powerBasis_dim])
  rwa [hmin, AdjoinRoot.powerBasis_gen] at h

theorem trace_root_pow_div_derivative_self (hg : g.Monic) (hd : 0 < g.natDegree) :
    Algebra.trace F (AdjoinRoot g)
      (AdjoinRoot.root g ^ (g.natDegree - 1) /
        aeval (AdjoinRoot.root g) (derivative g)) = 1 := by
  haveI : FiniteDimensional F (AdjoinRoot g) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hg.ne_zero).basis
  have hmin : minpoly F (AdjoinRoot.powerBasis hg.ne_zero).gen = g :=
    AdjoinRoot.minpoly_powerBasis_gen_of_monic hg
  have h := trace_pow_div_aeval_derivative_minpoly_self
    (AdjoinRoot.powerBasis hg.ne_zero)
    (by rwa [AdjoinRoot.powerBasis_dim])
  rwa [hmin, AdjoinRoot.powerBasis_gen, AdjoinRoot.powerBasis_dim] at h

end FLT.EulerDualBasis

namespace FLT
namespace EulerDualBasis
namespace Gates

open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.TameRamificationConverseThree
open _root_.AdjoinRoot
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AdjoinRoot

end FLT.EulerDualBasis.Gates

end

end

section
section

noncomputable section

open _root_.KaehlerDifferential
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.KaehlerDifferential

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq)

open _root_.AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

namespace IsCurveOver

export _root_.AlgebraicCurve.IsCurveOver (instFiniteResidue mk finiteResidue kaehler_free_rank_one rec)

open _root_.AlgebraicCurve.IsCurveOver

variable {K F}

end IsCurveOver

namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_ne_zero adicValuation_coe_eq_one_iff adicValuation_coe_irreducible ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ord_smul ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring mk.injEq rec ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk adicValuation_valuationSubring mem_iff_adicValuation_le_one isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one isEquiv_adicValuation_ofHeightOneSpectrum ord_ofHeightOneSpectrum_ne_zero_iff dCoord DCoordGenerates dCoord_ne_zero differentialCoeff differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_dCoord differentialCoeff_zero differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg deg_restrict_mul_inertiaDeg ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq)

open _root_.AlgebraicCurve.Place

variable {K F}
variable (v : Place K F)

end Place

variable {K F}

variable (K F)

def OrdDifferentialWellDefined : Prop :=
  ∀ (v : Place K F) (π π' : F), v.ord π = 1 → v.ord π' = 1 →
    ∃ u : F, v.ord u = 0 ∧
      KaehlerDifferential.D K F π' = u • KaehlerDifferential.D K F π

end AlgebraicCurve

namespace ModularCurve

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve

end ModularCurve

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq)

open _root_.AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

end AlgebraicCurve

namespace ModularCurve

end ModularCurve

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

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq)

open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

variable {D E : Divisor K F}

variable (K F)

end AlgebraicCurve

end

end

end

section
section

noncomputable section

open _root_.Polynomial
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial
open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsDedekindDomain

open scoped _root_.Polynomial.Bivariate _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial.Bivariate

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq)

namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_ne_zero adicValuation_coe_eq_one_iff adicValuation_coe_irreducible ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ord_smul ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring mk.injEq rec ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk adicValuation_valuationSubring mem_iff_adicValuation_le_one isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one isEquiv_adicValuation_ofHeightOneSpectrum ord_ofHeightOneSpectrum_ne_zero_iff dCoord DCoordGenerates dCoord_ne_zero differentialCoeff differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_dCoord differentialCoeff_zero differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg deg_restrict_mul_inertiaDeg ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq)

open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.ord_add_eq_min {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (h : v.ord f ≠ v.ord g) :
    v.ord (f + g) = min (v.ord f) (v.ord g) := by
  have hval : v.adicValuation f ≠ v.adicValuation g := by
    intro hcon
    exact h (by simp only [ord, hcon])
  have h1 : v.adicValuation (f + g) = max (v.adicValuation f) (v.adicValuation g) :=
    Valuation.map_add_of_distinct_val _ hval
  have hfg : f + g ≠ 0 := by
    intro hcon
    rw [hcon, _root_.map_zero] at h1
    rcases max_cases (v.adicValuation f) (v.adicValuation g) with ⟨hmax, -⟩ | ⟨hmax, -⟩ <;>
      rw [hmax] at h1
    · exact v.adicValuation_ne_zero hf h1.symm
    · exact v.adicValuation_ne_zero hg h1.symm
  rcases max_cases (v.adicValuation f) (v.adicValuation g) with ⟨hmax, hle⟩ | ⟨hmax, hlt⟩ <;>
    rw [hmax] at h1
  ·
    have hlog := (WithZero.log_le_log (v.adicValuation_ne_zero hg)
      (v.adicValuation_ne_zero hf)).mpr hle
    have h2 : v.ord (f + g) = v.ord f := by simp only [ord, h1]
    simp only [ord] at hlog h2 ⊢
    omega
  · have hlog := (WithZero.log_le_log (v.adicValuation_ne_zero hf)
      (v.adicValuation_ne_zero hg)).mpr hlt.le
    have h2 : v.ord (f + g) = v.ord g := by simp only [ord, h1]
    simp only [ord] at hlog h2 ⊢
    omega




-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.ord_add_eq_min :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.ord_add_eq_min
end AlgebraicCurve.Place

namespace WeierstrassCurve

export _root_.WeierstrassCurve (Affine mk.injEq a₁ map mk a₂ isIntegral_iff IsIntegral rec baseChange j)

namespace Affine

export _root_.WeierstrassCurve.Affine (CoordinateRing map baseChange FunctionField)

open _root_.WeierstrassCurve.Affine
open _root_.WeierstrassCurve

open _root_.WeierstrassCurve.Affine.CoordinateRing
open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve

variable {F : Type*} [Field F] {W : Affine F}

variable (v : AlgebraicCurve.Place F W.FunctionField)

end WeierstrassCurve.Affine

end
end

end

section
section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
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

namespace ModularCurve
namespace Lg37

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve
open ModularCurve.Ldgr36Si
open ModularCurve.Ldgr36Rc
open ModularCurve.Ldgr35Cs

section CompletionCarrier

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

abbrev lg37_completion (v : Place K F) : Type _ :=
  AdicCompletion (IsLocalRing.maximalIdeal v.toValuationSubring) v.toValuationSubring

def lg37_residueHat (v : Place K F) :
    lg37_completion v →+* v.ResidueField :=
  (AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal v.toValuationSubring)).toRingHom

theorem lg37_residueHat_algebraMap (v : Place K F) (x : v.toValuationSubring) :
    lg37_residueHat v
        (algebraMap v.toValuationSubring (lg37_completion v) x)
      = IsLocalRing.residue v.toValuationSubring x := rfl

structure Lg37CompletionSection (v : Place K F) where

  lift : v.ResidueField →ₐ[K] lg37_completion v

  residueHat_lift : ∀ a, lg37_residueHat v (lift a) = a

end CompletionCarrier

section Inhabitant

end Inhabitant

section Stratum

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [HasCanonicalLocalResidueKStar K E]

end Stratum

section MovedCarrier

variable {K K' F' : Type*} [Field K] [Field K'] [Field F']
  [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']
variable [HasCanonicalLocalResidueKStar K F']

end MovedCarrier

section CommittedPlace

end CommittedPlace

end ModularCurve.Lg37

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
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsLocalRing

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq)

open _root_.AlgebraicCurve

namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_ne_zero adicValuation_coe_eq_one_iff adicValuation_coe_irreducible ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ord_smul ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring mk.injEq rec ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk adicValuation_valuationSubring mem_iff_adicValuation_le_one isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one isEquiv_adicValuation_ofHeightOneSpectrum ord_ofHeightOneSpectrum_ne_zero_iff dCoord DCoordGenerates dCoord_ne_zero differentialCoeff differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_dCoord differentialCoeff_zero differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg deg_restrict_mul_inertiaDeg ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq)

open _root_.AlgebraicCurve.Place

section SinglePlace

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.ord_nonneg_of_mem {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n




-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.ord_nonneg_of_mem :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.ord_nonneg_of_mem
theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.mem_of_ord_nonneg {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)




-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.mem_of_ord_nonneg :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.mem_of_ord_nonneg
theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.mem_iff_ord_nonneg {f : F} (hf : f ≠ 0) :
    f ∈ v.toValuationSubring ↔ 0 ≤ v.ord f :=
  ⟨v.ord_nonneg_of_mem, v.mem_of_ord_nonneg hf⟩




-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.mem_iff_ord_nonneg :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.mem_iff_ord_nonneg
theorem exists_ord_pos : ∃ f : F, f ≠ 0 ∧ 0 < v.ord f := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  refine ⟨(π : F), ?_, ?_⟩
  · simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  · rw [v.ord_coe_irreducible hπ]
    exact one_pos

end SinglePlace

section Restrict

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F'] [Algebra F F']

theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.algebraMap_ne_zero {f : F} (hf : f ≠ 0) : algebraMap F F' f ≠ 0 := by
  simpa using hf




-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.algebraMap_ne_zero :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.algebraMap_ne_zero
variable (w : Place K F')

theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.comap_algebraMap_ne_top [Algebra.IsIntegral F F'] :
    w.toValuationSubring.comap (algebraMap F F') ≠ ⊤ := by
  intro htop
  apply w.ne_top'

  have hF : ∀ f : F, algebraMap F F' f ∈ w.toValuationSubring := fun f =>
    ValuationSubring.mem_comap.mp (htop ▸ ValuationSubring.mem_top f)

  refine SetLike.ext fun x => ⟨fun _ => ValuationSubring.mem_top x, fun _ => ?_⟩
  letI : Algebra F w.toValuationSubring :=
    ((algebraMap F F').codRestrict w.toValuationSubring.toSubring hF).toAlgebra
  letI : IsScalarTower F w.toValuationSubring F' :=
    IsScalarTower.of_algebraMap_eq fun f => rfl
  have hx : _root_.IsIntegral w.toValuationSubring x :=
    (Algebra.IsIntegral.isIntegral (R := F) x).tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hx
  exact hy ▸ y.2




-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.comap_algebraMap_ne_top :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.comap_algebraMap_ne_top
variable {w} in

theorem mem_comap_iff_ord_nonneg {f : F} (hf : f ≠ 0) :
    f ∈ w.toValuationSubring.comap (algebraMap F F') ↔
      0 ≤ w.ord (algebraMap F F' f) := by
  rw [ValuationSubring.mem_comap]
  exact w.mem_iff_ord_nonneg (algebraMap_ne_zero hf)

variable {w} in

theorem isUnit_mk_comap_iff {f : F} (hf : f ≠ 0)
    (hmem : f ∈ w.toValuationSubring.comap (algebraMap F F')) :
    IsUnit (⟨f, hmem⟩ : w.toValuationSubring.comap (algebraMap F F')) ↔
      w.ord (algebraMap F F' f) = 0 := by
  constructor
  · rintro h
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp h
    have hb' : f * (b : F) = 1 := by
      simpa [Subtype.ext_iff] using hb
    have hbne : (b : F) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hb'
      exact zero_ne_one hb'
    have hsum : w.ord (algebraMap F F' f) + w.ord (algebraMap F F' (b : F)) = 0 := by
      rw [← w.ord_mul (algebraMap_ne_zero hf) (algebraMap_ne_zero hbne), ← map_mul, hb',
        map_one, w.ord_one]
    have h1 : 0 ≤ w.ord (algebraMap F F' f) := (mem_comap_iff_ord_nonneg hf).mp hmem
    have h2 : 0 ≤ w.ord (algebraMap F F' (b : F)) := (mem_comap_iff_ord_nonneg hbne).mp b.2
    omega
  · intro h0
    have hinv : f⁻¹ ∈ w.toValuationSubring.comap (algebraMap F F') :=
      (mem_comap_iff_ord_nonneg (inv_ne_zero hf)).mpr (by rw [map_inv₀, w.ord_inv]; omega)
    exact ⟨⟨⟨f, hmem⟩, ⟨f⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hf),
      Subtype.ext (inv_mul_cancel₀ hf)⟩, rfl⟩

theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.exists_ord_algebraMap_pos [Algebra.IsIntegral F F'] :
    ∃ f : F, f ≠ 0 ∧ 0 < w.ord (algebraMap F F' f) := by
  have h := w.comap_algebraMap_ne_top (F := F)
  rw [ne_eq, SetLike.ext_iff, not_forall] at h
  obtain ⟨g, hg⟩ := h
  simp only [ValuationSubring.mem_top, iff_true] at hg
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact hg (zero_mem _)
  refine ⟨g⁻¹, inv_ne_zero hg0, ?_⟩
  rw [map_inv₀, w.ord_inv]
  have := (mem_comap_iff_ord_nonneg hg0).not.mp hg
  omega




-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.exists_ord_algebraMap_pos :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.exists_ord_algebraMap_pos
variable [Algebra.IsIntegral F F']

theorem ramificationIndex_set_nonempty :
    {n : ℕ | 0 < n ∧ ∃ f : F, f ≠ 0 ∧ w.ord (algebraMap F F' f) = n}.Nonempty := by
  obtain ⟨f, hf0, hf⟩ := w.exists_ord_algebraMap_pos (F := F)
  exact ⟨(w.ord (algebraMap F F' f)).toNat, by omega, f, hf0, by omega⟩

theorem isPrincipalIdealRing_comap :
    IsPrincipalIdealRing (w.toValuationSubring.comap (algebraMap F F')) := by
  obtain ⟨g, hg0, hge⟩ := w.exists_ord_eq_ramificationIndex (F := F)
  have hepos : 0 < ramificationIndex (F := F) w := w.ramificationIndex_pos (F := F)
  have hgmem : g ∈ w.toValuationSubring.comap (algebraMap F F') :=
    (mem_comap_iff_ord_nonneg hg0).mpr (by omega)
  refine (IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨⟨g, hgmem⟩, irreducible_mk_comap w hg0 hgmem hge, ?_⟩).toIsPrincipalIdealRing
  rintro ⟨f, hmem⟩ hx
  have hf : f ≠ 0 := by simpa [Subtype.ext_iff] using hx

  obtain ⟨c, hc⟩ := w.ramificationIndex_dvd_ord (F := F) hf
  have hnonneg : 0 ≤ w.ord (algebraMap F F' f) := (mem_comap_iff_ord_nonneg hf).mp hmem
  have hcnonneg : 0 ≤ c := by
    by_contra hneg
    have hcle : c ≤ -1 := by omega
    have : (ramificationIndex (F := F) w : ℤ) * c ≤ (ramificationIndex (F := F) w : ℤ) * -1 :=
      mul_le_mul_of_nonneg_left hcle (by omega)
    omega
  set n : ℕ := c.toNat with hn
  have hcn : (n : ℤ) = c := Int.toNat_of_nonneg hcnonneg
  refine ⟨n, ?_⟩

  have hgn : g ^ n ≠ 0 := pow_ne_zero _ hg0
  have hdiv0 : f / g ^ n ≠ 0 := div_ne_zero hf hgn
  have hu0 : w.ord (algebraMap F F' (f / g ^ n)) = 0 := by
    have hkey : algebraMap F F' (f / g ^ n)
        = algebraMap F F' f * (algebraMap F F' g) ^ (-(n : ℤ)) := by
      rw [div_eq_mul_inv, map_mul, map_inv₀, map_pow, ← zpow_natCast (algebraMap F F' g) n,
        ← _root_.zpow_neg]
    rw [hkey, w.ord_mul (algebraMap_ne_zero hf) (zpow_ne_zero _ (algebraMap_ne_zero hg0)),
      w.ord_zpow, hge, hc, ← hcn]
    ring
  have humem : f / g ^ n ∈ w.toValuationSubring.comap (algebraMap F F') :=
    (mem_comap_iff_ord_nonneg hdiv0).mpr (le_of_eq hu0.symm)
  have hu : IsUnit (⟨f / g ^ n, humem⟩ : w.toValuationSubring.comap (algebraMap F F')) :=
    (isUnit_mk_comap_iff hdiv0 humem).mpr hu0
  refine ⟨hu.unit, ?_⟩
  refine Subtype.ext ?_
  have hcoe : ((hu.unit : w.toValuationSubring.comap (algebraMap F F')) : F) = f / g ^ n := by
    rw [IsUnit.unit_spec]
  push_cast
  rw [hcoe, mul_comm, div_mul_cancel₀]
  exact hgn

section RestrictDef

variable [Algebra K F] [IsScalarTower K F F']

end RestrictDef

end Restrict

end Place

end AlgebraicCurve

end
end

end

section
section

noncomputable section

open _root_.Polynomial
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial
open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.WithZero
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsLocalRing
open _root_.IntermediateField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IntermediateField

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq)

namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_ne_zero adicValuation_coe_eq_one_iff adicValuation_coe_irreducible ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ord_smul ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring mk.injEq rec ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk adicValuation_valuationSubring mem_iff_adicValuation_le_one isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one isEquiv_adicValuation_ofHeightOneSpectrum ord_ofHeightOneSpectrum_ne_zero_iff dCoord DCoordGenerates dCoord_ne_zero differentialCoeff differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_dCoord differentialCoeff_zero differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg deg_restrict_mul_inertiaDeg ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq)

open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve

section Ultrametric

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.ord_add_eq_left {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (h : v.ord f < v.ord g) :
    v.ord (f + g) = v.ord f := by

  have hfv := v.adicValuation_ne_zero hf
  have hgv := v.adicValuation_ne_zero hg
  have hlt : v.adicValuation g < v.adicValuation f := by
    rw [← exp_log hfv, ← exp_log hgv]
    have hlog : log (v.adicValuation g) < log (v.adicValuation f) := by
      simp only [ord] at h
      omega
    exact lt_of_le_of_ne (exp_le_exp.mpr hlog.le)
      fun hcon => hlog.ne (exp_injective hcon)
  have h1 : v.adicValuation (f + g) = max (v.adicValuation f) (v.adicValuation g) :=
    Valuation.map_add_of_distinct_val _ (ne_of_lt hlt).symm
  rw [max_eq_left hlt.le] at h1
  simp only [ord, h1]




-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.ord_add_eq_left :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.ord_add_eq_left
end Ultrametric

section SumLeFinrank

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

end SumLeFinrank

end AlgebraicCurve.Place

namespace ModularCurve

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve

section RationalFunctionFieldInfty

end RationalFunctionFieldInfty

section Tower

variable (p : ℕ) [NeZero p]

end Tower

section Degree

variable (p : ℕ) [NeZero p]

end Degree

section Restriction

end Restriction

section Assembly

variable {p : ℕ} [NeZero p]

end Assembly

end ModularCurve

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
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsLocalRing
open scoped _root_.Polynomial _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq)

open _root_.AlgebraicCurve

namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_ne_zero adicValuation_coe_eq_one_iff adicValuation_coe_irreducible ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ord_smul ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring mk.injEq rec ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk adicValuation_valuationSubring mem_iff_adicValuation_le_one isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one isEquiv_adicValuation_ofHeightOneSpectrum ord_ofHeightOneSpectrum_ne_zero_iff dCoord DCoordGenerates dCoord_ne_zero differentialCoeff differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_dCoord differentialCoeff_zero differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg deg_restrict_mul_inertiaDeg ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq)

open _root_.AlgebraicCurve.Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

section OfHeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
  [Algebra K R] [IsScalarTower K R F]

end OfHeightOneSpectrum

end Place

namespace RationalFunctionField

export _root_.AlgebraicCurve.RationalFunctionField (heightOneSpectrumOfIrreducible heightOneSpectrumOfIrreducible_asIdeal exists_irreducible_span finitePlace finitePlace_def algebraMap_mem_ofHeightOneSpectrum residueFieldEquivOfHeightOneSpectrum deg_ofHeightOneSpectrum deg_finitePlace)

open _root_.AlgebraicCurve.RationalFunctionField

variable (K : Type*) [Field K]

theorem ord_finitePlace_ne_zero_iff {p : K[X]} (hp : Irreducible p) {q : K[X]} (hq : q ≠ 0) :
    (finitePlace K hp).ord (algebraMap K[X] (RatFunc K) q) ≠ 0 ↔ p ∣ q := by
  rw [finitePlace, Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) _ hq,
    heightOneSpectrumOfIrreducible_asIdeal, Ideal.mem_span_singleton]

section PlaceInfty

variable [DecidableEq (RatFunc K)]

scoped instance : Nontrivial (MonoidWithZeroHom.valueGroup (MonoidWithZeroHom.ofClass (RatFunc.inftyValuation K))) := by
  rw [Subgroup.nontrivial_iff_exists_ne_one]
  refine ⟨Units.mk0 (RatFunc.inftyValuation K RatFunc.X)
    (by rw [RatFunc.inftyValuation.X]; exact exp_ne_zero), ?_, ?_⟩
  · exact MonoidWithZeroHom.mem_valueGroup _ ⟨RatFunc.X, rfl⟩
  · rw [ne_eq, Units.ext_iff, Units.val_mk0, Units.val_one, RatFunc.inftyValuation.X]
    simp

def placeInfty : Place K (RatFunc K) where
  toValuationSubring := (RatFunc.inftyValuation K).valuationSubring
  algebraMap_mem' a := by
    rw [Valuation.mem_valuationSubring_iff]
    exact Valuation.IsTrivialOn.valuation_algebraMap_le_one (v := RatFunc.inftyValuation K) a
  ne_top' := by
    simp only [ne_eq, Valuation.valuationSubring_eq_top_iff, not_not]
    infer_instance
  isPrincipalIdealRing' :=
    (Valuation.valuationSubring_isDiscreteValuationRing
      (RatFunc.inftyValuation K)).toIsPrincipalIdealRing

@[scoped simp]
theorem placeInfty_toValuationSubring :
    (placeInfty K).toValuationSubring = (RatFunc.inftyValuation K).valuationSubring := rfl

theorem inftyValuation_isEquiv_adicValuation :
    (RatFunc.inftyValuation K).IsEquiv (placeInfty K).adicValuation :=
  (placeInfty K).isEquiv_adicValuation_of_valuationSubring_eq rfl

theorem placeInfty_ne_ofHeightOneSpectrum (w : HeightOneSpectrum K[X]) :
    placeInfty K ≠ Place.ofHeightOneSpectrum w := by
  intro h
  refine RatFunc.adicValuation_not_isEquiv_infty_valuation w
    ((Valuation.isEquiv_iff_valuationSubring _ _).mpr ?_)
  have h2 := congrArg Place.toValuationSubring h
  rw [placeInfty_toValuationSubring, Place.ofHeightOneSpectrum_toValuationSubring] at h2
  exact h2.symm

end PlaceInfty

variable {K}

theorem eq_ofHeightOneSpectrum_or_eq_placeInfty [DecidableEq (RatFunc K)]
    (v : Place K (RatFunc K)) :
    (∃ w : HeightOneSpectrum K[X], v = Place.ofHeightOneSpectrum w) ∨ v = placeInfty K := by
  rcases (RatFunc.valuation_isEquiv_infty_or_adic (v := v.adicValuation)).or with h | h
  · exact Or.inr (Place.ext (v.adicValuation_valuationSubring.symm.trans
      ((Valuation.isEquiv_iff_valuationSubring _ _).mp h)))
  · obtain ⟨w, hw, -⟩ := h
    exact Or.inl ⟨w, Place.ext (v.adicValuation_valuationSubring.symm.trans
      ((Valuation.isEquiv_iff_valuationSubring _ _).mp hw))⟩

theorem subsingleton_setOf_forall_ne_ofHeightOneSpectrum :
    {v : Place K (RatFunc K) |
      ∀ w : HeightOneSpectrum K[X], v ≠ Place.ofHeightOneSpectrum w}.Subsingleton := by
  classical
  intro v hv v' hv'
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, h⟩ | h
  · exact absurd h (hv w)
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v' with ⟨w, h'⟩ | h'
  · exact absurd h' (hv' w)
  rw [h, h']

theorem finite_setOf_valuation_ne_one {f : RatFunc K} (hf : f ≠ 0) :
    {w : HeightOneSpectrum K[X] | w.valuation (RatFunc K) f ≠ 1}.Finite := by
  have hnum : (Ideal.span {f.num} : Ideal K[X]) ≠ 0 := by
    simpa [Ideal.span_singleton_eq_bot] using RatFunc.num_ne_zero hf
  have hden : (Ideal.span {f.denom} : Ideal K[X]) ≠ 0 := by
    simpa [Ideal.span_singleton_eq_bot] using f.denom_ne_zero
  refine Set.Finite.subset ((Ideal.finite_factors hnum).union (Ideal.finite_factors hden))
    fun w hw => ?_
  by_contra hcon
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, Ideal.dvd_span_singleton] at hcon
  refine hw ?_
  have h1 : w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) f.num) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem w).mpr hcon.1
  have h2 : w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) f.denom) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem w).mpr hcon.2
  rw [show f = algebraMap K[X] (RatFunc K) f.num / algebraMap K[X] (RatFunc K) f.denom from
    f.num_div_denom.symm, map_div₀, h1, h2]
  exact div_one 1

theorem finite_setOf_ord_ne_zero {f : RatFunc K} (hf : f ≠ 0) :
    {v : Place K (RatFunc K) | v.ord f ≠ 0}.Finite := by
  refine Set.Finite.subset
    (Set.Finite.union
      (Set.Finite.image (Place.ofHeightOneSpectrum (K := K))
        (finite_setOf_valuation_ne_one hf))
      (Set.Subsingleton.finite subsingleton_setOf_forall_ne_ofHeightOneSpectrum))
    fun v hv => ?_
  simp only [Set.mem_setOf_eq] at hv
  simp only [Set.mem_union, Set.mem_image, Set.mem_setOf_eq]
  by_cases hcase : ∃ w : HeightOneSpectrum K[X], v = Place.ofHeightOneSpectrum w
  · obtain ⟨w, rfl⟩ := hcase
    refine Or.inl ⟨w, fun hone => hv ?_, rfl⟩
    exact ((Place.ofHeightOneSpectrum (K := K) w).ord_eq_zero_iff_adicValuation_eq_one hf).mpr
      ((Place.isEquiv_adicValuation_ofHeightOneSpectrum (K := K) (F := RatFunc K)
        w).eq_one_iff_eq_one.mp hone)
  · exact Or.inr fun w h => hcase ⟨w, h⟩

section ResidueDegree

variable (K)

end ResidueDegree

section DegInfty

variable (K) [DecidableEq (RatFunc K)]

theorem exists_sub_algebraMap_intDegree_neg {x : RatFunc K}
    (hx : RatFunc.inftyValuation K x ≤ 1) :
    ∃ c : K, x - algebraMap K (RatFunc K) c = 0 ∨
      (x - algebraMap K (RatFunc K) c).intDegree < 0 := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨0, Or.inl (by simp)⟩
  have hdeg : x.intDegree ≤ 0 := by
    rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero K hx0,
      show (1 : ℤᵐ⁰) = exp 0 from rfl, exp_le_exp] at hx
    exact hx
  have hnum0 : x.num ≠ 0 := RatFunc.num_ne_zero hx0
  have hden0 : x.denom ≠ 0 := x.denom_ne_zero
  rcases lt_or_eq_of_le hdeg with hlt | heq
  · exact ⟨0, Or.inr (by simpa using hlt)⟩

  have hndeg : x.num.natDegree = x.denom.natDegree := by
    have h2 := heq
    rw [RatFunc.intDegree, sub_eq_zero] at h2
    exact_mod_cast h2
  set c : K := x.num.leadingCoeff / x.denom.leadingCoeff with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact div_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hnum0)
      (Polynomial.leadingCoeff_ne_zero.mpr hden0)
  refine ⟨c, ?_⟩
  have hsub : x - algebraMap K (RatFunc K) c
      = algebraMap K[X] (RatFunc K) (x.num - Polynomial.C c * x.denom)
        / algebraMap K[X] (RatFunc K) x.denom := by
    rw [map_sub, map_mul, sub_div, x.num_div_denom, mul_div_assoc,
      div_self ((map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hden0),
      mul_one, IsScalarTower.algebraMap_apply K K[X] (RatFunc K), Polynomial.algebraMap_eq]
  rcases eq_or_ne (x.num - Polynomial.C c * x.denom) 0 with hzero | hnz
  · exact Or.inl (by rw [hsub, hzero, _root_.map_zero, zero_div])
  refine Or.inr ?_
  rw [hsub, RatFunc.intDegree_div ((map_ne_zero_iff _
      (IsFractionRing.injective K[X] (RatFunc K))).mpr hnz)
    ((map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hden0),
    RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial, sub_neg]

  have hCdeg : (Polynomial.C c * x.denom).degree = x.denom.degree := by
    rw [Polynomial.degree_mul, Polynomial.degree_C hc0, zero_add]
  have hdegeq : x.num.degree = (Polynomial.C c * x.denom).degree := by
    rw [hCdeg, Polynomial.degree_eq_natDegree hnum0, Polynomial.degree_eq_natDegree hden0,
      hndeg]
  have hlc : x.num.leadingCoeff = (Polynomial.C c * x.denom).leadingCoeff := by
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hc,
      div_mul_cancel₀ _ (Polynomial.leadingCoeff_ne_zero.mpr hden0)]
  have hlt := Polynomial.degree_sub_lt hdegeq hnum0 hlc
  rw [hdegeq, hCdeg] at hlt
  exact_mod_cast Polynomial.natDegree_lt_natDegree hnz hlt

theorem deg_placeInfty : (placeInfty K).deg = 1 := by
  have hbij : Function.Bijective (Algebra.ofId K (placeInfty K).ResidueField) := by
    constructor
    · exact fun a b h => (algebraMap K ((placeInfty K).ResidueField)).injective h
    · intro y
      obtain ⟨⟨x, hx⟩, rfl⟩ := IsLocalRing.residue_surjective y
      obtain ⟨c, hc⟩ := exists_sub_algebraMap_intDegree_neg K
        ((Valuation.mem_valuationSubring_iff _ _).mp hx)
      refine ⟨c, ?_⟩
      show IsLocalRing.residue _ (algebraMap K (placeInfty K).toValuationSubring c) = _
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
        Place.mem_maximalIdeal_iff_adicValuation_lt_one]
      show (placeInfty K).adicValuation (algebraMap K (RatFunc K) c - x) < 1
      rw [← (inftyValuation_isEquiv_adicValuation K).lt_one_iff_lt_one,
        show algebraMap K (RatFunc K) c - x = -(x - algebraMap K (RatFunc K) c) from
          (neg_sub _ _).symm, Valuation.map_neg]
      rcases hc with hc | hc
      · rw [hc, _root_.map_zero]
        exact zero_lt_one
      · rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuationDef]
        split
        · exact zero_lt_one
        · rw [show (1 : ℤᵐ⁰) = exp 0 from rfl, exp_lt_exp]
          exact hc
  rw [Place.deg, ← (AlgEquiv.ofBijective _ hbij).toLinearEquiv.finrank_eq,
    Module.finrank_self]

end DegInfty

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

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq)

open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)]
variable [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

omit [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)] [Nontrivial Ω[F⁄K]] in

theorem exists_smul_eq_of_ne_zero (v : Place K F) {ω ω₀ : Ω[F⁄K]}
    (hω : ω ≠ 0) (hω₀ : ω₀ ≠ 0) : ∃ g : F, g ≠ 0 ∧ ω = g • ω₀ := by
  set a := v.differentialCoeff ω with ha
  set b := v.differentialCoeff ω₀ with hb
  have h0 : b ≠ 0 := v.differentialCoeff_ne_zero hω₀
  refine ⟨a * b⁻¹, mul_ne_zero (v.differentialCoeff_ne_zero hω) (inv_ne_zero h0), ?_⟩
  have hω₀eq : ω₀ = b • v.dCoord := hb ▸ (v.differentialCoeff_smul_dCoord ω₀).symm
  rw [hω₀eq, smul_smul, mul_assoc, inv_mul_cancel₀ h0, mul_one]
  exact ha ▸ (v.differentialCoeff_smul_dCoord ω).symm

section TraceDescent

variable (K F)
variable (E : Type*) [Field E] [Algebra K E]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalDivisor (K := K) (F := E)]
variable [∀ v : Place K E, v.DCoordGenerates] [Nontrivial Ω[E⁄K]]
variable [Algebra E F]

end TraceDescent


section Engine

variable {E : Type*} [Field E] [Algebra K E]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalDivisor (K := K) (F := E)]
variable [∀ v : Place K E, v.DCoordGenerates] [Nontrivial Ω[E⁄K]]
variable [Algebra E F] [HasPrincipalDivisors K E]

end Engine


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

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq)

open _root_.AlgebraicCurve

namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_ne_zero adicValuation_coe_eq_one_iff adicValuation_coe_irreducible ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ord_smul ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring mk.injEq rec ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk adicValuation_valuationSubring mem_iff_adicValuation_le_one isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one isEquiv_adicValuation_ofHeightOneSpectrum ord_ofHeightOneSpectrum_ne_zero_iff dCoord DCoordGenerates dCoord_ne_zero differentialCoeff differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_dCoord differentialCoeff_zero differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg deg_restrict_mul_inertiaDeg ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq)

open _root_.AlgebraicCurve.Place

section Transport

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

noncomputable def _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.uniformizerSubring' : v.toValuationSubring :=
  (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose




-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.uniformizerSubring' :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.uniformizerSubring'
scoped instance instSMulCommClass_subring : SMulCommClass K v.toValuationSubring F :=
  IsScalarTower.to_smulCommClass

theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.kaehlerMap_subring_D_uniformizer :
    KaehlerDifferential.map K K v.toValuationSubring F
      (KaehlerDifferential.D K v.toValuationSubring v.uniformizerSubring') = v.dCoord := by
  rw [KaehlerDifferential.map_D K K v.toValuationSubring F]
  rfl




-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.kaehlerMap_subring_D_uniformizer :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.kaehlerMap_subring_D_uniformizer
end Transport


end Place


variable (K F : Type*) [Field K] [Field F] [Algebra K F]

def ValSubringKaehlerSpanTop : Prop :=
  ∀ v : Place K F,
    Submodule.span v.toValuationSubring
      {KaehlerDifferential.D K v.toValuationSubring (Place.uniformizerSubring' v)} = ⊤

variable {K F}

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

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)]
variable [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
variable [HasPrincipalDivisors K F]

variable (K F) in

def principalAdele : F →ₗ[K] adeleSpace K F where
  toFun f := ⟨diagonalHom K F f, diagonal_mem_adeleSpace f⟩
  map_add' f g := Subtype.ext ((diagonalHom K F).map_add f g)
  map_smul' c f := Subtype.ext ((diagonalHom K F).map_smul c f)

section P1NamedRows

open scoped _root_.Polynomial _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial

variable (K)
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]

def P1PolynomialGenerators : Set (RatFunc K) := Set.range fun n : ℕ => RatFunc.X ^ n

def P1PrincipalPartGenerators : Set (RatFunc K) :=
  {f | ∃ (p c : K[X]) (m : ℕ), p.Monic ∧ Irreducible p ∧ c.degree < p.degree ∧ 1 ≤ m ∧
    f = algebraMap K[X] (RatFunc K) c / (algebraMap K[X] (RatFunc K) p) ^ m}

def P1PartialFractionGenerators : Set (RatFunc K) :=
  P1PolynomialGenerators K ∪ P1PrincipalPartGenerators K

variable {K}

end P1NamedRows


section P1Gates

open scoped _root_.Polynomial _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial

theorem gate_algebraMap_polynomial_mem_span_P1PolynomialGenerators (q : K[X]) :
    algebraMap K[X] (RatFunc K) q ∈ Submodule.span K (P1PolynomialGenerators K) := by

  rw [← Polynomial.sum_C_mul_X_pow_eq q, Polynomial.sum, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_mul, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_X,
    ← RatFunc.smul_eq_C_mul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end P1Gates


end AlgebraicCurve


section AxiomAudit

end AxiomAudit


end


end


end


section
section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

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

namespace Mp72a102T1

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.RationalFunctionField
open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField
open ModularCurve.Lg37 ModularCurve.Ldgr37Ch
open Mp72a101T2

open scoped _root_.Polynomial _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial

attribute [local instance 2000] RatFunc.instAlgebraOfPolynomial

section Engine

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

noncomputable abbrev mp72a102_t1_maximalIdealHat (v : Place K F) :
    Ideal (lg37_completion v) :=
  (IsLocalRing.maximalIdeal v.toValuationSubring).map
    (algebraMap v.toValuationSubring (lg37_completion v))

theorem mp72a102_t1_isScalarTower (v : Place K F) :
    IsScalarTower K v.toValuationSubring (lg37_completion v) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem mp72a102_t1_isAdicComplete_maximalIdealHat (v : Place K F) :
    IsAdicComplete (mp72a102_t1_maximalIdealHat v) (lg37_completion v) :=
  (IsAdicComplete.map_algebraMap_iff (IsLocalRing.maximalIdeal v.toValuationSubring)
      (lg37_completion v)).mpr
    (AdicCompletion.isAdicComplete
      (IsPrincipalIdealRing.principal
        (IsLocalRing.maximalIdeal v.toValuationSubring)).fg)

theorem mp72a102_t1_henselianRing_completion (v : Place K F) :
    HenselianRing (lg37_completion v) (mp72a102_t1_maximalIdealHat v) :=
  letI := mp72a102_t1_isAdicComplete_maximalIdealHat v
  IsAdicComplete.henselianRing (lg37_completion v) (mp72a102_t1_maximalIdealHat v)

theorem mp72a102_t1_maximalIdealHat_le_ker_residueHat (v : Place K F) :
    mp72a102_t1_maximalIdealHat v ≤ RingHom.ker (lg37_residueHat v) :=
  Ideal.map_le_iff_le_comap.mpr fun s hs => by
    rw [Ideal.mem_comap, RingHom.mem_ker, lg37_residueHat_algebraMap]
    exact (IsLocalRing.residue_eq_zero_iff s).mpr hs

theorem mp72a102_t1_exists_completion_root_of_residue_root
    (v : Place K F) {p : K[X]} (hpmon : p.Monic) (hpsep : p.Separable)
    {rbar : v.ResidueField} (hrbar : Polynomial.aeval rbar p = 0) :
    ∃ α : lg37_completion v,
      Polynomial.aeval α p = 0 ∧ lg37_residueHat v α = rbar := by
  classical
  haveI _htower : IsScalarTower K v.toValuationSubring (lg37_completion v) :=
    mp72a102_t1_isScalarTower v

  obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (R := v.toValuationSubring) rbar

  have hapI : Polynomial.aeval a p ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    have h1 : IsLocalRing.residue v.toValuationSubring (Polynomial.aeval a p)
        = Polynomial.aeval rbar p := by
      rw [← ha, ← IsLocalRing.ResidueField.algebraMap_eq,
        Polynomial.aeval_algebraMap_apply]
    rw [h1, hrbar]

  have hapIhat : Polynomial.aeval
      (algebraMap v.toValuationSubring (lg37_completion v) a) p
        ∈ mp72a102_t1_maximalIdealHat v := by
    rw [Polynomial.aeval_algebraMap_apply]
    exact Ideal.mem_map_of_mem _ hapI

  have hfeval : ∀ x : lg37_completion v,
      (p.map (algebraMap K (lg37_completion v))).eval x = Polynomial.aeval x p :=
    fun x => by rw [Polynomial.eval_map, ← Polynomial.aeval_def]
  have hfderiv :
      (p.map (algebraMap K (lg37_completion v))).derivative.eval
          (algebraMap v.toValuationSubring (lg37_completion v) a)
        = Polynomial.aeval
            (algebraMap v.toValuationSubring (lg37_completion v) a)
            (Polynomial.derivative p) := by
    rw [Polynomial.derivative_map, Polynomial.eval_map, ← Polynomial.aeval_def]

  obtain ⟨u, w, huw⟩ := hpsep
  have hunit : IsUnit (Ideal.Quotient.mk (mp72a102_t1_maximalIdealHat v)
      ((p.map (algebraMap K (lg37_completion v))).derivative.eval
        (algebraMap v.toValuationSubring (lg37_completion v) a))) := by
    rw [hfderiv]
    set a₀ := algebraMap v.toValuationSubring (lg37_completion v) a
    have h1 : Polynomial.aeval a₀ u * Polynomial.aeval a₀ p
        + Polynomial.aeval a₀ w * Polynomial.aeval a₀ (Polynomial.derivative p)
        = 1 := by
      have h0 := congrArg (Polynomial.aeval (R := K) a₀) huw
      simpa only [map_add, map_mul, map_one] using h0
    have h2 := congrArg (Ideal.Quotient.mk (mp72a102_t1_maximalIdealHat v)) h1
    rw [map_add, map_mul, map_mul, map_one,
      Ideal.Quotient.eq_zero_iff_mem.mpr hapIhat, mul_zero, zero_add] at h2
    exact IsUnit.of_mul_eq_one _ ((mul_comm _ _).trans h2)

  obtain ⟨α, hαroot, hαnear⟩ :=
    (mp72a102_t1_henselianRing_completion v).is_henselian
      (p.map (algebraMap K (lg37_completion v))) (hpmon.map _)
      (algebraMap v.toValuationSubring (lg37_completion v) a)
      (by rw [hfeval]; exact hapIhat) hunit
  refine ⟨α, ?_, ?_⟩
  · rw [← hfeval]
    exact hαroot
  ·
    have h0 : lg37_residueHat v
        (α - algebraMap v.toValuationSubring (lg37_completion v) a) = 0 :=
      RingHom.mem_ker.mp (mp72a102_t1_maximalIdealHat_le_ker_residueHat v hαnear)
    have heq : lg37_residueHat v α
        = lg37_residueHat v
            (algebraMap v.toValuationSubring (lg37_completion v) a) := by
      rwa [map_sub, sub_eq_zero] at h0
    rw [heq, lg37_residueHat_algebraMap, ha]

end Engine


section FinitePlace

variable (K : Type*) [Field K]

end FinitePlace


section RatWs

end RatWs


end Mp72a102T1


end

end


end


section
section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
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
open _root_.Polynomial
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial

namespace Mp72a102T2

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.RationalFunctionField
open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField
open ModularCurve.Lg37 ModularCurve.Ldgr39Hf ModularCurve.Ldgr35Cs
open Mp72a101T2

open scoped _root_.Polynomial _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial

section ResidueCalculus

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mp72a102_t2_residueHat_algebraMap_base (v : Place K F) (c : K) :
    lg37_residueHat v (algebraMap K (lg37_completion v) c)
      = algebraMap K v.ResidueField c := by
  have h : algebraMap K (lg37_completion v) c
      = algebraMap v.toValuationSubring (lg37_completion v)
          (algebraMap K v.toValuationSubring c) := rfl
  rw [h, lg37_residueHat_algebraMap v]
  rfl

def mp72a102_t2_residueHatAlgHom (v : Place K F) :
    lg37_completion v →ₐ[K] v.ResidueField where
  toRingHom := lg37_residueHat v
  commutes' := mp72a102_t2_residueHat_algebraMap_base v

end ResidueCalculus


section Engine

variable {K : Type*} [Field K] {p : K[X]}

end Engine


section Corners

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [HasCanonicalLocalResidueKStar K E]

end Corners


section RatProduction

attribute [local instance 2000] RatFunc.instAlgebraOfPolynomial

end RatProduction


section AxiomAudit

end AxiomAudit


end Mp72a102T2


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
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsLocalRing

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq)

open _root_.AlgebraicCurve

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsIntegral F F']

namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_ne_zero adicValuation_coe_eq_one_iff adicValuation_coe_irreducible ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ord_smul ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring mk.injEq rec ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk adicValuation_valuationSubring mem_iff_adicValuation_le_one isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one isEquiv_adicValuation_ofHeightOneSpectrum ord_ofHeightOneSpectrum_ne_zero_iff dCoord DCoordGenerates dCoord_ne_zero differentialCoeff differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_dCoord differentialCoeff_zero differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg deg_restrict_mul_inertiaDeg ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq)

open _root_.AlgebraicCurve.Place

variable (w : Place K F')

scoped instance : IsLocalHom (restrictInclusion F w) where
  map_nonunit a ha := by

    have hord : w.ord (algebraMap F F' (a : F)) = 0 := by
      have h := w.ord_coe_unit ha.unit
      rwa [IsUnit.unit_spec, coe_restrictInclusion] at h

    have ha0 : (a : F) ≠ 0 := by
      rintro h0
      obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp ha
      have hb' : algebraMap F F' (a : F) * (b : F') = 1 := congrArg Subtype.val hb
      rw [h0, _root_.map_zero, zero_mul] at hb'
      exact zero_ne_one hb'
    exact (isUnit_mk_comap_iff ha0 a.2).mpr hord

end Place


namespace Divisor

export _root_.AlgebraicCurve.Divisor (degree degree_single principal smul_def smul_apply degree_smul)

open _root_.AlgebraicCurve.Divisor

end Divisor


end AlgebraicCurve


end

end


end


section
section

noncomputable section

open _root_.Module
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Module
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsLocalRing
open _root_.Module.IsLocalRing
open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.WithZero

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq)

open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_ne_zero adicValuation_coe_eq_one_iff adicValuation_coe_irreducible ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ord_smul ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring mk.injEq rec ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk adicValuation_valuationSubring mem_iff_adicValuation_le_one isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one isEquiv_adicValuation_ofHeightOneSpectrum ord_ofHeightOneSpectrum_ne_zero_iff dCoord DCoordGenerates dCoord_ne_zero differentialCoeff differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_dCoord differentialCoeff_zero differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg deg_restrict_mul_inertiaDeg ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq)

open _root_.AlgebraicCurve.Place

variable (v : Place K F)

theorem mk_mem_maximalIdeal_iff {f : F} (hf : f ∈ v.toValuationSubring) :
    (⟨f, hf⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring
      ↔ f = 0 ∨ 0 < v.ord f := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hu
    rcases eq_or_ne f 0 with rfl | hf0
    · exact Or.inl rfl
    · refine Or.inr ?_
      rcases lt_or_eq_of_le (v.ord_nonneg_of_mem hf) with h | h
      · exact h
      ·
        exfalso
        apply hu
        rw [← v.adicValuation_coe_eq_one_iff ⟨f, hf⟩]
        show v.adicValuation f = 1
        rw [v.adicValuation_eq_exp_neg_ord hf0, ← h, _root_.neg_zero, WithZero.exp_zero]
  · intro h hu
    have hne : f ≠ 0 := fun h0 => hu.ne_zero (Subtype.ext h0)
    have h0 : v.ord f = 0 := by
      obtain ⟨u, hu'⟩ := hu
      have hcoe : f = ((u : v.toValuationSubring) : F) := by rw [hu']
      rw [hcoe]; exact v.ord_coe_unit u
    rcases h with rfl | hpos
    · exact hne rfl
    · omega

end Place


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

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq)

open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_ne_zero adicValuation_coe_eq_one_iff adicValuation_coe_irreducible ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ord_smul ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring mk.injEq rec ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk adicValuation_valuationSubring mem_iff_adicValuation_le_one isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one isEquiv_adicValuation_ofHeightOneSpectrum ord_ofHeightOneSpectrum_ne_zero_iff dCoord DCoordGenerates dCoord_ne_zero differentialCoeff differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_dCoord differentialCoeff_zero differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg deg_restrict_mul_inertiaDeg ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq)

open _root_.AlgebraicCurve.Place

variable (v : Place K F)

def _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.uniformizerSubring : v.toValuationSubring :=
  (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose




-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.uniformizerSubring :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.uniformizerSubring
@[scoped simp]
theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.coe_uniformizerSubring : (v.uniformizerSubring : F) = v.uniformizer := rfl




-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.coe_uniformizerSubring :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.coe_uniformizerSubring
theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.irreducible_uniformizerSubring : Irreducible v.uniformizerSubring :=
  (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose_spec




-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.irreducible_uniformizerSubring :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.irreducible_uniformizerSubring
theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.uniformizerSubring_mem_maximalIdeal :
    v.uniformizerSubring ∈ IsLocalRing.maximalIdeal v.toValuationSubring :=
  (IsLocalRing.mem_maximalIdeal _).mpr v.irreducible_uniformizerSubring.not_isUnit




-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.uniformizerSubring_mem_maximalIdeal :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.uniformizerSubring_mem_maximalIdeal
theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.uniformizer_mem : v.uniformizer ∈ v.toValuationSubring :=
  v.uniformizerSubring.2




-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.uniformizer_mem :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.uniformizer_mem
def _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.simplePoleSubmodule : Submodule K F where
  carrier := {f | v.uniformizer * f ∈ v.toValuationSubring}
  add_mem' {f g} hf hg := by
    simpa only [Set.mem_setOf_eq, mul_add] using add_mem hf hg
  zero_mem' := by simpa only [Set.mem_setOf_eq, mul_zero] using zero_mem _
  smul_mem' c f hf := by
    show v.uniformizer * (c • f) ∈ v.toValuationSubring
    rw [Algebra.smul_def, mul_left_comm]
    exact mul_mem (v.algebraMap_mem' c) hf




-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.simplePoleSubmodule :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.simplePoleSubmodule
@[scoped simp]
theorem mem_simplePoleSubmodule {f : F} :
    f ∈ v.simplePoleSubmodule ↔ v.uniformizer * f ∈ v.toValuationSubring := Iff.rfl

theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.mem_simplePoleSubmodule_of_mem {f : F} (hf : f ∈ v.toValuationSubring) :
    f ∈ v.simplePoleSubmodule :=
  mul_mem v.uniformizer_mem hf




-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.mem_simplePoleSubmodule_of_mem :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.mem_simplePoleSubmodule_of_mem
def _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.simplePoleMulUniformizer : v.simplePoleSubmodule →ₗ[K] v.toValuationSubring where
  toFun f := ⟨v.uniformizer * f.1, f.2⟩
  map_add' f g := Subtype.ext (mul_add _ _ _)
  map_smul' c f := Subtype.ext <| by
    show v.uniformizer * ((c • f : v.simplePoleSubmodule) : F)
        = ((c • ⟨v.uniformizer * f.1, f.2⟩ : v.toValuationSubring) : F)
    simp only [Algebra.smul_def, MulMemClass.coe_mul, v.coe_algebraMap, Submodule.coe_smul,
      mul_left_comm]




-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.simplePoleMulUniformizer :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.simplePoleMulUniformizer
def _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.simplePoleResidueAux : v.simplePoleSubmodule →ₗ[K] v.ResidueField :=
  (Ideal.Quotient.mkₐ K (IsLocalRing.maximalIdeal v.toValuationSubring)).toLinearMap
    ∘ₗ v.simplePoleMulUniformizer




-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.simplePoleResidueAux :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.simplePoleResidueAux
theorem simplePoleResidueAux_apply (f : v.simplePoleSubmodule) :
    v.simplePoleResidueAux f = IsLocalRing.residue _ ⟨v.uniformizer * f.1, f.2⟩ := rfl

theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.simplePoleResidueAux_eq_zero_of_mem {f : F} (hf : f ∈ v.toValuationSubring) :
    v.simplePoleResidueAux ⟨f, v.mem_simplePoleSubmodule_of_mem hf⟩ = 0 := by
  rw [simplePoleResidueAux_apply, IsLocalRing.residue_eq_zero_iff]

  have hmul : (⟨v.uniformizer * f, mul_mem v.uniformizer_mem hf⟩ : v.toValuationSubring)
      = v.uniformizerSubring * ⟨f, hf⟩ := Subtype.ext rfl
  rw [hmul]
  exact Ideal.mul_mem_right _ _ v.uniformizerSubring_mem_maximalIdeal




-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.simplePoleResidueAux_eq_zero_of_mem :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.simplePoleResidueAux_eq_zero_of_mem
def _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.localResidueExtend : F →ₗ[K] v.ResidueField :=
  v.simplePoleResidueAux.exists_extend.choose




-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.localResidueExtend :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.localResidueExtend
theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.localResidueExtend_apply_of_mem {f : F} (hf : f ∈ v.simplePoleSubmodule) :
    v.localResidueExtend f = v.simplePoleResidueAux ⟨f, hf⟩ :=
  congrArg (fun φ => φ (⟨f, hf⟩ : v.simplePoleSubmodule))
    v.simplePoleResidueAux.exists_extend.choose_spec




-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.localResidueExtend_apply_of_mem :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.localResidueExtend_apply_of_mem
def _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.localResidueDataOfExtend : v.LocalResidueData where
  res := v.localResidueExtend
  res_of_mem f hf := by
    rw [v.localResidueExtend_apply_of_mem (v.mem_simplePoleSubmodule_of_mem hf),
      v.simplePoleResidueAux_eq_zero_of_mem hf]
  res_simplePole f hf := by
    rw [v.localResidueExtend_apply_of_mem hf, simplePoleResidueAux_apply]




-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.localResidueDataOfExtend :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.localResidueDataOfExtend
end Place


scoped instance instHasLocalResidue : HasLocalResidue K F where
  exists_data v := ⟨v.localResidueDataOfExtend⟩

variable [HasCanonicalLocalResidueKStar K F]

omit [HasCanonicalLocalResidueKStar K F] in

theorem gate_uniformizer_inv_mem_simplePoleSubmodule (v : Place K F) :
    v.uniformizer⁻¹ ∈ v.simplePoleSubmodule ∧ v.uniformizer⁻¹ ∉ v.toValuationSubring := by
  refine ⟨?_, ?_⟩
  · rw [Place.mem_simplePoleSubmodule, mul_inv_cancel₀ v.uniformizer_ne_zero]
    exact one_mem _
  · intro hmem
    have h0 := v.ord_nonneg_of_mem hmem
    rw [v.ord_inv, v.ord_uniformizer] at h0
    omega

end AlgebraicCurve


section AxiomAudit

end AxiomAudit


end


end


end


section
section

set_option maxHeartbeats 1600000

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

namespace ModularCurve

namespace MilneAvAg9bRd14CubeRowCartierSliceStart

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.RationalFunctionField
open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField

open scoped _root_.Polynomial _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial

theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve.MilneAvAg9bRd14CubeRowCartierSliceStart.ag9b14c_res_uniformizer_zpow_eq_zero_of_ne_neg_one
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (R : v.CanonicalLocalResidueDataK)
    {j : ℤ} (hj : j ≠ -1) :
    R.res (v.uniformizer ^ j) = 0 := by
  by_cases h0 : 0 ≤ j
  · refine R.res_of_mem _ (v.mem_of_ord_nonneg (zpow_ne_zero j v.uniformizer_ne_zero) ?_)
    rw [v.ord_zpow, v.ord_uniformizer, mul_one]
    exact h0
  · have hn1 : 1 ≤ (-j - 1).toNat := by omega
    have hjn : j = -(((-j - 1).toNat + 1 : ℕ) : ℤ) := by omega
    rw [hjn, _root_.zpow_neg, zpow_natCast]
    exact R.res_higherPoleMonomial _ hn1




-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.ModularCurve.MilneAvAg9bRd14CubeRowCartierSliceStart.ag9b14c_res_uniformizer_zpow_eq_zero_of_ne_neg_one :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve.MilneAvAg9bRd14CubeRowCartierSliceStart.ag9b14c_res_uniformizer_zpow_eq_zero_of_ne_neg_one
end MilneAvAg9bRd14CubeRowCartierSliceStart


end ModularCurve


end


end


end

end P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed
