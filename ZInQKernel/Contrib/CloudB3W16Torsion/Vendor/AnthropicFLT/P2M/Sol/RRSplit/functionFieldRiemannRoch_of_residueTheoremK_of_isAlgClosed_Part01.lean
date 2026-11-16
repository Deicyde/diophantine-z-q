/-
Copyright 2026 Anthropic, PBC. Released under Apache License 2.0.
Source: https://github.com/anthropics/fermats-last-theorem
Revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.lean; source lines 1-1352.
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
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorPushPull
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlacesOverDVR
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RatFuncPlaces
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_CanonicalDivisor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_CanonicalDivisorUniformizer
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CanonicalDivisor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_LocalResidue
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RiemannRochRows
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 6400000
set_option maxHeartbeats 12800000

namespace P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 6400000
set_option maxHeartbeats 12800000

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic)

open _root_.AlgebraicCurve
end AlgebraicCurve
namespace Classical

export _root_.Classical (choose_spec by_cases choose not_not not_forall)

open _root_.Classical
end Classical
namespace CongruenceSubgroup
open _root_.CongruenceSubgroup
end CongruenceSubgroup
namespace IntermediateField

export _root_.IntermediateField (toAlgebra inclusion_injective map_le_iff_le_comap mk val isIntegral_iff topEquiv_apply lift inclusion ext bot_eq_top_iff_finrank_eq_one equivOfEq algebraMap_apply smul_def adjoin mem_inf mk.injEq comap topEquiv mem_top adjoinRootEquivAdjoin restrictScalars rec adjoinRootEquivAdjoin_apply_root coe_smul AdjoinSimple.coe_gen map_sup mem_bot mem_map smul_mem restrict map)

open _root_.IntermediateField
end IntermediateField
namespace IsDedekindDomain

export _root_.IsDedekindDomain (mem_primesOverFinset_iff HeightOneSpectrum.valuationSubringAtPrime HeightOneSpectrum.valuation_of_algebraMap HeightOneSpectrum.intValuation_le_pow_iff_mem HeightOneSpectrum.asIdeal rec HeightOneSpectrum.intValuation_ne_zero HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring HeightOneSpectrum.ext mk HeightOneSpectrum)

open _root_.IsDedekindDomain
end IsDedekindDomain
namespace IsLocalRing

export _root_.IsLocalRing (rec ResidueField maximalIdeal residue_eq_zero_iff mem_maximalIdeal ResidueField.mapEquiv residue_surjective residue_ne_zero_iff_isUnit of_injective ResidueField.algebraMap_eq residue)

open _root_.IsLocalRing
end IsLocalRing
namespace KaehlerDifferential

export _root_.KaehlerDifferential (D map)

open _root_.KaehlerDifferential
end KaehlerDifferential
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

export _root_.Module (Finite.of_finite finrank_zero_of_subsingleton Injective support Basis.span equiv Finite.equiv rec finrank_eq_card_basis finrank mk Dual finrank_self Finite.of_injective restrictScalars finrank_zero_iff Basis.span_apply Finite.of_submodule_quotient finrank_pos finrank_prod mem_support_iff Basis)

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

export _root_.Polynomial (C X support derivative_map aeval_def leadingCoeff algebraMap_eq aeval basisMonomials ext_iff degree mapEquiv factor toSubring map degree_C Monic comp natDegree_X_pow coe_mul algHom_ext sum coe_smul Separable leadingCoeff_C natDegree transcendental_X X_ne_zero rec coe_zero natDegree_lt_natDegree leadingCoeff_mul mem_support_iff coe_add derivative degree_sub_lt algebraMap_apply coe_basisMonomials eval_map ext degree_eq_natDegree funext isUnit_iff ring degree_mul aeval_algebraMap_apply leadingCoeff_ne_zero eval monomial_one_right_eq_X_pow)

open _root_.Polynomial
end Polynomial
namespace RationalFunctionField
end RationalFunctionField
namespace WithZero

export _root_.WithZero (coe_add map coe_mul exp_lt_exp log_exp map' exp_ne_zero log exp exp_zero log_mul lift exp_le_exp exp_log)

open _root_.WithZero
end WithZero

section
section

noncomputable section

open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsLocalRing

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic)

open _root_.AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_coe_eq_one_iff ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ofHeightOneSpectrum mk.injEq rec ne_top' algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict mem_restrict_iff ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg fiber mem_fiber mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one DCoordGenerates differentialCoeff ordDifferential uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero)

open _root_.AlgebraicCurve.Place

variable {K F}

variable (v : Place K F)

end Place

namespace Divisor

export _root_.AlgebraicCurve.Divisor (degree degree_single principal smul_def smul_apply pullback pullback_apply degree_pullback)

open _root_.AlgebraicCurve.Divisor

variable {K F}

end Divisor

namespace Pic0

export _root_.AlgebraicCurve.Pic0 (mk mk_surjective)

open _root_.AlgebraicCurve.Pic0

variable {K F}

end Pic0

namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_coe_eq_one_iff ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ofHeightOneSpectrum mk.injEq rec ne_top' algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict mem_restrict_iff ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg fiber mem_fiber mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one DCoordGenerates differentialCoeff ordDifferential uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero)

open _root_.AlgebraicCurve.Place

open scoped Pointwise P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Pointwise

variable {K F}
variable (σ : F ≃ₐ[K] F)

variable (v : Place K F)

end Place

namespace Divisor

export _root_.AlgebraicCurve.Divisor (degree degree_single principal smul_def smul_apply pullback pullback_apply degree_pullback)

open _root_.AlgebraicCurve.Divisor

open scoped Pointwise P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Pointwise

variable {K F}

end Divisor

namespace Pic0

export _root_.AlgebraicCurve.Pic0 (mk mk_surjective)

open _root_.AlgebraicCurve.Pic0

open scoped Pointwise P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Pointwise

variable {K F}

end Pic0

namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_coe_eq_one_iff ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ofHeightOneSpectrum mk.injEq rec ne_top' algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict mem_restrict_iff ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg fiber mem_fiber mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one DCoordGenerates differentialCoeff ordDifferential uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero)

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

noncomputable section

open _root_.KaehlerDifferential
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.KaehlerDifferential

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic)

open _root_.AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

namespace IsCurveOver

export _root_.AlgebraicCurve.IsCurveOver (finite_residueField deg_eq_one_of_isAlgClosed mk rec)

open _root_.AlgebraicCurve.IsCurveOver

variable {K F}

end IsCurveOver

namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_coe_eq_one_iff ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ofHeightOneSpectrum mk.injEq rec ne_top' algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict mem_restrict_iff ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg fiber mem_fiber mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one DCoordGenerates differentialCoeff ordDifferential uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero)

open _root_.AlgebraicCurve.Place

variable {K F}
variable (v : Place K F)

end Place

variable {K F}

variable (K F)

end AlgebraicCurve

namespace ModularCurve

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve

end ModularCurve

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic)

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
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
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
namespace ModularCurve
namespace Lg37
open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve
open ModularCurve.Ldgr36Si
open ModularCurve.Ldgr36Rc
open ModularCurve.Ldgr35Cs
section CompletionCarrier
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

abbrev lg37_completion (v : Place K F) : Type _ :=
  AdicCompletion (IsLocalRing.maximalIdeal v.toValuationSubring) v.toValuationSubring
end CompletionCarrier
end ModularCurve.Lg37
end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
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
namespace ModularCurve
namespace Lg37
open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve
open ModularCurve.Ldgr36Si
open ModularCurve.Ldgr36Rc
open ModularCurve.Ldgr35Cs
section CompletionCarrier
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

def lg37_residueHat (v : Place K F) :
    lg37_completion v →+* v.ResidueField :=
  (AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal v.toValuationSubring)).toRingHom
end CompletionCarrier
end ModularCurve.Lg37
end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
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
namespace ModularCurve
namespace Lg37
open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve
open ModularCurve.Ldgr36Si
open ModularCurve.Ldgr36Rc
open ModularCurve.Ldgr35Cs
section CompletionCarrier
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem lg37_residueHat_algebraMap (v : Place K F) (x : v.toValuationSubring) :
    lg37_residueHat v
        (algebraMap v.toValuationSubring (lg37_completion v) x)
      = IsLocalRing.residue v.toValuationSubring x := rfl
end CompletionCarrier
end ModularCurve.Lg37
end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
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
namespace ModularCurve
namespace Lg37
open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve
open ModularCurve.Ldgr36Si
open ModularCurve.Ldgr36Rc
open ModularCurve.Ldgr35Cs
section CompletionCarrier
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

structure Lg37CompletionSection (v : Place K F) where

  lift : v.ResidueField →ₐ[K] lg37_completion v

  residueHat_lift : ∀ a, lg37_residueHat v (lift a) = a
end CompletionCarrier
end ModularCurve.Lg37
end

end

end

section
section

noncomputable section

open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsLocalRing

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic)

open _root_.AlgebraicCurve

namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_coe_eq_one_iff ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ofHeightOneSpectrum mk.injEq rec ne_top' algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict mem_restrict_iff ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg fiber mem_fiber mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one DCoordGenerates differentialCoeff ordDifferential uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero)

open _root_.AlgebraicCurve.Place

section SinglePlace

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.ord_nonneg_of_mem {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
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




theorem _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.mem_of_ord_nonneg {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)




theorem _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.mem_iff_ord_nonneg {f : F} (hf : f ≠ 0) :
    f ∈ v.toValuationSubring ↔ 0 ≤ v.ord f :=
  ⟨v.ord_nonneg_of_mem, v.mem_of_ord_nonneg hf⟩




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

theorem algebraMap_ne_zero {f : F} (hf : f ≠ 0) : algebraMap F F' f ≠ 0 := by
  simpa using hf

variable (w : Place K F')

theorem _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.comap_algebraMap_ne_top [Algebra.IsIntegral F F'] :
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

theorem _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.exists_ord_algebraMap_pos [Algebra.IsIntegral F F'] :
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
set_option autoImplicit false
noncomputable section
namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic)

open _root_.AlgebraicCurve
namespace Divisor

export _root_.AlgebraicCurve.Divisor (degree degree_single principal smul_def smul_apply pullback pullback_apply degree_pullback)

open _root_.AlgebraicCurve.Divisor
section Pullback
variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsIntegral F F']

theorem degree_eq_sum_support (D : Divisor K F) :
    degree D = ∑ v ∈ D.support, D v * (v.deg : ℤ) := by
  rw [degree, Finsupp.liftAddHom_apply, Finsupp.sum]
  rfl
end Pullback
end Divisor
end AlgebraicCurve
end

end

end

section
section

noncomputable section

open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsLocalRing
open scoped Polynomial P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Polynomial

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic)

open _root_.AlgebraicCurve

namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_coe_eq_one_iff ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ofHeightOneSpectrum mk.injEq rec ne_top' algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict mem_restrict_iff ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg fiber mem_fiber mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one DCoordGenerates differentialCoeff ordDifferential uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero)

open _root_.AlgebraicCurve.Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

section OfHeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
  [Algebra K R] [IsScalarTower K R F]

end OfHeightOneSpectrum

end Place

namespace RationalFunctionField

export _root_.AlgebraicCurve.RationalFunctionField (algebraMap_mem_ofHeightOneSpectrum)

open _root_.AlgebraicCurve.RationalFunctionField

variable (K : Type*) [Field K]

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
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero
open _root_.Module
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsLocalRing
open _root_.Module.IsLocalRing

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic)

open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_coe_eq_one_iff ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ofHeightOneSpectrum mk.injEq rec ne_top' algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict mem_restrict_iff ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg fiber mem_fiber mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one DCoordGenerates differentialCoeff ordDifferential uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero)

open _root_.AlgebraicCurve.Place

variable (v : Place K F)

def _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.uniformizerSubring : v.toValuationSubring :=
  (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose




@[scoped simp]
theorem _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.coe_uniformizerSubring : (v.uniformizerSubring : F) = v.uniformizer := rfl




theorem _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.irreducible_uniformizerSubring : Irreducible v.uniformizerSubring :=
  (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose_spec




theorem _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.uniformizerSubring_mem_maximalIdeal :
    v.uniformizerSubring ∈ IsLocalRing.maximalIdeal v.toValuationSubring :=
  (IsLocalRing.mem_maximalIdeal _).mpr v.irreducible_uniformizerSubring.not_isUnit




theorem _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.uniformizer_mem : v.uniformizer ∈ v.toValuationSubring :=
  v.uniformizerSubring.2




def _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.simplePoleSubmodule : Submodule K F where
  carrier := {f | v.uniformizer * f ∈ v.toValuationSubring}
  add_mem' {f g} hf hg := by
    simpa only [Set.mem_setOf_eq, mul_add] using add_mem hf hg
  zero_mem' := by simpa only [Set.mem_setOf_eq, mul_zero] using zero_mem _
  smul_mem' c f hf := by
    show v.uniformizer * (c • f) ∈ v.toValuationSubring
    rw [Algebra.smul_def, mul_left_comm]
    exact mul_mem (v.algebraMap_mem' c) hf




@[scoped simp]
theorem mem_simplePoleSubmodule {f : F} :
    f ∈ v.simplePoleSubmodule ↔ v.uniformizer * f ∈ v.toValuationSubring := Iff.rfl

theorem _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.mem_simplePoleSubmodule_of_mem {f : F} (hf : f ∈ v.toValuationSubring) :
    f ∈ v.simplePoleSubmodule :=
  mul_mem v.uniformizer_mem hf




def _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.simplePoleMulUniformizer : v.simplePoleSubmodule →ₗ[K] v.toValuationSubring where
  toFun f := ⟨v.uniformizer * f.1, f.2⟩
  map_add' f g := Subtype.ext (mul_add _ _ _)
  map_smul' c f := Subtype.ext <| by
    show v.uniformizer * ((c • f : v.simplePoleSubmodule) : F)
        = ((c • ⟨v.uniformizer * f.1, f.2⟩ : v.toValuationSubring) : F)
    simp only [Algebra.smul_def, MulMemClass.coe_mul, v.coe_algebraMap, Submodule.coe_smul,
      mul_left_comm]




def _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.simplePoleResidueAux : v.simplePoleSubmodule →ₗ[K] v.ResidueField :=
  (Ideal.Quotient.mkₐ K (IsLocalRing.maximalIdeal v.toValuationSubring)).toLinearMap
    ∘ₗ v.simplePoleMulUniformizer




theorem simplePoleResidueAux_apply (f : v.simplePoleSubmodule) :
    v.simplePoleResidueAux f = IsLocalRing.residue _ ⟨v.uniformizer * f.1, f.2⟩ := rfl

theorem _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.simplePoleResidueAux_eq_zero_of_mem {f : F} (hf : f ∈ v.toValuationSubring) :
    v.simplePoleResidueAux ⟨f, v.mem_simplePoleSubmodule_of_mem hf⟩ = 0 := by
  rw [simplePoleResidueAux_apply, IsLocalRing.residue_eq_zero_iff]

  have hmul : (⟨v.uniformizer * f, mul_mem v.uniformizer_mem hf⟩ : v.toValuationSubring)
      = v.uniformizerSubring * ⟨f, hf⟩ := Subtype.ext rfl
  rw [hmul]
  exact Ideal.mul_mem_right _ _ v.uniformizerSubring_mem_maximalIdeal




def _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.localResidueExtend : F →ₗ[K] v.ResidueField :=
  v.simplePoleResidueAux.exists_extend.choose




theorem _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.localResidueExtend_apply_of_mem {f : F} (hf : f ∈ v.simplePoleSubmodule) :
    v.localResidueExtend f = v.simplePoleResidueAux ⟨f, hf⟩ :=
  congrArg (fun φ => φ (⟨f, hf⟩ : v.simplePoleSubmodule))
    v.simplePoleResidueAux.exists_extend.choose_spec




end Place


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
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero
open _root_.Module
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsLocalRing
open _root_.Module.IsLocalRing
open _root_.Polynomial
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Polynomial

namespace Mp72a102T1

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.RationalFunctionField
open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField
open ModularCurve.Lg37 ModularCurve.Ldgr37Ch
open Mp72a101T2

open scoped Polynomial P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Polynomial

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
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
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
open _root_.Polynomial
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Polynomial
namespace Mp72a102T2
open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.RationalFunctionField
open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField
open ModularCurve.Lg37 ModularCurve.Ldgr39Hf ModularCurve.Ldgr35Cs
open Mp72a101T2
open scoped Polynomial P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Polynomial
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
end ResidueCalculus

end Mp72a102T2

end


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
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
open _root_.Polynomial
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Polynomial
namespace Mp72a102T2
open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.RationalFunctionField
open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField
open ModularCurve.Lg37 ModularCurve.Ldgr39Hf ModularCurve.Ldgr35Cs
open Mp72a101T2
open scoped Polynomial P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Polynomial
section ResidueCalculus
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

def mp72a102_t2_residueHatAlgHom (v : Place K F) :
    lg37_completion v →ₐ[K] v.ResidueField where
  toRingHom := lg37_residueHat v
  commutes' := mp72a102_t2_residueHat_algebraMap_base v
end ResidueCalculus

end Mp72a102T2

end


end


end


section
section

noncomputable section

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic)

open _root_.AlgebraicCurve

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsIntegral F F'] [HasPrincipalDivisors K F']

namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_coe_eq_one_iff ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ofHeightOneSpectrum mk.injEq rec ne_top' algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict mem_restrict_iff ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg fiber mem_fiber mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one DCoordGenerates differentialCoeff ordDifferential uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero)

open _root_.AlgebraicCurve.Place

end Place


namespace Divisor

export _root_.AlgebraicCurve.Divisor (degree degree_single principal smul_def smul_apply pullback pullback_apply degree_pullback)

open _root_.AlgebraicCurve.Divisor

end Divisor


namespace Divisor

export _root_.AlgebraicCurve.Divisor (degree degree_single principal smul_def smul_apply pullback pullback_apply degree_pullback)

open _root_.AlgebraicCurve.Divisor

end Divisor


end AlgebraicCurve


end

end


end


section
section
set_option autoImplicit false
noncomputable section
open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsLocalRing
namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic)

open _root_.AlgebraicCurve
variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsIntegral F F']
namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_coe_eq_one_iff ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ofHeightOneSpectrum mk.injEq rec ne_top' algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict mem_restrict_iff ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg fiber mem_fiber mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one DCoordGenerates differentialCoeff ordDifferential uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero)

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
      rw [h0, map_zero, zero_mul] at hb'
      exact zero_ne_one hb'
    exact (isUnit_mk_comap_iff ha0 a.2).mpr hord
end Place

end AlgebraicCurve

end


end


end


section
section

noncomputable section

open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsLocalRing

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic)

open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_coe_eq_one_iff ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ofHeightOneSpectrum mk.injEq rec ne_top' algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict mem_restrict_iff ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg fiber mem_fiber mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one DCoordGenerates differentialCoeff ordDifferential uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero)

open _root_.AlgebraicCurve.Place

variable (v : Place K F)

theorem _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.isUnit_mk_of_ord_eq_zero {f : F} (hf : f ≠ 0) (h : v.ord f = 0) :
    IsUnit (⟨f, v.mem_of_ord_nonneg hf h.ge⟩ : v.toValuationSubring) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [h, zpow_zero, mul_one] at hu
  have huf : (⟨f, v.mem_of_ord_nonneg hf h.ge⟩ : v.toValuationSubring)
      = (u : v.toValuationSubring) := Subtype.ext hu
  rw [huf]
  exact u.isUnit




theorem _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.residue_ne_zero_of_ord_eq_zero {f : F} (hf : f ≠ 0) (h : v.ord f = 0) :
    residue v.toValuationSubring (⟨f, v.mem_of_ord_nonneg hf h.ge⟩ : v.toValuationSubring)
      ≠ 0 :=
  (residue_ne_zero_iff_isUnit _).mpr (v.isUnit_mk_of_ord_eq_zero hf h)




def _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.IsRational : Prop := Function.Surjective (algebraMap K v.ResidueField)




def _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.residueInv : v.ResidueField → K :=
  Function.invFun (algebraMap K v.ResidueField)




theorem _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.algebraMap_residueInv (hv : v.IsRational) (x : v.ResidueField) :
    algebraMap K v.ResidueField (v.residueInv x) = x :=
  Function.invFun_eq (hv x)




open _root_.Classical _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Classical in

def _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.evalAt (f : F) : K :=
  if hf : f ∈ v.toValuationSubring then
    v.residueInv (residue v.toValuationSubring ⟨f, hf⟩)
  else 0




theorem _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.evalAt_of_mem {f : F} (hf : f ∈ v.toValuationSubring) :
    v.evalAt f = v.residueInv (residue v.toValuationSubring ⟨f, hf⟩) :=
  dif_pos hf




theorem _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.algebraMap_evalAt (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) :
    algebraMap K v.ResidueField (v.evalAt f)
      = residue v.toValuationSubring (⟨f, hf⟩ : v.toValuationSubring) := by
  rw [v.evalAt_of_mem hf]
  exact v.algebraMap_residueInv hv _




theorem _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.evalAt_ne_zero (hv : v.IsRational) {f : F} (hf : f ≠ 0) (h : v.ord f = 0) :
    v.evalAt f ≠ 0 := by
  intro h0
  have hres := v.algebraMap_evalAt hv (v.mem_of_ord_nonneg hf h.ge)
  rw [h0, _root_.map_zero] at hres
  exact v.residue_ne_zero_of_ord_eq_zero hf h hres.symm




end Place


namespace Divisor

export _root_.AlgebraicCurve.Divisor (degree degree_single principal smul_def smul_apply pullback pullback_apply degree_pullback)

open _root_.AlgebraicCurve.Divisor

end Divisor


namespace WeilDatum

end WeilDatum


end AlgebraicCurve


end

end


end


section
section
set_option autoImplicit false
noncomputable section
open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero
open _root_.CongruenceSubgroup
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.CongruenceSubgroup
namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic)

open _root_.AlgebraicCurve
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {D E : Divisor K F}

namespace Divisor
export _root_.AlgebraicCurve.Divisor (degree degree_single principal smul_def smul_apply pullback pullback_apply degree_pullback)
end Divisor
open scoped AlgebraicCurve.Divisor in
theorem Divisor.degree_nonneg_of_nonneg [IsCurveOver K F]
    {D : Divisor K F} (hD : ∀ v, 0 ≤ D v) : 0 ≤ Divisor.degree D := by
  rw [Divisor.degree_eq_sum_support]
  exact Finset.sum_nonneg fun v _ => mul_nonneg (hD v) (Int.natCast_nonneg _)
end AlgebraicCurve

end


set_option autoImplicit false
noncomputable section
open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero
open _root_.CongruenceSubgroup
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.CongruenceSubgroup
namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic)

open _root_.AlgebraicCurve
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {D E : Divisor K F}

theorem lSpace_eq_bot_of_degree_neg [IsCurveOver K F]
    (hD : Divisor.degree D < 0) : LSpace D = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  rw [Submodule.mem_bot]
  by_contra hf0
  obtain ⟨P, hPord, hPdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0

  have heff : ∀ v : Place K F, 0 ≤ (P + D) v := by
    intro v
    rw [Finsupp.add_apply, hPord]
    rcases mem_lSpace_iff_ord.mp hf with rfl | h
    · exact absurd rfl hf0
    · linarith [h v]
  have hdegPD : 0 ≤ Divisor.degree (P + D) := Divisor.degree_nonneg_of_nonneg heff
  rw [map_add, hPdeg, zero_add] at hdegPD
  exact absurd hdegPD (not_le.mpr hD)
end AlgebraicCurve

end


set_option autoImplicit false
noncomputable section
open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero
open _root_.CongruenceSubgroup
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.CongruenceSubgroup
namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic)

open _root_.AlgebraicCurve
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {D E : Divisor K F}
theorem ell_eq_zero_of_degree_neg [IsCurveOver K F] (hD : Divisor.degree D < 0) :
    ell D = 0 := by
  rw [ell, lSpace_eq_bot_of_degree_neg hD, finrank_bot]
end AlgebraicCurve

end


end


end

end P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed
