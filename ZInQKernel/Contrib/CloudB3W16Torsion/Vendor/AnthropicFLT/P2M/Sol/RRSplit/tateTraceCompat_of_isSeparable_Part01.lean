/-
Copyright 2026 Anthropic, PBC. Released under Apache License 2.0.
Source: https://github.com/anthropics/fermats-last-theorem
Revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_AlgebraicCurve_tateTraceCompat_of_isSeparable.lean; source lines 1-2340.
Includes FLT/Mathlib/RingTheory/LocalRing/MaximalIdeal/Basic.lean material:
Copyright (c) 2025 Salvatore Mercuri. Authors: Salvatore Mercuri, Kevin Buzzard.
Includes FLT/Mathlib/RingTheory/Valuation/ValuationSubring.lean material:
Copyright (c) 2025 Ruben Van de Velde.
Authors: Ruben Van de Velde, Kevin Buzzard, Salvatore Mercuri.
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
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_DedekindDomain_AdicValuation_InlineSpecific
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlaceCompletion
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_TateResidueCurrency
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 6400000
set_option maxHeartbeats 12800000

namespace P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 6400000
set_option maxHeartbeats 12800000

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Divisor HasPrincipalDivisors Pic0 IsCurveOver HasCanonicalLocalResidueKStar Place.mem_restrict_iff Place.mem_fiber Place.restrict_mem_fiber kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_completionTraceAt)

open _root_.AlgebraicCurve
end AlgebraicCurve
namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Divisor HasPrincipalDivisors Pic0 IsCurveOver HasCanonicalLocalResidueKStar Place.mem_restrict_iff Place.mem_fiber Place.restrict_mem_fiber kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_completionTraceAt)

namespace KwBwnmchRFTDCDischarge
open _root_.AlgebraicCurve
end AlgebraicCurve.KwBwnmchRFTDCDischarge
namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Divisor HasPrincipalDivisors Pic0 IsCurveOver HasCanonicalLocalResidueKStar Place.mem_restrict_iff Place.mem_fiber Place.restrict_mem_fiber kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_completionTraceAt)

namespace Place

export _root_.AlgebraicCurve.Place (ext ResidueField FiniteResidue heightOneSpectrum heightOneSpectrum_asIdeal ord ord_one ord_mul ord_inv ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring mk uniformizer ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict mem_restrict_iff fiber mem_fiber restrict_mem_fiber adicCompletion adicCompletionIntegers kw_ffgc_adicCompletionComap kw_ffgc_valued_adicCompletionComap kw_ffgc_adicCompletionComapIntegers kw_ffgc_algebraAdicCompletionComap kw_ffgc_algebraMap_adicCompletionComap_eq kw_ffgc_rankOne_adicCompletion kw_ffgc_absoluteValue kw_ffgc_adicCompletionComap_algebraMap_algebraMap kw_ffgc_completionLinearCombination kw_ffgc_denseRange_completionLinearCombination kw_ffgc_completionTraceF')

open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve
end AlgebraicCurve.Place
namespace FLT
namespace Gapsw7X3xCrossPlaceTraceDecomposition
end FLT.Gapsw7X3xCrossPlaceTraceDecomposition
namespace Filter

export _root_.Filter (mem_bot ker mk pi mem_comap map_top mem_ker mem_top comap unique map_mono map)

open _root_.Filter
end Filter
namespace IsDedekindDomain

export _root_.IsDedekindDomain (HeightOneSpectrum.adicCompletionIntegers HeightOneSpectrum.adicCompletionIntegers.integers HeightOneSpectrum.ext mk HeightOneSpectrum)

open _root_.IsDedekindDomain
end IsDedekindDomain
namespace IsDedekindDomain

export _root_.IsDedekindDomain (HeightOneSpectrum.adicCompletionIntegers HeightOneSpectrum.adicCompletionIntegers.integers HeightOneSpectrum.ext mk HeightOneSpectrum)

namespace HeightOneSpectrum

export _root_.IsDedekindDomain.HeightOneSpectrum (valuation_of_algebraMap intValuation_le_pow_iff_mem isMaximal mk comap valuedAdicCompletion_eq_valuation' adicCompletion valuation adicCompletionIntegers valuedAdicCompletion_surjective adicCompletionIntegers.integers mem_integers_of_valuation_le_one denseRange_algebraMap intValuation completionIdeal adicCompletion.mem_completionIdeal_pow)

open _root_.IsDedekindDomain.HeightOneSpectrum
open _root_.IsDedekindDomain
end IsDedekindDomain.HeightOneSpectrum
namespace IsLocalRing

export _root_.IsLocalRing (ResidueField maximalIdeal maximalIdeal.isMaximal of_injective)

open _root_.IsLocalRing
end IsLocalRing
namespace KaehlerDifferential

export _root_.KaehlerDifferential (finite D map)

open _root_.KaehlerDifferential
end KaehlerDifferential
namespace LinearMap

export _root_.LinearMap (mulLeft_apply single_apply toMatrix mem_range range sub_apply coe_range rank add_apply trace_eq_matrix_trace ker_eq_bot range_zero restrictScalars_apply id sum_apply range_comp codRestrict zero_apply smul_apply mulLeft ker_comp trace_comp_comm' mk coe_coe id_apply pi proj ext comp isIntegral trace quotKerEquivRange finiteDimensional range_comp_le_range single comp_assoc restrictScalars ker proj_apply mem_ker comp_apply toMatrix_mulVec_repr mem_range_self restrict pi_apply)

open _root_.LinearMap
end LinearMap
namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateTraceCompat)

namespace KwF4R1V384a
open _root_.ModularCurve
end ModularCurve.KwF4R1V384a
namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateTraceCompat)

namespace KwF4R1V386a
open _root_.ModularCurve
end ModularCurve.KwF4R1V386a
namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateTraceCompat)

namespace KwF4R1V410a
open _root_.ModularCurve
end ModularCurve.KwF4R1V410a
namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateTraceCompat)

namespace KwF4gRRTate

export _root_.ModularCurve.KwF4gRRTate (finrankTrace tateComm tateComm_apply tateCommRestrict tateCommRestrict_apply tateCommTrace tateComm_eq_of_commute adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateTraceCompat)

open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve
end ModularCurve.KwF4gRRTate
namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateTraceCompat)

namespace GF24a9RRDx
open _root_.ModularCurve
end ModularCurve.GF24a9RRDx
namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateTraceCompat)

namespace Lg37
open _root_.ModularCurve
end ModularCurve.Lg37
namespace Module

export _root_.Module (Basis.repr_reindex_apply Injective Free.chooseBasis Free.ChooseBasisIndex isTorsionFree_iff_algebraMap_injective Basis.localizationLocalization_apply equiv Finite.equiv finrank Free mk IsTorsionFree free_of_finite_type_torsion_free' restrictScalars Basis.equivFun_apply IsNoetherian.finite Finite.of_submodule_quotient finBasis Basis.localizationLocalization_repr_algebraMap finrank_eq_card_chooseBasisIndex Basis.reindex_apply Basis)

open _root_.Module
end Module
namespace MonoidWithZeroHom

export _root_.MonoidWithZeroHom (id_apply id ext mk coe_coe coe_one comp_apply comp_assoc comp)

open _root_.MonoidWithZeroHom
end MonoidWithZeroHom
namespace Multiplicative

export _root_.Multiplicative (ext smul)

open _root_.Multiplicative
end Multiplicative
namespace NNReal

export _root_.NNReal (pi rpow_le_one rpow_natCast smul_def coe_pow coe_one rpow_mul coe_eq_zero rpow_one coe_nonneg)

open _root_.NNReal
end NNReal
namespace NumberField

export _root_.NumberField (mk)

open _root_.NumberField
end NumberField
namespace Pointwise
open _root_.Pointwise
end Pointwise
namespace Polynomial

export _root_.Polynomial (X coe_one aeval_map_algebraMap aeval_def algebraMap_eq unique aeval ext_iff toSubring coe_pow isLocalization map lifts_and_degree_eq_and_monic comp_assoc Monic comp coe_mul coe_sub Separable lifts_iff_coeff_lifts algebraMap_apply ext funext ring aeval_algHom_apply lifts Separable.map)

open _root_.Polynomial
end Polynomial
namespace Submodule

export _root_.Submodule (quotEquivOfEq inclusion mem_sup_right map_top smul_mem' mk smul_mem mem_bot coe_mem Quotient.mk span restrictScalars projectionOnto_apply_left restrictScalars_top mem_closure_iff Quotient.restrictScalarsEquiv mem_comap injective_subtype mem_top Quotient.equiv mem_span_singleton mkQ map_mono map_smul' equivMapOfInjective zero quotientQuotientEquivQuotient coe_eq_zero range_subtype Quotient.mk_surjective restrictScalars_mono map mem_inf inclusion_apply Quotient.mk_eq_zero exists_isCompl projectionOnto finiteDimensional_of_le closure_eq topEquiv smul_def mk_eq_zero restrictScalarsEquiv closed_of_finiteDimensional mkQ_apply pi ext subtype_apply ker_mkQ add comap finiteDimensional_sup liftQ mem_sup_left smul restrictScalars_mem)

open _root_.Submodule
end Submodule
namespace TensorProduct

export _root_.TensorProduct (congr lift mk ext tmul map Algebra.smul_def mk_surjective)

open _root_.TensorProduct
end TensorProduct
namespace Topology
open _root_.Topology
end Topology
namespace Valuation

export _root_.Valuation (norm_add_le map_add' valuationSubring ext mem_valuationSubring_iff map_sub map Integers.isIntegrallyClosed Integers IsRankOneDiscrete congr RankOne.hom restrict_le_iff coe_coe restrict norm_def comap restrict_eq_zero_iff mk map_sub_swap norm_nonneg RankOne isOpen_closedBall)

open _root_.Valuation
end Valuation
namespace Valuation

export _root_.Valuation (norm_add_le map_add' valuationSubring ext mem_valuationSubring_iff map_sub map Integers.isIntegrallyClosed Integers IsRankOneDiscrete congr RankOne.hom restrict_le_iff coe_coe restrict norm_def comap restrict_eq_zero_iff mk map_sub_swap norm_nonneg RankOne isOpen_closedBall)

namespace IsRankOneDiscrete

export _root_.Valuation.IsRankOneDiscrete (valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective mk)

open _root_.Valuation.IsRankOneDiscrete
open _root_.Valuation
end Valuation.IsRankOneDiscrete
namespace Valued

export _root_.Valued (mk toNormedField.norm_def v toNontriviallyNormedField toNormedField.norm_le_one_iff isOpen_closedBall toNormedField ResidueField maximalIdeal)

open _root_.Valued
end Valued
namespace WithZero

export _root_.WithZero (coe_one map coe_mul exp_eq_coe_ofAdd coe exp_ne_zero exp exp_zero lift coe_pow le exp_le_exp)

open _root_.WithZero
end WithZero
namespace WithZeroMulInt

export _root_.WithZeroMulInt (toNNReal)

open _root_.WithZeroMulInt
end WithZeroMulInt

section
namespace IsLocalRing
export _root_.IsLocalRing (ResidueField maximalIdeal maximalIdeal.isMaximal of_injective)
end IsLocalRing
open scoped _root_.IsLocalRing in
theorem IsLocalRing.maximalIdeal_le {R : Type*} [CommSemiring R] [IsLocalRing R] {J : Ideal R}
    (hJ : J ≠ ⊤) (h : IsLocalRing.maximalIdeal R ≤ J) :
    J.IsMaximal :=
  (IsLocalRing.maximalIdeal.isMaximal R).eq_of_le hJ h ▸ IsLocalRing.maximalIdeal.isMaximal R

scoped instance instAlgebraSubtypeMemValuationSubring_fLT {K L : Type*} [Field K] [Semiring L]
    (O : ValuationSubring K) [Algebra K L] : Algebra O L where
  smul r x := r.1 • x
  algebraMap := (algebraMap K L).comp (algebraMap O K)
  commutes' _ _ := by simp [Algebra.commutes]
  smul_def' _ _ := by simp [← Algebra.smul_def]; rfl
end

section
section

set_option maxHeartbeats 6400000
set_option linter.unusedSectionVars false

open _root_.LinearMap
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.LinearMap
open _root_.Submodule
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.Submodule

noncomputable section

namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateTraceCompat)

namespace KwF4gRRTate

export _root_.ModularCurve.KwF4gRRTate (finrankTrace tateComm tateComm_apply tateCommRestrict tateCommRestrict_apply tateCommTrace tateComm_eq_of_commute adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateTraceCompat)

open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve

section FinrankTrace

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

end FinrankTrace

section TateComm

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

end TateComm

section TateFactoring

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

end TateFactoring

end ModularCurve.KwF4gRRTate

end

end

end

section
section

noncomputable section

open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.WithZero
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.IsLocalRing

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Divisor HasPrincipalDivisors Pic0 IsCurveOver HasCanonicalLocalResidueKStar Place.mem_restrict_iff Place.mem_fiber Place.restrict_mem_fiber kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_completionTraceAt)

open _root_.AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

namespace Place

export _root_.AlgebraicCurve.Place (ext ResidueField FiniteResidue heightOneSpectrum heightOneSpectrum_asIdeal ord ord_one ord_mul ord_inv ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring mk uniformizer ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict mem_restrict_iff fiber mem_fiber restrict_mem_fiber adicCompletion adicCompletionIntegers kw_ffgc_adicCompletionComap kw_ffgc_valued_adicCompletionComap kw_ffgc_adicCompletionComapIntegers kw_ffgc_algebraAdicCompletionComap kw_ffgc_algebraMap_adicCompletionComap_eq kw_ffgc_rankOne_adicCompletion kw_ffgc_absoluteValue kw_ffgc_adicCompletionComap_algebraMap_algebraMap kw_ffgc_completionLinearCombination kw_ffgc_denseRange_completionLinearCombination kw_ffgc_completionTraceF')

open _root_.AlgebraicCurve.Place

variable {K F}

variable (v : Place K F)

end Place

namespace Divisor

export _root_.AlgebraicCurve.Divisor (smul_def smul_apply)

open _root_.AlgebraicCurve.Divisor

variable {K F}

end Divisor

namespace Pic0

export _root_.AlgebraicCurve.Pic0 (mk mk_surjective)

open _root_.AlgebraicCurve.Pic0

variable {K F}

end Pic0

namespace Place

export _root_.AlgebraicCurve.Place (ext ResidueField FiniteResidue heightOneSpectrum heightOneSpectrum_asIdeal ord ord_one ord_mul ord_inv ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring mk uniformizer ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict mem_restrict_iff fiber mem_fiber restrict_mem_fiber adicCompletion adicCompletionIntegers kw_ffgc_adicCompletionComap kw_ffgc_valued_adicCompletionComap kw_ffgc_adicCompletionComapIntegers kw_ffgc_algebraAdicCompletionComap kw_ffgc_algebraMap_adicCompletionComap_eq kw_ffgc_rankOne_adicCompletion kw_ffgc_absoluteValue kw_ffgc_adicCompletionComap_algebraMap_algebraMap kw_ffgc_completionLinearCombination kw_ffgc_denseRange_completionLinearCombination kw_ffgc_completionTraceF')

open _root_.AlgebraicCurve.Place

open scoped _root_.Pointwise _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.Pointwise

variable {K F}
variable (σ : F ≃ₐ[K] F)

variable (v : Place K F)

end Place

namespace Divisor

export _root_.AlgebraicCurve.Divisor (smul_def smul_apply)

open _root_.AlgebraicCurve.Divisor

open scoped _root_.Pointwise _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.Pointwise

variable {K F}

end Divisor

namespace Pic0

export _root_.AlgebraicCurve.Pic0 (mk mk_surjective)

open _root_.AlgebraicCurve.Pic0

open scoped _root_.Pointwise _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.Pointwise

variable {K F}

end Pic0

namespace Place

export _root_.AlgebraicCurve.Place (ext ResidueField FiniteResidue heightOneSpectrum heightOneSpectrum_asIdeal ord ord_one ord_mul ord_inv ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring mk uniformizer ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict mem_restrict_iff fiber mem_fiber restrict_mem_fiber adicCompletion adicCompletionIntegers kw_ffgc_adicCompletionComap kw_ffgc_valued_adicCompletionComap kw_ffgc_adicCompletionComapIntegers kw_ffgc_algebraAdicCompletionComap kw_ffgc_algebraMap_adicCompletionComap_eq kw_ffgc_rankOne_adicCompletion kw_ffgc_absoluteValue kw_ffgc_adicCompletionComap_algebraMap_algebraMap kw_ffgc_completionLinearCombination kw_ffgc_denseRange_completionLinearCombination kw_ffgc_completionTraceF')

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

open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.WithZero
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.IsLocalRing

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Divisor HasPrincipalDivisors Pic0 IsCurveOver HasCanonicalLocalResidueKStar Place.mem_restrict_iff Place.mem_fiber Place.restrict_mem_fiber kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_completionTraceAt)

open _root_.AlgebraicCurve

namespace Place

export _root_.AlgebraicCurve.Place (ext ResidueField FiniteResidue heightOneSpectrum heightOneSpectrum_asIdeal ord ord_one ord_mul ord_inv ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring mk uniformizer ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict mem_restrict_iff fiber mem_fiber restrict_mem_fiber adicCompletion adicCompletionIntegers kw_ffgc_adicCompletionComap kw_ffgc_valued_adicCompletionComap kw_ffgc_adicCompletionComapIntegers kw_ffgc_algebraAdicCompletionComap kw_ffgc_algebraMap_adicCompletionComap_eq kw_ffgc_rankOne_adicCompletion kw_ffgc_absoluteValue kw_ffgc_adicCompletionComap_algebraMap_algebraMap kw_ffgc_completionLinearCombination kw_ffgc_denseRange_completionLinearCombination kw_ffgc_completionTraceF')

open _root_.AlgebraicCurve.Place

section SinglePlace

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve.Place.ord_nonneg_of_mem {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
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
  @_root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve.Place.ord_nonneg_of_mem
theorem _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve.Place.mem_of_ord_nonneg {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)




-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.mem_of_ord_nonneg :=
  @_root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve.Place.mem_of_ord_nonneg
theorem _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve.Place.mem_iff_ord_nonneg {f : F} (hf : f ≠ 0) :
    f ∈ v.toValuationSubring ↔ 0 ≤ v.ord f :=
  ⟨v.ord_nonneg_of_mem, v.mem_of_ord_nonneg hf⟩




-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.mem_iff_ord_nonneg :=
  @_root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve.Place.mem_iff_ord_nonneg
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

theorem _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve.Place.comap_algebraMap_ne_top [Algebra.IsIntegral F F'] :
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
  @_root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve.Place.comap_algebraMap_ne_top
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

theorem _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve.Place.exists_ord_algebraMap_pos [Algebra.IsIntegral F F'] :
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
  @_root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve.Place.exists_ord_algebraMap_pos
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

section

variable {F : Type*} [Field F]

namespace ValuationSubring
export _root_.ValuationSubring (comap subtype mem_comap subtype_apply toSubring algebraMap_apply ext zero_mem mk mem_top mul_mem algebraMap_injective add_mem eq_top_iff valuation inclusion)
end ValuationSubring
open scoped _root_.ValuationSubring in
theorem ValuationSubring.valued_eq_one_of_isUnit {K : Type*} [Field K] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀] (x : hv.v.valuationSubring)
    (hx : IsUnit x) : Valued.v x.val = 1 := by
  obtain ⟨u, hu⟩ := hx
  apply le_antisymm ((hv.v.mem_valuationSubring_iff _).1 x.2)
  rw [← Valued.v.map_one (R := K), ← Submonoid.coe_one, ← u.mul_inv, hu,
    Submonoid.coe_mul, Valued.v.map_mul]
  nth_rw 2 [← mul_one (Valued.v x.val)]
  exact mul_le_mul_right ((hv.v.mem_valuationSubring_iff _).1 (u⁻¹.val.property)) _

open scoped _root_.ValuationSubring in
theorem ValuationSubring.isUnit_of_valued_eq_one {K : Type*} [Field K] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀] (x : hv.v.valuationSubring)
    (hx : Valued.v x.val = 1) : IsUnit x := by
  have : IsUnit x.val := by rw [isUnit_iff_ne_zero, ne_eq, ← map_eq_zero hv.v, hx]; aesop
  obtain ⟨u, hu⟩ := this
  have hu_inv_le : Valued.v u⁻¹.val ≤ 1 := by
    rw [← one_mul (Valued.v _), ← hx, ← hu, ← Valued.v.map_mul, u.mul_inv, hu, hx, Valued.v.map_one]
  rw [isUnit_iff_exists]
  exact ⟨⟨u⁻¹.val, hu_inv_le⟩,  ⟨by aesop, by aesop⟩⟩

open scoped _root_.ValuationSubring in
theorem ValuationSubring.isUnit_iff_valued_eq_one {K : Type*} [Field K] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀] (x : hv.v.valuationSubring) :
    IsUnit x ↔ Valued.v x.val = 1 :=
  ⟨valued_eq_one_of_isUnit x, isUnit_of_valued_eq_one x⟩

end

end

end

section
section

noncomputable section

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Divisor HasPrincipalDivisors Pic0 IsCurveOver HasCanonicalLocalResidueKStar Place.mem_restrict_iff Place.mem_fiber Place.restrict_mem_fiber kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_completionTraceAt)

open _root_.AlgebraicCurve

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsIntegral F F'] [HasPrincipalDivisors K F']

namespace Place

export _root_.AlgebraicCurve.Place (ext ResidueField FiniteResidue heightOneSpectrum heightOneSpectrum_asIdeal ord ord_one ord_mul ord_inv ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring mk uniformizer ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict mem_restrict_iff fiber mem_fiber restrict_mem_fiber adicCompletion adicCompletionIntegers kw_ffgc_adicCompletionComap kw_ffgc_valued_adicCompletionComap kw_ffgc_adicCompletionComapIntegers kw_ffgc_algebraAdicCompletionComap kw_ffgc_algebraMap_adicCompletionComap_eq kw_ffgc_rankOne_adicCompletion kw_ffgc_absoluteValue kw_ffgc_adicCompletionComap_algebraMap_algebraMap kw_ffgc_completionLinearCombination kw_ffgc_denseRange_completionLinearCombination kw_ffgc_completionTraceF')

open _root_.AlgebraicCurve.Place

end Place

namespace Divisor

export _root_.AlgebraicCurve.Divisor (smul_def smul_apply)

open _root_.AlgebraicCurve.Divisor

end Divisor

namespace Divisor

export _root_.AlgebraicCurve.Divisor (smul_def smul_apply)

open _root_.AlgebraicCurve.Divisor

end Divisor

end AlgebraicCurve

end
end

end

section
section

set_option synthInstance.maxHeartbeats 3200000
set_option maxHeartbeats 6400000

noncomputable section

open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.IsDedekindDomain
open _root_.IsDedekindDomain.HeightOneSpectrum
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.IsDedekindDomain.HeightOneSpectrum
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.IsLocalRing
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.WithZero
open _root_.MonoidWithZeroHom
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.MonoidWithZeroHom

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Divisor HasPrincipalDivisors Pic0 IsCurveOver HasCanonicalLocalResidueKStar Place.mem_restrict_iff Place.mem_fiber Place.restrict_mem_fiber kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_completionTraceAt)

namespace Place

export _root_.AlgebraicCurve.Place (ext ResidueField FiniteResidue heightOneSpectrum heightOneSpectrum_asIdeal ord ord_one ord_mul ord_inv ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring mk uniformizer ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict mem_restrict_iff fiber mem_fiber restrict_mem_fiber adicCompletion adicCompletionIntegers kw_ffgc_adicCompletionComap kw_ffgc_valued_adicCompletionComap kw_ffgc_adicCompletionComapIntegers kw_ffgc_algebraAdicCompletionComap kw_ffgc_algebraMap_adicCompletionComap_eq kw_ffgc_rankOne_adicCompletion kw_ffgc_absoluteValue kw_ffgc_adicCompletionComap_algebraMap_algebraMap kw_ffgc_completionLinearCombination kw_ffgc_denseRange_completionLinearCombination kw_ffgc_completionTraceF')

open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve

section AdicCompletion

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (V : Place K F)

end AdicCompletion

section Henselian

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (V : Place K F)

end Henselian

section WithValLevel

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

end WithValLevel

section CompletionComap

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

end CompletionComap

section Bridge

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

end Bridge

end AlgebraicCurve.Place

end
end

end

section
section

set_option synthInstance.maxHeartbeats 3200000
set_option maxHeartbeats 6400000

noncomputable section

open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.IsDedekindDomain
open _root_.IsDedekindDomain.HeightOneSpectrum
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.IsDedekindDomain.HeightOneSpectrum
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.IsLocalRing
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.WithZero
open _root_.MonoidWithZeroHom
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.MonoidWithZeroHom

section HenselUniqueness

variable {R : Type*} [CommRing R] [IsLocalRing R]

end HenselUniqueness

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Divisor HasPrincipalDivisors Pic0 IsCurveOver HasCanonicalLocalResidueKStar Place.mem_restrict_iff Place.mem_fiber Place.restrict_mem_fiber kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_completionTraceAt)

namespace Place

export _root_.AlgebraicCurve.Place (ext ResidueField FiniteResidue heightOneSpectrum heightOneSpectrum_asIdeal ord ord_one ord_mul ord_inv ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring mk uniformizer ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict mem_restrict_iff fiber mem_fiber restrict_mem_fiber adicCompletion adicCompletionIntegers kw_ffgc_adicCompletionComap kw_ffgc_valued_adicCompletionComap kw_ffgc_adicCompletionComapIntegers kw_ffgc_algebraAdicCompletionComap kw_ffgc_algebraMap_adicCompletionComap_eq kw_ffgc_rankOne_adicCompletion kw_ffgc_absoluteValue kw_ffgc_adicCompletionComap_algebraMap_algebraMap kw_ffgc_completionLinearCombination kw_ffgc_denseRange_completionLinearCombination kw_ffgc_completionTraceF')

open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve

section IntegerComap

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

end IntegerComap

section ClosedRange

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

end ClosedRange

end AlgebraicCurve.Place

end
end

end

section
section

set_option synthInstance.maxHeartbeats 3200000
set_option maxHeartbeats 6400000

noncomputable section

open _root_.Polynomial
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.Polynomial
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.IsLocalRing
open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.IsDedekindDomain

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Divisor HasPrincipalDivisors Pic0 IsCurveOver HasCanonicalLocalResidueKStar Place.mem_restrict_iff Place.mem_fiber Place.restrict_mem_fiber kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_completionTraceAt)

namespace Place

export _root_.AlgebraicCurve.Place (ext ResidueField FiniteResidue heightOneSpectrum heightOneSpectrum_asIdeal ord ord_one ord_mul ord_inv ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring mk uniformizer ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict mem_restrict_iff fiber mem_fiber restrict_mem_fiber adicCompletion adicCompletionIntegers kw_ffgc_adicCompletionComap kw_ffgc_valued_adicCompletionComap kw_ffgc_adicCompletionComapIntegers kw_ffgc_algebraAdicCompletionComap kw_ffgc_algebraMap_adicCompletionComap_eq kw_ffgc_rankOne_adicCompletion kw_ffgc_absoluteValue kw_ffgc_adicCompletionComap_algebraMap_algebraMap kw_ffgc_completionLinearCombination kw_ffgc_denseRange_completionLinearCombination kw_ffgc_completionTraceF')

open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve

section CompletionAlgebra

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

scoped instance kw_ffgc_isIntegrallyClosed_adicCompletionIntegers :
    IsIntegrallyClosed (W.restrict F).adicCompletionIntegers :=
  Valuation.Integers.isIntegrallyClosed
    (HeightOneSpectrum.adicCompletionIntegers.integers
      (K := F) (v := (W.restrict F).heightOneSpectrum))

theorem kw_ffgc_adicCompletionComapIntegers_injective :
    Function.Injective (kw_ffgc_adicCompletionComapIntegers F W) := by
  intro a b hab
  exact Subtype.ext ((kw_ffgc_adicCompletionComap F W).injective
    (congrArg Subtype.val hab))

scoped instance kw_ffgc_isTorsionFree_adicCompletionComapIntegers :
    Module.IsTorsionFree (W.restrict F).adicCompletionIntegers W.adicCompletionIntegers :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr
    (kw_ffgc_adicCompletionComapIntegers_injective F W)

end CompletionAlgebra

section IrreducibleValuation

open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.WithZero

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (V : Place K F)

end IrreducibleValuation

section SpectralSetup

open scoped _root_.Valued _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.Valued _root_.NNReal _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.NNReal _root_.WithZero _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.WithZero

open _root_.WithZeroMulInt
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.WithZeroMulInt
open _root_.Valuation.IsRankOneDiscrete
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.Valuation.IsRankOneDiscrete

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (V : Place K F)

theorem kw_ffgc_norm_adicCompletion_eq (x : V.adicCompletion) :
    letI := kw_ffgc_rankOne_adicCompletion V
    ‖x‖ = (WithZeroMulInt.toNNReal (two_ne_zero) (Valued.v x) : ℝ) := by
  letI := kw_ffgc_rankOne_adicCompletion V
  have h := valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective
    (V.heightOneSpectrum.valuedAdicCompletion_surjective F) x
  simp only [Valued.toNormedField.norm_def, Valuation.RankOne.hom]
  rw [← h]; rfl

end SpectralSetup

section AbsoluteValue

open scoped _root_.Valued _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.Valued _root_.NNReal _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.NNReal _root_.WithZero _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.WithZero

open _root_.WithZeroMulInt
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.WithZeroMulInt
open _root_.Valuation.IsRankOneDiscrete
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.Valuation.IsRankOneDiscrete

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

theorem kw_ffgc_absoluteValue_extends (c : (W.restrict F).adicCompletion) :
    letI := kw_ffgc_rankOne_adicCompletion (W.restrict F)
    kw_ffgc_absoluteValue F W
      (algebraMap (W.restrict F).adicCompletion W.adicCompletion c) = ‖c‖ := by
  letI := kw_ffgc_rankOne_adicCompletion (W.restrict F)
  letI := kw_ffgc_rankOne_adicCompletion W
  have hr : (0 : ℝ) < (W.ramificationIndex F : ℝ) :=
    Nat.cast_pos.mpr (W.ramificationIndex_pos (F := F))
  show ‖algebraMap (W.restrict F).adicCompletion W.adicCompletion c‖
      ^ ((W.ramificationIndex F : ℝ))⁻¹ = ‖c‖
  rw [kw_ffgc_norm_adicCompletion_eq W, kw_ffgc_norm_adicCompletion_eq (W.restrict F),
    kw_ffgc_algebraMap_adicCompletionComap_eq, kw_ffgc_valued_adicCompletionComap,
    map_pow, NNReal.coe_pow, ← Real.rpow_natCast, ← Real.rpow_mul (NNReal.coe_nonneg _),
    mul_inv_cancel₀ hr.ne', Real.rpow_one]

end AbsoluteValue

section IntegralClosure

open scoped _root_.Valued _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.Valued _root_.NNReal _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.NNReal _root_.WithZero _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.WithZero

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

theorem kw_ffgc_isIntegral_adicCompletionIntegers_of_algebraic
    [Algebra.IsAlgebraic (W.restrict F).adicCompletion W.adicCompletion]
    (x : W.adicCompletionIntegers) :
    _root_.IsIntegral (W.restrict F).adicCompletionIntegers x := by
  letI := kw_ffgc_rankOne_adicCompletion (W.restrict F)
  letI := kw_ffgc_rankOne_adicCompletion W
  letI : NontriviallyNormedField (W.restrict F).adicCompletion :=
    Valued.toNontriviallyNormedField (W.restrict F).adicCompletion ℤᵐ⁰
  haveI : IsUltrametricDist (W.restrict F).adicCompletion :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (fun a b => Valuation.norm_add_le Valued.v a b)
  have hr : (0 : ℝ) < ((W.ramificationIndex F : ℝ))⁻¹ :=
    inv_pos.mpr (Nat.cast_pos.mpr (W.ramificationIndex_pos (F := F)))

  have hxn : ‖(x : W.adicCompletion)‖ ≤ 1 :=
    (Valued.toNormedField.norm_le_one_iff).mpr x.2

  have hsn : spectralNorm (W.restrict F).adicCompletion W.adicCompletion
        (x : W.adicCompletion)
      = ‖(x : W.adicCompletion)‖ ^ ((W.ramificationIndex F : ℝ))⁻¹ :=
    (spectralNorm_unique_field_norm_ext (f := kw_ffgc_absoluteValue F W)
      (kw_ffgc_absoluteValue_extends F W) (x : W.adicCompletion)).symm

  have hspec : spectralValue (minpoly (W.restrict F).adicCompletion
      (x : W.adicCompletion)) ≤ 1 := by
    show spectralNorm (W.restrict F).adicCompletion W.adicCompletion
      (x : W.adicCompletion) ≤ 1
    rw [hsn]; exact Real.rpow_le_one (norm_nonneg _) hxn hr.le
  have hmon : (minpoly (W.restrict F).adicCompletion (x : W.adicCompletion)).Monic :=
    minpoly.monic (Algebra.IsAlgebraic.isAlgebraic
      (R := (W.restrict F).adicCompletion) (x : W.adicCompletion)).isIntegral

  have hlift : minpoly (W.restrict F).adicCompletion (x : W.adicCompletion)
      ∈ Polynomial.lifts (algebraMap (W.restrict F).adicCompletionIntegers
          (W.restrict F).adicCompletion) := by
    refine (Polynomial.lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, ?_⟩, rfl⟩
    exact (Valued.toNormedField.norm_le_one_iff).mp
      ((spectralValue_le_one_iff hmon).mp hspec n)
  obtain ⟨P, hP, -, hPmon⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hmon

  have hxintW : _root_.IsIntegral (W.restrict F).adicCompletionIntegers (x : W.adicCompletion) := by
    refine ⟨P, hPmon, ?_⟩
    rw [← Polynomial.aeval_def,
      ← Polynomial.aeval_map_algebraMap (W.restrict F).adicCompletion, hP, minpoly.aeval]
  exact (isIntegral_algHom_iff
    (IsScalarTower.toAlgHom (W.restrict F).adicCompletionIntegers
      W.adicCompletionIntegers W.adicCompletion)
    Subtype.val_injective).mp hxintW

theorem kw_ffgc_isIntegralClosure_adicCompletionIntegers
    [Algebra.IsAlgebraic (W.restrict F).adicCompletion W.adicCompletion] :
    IsIntegralClosure W.adicCompletionIntegers (W.restrict F).adicCompletionIntegers
      W.adicCompletion where
  algebraMap_injective := Subtype.val_injective
  isIntegral_iff {x} := by
    constructor
    · intro hx
      have hxW : _root_.IsIntegral W.adicCompletionIntegers x := hx.tower_top
      haveI : IsIntegrallyClosed W.adicCompletionIntegers :=
        Valuation.Integers.isIntegrallyClosed
          (HeightOneSpectrum.adicCompletionIntegers.integers
            (K := F') (v := W.heightOneSpectrum))
      exact IsIntegrallyClosed.isIntegral_iff.mp hxW
    · rintro ⟨y, rfl⟩
      exact (kw_ffgc_isIntegral_adicCompletionIntegers_of_algebraic F W y).map
        (IsScalarTower.toAlgHom (W.restrict F).adicCompletionIntegers
          W.adicCompletionIntegers W.adicCompletion)

end IntegralClosure

section ClosedAdjoin

open scoped _root_.Valued _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.Valued _root_.NNReal _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.NNReal _root_.WithZero _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.WithZero

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

end ClosedAdjoin

section Bridge

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

end Bridge

end AlgebraicCurve.Place



end

end


end


section
section

set_option synthInstance.maxHeartbeats 3200000
set_option maxHeartbeats 6400000

noncomputable section

open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.IsDedekindDomain
open _root_.IsDedekindDomain.HeightOneSpectrum
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.IsDedekindDomain.HeightOneSpectrum
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.IsLocalRing
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.WithZero

open scoped _root_.Valued _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.Valued _root_.WithZero _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.WithZero

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Divisor HasPrincipalDivisors Pic0 IsCurveOver HasCanonicalLocalResidueKStar Place.mem_restrict_iff Place.mem_fiber Place.restrict_mem_fiber kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_completionTraceAt)

namespace Place

export _root_.AlgebraicCurve.Place (ext ResidueField FiniteResidue heightOneSpectrum heightOneSpectrum_asIdeal ord ord_one ord_mul ord_inv ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring mk uniformizer ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict mem_restrict_iff fiber mem_fiber restrict_mem_fiber adicCompletion adicCompletionIntegers kw_ffgc_adicCompletionComap kw_ffgc_valued_adicCompletionComap kw_ffgc_adicCompletionComapIntegers kw_ffgc_algebraAdicCompletionComap kw_ffgc_algebraMap_adicCompletionComap_eq kw_ffgc_rankOne_adicCompletion kw_ffgc_absoluteValue kw_ffgc_adicCompletionComap_algebraMap_algebraMap kw_ffgc_completionLinearCombination kw_ffgc_denseRange_completionLinearCombination kw_ffgc_completionTraceF')

open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve

section FiniteDimensional

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

end FiniteDimensional


section CompletionTrace

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

theorem kw_ffgc_completionTraceF'_apply [FiniteDimensional F F'] (g : F') :
    kw_ffgc_completionTraceF' F W g
      = Algebra.trace (W.restrict F).adicCompletion W.adicCompletion
          (algebraMap F' W.adicCompletion g) := rfl

end CompletionTrace


section ResidueCompletion

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (V : Place K F)

end ResidueCompletion


end AlgebraicCurve.Place



end

end


end


section
section

noncomputable section

open _root_.KaehlerDifferential
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.KaehlerDifferential

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Divisor HasPrincipalDivisors Pic0 IsCurveOver HasCanonicalLocalResidueKStar Place.mem_restrict_iff Place.mem_fiber Place.restrict_mem_fiber kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_completionTraceAt)

open _root_.AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

namespace IsCurveOver

export _root_.AlgebraicCurve.IsCurveOver (mk)

open _root_.AlgebraicCurve.IsCurveOver

variable {K F}

end IsCurveOver


namespace Place

export _root_.AlgebraicCurve.Place (ext ResidueField FiniteResidue heightOneSpectrum heightOneSpectrum_asIdeal ord ord_one ord_mul ord_inv ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring mk uniformizer ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict mem_restrict_iff fiber mem_fiber restrict_mem_fiber adicCompletion adicCompletionIntegers kw_ffgc_adicCompletionComap kw_ffgc_valued_adicCompletionComap kw_ffgc_adicCompletionComapIntegers kw_ffgc_algebraAdicCompletionComap kw_ffgc_algebraMap_adicCompletionComap_eq kw_ffgc_rankOne_adicCompletion kw_ffgc_absoluteValue kw_ffgc_adicCompletionComap_algebraMap_algebraMap kw_ffgc_completionLinearCombination kw_ffgc_denseRange_completionLinearCombination kw_ffgc_completionTraceF')

open _root_.AlgebraicCurve.Place

variable {K F}
variable (v : Place K F)

end Place


variable {K F}

variable (K F)

end AlgebraicCurve


namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateTraceCompat)

open _root_.ModularCurve

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve

end ModularCurve


namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Divisor HasPrincipalDivisors Pic0 IsCurveOver HasCanonicalLocalResidueKStar Place.mem_restrict_iff Place.mem_fiber Place.restrict_mem_fiber kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_completionTraceAt)

open _root_.AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

end AlgebraicCurve


namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateTraceCompat)

open _root_.ModularCurve

end ModularCurve


end

end


end


section
section

noncomputable section

open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.WithZero
open _root_.Module
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.Module
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.IsLocalRing
open _root_.Module.IsLocalRing

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Divisor HasPrincipalDivisors Pic0 IsCurveOver HasCanonicalLocalResidueKStar Place.mem_restrict_iff Place.mem_fiber Place.restrict_mem_fiber kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_completionTraceAt)

open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

export _root_.AlgebraicCurve.Place (ext ResidueField FiniteResidue heightOneSpectrum heightOneSpectrum_asIdeal ord ord_one ord_mul ord_inv ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring mk uniformizer ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict mem_restrict_iff fiber mem_fiber restrict_mem_fiber adicCompletion adicCompletionIntegers kw_ffgc_adicCompletionComap kw_ffgc_valued_adicCompletionComap kw_ffgc_adicCompletionComapIntegers kw_ffgc_algebraAdicCompletionComap kw_ffgc_algebraMap_adicCompletionComap_eq kw_ffgc_rankOne_adicCompletion kw_ffgc_absoluteValue kw_ffgc_adicCompletionComap_algebraMap_algebraMap kw_ffgc_completionLinearCombination kw_ffgc_denseRange_completionLinearCombination kw_ffgc_completionTraceF')

open _root_.AlgebraicCurve.Place

variable (v : Place K F)

def _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve.Place.uniformizerSubring : v.toValuationSubring :=
  (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose




-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.uniformizerSubring :=
  @_root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve.Place.uniformizerSubring
theorem _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve.Place.uniformizer_mem : v.uniformizer ∈ v.toValuationSubring :=
  v.uniformizerSubring.2




-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.uniformizer_mem :=
  @_root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve.Place.uniformizer_mem
end Place


variable [HasCanonicalLocalResidueKStar K F]

end AlgebraicCurve


section AxiomAudit

end AxiomAudit


end


end


end


section
section

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 3200000
set_option linter.unusedSectionVars false

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.ModularCurve.GF24a9RRDx
open _root_.AlgebraicCurve.Place
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve.Place
open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.IsDedekindDomain

noncomputable section

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Divisor HasPrincipalDivisors Pic0 IsCurveOver HasCanonicalLocalResidueKStar Place.mem_restrict_iff Place.mem_fiber Place.restrict_mem_fiber kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_completionTraceAt)

open _root_.AlgebraicCurve

section LocalResidueCompletion

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

variable [HasCanonicalLocalResidueKStar K E]

end LocalResidueCompletion


section CompletionTraceAt

variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F] [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]

end CompletionTraceAt


section MPGKPowBasisLocalMint

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]
variable [Algebra.IsIntegral E F]

end MPGKPowBasisLocalMint


section CompletionTraceSumMint

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

end CompletionTraceSumMint


section EffBaseDescentMint

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

end EffBaseDescentMint


section MainReduction

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]
variable [Algebra.IsIntegral E F] [FiniteDimensional E F]

end MainReduction


end AlgebraicCurve


end

end


end


section
section

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 3200000
set_option linter.unusedSectionVars false

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve.Place
open _root_.LinearMap
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.LinearMap
open _root_.Submodule
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.Submodule
open _root_.ModularCurve.KwF4gRRTate
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.ModularCurve.KwF4gRRTate

noncomputable section

namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateTraceCompat)

namespace KwF4gRRTate

export _root_.ModularCurve.KwF4gRRTate (finrankTrace tateComm tateComm_apply tateCommRestrict tateCommRestrict_apply tateCommTrace tateComm_eq_of_commute adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateTraceCompat)

open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve

section TateProj

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

theorem mem_adicIntegersKSubmod_iff (x : u.adicCompletion) :
    x ∈ adicIntegersKSubmod u ↔ x ∈ u.adicCompletionIntegers := Iff.rfl

theorem tateProj_mem_integers (x : u.adicCompletion) :
    tateProj u x ∈ u.adicCompletionIntegers :=
  (mem_adicIntegersKSubmod_iff u _).mp
    (Submodule.coe_mem
      (Submodule.projectionOnto (adicIntegersKSubmod u) _
        (Classical.choose_spec (Submodule.exists_isCompl (adicIntegersKSubmod u))) x))

theorem tateProj_of_mem {x : u.adicCompletion} (hx : x ∈ u.adicCompletionIntegers) :
    tateProj u x = x := by
  have h := Submodule.projectionOnto_apply_left
    (Classical.choose_spec (Submodule.exists_isCompl (adicIntegersKSubmod u)))
    (⟨x, (mem_adicIntegersKSubmod_iff u x).mpr hx⟩ : adicIntegersKSubmod u)
  have hcoe := congrArg (Subtype.val (p := fun y => y ∈ adicIntegersKSubmod u)) h
  exact hcoe

theorem tateProj_idem : tateProj u ∘ₗ tateProj u = tateProj u := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply]
  exact tateProj_of_mem u (tateProj_mem_integers u x)

theorem range_tateProj : LinearMap.range (tateProj u) = adicIntegersKSubmod u := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    exact tateProj_mem_integers u y
  · intro x hx
    exact ⟨x, tateProj_of_mem u hx⟩

end TateProj


section TateResDef

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

end TateResDef


section TateAtoms

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

variable [HasCanonicalLocalResidueKStar K L]

variable (F E : Type*) [Field F] [Algebra K F] [Field E] [Algebra K E]
variable [Algebra E F] [IsScalarTower K E F] [Algebra.IsIntegral E F]
variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalLocalResidueKStar K E]

end TateAtoms


end ModularCurve.KwF4gRRTate



end


end


end


section
section

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 3200000
set_option linter.unusedSectionVars false

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve.Place
open _root_.LinearMap
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.LinearMap
open _root_.Submodule
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.Submodule
open _root_.ModularCurve.KwF4gRRTate
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.ModularCurve.KwF4gRRTate
open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.IsDedekindDomain
open _root_.IsDedekindDomain.HeightOneSpectrum
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.IsDedekindDomain.HeightOneSpectrum
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.IsLocalRing

noncomputable section

namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateTraceCompat)

namespace KwF4gRRTate

export _root_.ModularCurve.KwF4gRRTate (finrankTrace tateComm tateComm_apply tateCommRestrict tateCommRestrict_apply tateCommTrace tateComm_eq_of_commute adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateTraceCompat)

open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve

section PoleWindow

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

def poleWindowKSubmod (πh : u.adicCompletionIntegers) (M : ℕ) :
    Submodule K u.adicCompletion where
  carrier := {x | (πh : u.adicCompletion)^M * x ∈ u.adicCompletionIntegers}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, mul_add] at ha hb ⊢; exact add_mem ha hb
  zero_mem' := by simp only [Set.mem_setOf_eq, mul_zero]; exact zero_mem _
  smul_mem' c x hx := by
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply K L u.adicCompletion, mul_left_comm]
    exact mul_mem ((kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff u _).mpr
      (u.algebraMap_mem' c)) hx

theorem mem_poleWindowKSubmod_iff (πh : u.adicCompletionIntegers) (M : ℕ)
    (x : u.adicCompletion) :
    x ∈ poleWindowKSubmod u πh M ↔ (πh : u.adicCompletion)^M * x ∈ u.adicCompletionIntegers :=
  Iff.rfl

theorem adicIntegersKSubmod_le_poleWindowKSubmod (πh : u.adicCompletionIntegers) (M : ℕ) :
    adicIntegersKSubmod u ≤ poleWindowKSubmod u πh M :=
  fun _ hx => mul_mem (pow_mem πh.2 M) hx

theorem kwF4gRRTate_clearPole (πh : u.adicCompletionIntegers) (hπh : Irreducible πh)
    (fh : u.adicCompletion) :
    ∃ M : ℕ, (πh : u.adicCompletion)^M * fh ∈ u.adicCompletionIntegers := by
  obtain ⟨a, b, hb, hfh⟩ := IsFractionRing.div_surjective
    (A := u.adicCompletionIntegers) (K := u.adicCompletion) fh
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨M, ub, hbeq⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hπh
  refine ⟨M, ?_⟩

  have hcoe : ∀ x : u.adicCompletionIntegers,
      (x : u.adicCompletion) = algebraMap _ u.adicCompletion x := fun _ => rfl
  have hbK0 : (b : u.adicCompletion) ≠ 0 := by
    rw [hcoe]; exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hb0
  have hbfh : (b : u.adicCompletion) * fh = (a : u.adicCompletion) := by
    rw [← hfh, hcoe b, hcoe a, mul_div_cancel₀ _ (hcoe b ▸ hbK0)]

  have hπheq : ((ub⁻¹ : u.adicCompletionIntegersˣ) : u.adicCompletionIntegers) * b = πh ^ M := by
    rw [hbeq, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

  have hπheqK : ((((ub⁻¹ : u.adicCompletionIntegersˣ) : u.adicCompletionIntegers)
        : u.adicCompletion)) * (b : u.adicCompletion)
      = (πh : u.adicCompletion)^M := by
    have := congrArg (algebraMap u.adicCompletionIntegers u.adicCompletion) hπheq
    simp only [map_mul, map_pow] at this
    exact this

  rw [← hπheqK, mul_assoc, hbfh]
  exact mul_mem (Subtype.coe_prop _) a.2

variable (K L) in

def KwF4gRRTatePoleWindowFinite : Prop :=
  ∀ (u : Place K L) [u.FiniteResidue] (πh : u.adicCompletionIntegers) (_ : Irreducible πh)
    (M : ℕ),
    FiniteDimensional K
      (poleWindowKSubmod u πh M ⧸
        (adicIntegersKSubmod u).comap (poleWindowKSubmod u πh M).subtype)

end PoleWindow


end ModularCurve.KwF4gRRTate



end


end


end


section
section

set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open scoped _root_.WithZero _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.WithZero _root_.Multiplicative _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.Multiplicative _root_.Topology _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.Topology
open _root_.Filter
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.Filter

namespace IsDedekindDomain

export _root_.IsDedekindDomain (HeightOneSpectrum.adicCompletionIntegers HeightOneSpectrum.adicCompletionIntegers.integers HeightOneSpectrum.ext mk HeightOneSpectrum)

namespace HeightOneSpectrum

export _root_.IsDedekindDomain.HeightOneSpectrum (valuation_of_algebraMap intValuation_le_pow_iff_mem isMaximal mk comap valuedAdicCompletion_eq_valuation' adicCompletion valuation adicCompletionIntegers valuedAdicCompletion_surjective adicCompletionIntegers.integers mem_integers_of_valuation_le_one denseRange_algebraMap intValuation completionIdeal adicCompletion.mem_completionIdeal_pow)

open _root_.IsDedekindDomain.HeightOneSpectrum
open _root_.IsDedekindDomain

variable {A : Type*} (K : Type*) [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    [IsDedekindDomain A] (v : HeightOneSpectrum A)

namespace adicCompletion

export _root_.IsDedekindDomain.HeightOneSpectrum.adicCompletion (mem_completionIdeal_pow)

open _root_.IsDedekindDomain.HeightOneSpectrum.adicCompletion



theorem isOpen_setOf_valued_le {γ : ℤᵐ⁰} (hγ : γ ≠ 0) :
    IsOpen {y : v.adicCompletion K | Valued.v y ≤ γ} := by

  obtain ⟨z, hz⟩ := valuedAdicCompletion_surjective K v γ
  have hz0 : ((Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)) z ≠ 0 := by rw [hz]; exact hγ
  have hr0 : (((Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰))).restrict z ≠ 0 := fun h =>
    hz0 ((Valuation.restrict_eq_zero_iff ((Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰))).mp h)
  have hset : {y : v.adicCompletion K | Valued.v y ≤ γ}
      = {y : v.adicCompletion K | (((Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰))).restrict y ≤ (((Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰))).restrict z} := by
    ext y
    simp only [Set.mem_setOf_eq, Valuation.restrict_le_iff, hz]
  rw [hset]
  exact Valued.isOpen_closedBall _ hr0

end adicCompletion


section NumberField

open _root_.NumberField
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.NumberField

variable (F : Type*) [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F))

end NumberField


end IsDedekindDomain.HeightOneSpectrum



section AxiomAudit

open _root_.IsDedekindDomain.HeightOneSpectrum
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.IsDedekindDomain.HeightOneSpectrum

end AxiomAudit


end


end


section
section

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 3200000
set_option linter.unusedSectionVars false

noncomputable section

open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.IsDedekindDomain
open _root_.IsDedekindDomain.HeightOneSpectrum
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.IsDedekindDomain.HeightOneSpectrum
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.IsLocalRing
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.WithZero
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.ModularCurve.Lg37
open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve.Place

namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateTraceCompat)

namespace KwF4R1V410a
open _root_.ModularCurve

scoped instance kwF4R1V410a_subsingletonHeightOneSpectrumDVR
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    Subsingleton (HeightOneSpectrum O) :=
  ⟨fun a b => IsDedekindDomain.HeightOneSpectrum.ext
    (((IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime O).mp
      inferInstance).2.unique ⟨a.3, a.2⟩ ⟨b.3, b.2⟩)⟩

section Bridge

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)






theorem kwF4R1V410a_algebraMap_mem_completionIdeal_pow_iff (n : ℕ) (x : (w.toValuationSubring)) :
    algebraMap ((w.toValuationSubring)) ((w.adicCompletionIntegers)) x ∈ ((w.heightOneSpectrum.completionIdeal F)) ^ n ↔ x ∈ ((IsLocalRing.maximalIdeal w.toValuationSubring)) ^ n := by
  have hval : Valued.v (algebraMap ((w.toValuationSubring)) ((w.adicCompletionIntegers)) x).val
      = w.heightOneSpectrum.intValuation x := by
    have h1 : (algebraMap ((w.toValuationSubring)) ((w.adicCompletionIntegers)) x).val
        = ((algebraMap ((w.toValuationSubring)) F x : F) : w.adicCompletion) := rfl
    rw [h1, valuedAdicCompletion_eq_valuation' (K := F) w.heightOneSpectrum,
      valuation_of_algebraMap]
  rw [adicCompletion.mem_completionIdeal_pow, hval, ← WithZero.exp_eq_coe_ofAdd,
    intValuation_le_pow_iff_mem, w.heightOneSpectrum_asIdeal]

theorem kwF4R1V410a_exists_sub_mem_completionIdeal_pow (n : ℕ) (y : (w.adicCompletionIntegers)) :
    ∃ x : (w.toValuationSubring), y - algebraMap ((w.toValuationSubring)) ((w.adicCompletionIntegers)) x ∈ ((w.heightOneSpectrum.completionIdeal F)) ^ n := by

  have hball_open : IsOpen {z : w.adicCompletion |
      Valued.v (z - y.val) ≤ WithZero.exp (-(n : ℤ))} :=
    (adicCompletion.isOpen_setOf_valued_le F w.heightOneSpectrum
      WithZero.exp_ne_zero).preimage (continuous_sub_right y.val)
  have hy_mem : y.val ∈ {z : w.adicCompletion |
      Valued.v (z - y.val) ≤ WithZero.exp (-(n : ℤ))} := by
    simp only [Set.mem_setOf_eq, sub_self, _root_.map_zero]; exact WithZero.zero_le _
  have hmeet := mem_closure_iff.mp
    ((denseRange_algebraMap F w.heightOneSpectrum) y.val) _ hball_open hy_mem

  have hexists : ∃ z : F, Valued.v (algebraMap F w.adicCompletion z - y.val)
      ≤ WithZero.exp (-(n : ℤ)) := by
    rcases hmeet with ⟨z₀, hz₀_ball, z, hz_eq⟩
    exact ⟨z, hz_eq ▸ hz₀_ball⟩
  obtain ⟨z, hz⟩ := hexists
  rw [show algebraMap F w.adicCompletion z = ((z : F) : w.adicCompletion) from rfl] at hz

  have hz_val_le : w.heightOneSpectrum.valuation F z ≤ 1 := by
    have hzhat : Valued.v ((z : w.adicCompletion)) ≤ (1 : ℤᵐ⁰) := by
      calc Valued.v ((z : w.adicCompletion))
          = Valued.v (((z : w.adicCompletion) - y.val) + y.val) := by ring_nf
        _ ≤ max (Valued.v ((z : w.adicCompletion) - y.val)) (Valued.v y.val) :=
            Valuation.map_add _ _ _
        _ ≤ (1 : ℤᵐ⁰) := max_le
            (hz.trans (by rw [← WithZero.exp_zero]; exact WithZero.exp_le_exp.mpr (by omega)))
            y.2
    rwa [valuedAdicCompletion_eq_valuation'] at hzhat
  have hz_mem : z ∈ ((w.toValuationSubring) : ValuationSubring F) := by
    obtain ⟨r, hr⟩ := mem_integers_of_valuation_le_one F z
      (fun v' => by
        obtain rfl : v' = w.heightOneSpectrum := Subsingleton.elim _ _
        exact hz_val_le)
    exact hr ▸ r.2
  refine ⟨⟨z, hz_mem⟩, ?_⟩
  rw [adicCompletion.mem_completionIdeal_pow, ← WithZero.exp_eq_coe_ofAdd]
  have hsub : (y - algebraMap ((w.toValuationSubring)) ((w.adicCompletionIntegers)) ⟨z, hz_mem⟩ : (w.adicCompletionIntegers)).val
      = y.val - ((z : F) : w.adicCompletion) := rfl
  rw [hsub, Valuation.map_sub_swap]
  exact hz

def kwF4R1V410a_quotientEquiv (n : ℕ) :
    ((w.toValuationSubring)) ⧸ ((IsLocalRing.maximalIdeal w.toValuationSubring)) ^ n ≃+* ((w.adicCompletionIntegers)) ⧸ ((w.heightOneSpectrum.completionIdeal F)) ^ n :=
  RingEquiv.ofBijective
    (Ideal.quotientMap _ (algebraMap ((w.toValuationSubring)) ((w.adicCompletionIntegers)))
      (fun x hx => (kwF4R1V410a_algebraMap_mem_completionIdeal_pow_iff w n x).mpr hx))
    ⟨Ideal.quotientMap_injective'
      (fun x hx => (kwF4R1V410a_algebraMap_mem_completionIdeal_pow_iff w n x).mp
        (Ideal.mem_comap.mp hx)),
    fun y => by
      obtain ⟨y', rfl⟩ := Ideal.Quotient.mk_surjective y
      obtain ⟨x, hx⟩ := kwF4R1V410a_exists_sub_mem_completionIdeal_pow w n y'
      refine ⟨Ideal.Quotient.mk _ x, ?_⟩
      rw [Ideal.quotientMap_mk]
      exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (by
        rw [← neg_sub, neg_mem_iff]; exact hx)⟩

theorem kwF4R1V410a_quotientEquiv_mk (n : ℕ) (x : (w.toValuationSubring)) :
    kwF4R1V410a_quotientEquiv w n (Ideal.Quotient.mk _ x)
      = Ideal.Quotient.mk _ (algebraMap ((w.toValuationSubring)) ((w.adicCompletionIntegers)) x) := rfl

end Bridge


end ModularCurve.KwF4R1V410a



end

end


end


section
section

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 3200000
set_option linter.unusedSectionVars false

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve.Place
open _root_.LinearMap
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.LinearMap
open _root_.Submodule
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.Submodule
open _root_.ModularCurve.KwF4gRRTate
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.ModularCurve.KwF4gRRTate
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.ModularCurve.KwF4R1V410a
open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.IsDedekindDomain
open _root_.IsDedekindDomain.HeightOneSpectrum
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.IsDedekindDomain.HeightOneSpectrum
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.IsLocalRing

noncomputable section

namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateTraceCompat)

namespace KwF4gRRTate

export _root_.ModularCurve.KwF4gRRTate (finrankTrace tateComm tateComm_apply tateCommRestrict tateCommRestrict_apply tateCommTrace tateComm_eq_of_commute adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateTraceCompat)

open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve

section PoleWindowShift

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

theorem coe_smul_K (c : K) (x : u.adicCompletionIntegers) :
    ((c • x : u.adicCompletionIntegers) : u.adicCompletion) = c • (x : u.adicCompletion) := by
  rw [Algebra.smul_def, Algebra.smul_def]
  rfl

def poleWindowShift (πh : u.adicCompletionIntegers) (M : ℕ) :
    poleWindowKSubmod u πh M →ₗ[K] u.adicCompletionIntegers where
  toFun x := ⟨(πh : u.adicCompletion)^M * (x : u.adicCompletion), x.2⟩
  map_add' x y := by apply Subtype.ext; push_cast; ring
  map_smul' c x := by
    apply Subtype.ext
    rw [coe_smul_K]
    show (πh : u.adicCompletion)^M * (c • (x : u.adicCompletion))
        = c • ((πh : u.adicCompletion)^M * (x : u.adicCompletion))
    rw [mul_smul_comm]

theorem poleWindowShift_injective (πh : u.adicCompletionIntegers) (hπh : Irreducible πh)
    (M : ℕ) : Function.Injective (poleWindowShift u πh M) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  have hπhM0 : (πh : u.adicCompletion)^M ≠ 0 := by
    refine pow_ne_zero M ?_
    intro hz
    exact hπh.ne_zero (Subtype.ext hz)
  have hx0 : (x : u.adicCompletion) = 0 := by
    have := congrArg Subtype.val hx
    push_cast at this
    exact (mul_eq_zero.mp this).resolve_left hπhM0
  exact Subtype.ext hx0

theorem poleWindowShift_surjective (πh : u.adicCompletionIntegers) (hπh : Irreducible πh)
    (M : ℕ) : Function.Surjective (poleWindowShift u πh M) := by
  intro y
  have hπhM0 : (πh : u.adicCompletion)^M ≠ 0 := by
    refine pow_ne_zero M ?_
    intro hz; exact hπh.ne_zero (Subtype.ext hz)
  refine ⟨⟨(y : u.adicCompletion) / (πh : u.adicCompletion)^M, ?_⟩, ?_⟩
  · rw [mem_poleWindowKSubmod_iff, mul_div_cancel₀ _ hπhM0]; exact y.2
  · apply Subtype.ext
    show (πh : u.adicCompletion)^M * ((y : u.adicCompletion) / (πh : u.adicCompletion)^M)
        = (y : u.adicCompletion)
    rw [mul_div_cancel₀ _ hπhM0]

def poleWindowShiftEquiv (πh : u.adicCompletionIntegers) (hπh : Irreducible πh) (M : ℕ) :
    poleWindowKSubmod u πh M ≃ₗ[K] u.adicCompletionIntegers :=
  LinearEquiv.ofBijective (poleWindowShift u πh M)
    ⟨poleWindowShift_injective u πh hπh M, poleWindowShift_surjective u πh hπh M⟩

def piPowKSubmod (πh : u.adicCompletionIntegers) (M : ℕ) :
    Submodule K u.adicCompletionIntegers where
  carrier := {y | ∃ x : u.adicCompletionIntegers, y = πh^M * x}
  add_mem' := by rintro a b ⟨xa, rfl⟩ ⟨xb, rfl⟩; exact ⟨xa + xb, by ring⟩
  zero_mem' := ⟨0, by ring⟩
  smul_mem' c y := by
    rintro ⟨x, rfl⟩
    exact ⟨c • x, by rw [Algebra.smul_def, Algebra.smul_def, mul_left_comm]⟩

theorem poleWindowShift_image_integers (πh : u.adicCompletionIntegers) (M : ℕ) :
    Submodule.map (poleWindowShift u πh M)
        ((adicIntegersKSubmod u).comap (poleWindowKSubmod u πh M).subtype)
      = piPowKSubmod u πh M := by
  ext y
  constructor
  · rintro ⟨⟨x, hxP⟩, hxA, rfl⟩
    refine ⟨⟨(x : u.adicCompletion), hxA⟩, ?_⟩
    apply Subtype.ext; push_cast; rfl
  · rintro ⟨x, rfl⟩
    refine ⟨⟨(x : u.adicCompletion),
      adicIntegersKSubmod_le_poleWindowKSubmod u πh M x.2⟩, x.2, ?_⟩
    apply Subtype.ext; push_cast; rfl

variable (K L) in

def KwF4gRRTateDVRQuotPowKFinite : Prop :=
  ∀ (u : Place K L) [u.FiniteResidue] (πh : u.adicCompletionIntegers) (_ : Irreducible πh)
    (M : ℕ),
    FiniteDimensional K (u.adicCompletionIntegers ⧸ piPowKSubmod u πh M)

theorem kwF4gRRTate_poleWindowFinite_of_DVRQuotPowKFinite
    (hDVR : KwF4gRRTateDVRQuotPowKFinite K L) :
    KwF4gRRTatePoleWindowFinite K L := by
  intro u _ πh hπh M
  haveI := hDVR u πh hπh M

  have e := (poleWindowShiftEquiv u πh hπh M).toLinearMap
  let e' := Submodule.Quotient.equiv
    ((adicIntegersKSubmod u).comap (poleWindowKSubmod u πh M).subtype)
    (piPowKSubmod u πh M)
    (poleWindowShiftEquiv u πh hπh M)
    (poleWindowShift_image_integers u πh M)
  exact FiniteDimensional.of_injective e'.toLinearMap e'.injective

end PoleWindowShift


end ModularCurve.KwF4gRRTate



end


end


end


section
section

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 3200000
set_option linter.unusedSectionVars false

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve.Place
open _root_.LinearMap
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.LinearMap
open _root_.Submodule
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.Submodule
open _root_.ModularCurve.KwF4gRRTate
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.ModularCurve.KwF4gRRTate

noncomputable section

namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateTraceCompat)

namespace KwF4gRRTate

export _root_.ModularCurve.KwF4gRRTate (finrankTrace tateComm tateComm_apply tateCommRestrict tateCommRestrict_apply tateCommTrace tateComm_eq_of_commute adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateTraceCompat)

open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve

section AgreementReduce

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

theorem principalPart_mul_zero_of_mem_integers
    {gh : u.adicCompletion} (hgh : gh ∈ u.adicCompletionIntegers)
    {a : u.adicCompletion} (ha : a ∈ u.adicCompletionIntegers) :
    gh * a - tateProj u (gh * a) = 0 := by
  rw [tateProj_of_mem u (mul_mem hgh ha), sub_self]

theorem tateCommRestrict_single_term
    {gh : u.adicCompletion} (hgh : gh ∈ u.adicCompletionIntegers)
    (fh : u.adicCompletion) (a : LinearMap.range (tateProj u)) :
    (tateCommRestrict (tateProj u) (lmulK u fh) (lmulK u gh) a : u.adicCompletion)
      = tateProj u (gh * (fh * (a : u.adicCompletion)
          - tateProj u (fh * (a : u.adicCompletion)))) := by
  have haInt : (a : u.adicCompletion) ∈ u.adicCompletionIntegers :=
    (range_tateProj u ▸ a.2 : (a : u.adicCompletion) ∈ adicIntegersKSubmod u)
  have hcomm : lmulK u fh ∘ₗ lmulK u gh = lmulK u gh ∘ₗ lmulK u fh := by
    refine LinearMap.ext fun x => ?_; show fh * (gh * x) = gh * (fh * x); ring
  rw [tateCommRestrict_apply, tateComm_eq_of_commute hcomm]
  show tateProj u (gh * (fh * ↑a - tateProj u (fh * ↑a)))
      - tateProj u (fh * (gh * ↑a - tateProj u (gh * ↑a)))
    = tateProj u (gh * (fh * ↑a - tateProj u (fh * ↑a)))
  rw [principalPart_mul_zero_of_mem_integers u hgh haInt, mul_zero, _root_.map_zero, sub_zero]

end AgreementReduce


end ModularCurve.KwF4gRRTate



end


end


end


section
section

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 3200000
set_option linter.unusedSectionVars false

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve.Place
open _root_.LinearMap
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.LinearMap
open _root_.Submodule
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.Submodule
open _root_.ModularCurve.KwF4gRRTate
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.ModularCurve.KwF4gRRTate

noncomputable section

namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateTraceCompat)

namespace KwF4gRRTate

export _root_.ModularCurve.KwF4gRRTate (finrankTrace tateComm tateComm_apply tateCommRestrict tateCommRestrict_apply tateCommTrace tateComm_eq_of_commute adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateTraceCompat)

open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve

section FinrankTraceCyclicity

variable {K M N : Type*} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

theorem range_comp_map_left (f : M →ₗ[K] N) (g : N →ₗ[K] M) :
    ∀ x ∈ LinearMap.range (g ∘ₗ f), f x ∈ LinearMap.range (f ∘ₗ g) := by
  rintro x ⟨y, rfl⟩
  exact ⟨f y, rfl⟩

theorem finrankTrace_comp_comm (f : M →ₗ[K] N) (g : N →ₗ[K] M)
    [FiniteDimensional K (LinearMap.range (g ∘ₗ f))]
    [FiniteDimensional K (LinearMap.range (f ∘ₗ g))] :
    finrankTrace (g ∘ₗ f) = finrankTrace (f ∘ₗ g) := by
  set W := LinearMap.range (g ∘ₗ f)
  set W' := LinearMap.range (f ∘ₗ g)

  let fR : W →ₗ[K] W' := f.restrict (range_comp_map_left f g)
  let gR : W' →ₗ[K] W := g.restrict (range_comp_map_left g f)

  have hgf : (g ∘ₗ f).restrict (fun x _ => LinearMap.mem_range_self _ x) = gR ∘ₗ fR := by
    apply LinearMap.ext; intro x; apply Subtype.ext; rfl
  have hfg : (f ∘ₗ g).restrict (fun x _ => LinearMap.mem_range_self _ x) = fR ∘ₗ gR := by
    apply LinearMap.ext; intro x; apply Subtype.ext; rfl
  unfold finrankTrace
  rw [hgf, hfg, LinearMap.trace_comp_comm']

end FinrankTraceCyclicity


end ModularCurve.KwF4gRRTate



end


end


end


section
section

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 3200000
set_option linter.unusedSectionVars false

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve.Place
open _root_.LinearMap
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.LinearMap
open _root_.Submodule
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.Submodule
open _root_.ModularCurve.KwF4gRRTate
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.ModularCurve.KwF4gRRTate

noncomputable section

namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateTraceCompat)

namespace KwF4gRRTate

export _root_.ModularCurve.KwF4gRRTate (finrankTrace tateComm tateComm_apply tateCommRestrict tateCommRestrict_apply tateCommTrace tateComm_eq_of_commute adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateTraceCompat)

open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve

section DeltaLemmas

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (pA pA' : V →ₗ[K] V)

structure SameRangeIdemProjectors : Prop where
  idem_pA : ∀ x, pA (pA x) = pA x
  idem_pA' : ∀ x, pA' (pA' x) = pA' x
  range_eq : LinearMap.range pA = LinearMap.range pA'

variable {pA pA'}

theorem pA_fixes_range (h : SameRangeIdemProjectors pA pA') :
    ∀ x ∈ LinearMap.range pA, pA x = x := by
  rintro x ⟨y, rfl⟩; exact h.idem_pA y

theorem pA'_fixes_range (h : SameRangeIdemProjectors pA pA') :
    ∀ x ∈ LinearMap.range pA, pA' x = x := by
  rintro x hx
  rw [h.range_eq] at hx
  obtain ⟨y, rfl⟩ := hx
  exact h.idem_pA' y

theorem delta_zero_on_range (h : SameRangeIdemProjectors pA pA')
    {x : V} (hx : x ∈ LinearMap.range pA) :
    (pA - pA') x = 0 := by
  simp only [LinearMap.sub_apply, pA_fixes_range h x hx, pA'_fixes_range h x hx, sub_self]

theorem delta_range_subset (h : SameRangeIdemProjectors pA pA')
    (x : V) : (pA - pA') x ∈ LinearMap.range pA := by
  simp only [LinearMap.sub_apply]
  refine sub_mem (LinearMap.mem_range_self pA x) ?_
  rw [h.range_eq]; exact LinearMap.mem_range_self pA' x

end DeltaLemmas


section Mint

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

def KwF4gRRTateProjectorIndep : Prop :=
  ∀ (u : Place K L) (pA' : u.adicCompletion →ₗ[K] u.adicCompletion),
    SameRangeIdemProjectors (tateProj u) pA' →
    ∀ (fh gh : u.adicCompletion), gh ∈ u.adicCompletionIntegers →
    ∀ [FiniteDimensional K (LinearMap.range
        (tateCommRestrict (tateProj u) (lmulK u fh) (lmulK u gh)))]
      [FiniteDimensional K (LinearMap.range
        (tateCommRestrict pA' (lmulK u fh) (lmulK u gh)))],
    tateCommTrace (tateProj u) (lmulK u fh) (lmulK u gh)
      = tateCommTrace pA' (lmulK u fh) (lmulK u gh)

end Mint


section DiffComputation

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)
variable (pA' : u.adicCompletion →ₗ[K] u.adicCompletion)

theorem tateCommRestrict_diff
    (h : SameRangeIdemProjectors (tateProj u) pA')
    {gh : u.adicCompletion} (hgh : gh ∈ u.adicCompletionIntegers)
    (fh : u.adicCompletion) (a : LinearMap.range (tateProj u)) :
    (tateCommRestrict (tateProj u) (lmulK u fh) (lmulK u gh) a : u.adicCompletion)
      - tateComm pA' (lmulK u fh) (lmulK u gh) (a : u.adicCompletion)
      = (tateProj u - pA') (gh * fh * (a : u.adicCompletion))
        - gh * (tateProj u - pA') (fh * (a : u.adicCompletion)) := by

  have haO : (a : u.adicCompletion) ∈ u.adicCompletionIntegers :=
    (range_tateProj u ▸ a.2 : (a : u.adicCompletion) ∈ adicIntegersKSubmod u)

  have hmemO_of_rangeP : ∀ {x : u.adicCompletion},
      x ∈ LinearMap.range (tateProj u) → x ∈ u.adicCompletionIntegers := fun {x} hx =>
    (range_tateProj u ▸ hx : x ∈ adicIntegersKSubmod u)
  have hmemP_of_O : ∀ {x : u.adicCompletion},
      x ∈ u.adicCompletionIntegers → x ∈ LinearMap.range (tateProj u) := fun {x} hx => by
    rw [range_tateProj u]; exact hx

  rw [tateCommRestrict_single_term u hgh fh a]

  have hcomm : lmulK u fh ∘ₗ lmulK u gh = lmulK u gh ∘ₗ lmulK u fh := by
    refine LinearMap.ext fun x => ?_; show fh * (gh * x) = gh * (fh * x); ring
  have hghaP : gh * (a : u.adicCompletion) ∈ LinearMap.range (tateProj u) :=
    hmemP_of_O (mul_mem hgh haO)
  have hpA'_gha : pA' (gh * (a : u.adicCompletion)) = gh * (a : u.adicCompletion) :=
    pA'_fixes_range h _ hghaP
  have hpA'_single :
      tateComm pA' (lmulK u fh) (lmulK u gh) (a : u.adicCompletion)
      = pA' (gh * (fh * (a : u.adicCompletion)
          - pA' (fh * (a : u.adicCompletion)))) := by
    rw [tateComm_eq_of_commute hcomm]
    show pA' (gh * (fh * ↑a - pA' (fh * ↑a)))
        - pA' (fh * (gh * ↑a - pA' (gh * ↑a)))
      = pA' (gh * (fh * ↑a - pA' (fh * ↑a)))
    rw [hpA'_gha, sub_self, mul_zero, _root_.map_zero, sub_zero]
  rw [hpA'_single]

  set fa := fh * (a : u.adicCompletion)

  have hPfaO : tateProj u fa ∈ u.adicCompletionIntegers :=
    hmemO_of_rangeP (LinearMap.mem_range_self (tateProj u) fa)
  have hPfaO' : pA' fa ∈ u.adicCompletionIntegers :=
    hmemO_of_rangeP (h.range_eq ▸ LinearMap.mem_range_self pA' fa)

  have hghPfa : tateProj u (gh * tateProj u fa) = gh * tateProj u fa :=
    tateProj_of_mem u (mul_mem hgh hPfaO)
  have hghPfa' : pA' (gh * pA' fa) = gh * pA' fa :=
    pA'_fixes_range h _ (hmemP_of_O (mul_mem hgh hPfaO'))

  rw [mul_sub, map_sub, mul_sub, map_sub, hghPfa, hghPfa']
  simp only [LinearMap.sub_apply]
  rw [show gh * fh * (a : u.adicCompletion) = gh * fa from (mul_assoc gh fh _).symm ▸ rfl]
  ring

end DiffComputation


end ModularCurve.KwF4gRRTate



end


end


end


section
section

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 3200000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve.Place
open _root_.LinearMap
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.LinearMap
open _root_.Submodule
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.Submodule
open _root_.ModularCurve.KwF4gRRTate
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.ModularCurve.KwF4gRRTate

noncomputable section

namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateTraceCompat)

namespace KwF4gRRTate

export _root_.ModularCurve.KwF4gRRTate (finrankTrace tateComm tateComm_apply tateCommRestrict tateCommRestrict_apply tateCommTrace tateComm_eq_of_commute adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateTraceCompat)

open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve

section TraceOnSuperspace

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem finrankTrace_eq_trace_on_superspace
    (φ : V →ₗ[K] V) (W : Submodule K V) [FiniteDimensional K W]
    (hrange : LinearMap.range φ ≤ W) (hW : ∀ x ∈ W, φ x ∈ W) :
    haveI : FiniteDimensional K (LinearMap.range φ) :=
      Submodule.finiteDimensional_of_le hrange
    finrankTrace φ = LinearMap.trace K W (φ.restrict hW) := by
  haveI : FiniteDimensional K (LinearMap.range φ) := Submodule.finiteDimensional_of_le hrange

  let i : LinearMap.range φ →ₗ[K] W := Submodule.inclusion hrange

  let π : W →ₗ[K] LinearMap.range φ :=
    { toFun := fun w => ⟨φ (w : V), LinearMap.mem_range_self φ (w : V)⟩
      map_add' := fun w₁ w₂ => by simp [Subtype.ext_iff]
      map_smul' := fun c w => by simp [Subtype.ext_iff] }

  have hip : i ∘ₗ π = φ.restrict hW := by
    apply LinearMap.ext; intro w; apply Subtype.ext; rfl

  have hpi : π ∘ₗ i = φ.restrict (fun x _ => LinearMap.mem_range_self φ x) := by
    apply LinearMap.ext; intro x; apply Subtype.ext; rfl
  unfold finrankTrace
  rw [← hpi, ← hip, LinearMap.trace_comp_comm']

end TraceOnSuperspace


section Additivity

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem finrankTrace_sub_eq
    (φ ψ : V →ₗ[K] V)
    [FiniteDimensional K (LinearMap.range φ)]
    [FiniteDimensional K (LinearMap.range ψ)] :
    haveI : FiniteDimensional K
        ((LinearMap.range φ ⊔ LinearMap.range ψ : Submodule K V) : Type _) :=
      Submodule.finiteDimensional_sup _ _
    finrankTrace φ - finrankTrace ψ
      = LinearMap.trace K (LinearMap.range φ ⊔ LinearMap.range ψ : Submodule K V)
          ((φ - ψ).restrict
            (p := (LinearMap.range φ ⊔ LinearMap.range ψ : Submodule K V))
            (fun x _ => sub_mem
              (Submodule.mem_sup_left (LinearMap.mem_range_self φ x))
              (Submodule.mem_sup_right (LinearMap.mem_range_self ψ x)))) := by
  set W' : Submodule K V := LinearMap.range φ ⊔ LinearMap.range ψ with hW'
  haveI : FiniteDimensional K W' := Submodule.finiteDimensional_sup _ _
  have hφW : ∀ x ∈ W', φ x ∈ W' := fun x _ =>
    Submodule.mem_sup_left (LinearMap.mem_range_self φ x)
  have hψW : ∀ x ∈ W', ψ x ∈ W' := fun x _ =>
    Submodule.mem_sup_right (LinearMap.mem_range_self ψ x)
  rw [finrankTrace_eq_trace_on_superspace φ W' le_sup_left hφW,
    finrankTrace_eq_trace_on_superspace ψ W' le_sup_right hψW,
    ← map_sub]

  refine congrArg (LinearMap.trace K W') (LinearMap.ext fun x => Subtype.ext ?_)
  rfl

end Additivity


end ModularCurve.KwF4gRRTate



end


end


end


section
section

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 3200000
set_option linter.unusedSectionVars false

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve.Place
open _root_.LinearMap
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.LinearMap
open _root_.Submodule
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.Submodule
open _root_.ModularCurve.KwF4gRRTate
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.ModularCurve.KwF4gRRTate
open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.IsDedekindDomain
open _root_.IsDedekindDomain.HeightOneSpectrum
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.IsDedekindDomain.HeightOneSpectrum
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.IsLocalRing

noncomputable section

namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateTraceCompat)

namespace KwF4gRRTate

export _root_.ModularCurve.KwF4gRRTate (finrankTrace tateComm tateComm_apply tateCommRestrict tateCommRestrict_apply tateCommTrace tateComm_eq_of_commute adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateTraceCompat)

open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve

section DVRQuotDischarge

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

theorem piPowKSubmod_eq_restrictScalars (πh : u.adicCompletionIntegers) (M : ℕ) :
    piPowKSubmod u πh M
      = (Ideal.span {πh^M} : Ideal u.adicCompletionIntegers).restrictScalars K := by
  ext y
  rw [Submodule.restrictScalars_mem, Ideal.mem_span_singleton]
  exact ⟨fun ⟨x, h⟩ => ⟨x, h⟩, fun ⟨x, h⟩ => ⟨x, h⟩⟩

def quotPiPowEquivIdealQuot (πh : u.adicCompletionIntegers) (M : ℕ) :
    (u.adicCompletionIntegers ⧸ piPowKSubmod u πh M)
      ≃ₗ[K] (u.adicCompletionIntegers ⧸ (Ideal.span {πh^M} : Ideal u.adicCompletionIntegers)) :=
  (Submodule.quotEquivOfEq _ _ (piPowKSubmod_eq_restrictScalars u πh M)).trans
    (Submodule.Quotient.restrictScalarsEquiv K _)

variable (K L) in

def KwF4gRRTateDVRCotangentKFinite : Prop :=
  ∀ (u : Place K L) [u.FiniteResidue] (πh : u.adicCompletionIntegers) (_ : Irreducible πh),
    FiniteDimensional K
      (u.adicCompletionIntegers ⧸ (Ideal.span {πh} : Ideal u.adicCompletionIntegers))

theorem range_mulLeft_eq_restrictScalars_span (a : u.adicCompletionIntegers) :
    LinearMap.range (LinearMap.mulLeft K a)
      = (Ideal.span {a} : Ideal u.adicCompletionIntegers).restrictScalars K := by
  ext y
  simp only [LinearMap.mem_range, LinearMap.mulLeft_apply, Submodule.restrictScalars_mem,
    Ideal.mem_span_singleton]
  exact ⟨fun ⟨x, hx⟩ => ⟨x, hx.symm⟩, fun ⟨x, hx⟩ => ⟨x, hx.symm⟩⟩

set_option maxHeartbeats 25600000 in

theorem finiteDimensional_restrictScalarsQuot_pow [u.FiniteResidue]
    (hCot : KwF4gRRTateDVRCotangentKFinite K L)
    (πh : u.adicCompletionIntegers) (hπh : Irreducible πh) (M : ℕ) :
    FiniteDimensional K (u.adicCompletionIntegers ⧸
      (Ideal.span {πh^M} : Ideal u.adicCompletionIntegers).restrictScalars K) := by
  induction M with
  | zero =>
    rw [pow_zero, Ideal.span_singleton_one, Submodule.restrictScalars_top]
    infer_instance
  | succ M ih =>
    have hle : (Ideal.span {πh^(M+1)} : Ideal u.adicCompletionIntegers)
        ≤ Ideal.span {πh^M} := by
      rw [Ideal.span_singleton_le_span_singleton, pow_succ]; exact ⟨πh, rfl⟩
    have hle' : (Ideal.span {πh^(M+1)} : Ideal u.adicCompletionIntegers).restrictScalars K
        ≤ (Ideal.span {πh^M} : Ideal u.adicCompletionIntegers).restrictScalars K :=
      Submodule.restrictScalars_mono K hle

    set N : Submodule K (u.adicCompletionIntegers ⧸
        (Ideal.span {πh^(M+1)} : Ideal u.adicCompletionIntegers).restrictScalars K) :=
      (Submodule.restrictScalars K (Ideal.span {πh^M} : Ideal u.adicCompletionIntegers)).map
        (Submodule.restrictScalars K (Ideal.span {πh^(M+1)} : Ideal _)).mkQ with hN_def

    haveI hquot : FiniteDimensional K
        ((u.adicCompletionIntegers ⧸
          (Ideal.span {πh^(M+1)} : Ideal _).restrictScalars K) ⧸ N) := by
      haveI := ih
      exact Module.Finite.equiv
        (Submodule.quotientQuotientEquivQuotient _ _ hle').symm

    haveI hN : FiniteDimensional K N := by
      set φ : u.adicCompletionIntegers →ₗ[K] (u.adicCompletionIntegers ⧸
          (Ideal.span {πh^(M+1)} : Ideal u.adicCompletionIntegers).restrictScalars K) :=
        (Submodule.restrictScalars K
            (Ideal.span {πh^(M+1)} : Ideal u.adicCompletionIntegers)).mkQ ∘ₗ
          LinearMap.mulLeft K (πh^M) with hφ_def
      have hrange : LinearMap.range φ = N := by
        rw [hφ_def, LinearMap.range_comp, range_mulLeft_eq_restrictScalars_span, hN_def]
      have hker : LinearMap.ker φ
          = (Ideal.span {πh} : Ideal u.adicCompletionIntegers).restrictScalars K := by
        simp only [hφ_def, LinearMap.ker_comp, Submodule.ker_mkQ]
        ext x
        simp only [Submodule.mem_comap, LinearMap.mulLeft_apply, Submodule.restrictScalars_mem,
          Ideal.mem_span_singleton]
        have hπM : (πh : u.adicCompletionIntegers)^M ≠ 0 := pow_ne_zero M hπh.ne_zero
        constructor
        · rintro ⟨c, hc⟩
          exact ⟨c, mul_left_cancel₀ hπM (by rw [hc, pow_succ, mul_assoc])⟩
        · rintro ⟨c, hc⟩
          exact ⟨c, by rw [hc, pow_succ, mul_assoc]⟩

      let e₁ : (u.adicCompletionIntegers ⧸
            (Ideal.span {πh} : Ideal u.adicCompletionIntegers).restrictScalars K)
          ≃ₗ[K] (u.adicCompletionIntegers ⧸ LinearMap.ker φ) :=
        Submodule.quotEquivOfEq _ _ hker.symm
      let e₂ : (u.adicCompletionIntegers ⧸ LinearMap.ker φ) ≃ₗ[K] LinearMap.range φ :=
        φ.quotKerEquivRange
      let e₃ : (LinearMap.range φ : Submodule K _) ≃ₗ[K] N := LinearEquiv.ofEq _ _ hrange
      haveI hCK : FiniteDimensional K (u.adicCompletionIntegers ⧸
          (Ideal.span {πh} : Ideal u.adicCompletionIntegers).restrictScalars K) := by
        haveI := hCot u πh hπh
        exact Module.Finite.equiv
          (Submodule.Quotient.restrictScalarsEquiv K
            (Ideal.span {πh} : Ideal u.adicCompletionIntegers)).symm
      exact Module.Finite.equiv ((e₁.trans e₂).trans e₃)
    exact Module.Finite.of_submodule_quotient N

theorem finiteDimensional_idealQuot_pow [u.FiniteResidue]
    (hCot : KwF4gRRTateDVRCotangentKFinite K L)
    (πh : u.adicCompletionIntegers) (hπh : Irreducible πh) (M : ℕ) :
    FiniteDimensional K
      (u.adicCompletionIntegers ⧸ (Ideal.span {πh^M} : Ideal u.adicCompletionIntegers)) := by
  haveI := finiteDimensional_restrictScalarsQuot_pow u hCot πh hπh M
  exact Module.Finite.equiv (Submodule.Quotient.restrictScalarsEquiv K _)

theorem kwF4gRRTate_DVRQuotPowKFinite_of_cotangent
    (hCot : KwF4gRRTateDVRCotangentKFinite K L) :
    KwF4gRRTateDVRQuotPowKFinite K L := by
  intro u _ πh hπh M
  haveI := finiteDimensional_idealQuot_pow u hCot πh hπh M
  exact Module.Finite.equiv (quotPiPowEquivIdealQuot u πh M).symm

end DVRQuotDischarge


end ModularCurve.KwF4gRRTate



end


end


end


section
section

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 3200000
set_option linter.unusedSectionVars false

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve.Place
open _root_.LinearMap
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.LinearMap
open _root_.Submodule
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.Submodule
open _root_.ModularCurve.KwF4gRRTate
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.ModularCurve.KwF4gRRTate
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.ModularCurve.KwF4R1V410a
open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.IsDedekindDomain
open _root_.IsDedekindDomain.HeightOneSpectrum
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.IsDedekindDomain.HeightOneSpectrum
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.IsLocalRing

noncomputable section

namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateTraceCompat)

namespace KwF4gRRTate

export _root_.ModularCurve.KwF4gRRTate (finrankTrace tateComm tateComm_apply tateCommRestrict tateCommRestrict_apply tateCommTrace tateComm_eq_of_commute adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateTraceCompat)

open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve

section DVRCotangentDischarge

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

scoped instance instIsScalarTower_K_toValuationSubring_adicCompletionIntegers :
    IsScalarTower K u.toValuationSubring u.adicCompletionIntegers := by
  refine IsScalarTower.of_algebraMap_eq fun k => ?_
  apply Subtype.ext
  show algebraMap K u.adicCompletion k
    = (algebraMap u.toValuationSubring u.adicCompletionIntegers (algebraMap K _ k)).val
  rw [IsScalarTower.algebraMap_apply K L u.adicCompletion]
  rfl

theorem span_irreducible_eq_completionIdeal_pow_one
    (πh : u.adicCompletionIntegers) (hπh : Irreducible πh) :
    (Ideal.span {πh} : Ideal u.adicCompletionIntegers)
      = (u.heightOneSpectrum.completionIdeal L) ^ 1 := by
  rw [pow_one, ← hπh.maximalIdeal_eq]

def quotientEquivKAlg (n : ℕ) :
    (u.toValuationSubring ⧸ (IsLocalRing.maximalIdeal u.toValuationSubring) ^ n)
      ≃ₐ[K] (u.adicCompletionIntegers ⧸ (u.heightOneSpectrum.completionIdeal L) ^ n) :=
  { kwF4R1V410a_quotientEquiv u n with
    commutes' := fun k => by
      show kwF4R1V410a_quotientEquiv u n (algebraMap K _ k) = algebraMap K _ k
      rw [IsScalarTower.algebraMap_apply K u.toValuationSubring
          (u.toValuationSubring ⧸ (IsLocalRing.maximalIdeal u.toValuationSubring) ^ n),
        Ideal.Quotient.algebraMap_eq, kwF4R1V410a_quotientEquiv_mk,
        IsScalarTower.algebraMap_apply K u.adicCompletionIntegers
          (u.adicCompletionIntegers ⧸ (u.heightOneSpectrum.completionIdeal L) ^ n),
        Ideal.Quotient.algebraMap_eq,
        IsScalarTower.algebraMap_apply K u.toValuationSubring u.adicCompletionIntegers] }

def quotSpanIrreducibleEquivResidueField (πh : u.adicCompletionIntegers) (hπh : Irreducible πh) :
    (u.adicCompletionIntegers ⧸ (Ideal.span {πh} : Ideal u.adicCompletionIntegers))
      ≃ₗ[K] u.ResidueField :=
  (Ideal.quotientEquivAlgOfEq K
      (span_irreducible_eq_completionIdeal_pow_one u πh hπh)).toLinearEquiv.trans
    ((quotientEquivKAlg u 1).symm.toLinearEquiv.trans
      (Ideal.quotientEquivAlgOfEq K
        (pow_one (IsLocalRing.maximalIdeal u.toValuationSubring))).toLinearEquiv)

theorem kwF4gRRTate_DVRCotangentKFinite : KwF4gRRTateDVRCotangentKFinite K L := by
  intro u _ πh hπh
  haveI : Module.Finite K u.ResidueField := FiniteResidue.finite
  exact Module.Finite.equiv (quotSpanIrreducibleEquivResidueField u πh hπh).symm

end DVRCotangentDischarge


end ModularCurve.KwF4gRRTate



end


end


end


section
section

set_option maxHeartbeats 12800000
set_option synthInstance.maxHeartbeats 6400000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve.Place
open _root_.LinearMap
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.LinearMap
open _root_.Submodule
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.Submodule
open _root_.ModularCurve.KwF4gRRTate
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.ModularCurve.KwF4gRRTate

noncomputable section

namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateTraceCompat)

namespace KwF4gRRTate

export _root_.ModularCurve.KwF4gRRTate (finrankTrace tateComm tateComm_apply tateCommRestrict tateCommRestrict_apply tateCommTrace tateComm_eq_of_commute adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateTraceCompat)

open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve

section DeltaQuotFactor

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {pA pA' : V →ₗ[K] V}

def deltaQuotFactor (h : SameRangeIdemProjectors pA pA') :
    (V ⧸ LinearMap.range pA) →ₗ[K] LinearMap.range pA :=
  (LinearMap.range pA).liftQ
    (LinearMap.codRestrict (LinearMap.range pA) (pA - pA') (delta_range_subset h))
    (fun x hx => by
      apply Subtype.ext
      exact delta_zero_on_range h hx)

theorem deltaQuotFactor_apply (h : SameRangeIdemProjectors pA pA') (x : V) :
    (deltaQuotFactor h (Submodule.Quotient.mk x) : V) = (pA - pA') x := rfl

end DeltaQuotFactor


section TermRangeFinite

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)
variable [u.FiniteResidue]

def KwF4gRRTatePoleWindowImageFinite : Prop :=
  ∀ (fh : u.adicCompletion),
    FiniteDimensional K (Submodule.map (adicIntegersKSubmod u).mkQ
      (Submodule.map (lmulK u fh) (adicIntegersKSubmod u)))

end TermRangeFinite


section DiffTraceZero

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)
variable (pA' : u.adicCompletion →ₗ[K] u.adicCompletion)

def KwF4gRRTateCommFiniteGen : Prop :=
  ∀ (h : SameRangeIdemProjectors (tateProj u) pA') (fh gh : u.adicCompletion),
    FiniteDimensional K
      (LinearMap.range (tateCommRestrict pA' (lmulK u fh) (lmulK u gh)))

end DiffTraceZero


end ModularCurve.KwF4gRRTate



end


end


end

end P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable
