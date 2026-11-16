/-
Copyright 2026 Anthropic, PBC. Released under Apache License 2.0.
Source: https://github.com/anthropics/fermats-last-theorem
Revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_AlgebraicCurve_tateAgreement.lean; source lines 1-2457.
Includes FLT/Mathlib/RingTheory/LocalRing/MaximalIdeal/Basic.lean material:
Copyright (c) 2025 Salvatore Mercuri. Authors: Salvatore Mercuri, Kevin Buzzard.
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
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CanonicalLocalResidueInstance
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 6400000
set_option maxHeartbeats 12800000

namespace P2MW.S_AlgebraicCurve_tateAgreement

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 6400000
set_option maxHeartbeats 12800000

section
namespace IsLocalRing
export _root_.IsLocalRing (ResidueField maximalIdeal residue_eq_zero_iff maximalIdeal.isMaximal residue_surjective of_injective residue)
end IsLocalRing
open scoped _root_.IsLocalRing in
theorem IsLocalRing.maximalIdeal_le {R : Type*} [CommSemiring R] [IsLocalRing R] {J : Ideal R}
    (hJ : J ≠ ⊤) (h : IsLocalRing.maximalIdeal R ≤ J) :
    J.IsMaximal :=
  (IsLocalRing.maximalIdeal.isMaximal R).eq_of_le hJ h ▸ IsLocalRing.maximalIdeal.isMaximal R
end
namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.FiniteResidue Place.ord Divisor HasPrincipalDivisors Pic0 Place.FiniteResidue.finite IsCurveOver HasCanonicalLocalResidueKStar kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kwHgfV352_localResidueCompletion completionSection_nonempty_generic localResidue_eq_resStar)

open _root_.AlgebraicCurve
end AlgebraicCurve
namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.FiniteResidue Place.ord Divisor HasPrincipalDivisors Pic0 Place.FiniteResidue.finite IsCurveOver HasCanonicalLocalResidueKStar kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kwHgfV352_localResidueCompletion completionSection_nonempty_generic localResidue_eq_resStar)

namespace FiberKaehlerLocalDatum
open _root_.AlgebraicCurve
end AlgebraicCurve.FiberKaehlerLocalDatum
namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.FiniteResidue Place.ord Divisor HasPrincipalDivisors Pic0 Place.FiniteResidue.finite IsCurveOver HasCanonicalLocalResidueKStar kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kwHgfV352_localResidueCompletion completionSection_nonempty_generic localResidue_eq_resStar)

namespace Place

export _root_.AlgebraicCurve.Place (ext ResidueField FiniteResidue heightOneSpectrum heightOneSpectrum_asIdeal adicValuation adicValuation_ne_zero ord ord_zero ord_mul ord_unit_smul_zpow exists_unit_mul_zpow FiniteResidue.finite algebraMap_mem' toValuationSubring mk DCoordGenerates uniformizer ord_uniformizer uniformizer_ne_zero localResidue localResidue_eq_zero_of_ord_nonneg restrict adicCompletion adicCompletionIntegers uniformizerSubring coe_uniformizerSubring uniformizerSubring_mem_maximalIdeal uniformizer_mem poleSubmodule mem_poleSubmodule mem_poleSubmodule_iff_ord)

open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve
end AlgebraicCurve.Place
namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.FiniteResidue Place.ord Divisor HasPrincipalDivisors Pic0 Place.FiniteResidue.finite IsCurveOver HasCanonicalLocalResidueKStar kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kwHgfV352_localResidueCompletion completionSection_nonempty_generic localResidue_eq_resStar)

namespace RationalFunctionField
open _root_.AlgebraicCurve.RationalFunctionField
open _root_.AlgebraicCurve
end AlgebraicCurve.RationalFunctionField
namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (Surjective IsIntegral)

open _root_.AlgebraicGeometry
end AlgebraicGeometry
namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (Surjective IsIntegral)

namespace KwSmoothIrredRelDimConstantEngine
open _root_.AlgebraicGeometry
end AlgebraicGeometry.KwSmoothIrredRelDimConstantEngine
namespace BigOperators
open _root_.BigOperators
end BigOperators
namespace CategoryTheory

export _root_.CategoryTheory (inclusion Quotient Injective exp Quotient.equiv comp_apply id_apply sum Quotient.mk)

open _root_.CategoryTheory
end CategoryTheory
namespace CategoryTheory

export _root_.CategoryTheory (inclusion Quotient Injective exp Quotient.equiv comp_apply id_apply sum Quotient.mk)

namespace Limits

export _root_.CategoryTheory.Limits (span ker)

open _root_.CategoryTheory.Limits
open _root_.CategoryTheory
end CategoryTheory.Limits
namespace Classical

export _root_.Classical (choose_spec em choose)

open _root_.Classical
end Classical
namespace CongruenceSubgroup
open _root_.CongruenceSubgroup
end CongruenceSubgroup
namespace Deformation
namespace ModpDieudonne
end Deformation.ModpDieudonne
namespace Deformation
namespace PDivisible
end Deformation.PDivisible
namespace FLT
namespace HopfSpec
end FLT.HopfSpec
namespace Filter

export _root_.Filter (mem_bot ker eventually_atTop mk mem_comap map_top atTop mem_ker mem_sup mem_top comap unique map_mono map)

open _root_.Filter
end Filter
namespace FunctionField
open _root_.FunctionField
end FunctionField
namespace GoodReductionJacobian
end GoodReductionJacobian
namespace IntermediateField

export _root_.IntermediateField (mk val lift inclusion ext algebraMap_apply smul_def mem_inf finiteDimensional_sup comap mem_top restrictScalars restrictScalars_top mem_bot map_mono restrict map)

open _root_.IntermediateField
end IntermediateField
namespace IsDedekindDomain

export _root_.IsDedekindDomain (HeightOneSpectrum.ext mk HeightOneSpectrum)

open _root_.IsDedekindDomain
end IsDedekindDomain
namespace IsDedekindDomain

export _root_.IsDedekindDomain (HeightOneSpectrum.ext mk HeightOneSpectrum)

namespace HeightOneSpectrum

export _root_.IsDedekindDomain.HeightOneSpectrum (valuation_of_algebraMap intValuation_le_pow_iff_mem isMaximal mk mem_adicCompletionIntegers comap valuedAdicCompletion_eq_valuation' adicCompletion valuation adicCompletionIntegers valuedAdicCompletion_surjective mem_integers_of_valuation_le_one denseRange_algebraMap intValuation exists_ofAdd_natCast_lt completionIdeal adicCompletion.maximalIdeal_eq_span_uniformizer adicCompletion.mem_completionIdeal_pow)

open _root_.IsDedekindDomain.HeightOneSpectrum
open _root_.IsDedekindDomain
end IsDedekindDomain.HeightOneSpectrum
namespace IsLocalRing

export _root_.IsLocalRing (ResidueField maximalIdeal residue_eq_zero_iff maximalIdeal.isMaximal residue_surjective of_injective residue)

open _root_.IsLocalRing
end IsLocalRing
namespace KaehlerDifferential

export _root_.KaehlerDifferential (finite D map)

open _root_.KaehlerDifferential
end KaehlerDifferential
namespace Ldgr23CohenDefectCorrectionSlice
end Ldgr23CohenDefectCorrectionSlice
namespace Ldgr24DefectKernelSlice
end Ldgr24DefectKernelSlice
namespace Ldgr25CorrectedChoiceSlice
end Ldgr25CorrectedChoiceSlice
namespace Ldgr30BankGate
end Ldgr30BankGate
namespace LinearMap

export _root_.LinearMap (mulLeft_apply mem_range range sub_apply ker_eq_bot id range_comp codRestrict inr mulLeft ker_comp trace_comp_comm' mk coe_coe id_apply finiteDimensional_range ext comp trace quotKerEquivRange finiteDimensional range_comp_le_range single lsum restrictScalars ker mem_ker comp_apply trace_conj' mem_range_self restrict)

open _root_.LinearMap
end LinearMap
namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateAgreement)

open _root_.ModularCurve
end ModularCurve
namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateAgreement)

namespace KwF4R1V391a
open _root_.ModularCurve.KwF4R1V391a
open _root_.ModularCurve
end ModularCurve.KwF4R1V391a
namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateAgreement)

namespace KwF4R1V392a
open _root_.ModularCurve
end ModularCurve.KwF4R1V392a
namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateAgreement)

namespace KwF4R1V394a
open _root_.ModularCurve
end ModularCurve.KwF4R1V394a
namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateAgreement)

namespace KwF4R1V410a
open _root_.ModularCurve
end ModularCurve.KwF4R1V410a
namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateAgreement)

namespace KwF4gRRTate

export _root_.ModularCurve.KwF4gRRTate (finrankTrace tateComm tateCommRestrict tateCommRestrict_apply tateCommTrace tateComm_eq_of_commute adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateAgreement)

open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve
end ModularCurve.KwF4gRRTate
namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateAgreement)

namespace KwNo6HrouteR
open _root_.ModularCurve
end ModularCurve.KwNo6HrouteR
namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateAgreement)

namespace KwNo6HrouteS
open _root_.ModularCurve
end ModularCurve.KwNo6HrouteS
namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateAgreement)

namespace KwNo6HrouteV
open _root_.ModularCurve
end ModularCurve.KwNo6HrouteV
namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateAgreement)

namespace KwNo6HrouteY
open _root_.ModularCurve
end ModularCurve.KwNo6HrouteY
namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateAgreement)

namespace KwNo6HrouteZ
open _root_.ModularCurve
end ModularCurve.KwNo6HrouteZ
namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateAgreement)

namespace KwNo6Pin

export _root_.ModularCurve.KwNo6Pin (aCoeff aCoeff_zero aCoeff_add aCoeff_shift aCoeff_shift_pow clearedHat resStar aCoeff_clearedHat_of_le resStar_simplePole resStar_higherPoleMonomial)

open _root_.ModularCurve.KwNo6Pin
open _root_.ModularCurve
end ModularCurve.KwNo6Pin
namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateAgreement)

namespace KwNo6Section
open _root_.ModularCurve.KwNo6Section
open _root_.ModularCurve
end ModularCurve.KwNo6Section
namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateAgreement)

namespace KwOdaDHDR
open _root_.ModularCurve
end ModularCurve.KwOdaDHDR
namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateAgreement)

namespace KwTateRR3
open _root_.ModularCurve
end ModularCurve.KwTateRR3
namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateAgreement)

namespace GF24a11bRowACurrencyBridge
open _root_.ModularCurve
end ModularCurve.GF24a11bRowACurrencyBridge
namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateAgreement)

namespace GF24a12CohenSupply
open _root_.ModularCurve
end ModularCurve.GF24a12CohenSupply
namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateAgreement)

namespace GF24a9RRDx
open _root_.ModularCurve
end ModularCurve.GF24a9RRDx
namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateAgreement)

namespace Ldgr25CotraceCompatSlice
open _root_.ModularCurve
end ModularCurve.Ldgr25CotraceCompatSlice
namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateAgreement)

namespace Ldgr25PlaceExtensionSlice
open _root_.ModularCurve
end ModularCurve.Ldgr25PlaceExtensionSlice
namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateAgreement)

namespace Ldgr29SimplePoleResidueSlice
open _root_.ModularCurve
end ModularCurve.Ldgr29SimplePoleResidueSlice
namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateAgreement)

namespace Ldgr31PerPlaceRowJoinSlice
open _root_.ModularCurve
end ModularCurve.Ldgr31PerPlaceRowJoinSlice
namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateAgreement)

namespace Ldgr32RegularLegSlice
open _root_.ModularCurve
end ModularCurve.Ldgr32RegularLegSlice
namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateAgreement)

namespace Ldgr35Cs
open _root_.ModularCurve.Ldgr35Cs
open _root_.ModularCurve
end ModularCurve.Ldgr35Cs
namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateAgreement)

namespace Ldgr36Rc
open _root_.ModularCurve.Ldgr36Rc
open _root_.ModularCurve
end ModularCurve.Ldgr36Rc
namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateAgreement)

namespace Ldgr36Si
open _root_.ModularCurve.Ldgr36Si
open _root_.ModularCurve
end ModularCurve.Ldgr36Si
namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateAgreement)

namespace Lg37

export _root_.ModularCurve.Lg37 (lg37_completion lg37_residueHat lg37_residueHat_algebraMap Lg37CompletionSection)

open _root_.ModularCurve.Lg37
open _root_.ModularCurve
end ModularCurve.Lg37
namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateAgreement)

namespace Mp72a102T3

export _root_.ModularCurve.Mp72a102T3 (mp72a102_t3_evalₐ_zero_depth mp72a102_t3_evalₐ_factor mp72a102_t3_evalₐ_succ_mul_eq_zero mp72a102_t3_evalDepth_mul mp72a102_t3_sigma_taylor_expansion)

open _root_.ModularCurve.Mp72a102T3
open _root_.ModularCurve
end ModularCurve.Mp72a102T3
namespace Modularity
namespace Ldgr26CorrectedRowsBandSlice
end Modularity.Ldgr26CorrectedRowsBandSlice
namespace Modularity
namespace Ldgr27TraceSemilinearSlice
end Modularity.Ldgr27TraceSemilinearSlice
namespace Module

export _root_.Module (Injective support equiv Finite.equiv mk restrictScalars Finite.of_submodule_quotient mem_support_iff notMem_support_iff)

open _root_.Module
end Module
namespace MonoidWithZeroHom

export _root_.MonoidWithZeroHom (id_apply id ext mk ValueGroup₀ coe_coe comp_apply ValueGroup₀.embedding ValueGroup₀.embedding_strictMono comp inr)

open _root_.MonoidWithZeroHom
end MonoidWithZeroHom
namespace Mp72a102T1
open _root_.Mp72a102T1
end Mp72a102T1
namespace Mp72a102T2
open _root_.Mp72a102T2
end Mp72a102T2
namespace Mp72a103T2

export _root_.Mp72a103T2 (mp72a103_t2_taylor_coeff_eq_zero_of_depth)

open _root_.Mp72a103T2
end Mp72a103T2
namespace Multiplicative

export _root_.Multiplicative (ext)

open _root_.Multiplicative
end Multiplicative
namespace NeronModelInfra
end NeronModelInfra
namespace NeronOggShafarevich
end NeronOggShafarevich
namespace NumberField

export _root_.NumberField (mk)

open _root_.NumberField
end NumberField
namespace Order

export _root_.Order (lt_succ_iff succ one_le_iff_ne_zero Ideal)

open _root_.Order
end Order
namespace PadicInt

export _root_.PadicInt (lift valuation coe_sub ext algebraMap_apply)

open _root_.PadicInt
end PadicInt
namespace Pointwise
open _root_.Pointwise
end Pointwise
namespace Polynomial

export _root_.Polynomial (C support algebraMap_eq unique lsum ext_iff map comp sum coe_sub mem_support_iff notMem_support_iff erase algebraMap_apply ext ring)

open _root_.Polynomial
end Polynomial
namespace RationalFunctionField
end RationalFunctionField
namespace Submodule

export _root_.Submodule (quotEquivOfEq inclusion mem_sup_right map_top smul_mem' mk mem_bot coe_mem Quotient.mk span restrictScalars projectionOnto_apply_left restrictScalars_top mem_closure_iff Quotient.restrictScalarsEquiv mem_comap injective_subtype mem_top Quotient.equiv mem_span_singleton mkQ map_mono map_smul' equivMapOfInjective zero map_add_le quotientQuotientEquivQuotient range_subtype disjoint_def Quotient.mk_surjective restrictScalars_mono map mem_inf inclusion_apply mem_sup Quotient.mk_eq_zero exists_isCompl projectionOnto finiteDimensional_of_le smul_def mk_eq_zero restrictScalarsEquiv mkQ_apply ext factor_mk subtype_apply ker_mkQ comap factorPow finiteDimensional_sup projectionOnto_apply_right liftQ mem_sup_left restrictScalars_mem)

open _root_.Submodule
end Submodule
namespace TensorProduct

export _root_.TensorProduct (congr lift mk ext map Algebra.smul_def mk_surjective)

open _root_.TensorProduct
end TensorProduct
namespace Topology
open _root_.Topology
end Topology
namespace WithZero

export _root_.WithZero (map exp_lt_exp exp_eq_coe_ofAdd exp_neg coe exp_ne_zero exp exp_zero exp_add lift le exp_nsmul exp_le_exp exp_log)

open _root_.WithZero
end WithZero

section
section

set_option maxHeartbeats 6400000
set_option linter.unusedSectionVars false

open _root_.LinearMap
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.LinearMap
open _root_.Submodule
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.Submodule

noncomputable section

namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateAgreement)

namespace KwF4gRRTate

export _root_.ModularCurve.KwF4gRRTate (finrankTrace tateComm tateCommRestrict tateCommRestrict_apply tateCommTrace tateComm_eq_of_commute adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateAgreement)

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
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.WithZero
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.IsLocalRing

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.FiniteResidue Place.ord Divisor HasPrincipalDivisors Pic0 Place.FiniteResidue.finite IsCurveOver HasCanonicalLocalResidueKStar kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kwHgfV352_localResidueCompletion completionSection_nonempty_generic localResidue_eq_resStar)

open _root_.AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

namespace Place

export _root_.AlgebraicCurve.Place (ext ResidueField FiniteResidue heightOneSpectrum heightOneSpectrum_asIdeal adicValuation adicValuation_ne_zero ord ord_zero ord_mul ord_unit_smul_zpow exists_unit_mul_zpow FiniteResidue.finite algebraMap_mem' toValuationSubring mk DCoordGenerates uniformizer ord_uniformizer uniformizer_ne_zero localResidue localResidue_eq_zero_of_ord_nonneg restrict adicCompletion adicCompletionIntegers uniformizerSubring coe_uniformizerSubring uniformizerSubring_mem_maximalIdeal uniformizer_mem poleSubmodule mem_poleSubmodule mem_poleSubmodule_iff_ord)

open _root_.AlgebraicCurve.Place

variable {K F}

variable (v : Place K F)

end Place

namespace Divisor

export _root_.AlgebraicCurve.Divisor (smul_def)

open _root_.AlgebraicCurve.Divisor

variable {K F}

end Divisor

namespace Pic0

export _root_.AlgebraicCurve.Pic0 (mk mk_surjective)

open _root_.AlgebraicCurve.Pic0

variable {K F}

end Pic0

namespace Place

export _root_.AlgebraicCurve.Place (ext ResidueField FiniteResidue heightOneSpectrum heightOneSpectrum_asIdeal adicValuation adicValuation_ne_zero ord ord_zero ord_mul ord_unit_smul_zpow exists_unit_mul_zpow FiniteResidue.finite algebraMap_mem' toValuationSubring mk DCoordGenerates uniformizer ord_uniformizer uniformizer_ne_zero localResidue localResidue_eq_zero_of_ord_nonneg restrict adicCompletion adicCompletionIntegers uniformizerSubring coe_uniformizerSubring uniformizerSubring_mem_maximalIdeal uniformizer_mem poleSubmodule mem_poleSubmodule mem_poleSubmodule_iff_ord)

open _root_.AlgebraicCurve.Place

open scoped _root_.Pointwise _root_.P2MW.S_AlgebraicCurve_tateAgreement.Pointwise

variable {K F}
variable (σ : F ≃ₐ[K] F)

variable (v : Place K F)

end Place

namespace Divisor

export _root_.AlgebraicCurve.Divisor (smul_def)

open _root_.AlgebraicCurve.Divisor

open scoped _root_.Pointwise _root_.P2MW.S_AlgebraicCurve_tateAgreement.Pointwise

variable {K F}

end Divisor

namespace Pic0

export _root_.AlgebraicCurve.Pic0 (mk mk_surjective)

open _root_.AlgebraicCurve.Pic0

open scoped _root_.Pointwise _root_.P2MW.S_AlgebraicCurve_tateAgreement.Pointwise

variable {K F}

end Pic0

namespace Place

export _root_.AlgebraicCurve.Place (ext ResidueField FiniteResidue heightOneSpectrum heightOneSpectrum_asIdeal adicValuation adicValuation_ne_zero ord ord_zero ord_mul ord_unit_smul_zpow exists_unit_mul_zpow FiniteResidue.finite algebraMap_mem' toValuationSubring mk DCoordGenerates uniformizer ord_uniformizer uniformizer_ne_zero localResidue localResidue_eq_zero_of_ord_nonneg restrict adicCompletion adicCompletionIntegers uniformizerSubring coe_uniformizerSubring uniformizerSubring_mem_maximalIdeal uniformizer_mem poleSubmodule mem_poleSubmodule mem_poleSubmodule_iff_ord)

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
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.WithZero
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.IsLocalRing

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.FiniteResidue Place.ord Divisor HasPrincipalDivisors Pic0 Place.FiniteResidue.finite IsCurveOver HasCanonicalLocalResidueKStar kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kwHgfV352_localResidueCompletion completionSection_nonempty_generic localResidue_eq_resStar)

open _root_.AlgebraicCurve

namespace Place

export _root_.AlgebraicCurve.Place (ext ResidueField FiniteResidue heightOneSpectrum heightOneSpectrum_asIdeal adicValuation adicValuation_ne_zero ord ord_zero ord_mul ord_unit_smul_zpow exists_unit_mul_zpow FiniteResidue.finite algebraMap_mem' toValuationSubring mk DCoordGenerates uniformizer ord_uniformizer uniformizer_ne_zero localResidue localResidue_eq_zero_of_ord_nonneg restrict adicCompletion adicCompletionIntegers uniformizerSubring coe_uniformizerSubring uniformizerSubring_mem_maximalIdeal uniformizer_mem poleSubmodule mem_poleSubmodule mem_poleSubmodule_iff_ord)

open _root_.AlgebraicCurve.Place

section SinglePlace

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve.Place.ord_nonneg_of_mem {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
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
  @_root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve.Place.ord_nonneg_of_mem
theorem _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve.Place.mem_of_ord_nonneg {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)




-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.mem_of_ord_nonneg :=
  @_root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve.Place.mem_of_ord_nonneg
theorem _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve.Place.mem_iff_ord_nonneg {f : F} (hf : f ≠ 0) :
    f ∈ v.toValuationSubring ↔ 0 ≤ v.ord f :=
  ⟨v.ord_nonneg_of_mem, v.mem_of_ord_nonneg hf⟩




-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.mem_iff_ord_nonneg :=
  @_root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve.Place.mem_iff_ord_nonneg
end SinglePlace

section Restrict

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F'] [Algebra F F']

variable (w : Place K F')

variable [Algebra.IsIntegral F F']

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

open scoped _root_.Multiplicative _root_.P2MW.S_AlgebraicCurve_tateAgreement.Multiplicative _root_.WithZero _root_.P2MW.S_AlgebraicCurve_tateAgreement.WithZero

open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.IsDedekindDomain
open _root_.IsDedekindDomain.HeightOneSpectrum
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.IsDedekindDomain.HeightOneSpectrum
open _root_.MonoidWithZeroHom
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.MonoidWithZeroHom

namespace MazurTorsion

section Henselian

variable {A : Type*} [CommRing A] [IsDedekindDomain A]
  (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
  (v : IsDedekindDomain.HeightOneSpectrum A)

theorem isClosed_setOf_valued_le (γ : ℤᵐ⁰) :
    IsClosed {x : v.adicCompletion K | Valued.v x ≤ γ} := by
  obtain ⟨z, hz⟩ := valuedAdicCompletion_surjective K v γ
  have h := Valued.isClosed_closedBall (R := v.adicCompletion K) (Γ₀ := ℤᵐ⁰)
    ((Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).restrict z)
  convert h using 1
  ext x
  simp only [Set.mem_setOf_eq]
  rw [Valuation.restrict_le_iff, hz]

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

scoped instance instIsAdicCompleteCompletionIdealAdicCompletionIntegers :
    IsAdicComplete (v.completionIdeal K) (v.adicCompletionIntegers K) where
  haus' x hx := by
    have hx' : ∀ n : ℕ, Valued.v x.val ≤ WithZero.exp (-(n : ℤ)) := by
      intro n
      have h := hx n
      simp only [Ideal.smul_eq_mul, Ideal.mul_top, SModEq.zero,
        adicCompletion.mem_completionIdeal_pow K v] at h
      exact h
    by_contra hx0
    have hxne : x.val ≠ (0 : v.adicCompletion K) := fun h => hx0 (Subtype.ext h)
    have hvne : Valued.v x.val ≠ 0 :=
      (Valuation.ne_zero_iff (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)).mpr hxne
    obtain ⟨k, hk⟩ := exists_ofAdd_natCast_lt hvne
    exact absurd (hx' k) (not_le.mpr hk)
  prec' f hf := by
    classical

    have hf' : ∀ m n : ℕ, m ≤ n →
        Valued.v ((f m - f n : v.adicCompletionIntegers K)).val ≤ WithZero.exp (-(m : ℤ)) := by
      intro m n hmn
      have h := hf hmn
      simp only [Ideal.smul_eq_mul, Ideal.mul_top, SModEq.sub_mem,
        adicCompletion.mem_completionIdeal_pow K v] at h
      exact h

    have hcoe : ∀ a b : ℕ, ((f a - f b : v.adicCompletionIntegers K)).val
        = (f a).val - (f b).val := fun a b => rfl

    have hcauchy : CauchySeq (fun n => (f n).val : ℕ → v.adicCompletion K) := by
      rw [(Valued.hasBasis_uniformity (v.adicCompletion K) ℤᵐ⁰).cauchySeq_iff]
      rintro γ -
      have hγ0 : (ValueGroup₀.embedding γ.val : ℤᵐ⁰) ≠ 0 := by
        intro h0
        exact γ.ne_zero (ValueGroup₀.embedding_strictMono.injective
          (h0.trans (_root_.map_zero _).symm))
      obtain ⟨k, hk⟩ := exists_ofAdd_natCast_lt hγ0
      refine ⟨k, fun m hm n hn => ?_⟩
      have key : ∀ a b : ℕ, k ≤ a → a ≤ b →
          Valued.v ((f b).val - (f a).val) < ValueGroup₀.embedding γ.val := by
        intro a b hka hab
        have h1 : Valued.v ((f b).val - (f a).val) ≤ WithZero.exp (-(a : ℤ)) := by
          rw [Valuation.map_sub_swap, ← hcoe a b]
          exact hf' a b hab
        have h2 : WithZero.exp (-(a : ℤ)) ≤ WithZero.exp (-(k : ℤ)) := by
          rw [WithZero.exp_le_exp]
          omega
        exact lt_of_le_of_lt (h1.trans h2) hk
      show ((Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).restrict
        ((f n).val - (f m).val)) < γ.val
      rw [Valuation.restrict_lt_iff_lt_embedding]
      rcases le_total m n with hmn | hnm
      · exact key m n hm hmn
      · rw [Valuation.map_sub_swap]
        exact key n m hn hnm

    obtain ⟨L₀, hL₀⟩ := cauchySeq_tendsto_of_complete hcauchy

    have hbound : ∀ n : ℕ, Valued.v (L₀ - (f n).val) ≤ WithZero.exp (-(n : ℤ)) := by
      intro n
      have hclosed : IsClosed {y : v.adicCompletion K |
          Valued.v (y - (f n).val) ≤ WithZero.exp (-(n : ℤ))} := by
        have hpre : {y : v.adicCompletion K |
            Valued.v (y - (f n).val) ≤ WithZero.exp (-(n : ℤ))}
              = (fun y => y - (f n).val) ⁻¹'
                {z : v.adicCompletion K | Valued.v z ≤ WithZero.exp (-(n : ℤ))} := rfl
        rw [hpre]
        exact (isClosed_setOf_valued_le K v _).preimage (continuous_sub_right ((f n).val))
      have hev : ∀ᶠ m in Filter.atTop, (f m).val ∈ {y : v.adicCompletion K |
          Valued.v (y - (f n).val) ≤ WithZero.exp (-(n : ℤ))} := by
        refine Filter.eventually_atTop.mpr ⟨n, fun m hm => ?_⟩
        have h := hf' n m hm
        rw [hcoe n m] at h
        rw [Set.mem_setOf_eq, Valuation.map_sub_swap]
        exact h
      exact hclosed.mem_of_tendsto hL₀ hev

    have hL₀mem : L₀ ∈ v.adicCompletionIntegers K := by
      rw [mem_adicCompletionIntegers]
      have h0 : Valued.v (L₀ - (f 0).val) ≤ (1 : ℤᵐ⁰) := by
        have h := hbound 0
        simpa using h
      have h1 : Valued.v ((f 0).val) ≤ (1 : ℤᵐ⁰) := (f 0).2
      have hmax : Valued.v ((L₀ - (f 0).val) + (f 0).val) ≤ (1 : ℤᵐ⁰) :=
        Valuation.map_add_le _ h0 h1
      have hL : (L₀ - (f 0).val) + (f 0).val = L₀ := by ring
      rwa [hL] at hmax

    refine ⟨⟨L₀, hL₀mem⟩, fun n => ?_⟩
    have h : Valued.v ((f n).val - L₀) ≤ WithZero.exp (-(n : ℤ)) := by
      rw [Valuation.map_sub_swap]
      exact hbound n
    simp only [Ideal.smul_eq_mul, Ideal.mul_top, SModEq.sub_mem,
      adicCompletion.mem_completionIdeal_pow K v]
    have hsub : ((f n - (⟨L₀, hL₀mem⟩ : v.adicCompletionIntegers K) :
        v.adicCompletionIntegers K)).val = (f n).val - L₀ := rfl
    rw [hsub]
    exact h

end Henselian

section Uniformizer

variable {A : Type*} [CommRing A] [IsDedekindDomain A]
  (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
  (v : IsDedekindDomain.HeightOneSpectrum A)

end Uniformizer

section DVR

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

end DVR

section Cover

end Cover

section Consequences

end Consequences

section PadicGate

end PadicGate

end MazurTorsion


end


end


section
section

set_option synthInstance.maxHeartbeats 3200000
set_option maxHeartbeats 6400000

noncomputable section

open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.IsDedekindDomain
open _root_.IsDedekindDomain.HeightOneSpectrum
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.IsDedekindDomain.HeightOneSpectrum
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.IsLocalRing
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.WithZero
open _root_.MonoidWithZeroHom
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.MonoidWithZeroHom

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.FiniteResidue Place.ord Divisor HasPrincipalDivisors Pic0 Place.FiniteResidue.finite IsCurveOver HasCanonicalLocalResidueKStar kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kwHgfV352_localResidueCompletion completionSection_nonempty_generic localResidue_eq_resStar)

namespace Place

export _root_.AlgebraicCurve.Place (ext ResidueField FiniteResidue heightOneSpectrum heightOneSpectrum_asIdeal adicValuation adicValuation_ne_zero ord ord_zero ord_mul ord_unit_smul_zpow exists_unit_mul_zpow FiniteResidue.finite algebraMap_mem' toValuationSubring mk DCoordGenerates uniformizer ord_uniformizer uniformizer_ne_zero localResidue localResidue_eq_zero_of_ord_nonneg restrict adicCompletion adicCompletionIntegers uniformizerSubring coe_uniformizerSubring uniformizerSubring_mem_maximalIdeal uniformizer_mem poleSubmodule mem_poleSubmodule mem_poleSubmodule_iff_ord)

open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve

section AdicCompletion

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (V : Place K F)

end AdicCompletion


section Henselian

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (V : Place K F)

scoped instance kw_ffgc_isAdicComplete_placeAdicCompletionIntegers :
    IsAdicComplete (maximalIdeal V.adicCompletionIntegers) V.adicCompletionIntegers :=
  inferInstance

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

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

noncomputable section

open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.WithZero
open _root_.Module
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.Module
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.IsLocalRing
open _root_.Module.IsLocalRing

namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateAgreement)

namespace Lg37

export _root_.ModularCurve.Lg37 (lg37_completion lg37_residueHat lg37_residueHat_algebraMap Lg37CompletionSection)

open _root_.ModularCurve.Lg37
open _root_.ModularCurve

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve
open _root_.ModularCurve.Ldgr36Si
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.Ldgr36Si
open _root_.ModularCurve.Ldgr36Rc
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.Ldgr36Rc
open _root_.ModularCurve.Ldgr35Cs
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.Ldgr35Cs

section CompletionCarrier

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

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

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

noncomputable section

open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.IsDedekindDomain
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.IsLocalRing
open _root_.Polynomial
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.Polynomial

open scoped _root_.Polynomial _root_.P2MW.S_AlgebraicCurve_tateAgreement.Polynomial

namespace Mp72a103T2

export _root_.Mp72a103T2 (mp72a103_t2_taylor_coeff_eq_zero_of_depth)

open _root_.Mp72a103T2

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.RationalFunctionField
open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve.RationalFunctionField
open _root_.ModularCurve.Lg37
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.Lg37
open _root_.ModularCurve.Mp72a102T3
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.Mp72a102T3
open _root_.Mp72a102T2
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.Mp72a102T2

section Calculus

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mp72a103_t2_evalDepth_pow_uniformizer_mul_eq_zero (v : Place K F) :
    ∀ (m : ℕ) (z : lg37_completion v),
      AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) m
        (algebraMap v.toValuationSubring (lg37_completion v)
            v.uniformizerSubring ^ m * z) = 0 := by
  intro m
  induction m with
  | zero => intro z; exact mp72a102_t3_evalₐ_zero_depth _ _
  | succ m ih =>
    intro z
    have hkill := mp72a102_t3_evalₐ_succ_mul_eq_zero
      (maximalIdeal v.toValuationSubring) v.uniformizerSubring_mem_maximalIdeal (ih z)
    have hgoal : algebraMap v.toValuationSubring (lg37_completion v)
          v.uniformizerSubring ^ (m + 1) * z
        = algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring
          * (algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ m * z) := by
      rw [pow_succ', mul_assoc]
    rw [hgoal]
    exact hkill

end Calculus


section NumeratorBand

variable {K : Type*} [Field K] [CharZero K]

end NumeratorBand


section RatProduction

attribute [local instance 2000] RatFunc.instAlgebraOfPolynomial

variable [HasCanonicalLocalResidueKStar ℚ (RatFunc ℚ)]
variable [HasCanonicalLocalResidueKStar (AlgebraicClosure ℚ) (RatFunc (AlgebraicClosure ℚ))]

end RatProduction


end Mp72a103T2


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
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.GF24a9RRDx
open _root_.AlgebraicCurve.Place
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve.Place
open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.IsDedekindDomain

noncomputable section

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.FiniteResidue Place.ord Divisor HasPrincipalDivisors Pic0 Place.FiniteResidue.finite IsCurveOver HasCanonicalLocalResidueKStar kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kwHgfV352_localResidueCompletion completionSection_nonempty_generic localResidue_eq_resStar)

open _root_.AlgebraicCurve

section LocalResidueCompletion

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

variable [HasCanonicalLocalResidueKStar K E]

theorem kwHgfV352_localResidueCompletion_spec (v : Place K E) (xh : v.adicCompletion)
    {x : E} (hx : algebraMap E v.adicCompletion x - xh ∈ v.adicCompletionIntegers) :
    kwHgfV352_localResidueCompletion v xh = v.localResidue x := by
  unfold kwHgfV352_localResidueCompletion
  set x₀ := (kwHgfV352_exists_sub_mem_adicCompletionIntegers v xh).choose
  have hx₀ := (kwHgfV352_exists_sub_mem_adicCompletionIntegers v xh).choose_spec
  have heq : algebraMap E v.adicCompletion (x₀ - x)
      = (algebraMap E v.adicCompletion x₀ - xh) - (algebraMap E v.adicCompletion x - xh) := by
    rw [map_sub]; ring
  have hdiff : algebraMap E v.adicCompletion (x₀ - x) ∈ v.adicCompletionIntegers :=
    heq ▸ sub_mem hx₀ hx
  have hov : x₀ - x ∈ v.toValuationSubring :=
    (kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff v _).mp hdiff
  have hzero : v.localResidue (x₀ - x) = 0 :=
    v.localResidue_eq_zero_of_ord_nonneg (Or.inr (v.ord_nonneg_of_mem hov))
  rw [map_sub, sub_eq_zero] at hzero
  exact hzero

theorem kwHgfV352_localResidueCompletion_algebraMap (v : Place K E) (x : E) :
    kwHgfV352_localResidueCompletion v (algebraMap E v.adicCompletion x)
      = v.localResidue x :=
  kwHgfV352_localResidueCompletion_spec v _
    (by rw [sub_self]; exact zero_mem _)

theorem kwHgfV352_localResidueCompletion_eq_zero_of_mem_integers (v : Place K E)
    {xh : v.adicCompletion} (hxh : xh ∈ v.adicCompletionIntegers) :
    kwHgfV352_localResidueCompletion v xh = 0 := by
  rw [kwHgfV352_localResidueCompletion_spec v xh (x := 0)
    (by rw [_root_.map_zero, zero_sub]; exact neg_mem hxh)]
  exact _root_.map_zero _

theorem kwHgfV352_localResidueCompletion_add (v : Place K E)
    (xh yh : v.adicCompletion) :
    kwHgfV352_localResidueCompletion v (xh + yh)
      = kwHgfV352_localResidueCompletion v xh
        + kwHgfV352_localResidueCompletion v yh := by
  obtain ⟨x, hx⟩ := kwHgfV352_exists_sub_mem_adicCompletionIntegers v xh
  obtain ⟨y, hy⟩ := kwHgfV352_exists_sub_mem_adicCompletionIntegers v yh
  have heq : algebraMap E v.adicCompletion (x + y) - (xh + yh)
      = (algebraMap E v.adicCompletion x - xh) + (algebraMap E v.adicCompletion y - yh) := by
    rw [map_add]; ring
  rw [kwHgfV352_localResidueCompletion_spec v xh hx,
    kwHgfV352_localResidueCompletion_spec v yh hy,
    kwHgfV352_localResidueCompletion_spec v (xh + yh) (x := x + y)
      (heq ▸ add_mem hx hy),
    map_add]

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
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve.Place
open _root_.LinearMap
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.LinearMap
open _root_.Submodule
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.Submodule
open _root_.ModularCurve.KwF4gRRTate
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.KwF4gRRTate

noncomputable section

namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateAgreement)

namespace KwF4gRRTate

export _root_.ModularCurve.KwF4gRRTate (finrankTrace tateComm tateCommRestrict tateCommRestrict_apply tateCommTrace tateComm_eq_of_commute adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateAgreement)

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
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve.Place
open _root_.LinearMap
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.LinearMap
open _root_.Submodule
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.Submodule
open _root_.ModularCurve.KwF4gRRTate
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.KwF4gRRTate
open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.IsDedekindDomain
open _root_.IsDedekindDomain.HeightOneSpectrum
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.IsDedekindDomain.HeightOneSpectrum
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.IsLocalRing

noncomputable section

namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateAgreement)

namespace KwF4gRRTate

export _root_.ModularCurve.KwF4gRRTate (finrankTrace tateComm tateCommRestrict tateCommRestrict_apply tateCommTrace tateComm_eq_of_commute adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateAgreement)

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

open scoped _root_.WithZero _root_.P2MW.S_AlgebraicCurve_tateAgreement.WithZero _root_.Multiplicative _root_.P2MW.S_AlgebraicCurve_tateAgreement.Multiplicative _root_.Topology _root_.P2MW.S_AlgebraicCurve_tateAgreement.Topology
open _root_.Filter
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.Filter

namespace IsDedekindDomain

export _root_.IsDedekindDomain (HeightOneSpectrum.ext mk HeightOneSpectrum)

namespace HeightOneSpectrum

export _root_.IsDedekindDomain.HeightOneSpectrum (valuation_of_algebraMap intValuation_le_pow_iff_mem isMaximal mk mem_adicCompletionIntegers comap valuedAdicCompletion_eq_valuation' adicCompletion valuation adicCompletionIntegers valuedAdicCompletion_surjective mem_integers_of_valuation_le_one denseRange_algebraMap intValuation exists_ofAdd_natCast_lt completionIdeal adicCompletion.maximalIdeal_eq_span_uniformizer adicCompletion.mem_completionIdeal_pow)

open _root_.IsDedekindDomain.HeightOneSpectrum
open _root_.IsDedekindDomain

variable {A : Type*} (K : Type*) [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    [IsDedekindDomain A] (v : HeightOneSpectrum A)

namespace adicCompletion

export _root_.IsDedekindDomain.HeightOneSpectrum.adicCompletion (uniformizer_ne_zero maximalIdeal_eq_span_uniformizer mem_completionIdeal_pow)

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
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.NumberField

variable (F : Type*) [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F))

end NumberField


end IsDedekindDomain.HeightOneSpectrum



section AxiomAudit

open _root_.IsDedekindDomain.HeightOneSpectrum
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.IsDedekindDomain.HeightOneSpectrum

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
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.IsDedekindDomain
open _root_.IsDedekindDomain.HeightOneSpectrum
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.IsDedekindDomain.HeightOneSpectrum
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.IsLocalRing
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.WithZero
open _root_.ModularCurve.Lg37
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.Lg37
open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve.Place

namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateAgreement)

namespace KwF4R1V410a
open _root_.ModularCurve

theorem kwF4R1V410a_factorPow_evalₐ {R : Type*} [CommRing R] {I : Ideal R}
    {m n : ℕ} (hle : m ≤ n) (z : AdicCompletion I R) :
    Ideal.Quotient.factorPow I hle (AdicCompletion.evalₐ I n z)
      = AdicCompletion.evalₐ I m z := by
  rw [← AdicCompletion.factor_eval_eq_evalₐ I z (n := n) (le_of_eq (Ideal.mul_top _)),
    ← AdicCompletion.factor_eval_eq_evalₐ I z (n := m) (le_of_eq (Ideal.mul_top _)),
    AdicCompletion.eval_apply, AdicCompletion.eval_apply, ← z.prop hle]

  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (z.val n)
  rw [← hx]; rfl

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

theorem kwF4R1V410a_quotientEquiv_factorPow {m n : ℕ} (hle : m ≤ n)
    (z : ((w.toValuationSubring)) ⧸ ((IsLocalRing.maximalIdeal w.toValuationSubring)) ^ n) :
    Ideal.Quotient.factorPow ((w.heightOneSpectrum.completionIdeal F)) hle (kwF4R1V410a_quotientEquiv w n z)
      = kwF4R1V410a_quotientEquiv w m (Ideal.Quotient.factorPow ((IsLocalRing.maximalIdeal w.toValuationSubring)) hle z) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [kwF4R1V410a_quotientEquiv_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk,
    kwF4R1V410a_quotientEquiv_mk]

def kwF4R1V410a_forwardFamily (n : ℕ) :
    lg37_completion w →+* ((w.adicCompletionIntegers)) ⧸ ((w.heightOneSpectrum.completionIdeal F))^n :=
  RingHom.comp ((kwF4R1V410a_quotientEquiv w n).toRingHom)
    ((AdicCompletion.evalₐ ((IsLocalRing.maximalIdeal w.toValuationSubring)) n).toRingHom)

theorem kwF4R1V410a_forwardFamily_compat {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow ((w.heightOneSpectrum.completionIdeal F)) hle).comp (kwF4R1V410a_forwardFamily w n)
      = kwF4R1V410a_forwardFamily w m := by
  refine RingHom.ext fun z => ?_
  show Ideal.Quotient.factorPow ((w.heightOneSpectrum.completionIdeal F)) hle
      (kwF4R1V410a_quotientEquiv w n (AdicCompletion.evalₐ ((IsLocalRing.maximalIdeal w.toValuationSubring)) n z))
    = kwF4R1V410a_quotientEquiv w m (AdicCompletion.evalₐ ((IsLocalRing.maximalIdeal w.toValuationSubring)) m z)
  rw [kwF4R1V410a_quotientEquiv_factorPow w hle, kwF4R1V410a_factorPow_evalₐ hle z]

def kwF4R1V410a_forward : lg37_completion w →+* ((w.adicCompletionIntegers)) :=
  haveI := kw_ffgc_isAdicComplete_placeAdicCompletionIntegers w
  IsAdicComplete.liftRingHom ((w.heightOneSpectrum.completionIdeal F)) (kwF4R1V410a_forwardFamily w)
    (kwF4R1V410a_forwardFamily_compat w)

theorem kwF4R1V410a_mk_forward (n : ℕ) (z : lg37_completion w) :
    Ideal.Quotient.mk (((w.heightOneSpectrum.completionIdeal F))^n) (kwF4R1V410a_forward w z)
      = kwF4R1V410a_quotientEquiv w n (AdicCompletion.evalₐ ((IsLocalRing.maximalIdeal w.toValuationSubring)) n z) := by
  haveI := kw_ffgc_isAdicComplete_placeAdicCompletionIntegers w
  exact IsAdicComplete.mk_liftRingHom ((w.heightOneSpectrum.completionIdeal F)) (kwF4R1V410a_forwardFamily w)
    (kwF4R1V410a_forwardFamily_compat w) n z

def kwF4R1V410a_backwardFamily (n : ℕ) : ((w.adicCompletionIntegers)) →+* ((w.toValuationSubring)) ⧸ ((IsLocalRing.maximalIdeal w.toValuationSubring))^n :=
  RingHom.comp ((kwF4R1V410a_quotientEquiv w n).symm.toRingHom)
    (Ideal.Quotient.mk (((w.heightOneSpectrum.completionIdeal F))^n))

theorem kwF4R1V410a_backwardFamily_compat {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow ((IsLocalRing.maximalIdeal w.toValuationSubring)) hle).comp (kwF4R1V410a_backwardFamily w n)
      = kwF4R1V410a_backwardFamily w m := by
  refine RingHom.ext fun y => ?_
  show Ideal.Quotient.factorPow ((IsLocalRing.maximalIdeal w.toValuationSubring)) hle
      ((kwF4R1V410a_quotientEquiv w n).symm (Ideal.Quotient.mk (((w.heightOneSpectrum.completionIdeal F))^n) y))
    = (kwF4R1V410a_quotientEquiv w m).symm (Ideal.Quotient.mk (((w.heightOneSpectrum.completionIdeal F))^m) y)
  apply (kwF4R1V410a_quotientEquiv w m).injective
  rw [RingEquiv.apply_symm_apply, ← kwF4R1V410a_quotientEquiv_factorPow w hle,
    RingEquiv.apply_symm_apply, Ideal.Quotient.factor_mk]

def kwF4R1V410a_backward : ((w.adicCompletionIntegers)) →+* lg37_completion w :=
  AdicCompletion.liftRingHom ((IsLocalRing.maximalIdeal w.toValuationSubring)) (kwF4R1V410a_backwardFamily w)
    (kwF4R1V410a_backwardFamily_compat w)

theorem kwF4R1V410a_evalₐ_backward (n : ℕ) (y : (w.adicCompletionIntegers)) :
    AdicCompletion.evalₐ ((IsLocalRing.maximalIdeal w.toValuationSubring)) n (kwF4R1V410a_backward w y)
      = (kwF4R1V410a_quotientEquiv w n).symm (Ideal.Quotient.mk (((w.heightOneSpectrum.completionIdeal F))^n) y) :=
  AdicCompletion.evalₐ_liftRingHom ((IsLocalRing.maximalIdeal w.toValuationSubring)) (kwF4R1V410a_backwardFamily w)
    (kwF4R1V410a_backwardFamily_compat w) n y

theorem kwF4R1V410a_forward_backward :
    (kwF4R1V410a_forward w).comp (kwF4R1V410a_backward w) = RingHom.id _ := by
  haveI := kw_ffgc_isAdicComplete_placeAdicCompletionIntegers w
  have hfun : (fun y => kwF4R1V410a_forward w (kwF4R1V410a_backward w y))
      = _root_.id := IsHausdorff.funext' ((w.heightOneSpectrum.completionIdeal F)) (fun n y => by
    rw [kwF4R1V410a_mk_forward, kwF4R1V410a_evalₐ_backward,
      RingEquiv.apply_symm_apply, _root_.id])
  exact RingHom.ext (fun y => congrFun hfun y)

theorem kwF4R1V410a_backward_forward :
    (kwF4R1V410a_backward w).comp (kwF4R1V410a_forward w) = RingHom.id _ := by
  refine RingHom.ext (fun z => AdicCompletion.ext_evalₐ (fun n => ?_))
  rw [RingHom.comp_apply, kwF4R1V410a_evalₐ_backward, kwF4R1V410a_mk_forward,
    RingEquiv.symm_apply_apply, RingHom.id_apply]

def kwF4R1V410a_ringEquiv : lg37_completion w ≃+* ((w.adicCompletionIntegers)) :=
  RingEquiv.ofRingHom (kwF4R1V410a_forward w) (kwF4R1V410a_backward w)
    (kwF4R1V410a_forward_backward w) (kwF4R1V410a_backward_forward w)

theorem kwF4R1V410a_ringEquiv_apply (z : lg37_completion w) :
    kwF4R1V410a_ringEquiv w z = kwF4R1V410a_forward w z := rfl

theorem kwF4R1V410a_ringEquiv_of (x : (w.toValuationSubring)) :
    kwF4R1V410a_ringEquiv w (algebraMap ((w.toValuationSubring)) (lg37_completion w) x)
      = algebraMap ((w.toValuationSubring)) ((w.adicCompletionIntegers)) x := by
  haveI := kw_ffgc_isAdicComplete_placeAdicCompletionIntegers w
  have hfun : (fun x => kwF4R1V410a_ringEquiv w
        (algebraMap ((w.toValuationSubring)) (lg37_completion w) x))
      = algebraMap ((w.toValuationSubring)) ((w.adicCompletionIntegers)) := IsHausdorff.funext' ((w.heightOneSpectrum.completionIdeal F)) (fun n x => by
    rw [kwF4R1V410a_ringEquiv_apply, kwF4R1V410a_mk_forward,
      show algebraMap ((w.toValuationSubring)) (lg37_completion w) x
        = AdicCompletion.of ((IsLocalRing.maximalIdeal w.toValuationSubring)) ((w.toValuationSubring)) x from rfl,
      AdicCompletion.evalₐ_of, kwF4R1V410a_quotientEquiv_mk])
  exact congrFun hfun x

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
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve.Place
open _root_.LinearMap
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.LinearMap
open _root_.Submodule
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.Submodule
open _root_.ModularCurve.KwF4gRRTate
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.KwF4gRRTate
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.KwF4R1V410a
open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.IsDedekindDomain
open _root_.IsDedekindDomain.HeightOneSpectrum
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.IsDedekindDomain.HeightOneSpectrum
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.IsLocalRing

noncomputable section

namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateAgreement)

namespace KwF4gRRTate

export _root_.ModularCurve.KwF4gRRTate (finrankTrace tateComm tateCommRestrict tateCommRestrict_apply tateCommTrace tateComm_eq_of_commute adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateAgreement)

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
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve.Place
open _root_.LinearMap
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.LinearMap
open _root_.Submodule
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.Submodule
open _root_.ModularCurve.KwF4gRRTate
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.KwF4gRRTate

noncomputable section

namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateAgreement)

namespace KwF4gRRTate

export _root_.ModularCurve.KwF4gRRTate (finrankTrace tateComm tateCommRestrict tateCommRestrict_apply tateCommTrace tateComm_eq_of_commute adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateAgreement)

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
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve.Place
open _root_.LinearMap
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.LinearMap
open _root_.Submodule
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.Submodule
open _root_.ModularCurve.KwF4gRRTate
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.KwF4gRRTate

noncomputable section

namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateAgreement)

namespace KwF4gRRTate

export _root_.ModularCurve.KwF4gRRTate (finrankTrace tateComm tateCommRestrict tateCommRestrict_apply tateCommTrace tateComm_eq_of_commute adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateAgreement)

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
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve.Place
open _root_.LinearMap
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.LinearMap
open _root_.Submodule
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.Submodule
open _root_.ModularCurve.KwF4gRRTate
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.KwF4gRRTate

noncomputable section

namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateAgreement)

namespace KwF4gRRTate

export _root_.ModularCurve.KwF4gRRTate (finrankTrace tateComm tateCommRestrict tateCommRestrict_apply tateCommTrace tateComm_eq_of_commute adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateAgreement)

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
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve.Place
open _root_.LinearMap
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.LinearMap
open _root_.Submodule
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.Submodule
open _root_.ModularCurve.KwF4gRRTate
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.KwF4gRRTate

noncomputable section

namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateAgreement)

namespace KwF4gRRTate

export _root_.ModularCurve.KwF4gRRTate (finrankTrace tateComm tateCommRestrict tateCommRestrict_apply tateCommTrace tateComm_eq_of_commute adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateAgreement)

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
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve.Place
open _root_.LinearMap
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.LinearMap
open _root_.Submodule
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.Submodule
open _root_.ModularCurve.KwF4gRRTate
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.KwF4gRRTate
open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.IsDedekindDomain
open _root_.IsDedekindDomain.HeightOneSpectrum
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.IsDedekindDomain.HeightOneSpectrum
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.IsLocalRing

noncomputable section

namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateAgreement)

namespace KwF4gRRTate

export _root_.ModularCurve.KwF4gRRTate (finrankTrace tateComm tateCommRestrict tateCommRestrict_apply tateCommTrace tateComm_eq_of_commute adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateAgreement)

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
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve.Place
open _root_.LinearMap
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.LinearMap
open _root_.Submodule
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.Submodule
open _root_.ModularCurve.KwF4gRRTate
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.KwF4gRRTate
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.KwF4R1V410a
open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.IsDedekindDomain
open _root_.IsDedekindDomain.HeightOneSpectrum
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.IsDedekindDomain.HeightOneSpectrum
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.IsLocalRing

noncomputable section

namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateAgreement)

namespace KwF4gRRTate

export _root_.ModularCurve.KwF4gRRTate (finrankTrace tateComm tateCommRestrict tateCommRestrict_apply tateCommTrace tateComm_eq_of_commute adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateAgreement)

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
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve.Place
open _root_.LinearMap
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.LinearMap
open _root_.Submodule
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.Submodule
open _root_.ModularCurve.KwF4gRRTate
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.KwF4gRRTate

noncomputable section

namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateAgreement)

namespace KwF4gRRTate

export _root_.ModularCurve.KwF4gRRTate (finrankTrace tateComm tateCommRestrict tateCommRestrict_apply tateCommTrace tateComm_eq_of_commute adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateAgreement)

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


section
section

set_option maxHeartbeats 12800000
set_option synthInstance.maxHeartbeats 6400000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve.Place
open _root_.LinearMap
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.LinearMap
open _root_.Submodule
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.Submodule
open _root_.ModularCurve.KwF4gRRTate
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.KwF4gRRTate

noncomputable section

namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateAgreement)

namespace KwF4gRRTate

export _root_.ModularCurve.KwF4gRRTate (finrankTrace tateComm tateCommRestrict tateCommRestrict_apply tateCommTrace tateComm_eq_of_commute adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateAgreement)

open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve

section Composite

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem kwF4gRRTate_poleWindowFinite : KwF4gRRTatePoleWindowFinite K L :=
  kwF4gRRTate_poleWindowFinite_of_DVRQuotPowKFinite
    (kwF4gRRTate_DVRQuotPowKFinite_of_cotangent
      kwF4gRRTate_DVRCotangentKFinite)

end Composite


section Subset

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

theorem lmul_adicIntegers_subset_poleWindow (fh : u.adicCompletion)
    (πh : u.adicCompletionIntegers) (M : ℕ)
    (hfhM : (πh : u.adicCompletion)^M * fh ∈ u.adicCompletionIntegers) :
    Submodule.map (lmulK u fh) (adicIntegersKSubmod u) ≤ poleWindowKSubmod u πh M := by
  rintro x ⟨a, ha, rfl⟩

  rw [mem_poleWindowKSubmod_iff]
  show (πh : u.adicCompletion)^M * (lmulK u fh) a ∈ u.adicCompletionIntegers
  have : (lmulK u fh) a = fh * a := rfl
  rw [this, ← mul_assoc]
  exact mul_mem hfhM (show a ∈ u.adicCompletionIntegers from ha)

end Subset


section Discharge

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)
variable [u.FiniteResidue]

theorem kwF4gRRTate_poleWindowImageFinite :
    KwF4gRRTatePoleWindowImageFinite u := by
  intro fh
  obtain ⟨πh, hπh⟩ := IsDiscreteValuationRing.exists_irreducible u.adicCompletionIntegers
  obtain ⟨M, hfhM⟩ := kwF4gRRTate_clearPole u πh hπh fh

  set A := adicIntegersKSubmod u
  set P := poleWindowKSubmod u πh M
  have hsub : Submodule.map A.mkQ (Submodule.map (lmulK u fh) A)
      ≤ Submodule.map A.mkQ P :=
    Submodule.map_mono (lmul_adicIntegers_subset_poleWindow u fh πh M hfhM)

  suffices hPim : FiniteDimensional K (Submodule.map A.mkQ P : Submodule K _) by
    exact Submodule.finiteDimensional_of_le hsub

  haveI : FiniteDimensional K (P ⧸ (A.comap P.subtype)) :=
    kwF4gRRTate_poleWindowFinite (K := K) (L := L) u πh hπh M
  let r : P →ₗ[K] (u.adicCompletion ⧸ A) := A.mkQ ∘ₗ P.subtype
  have hrange : LinearMap.range r = Submodule.map A.mkQ P := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hker : LinearMap.ker r = A.comap P.subtype := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have e : (P ⧸ (A.comap P.subtype)) ≃ₗ[K] LinearMap.range r := hker ▸ r.quotKerEquivRange
  rw [← hrange]
  exact e.finiteDimensional

end Discharge


end ModularCurve.KwF4gRRTate



end


end


end

end P2MW.S_AlgebraicCurve_tateAgreement
