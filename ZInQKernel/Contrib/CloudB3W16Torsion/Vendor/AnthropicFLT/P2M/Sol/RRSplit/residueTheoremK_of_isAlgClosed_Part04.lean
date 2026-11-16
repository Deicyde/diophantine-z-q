/-
Copyright 2026 Anthropic, PBC. Released under Apache License 2.0.
Source: https://github.com/anthropics/fermats-last-theorem
Revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.lean; source lines 5270-7508.
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
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.RRSplit.residueTheoremK_of_isAlgClosed_Part03

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 6400000
set_option maxHeartbeats 12800000

namespace P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed

-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.ord_nonneg_of_mem :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.ord_nonneg_of_mem
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.mem_of_ord_nonneg :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.mem_of_ord_nonneg
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.mem_iff_ord_nonneg :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.mem_iff_ord_nonneg
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.exists_ord_pos :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.exists_ord_pos
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.aeval_mem :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.aeval_mem
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.exists_coeff_ord_ne_zero :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.exists_coeff_ord_ne_zero
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.isUnit_algebraMap :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.isUnit_algebraMap
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.adicValuation_algebraMap :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.adicValuation_algebraMap
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.ord_algebraMap :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.ord_algebraMap
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.ord_eq_neg_log_of_valuationSubring_eq :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.ord_eq_neg_log_of_valuationSubring_eq
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.ord_prod :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.ord_prod
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.ord_add_eq_min :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.ord_add_eq_min
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.ord_add_eq_left :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.ord_add_eq_left
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.subsingleton_canonicalLocalResidueDataK_of_surj :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.subsingleton_canonicalLocalResidueDataK_of_surj
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.mem_regularSubmodule :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.mem_regularSubmodule
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.regularPoleSubmodule :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.regularPoleSubmodule
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.mem_regularPoleSubmodule :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.mem_regularPoleSubmodule
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.regularPoleSubmodule_mono :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.regularPoleSubmodule_mono
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.iSup_regularPoleSubmodule_eq_top :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.iSup_regularPoleSubmodule_eq_top
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.exists_mem_regularPoleSubmodule :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.exists_mem_regularPoleSubmodule


section
section

noncomputable section

open _root_.KaehlerDifferential
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.KaehlerDifferential

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Place.ord Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential diagonalHom diagonalHom_apply diagonal_mem_adeleSpace HasCanonicalDivisor HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTerm kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_support_finite_of_adeleSpace weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK HasCanonicalLocalResidueKStar.dataKStar Place.mem_fiber Place.valuationSubringAlgebra Place.finite_setOf_restrict_eq kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kaehlerCotrace kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt KwHgfV352CompletionTraceSum FiberKaehlerCotraceResidueIdentityK CotraceResidueIdentityOnFiberLocalizedK Place.finiteResidue_of_deg_pos residueTraceCompletionCommute residueTheoremK_ratFunc_of_isAlgClosed)

open _root_.AlgebraicCurve

open scoped _root_.Polynomial _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.Polynomial
open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField

section PerfectDCoord

variable (K : Type*) [Field K] [PerfectField K]

theorem exists_ne_zero_smul_dX_of_uniformizer (v : Place K (RatFunc K)) :
    ∃ c : RatFunc K, c ≠ 0 ∧
      KaehlerDifferential.D K (RatFunc K) v.uniformizer = c • dX K := by
  classical
  have hord : v.ord v.uniformizer = 1 := v.ord_uniformizer
  have hpi0 : v.uniformizer ≠ 0 := v.uniformizer_ne_zero
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
  ·
    obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
    obtain ⟨hne, -⟩ := ratFuncDXCoeff_ne_zero_and_ord_eq_zero_of_ord_eq_one hp hwp
      (PerfectField.separable_of_irreducible hp) hpi0 hord
    exact ⟨ratFuncDXCoeff K _, hne, D_eq_ratFuncDXCoeff_smul_dX K _⟩
  ·
    obtain ⟨e, he0, -, hDe⟩ := exists_dXCoeff_ord_two_of_ord_placeInfty_eq_one hpi0 hord
    exact ⟨e, he0, hDe⟩

namespace RationalFunctionField

export _root_.AlgebraicCurve.RationalFunctionField (heightOneSpectrumOfIrreducible heightOneSpectrumOfIrreducible_asIdeal exists_irreducible_span finitePlace finitePlace_def algebraMap_mem_ofHeightOneSpectrum deg_ofHeightOneSpectrum deg_finitePlace)

open _root_.AlgebraicCurve.RationalFunctionField

scoped instance (priority := low) instDCoordGeneratesPerfectField (v : Place K (RatFunc K)) :
    v.DCoordGenerates := by
  obtain ⟨c, hc0, hDc⟩ := exists_ne_zero_smul_dX_of_uniformizer K v
  refine ⟨?_⟩
  have hdc : v.dCoord = KaehlerDifferential.D K (RatFunc K) v.uniformizer := rfl
  rw [hdc, hDc, eq_top_iff, ← span_dX_eq_top K, Submodule.span_singleton_le_iff_mem]
  exact Submodule.mem_span_singleton.mpr
    ⟨c⁻¹, by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]⟩

end RationalFunctionField


end PerfectDCoord


section Profile

variable (K : Type*) [Field K]

section PerfectProfileValues

variable [PerfectField K] [DecidableEq (RatFunc K)]

theorem p1DifferentialCoeffUnitFinite_dX_of_perfectField :
    P1DifferentialCoeffUnitFinite K (dX_ne_zero K) := by
  intro v hvinf
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
  · obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
    exact ord_differentialCoeff_dX_ofHeightOneSpectrum hp hwp
      (PerfectField.separable_of_irreducible hp)
  · exact absurd rfl hvinf

theorem ordDifferential_dX_of_ne_placeInfty_of_perfectField {v : Place K (RatFunc K)}
    (hv : v ≠ placeInfty K) : v.ordDifferential (dX K) = 0 := by
  rw [Place.ordDifferential]
  exact p1DifferentialCoeffUnitFinite_dX_of_perfectField K v hv

theorem ordDifferential_dX_placeInfty_of_perfectField :
    (placeInfty K).ordDifferential (dX K) = -2 :=
  ordDifferential_placeInfty_D_ratFuncX K
    (ordDifferentialWellDefined_ratFunc_of_perfectField K)

theorem exists_divisor_smul_dX_of_perfectField {c : RatFunc K} (hc : c ≠ 0) :
    ∃ D : Divisor K (RatFunc K),
      (∀ v : Place K (RatFunc K), D v = v.ordDifferential (c • dX K)) ∧
        Divisor.degree D = -2 := by
  obtain ⟨Dc, hDc, hDcdeg⟩ :=
    HasPrincipalDivisors.exists_divisor (K := K) (F := RatFunc K) c hc
  refine ⟨Dc + Finsupp.single (placeInfty K) (-2), fun v => ?_, ?_⟩
  ·
    rw [Finsupp.add_apply, hDc v,
      v.ordDifferential_smul hc (v.differentialCoeff_ne_zero (dX_ne_zero K))]
    rcases eq_or_ne v (placeInfty K) with rfl | hne
    · rw [ordDifferential_dX_placeInfty_of_perfectField K, Finsupp.single_eq_same]
    · rw [ordDifferential_dX_of_ne_placeInfty_of_perfectField K hne,
        Finsupp.single_eq_of_ne hne]
  ·
    rw [map_add, hDcdeg, zero_add, Divisor.degree_single, deg_placeInfty K, Nat.cast_one,
      mul_one]

end PerfectProfileValues


section PerfectInstance

variable [PerfectField K]

scoped instance instHasCanonicalDivisorRatFuncPerfectField :
    HasCanonicalDivisor (K := K) (F := RatFunc K) where
  exists_divisor ω hω := by
    classical
    obtain ⟨c, hc⟩ := exists_smul_dX_eq K ω
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      exact hω hc.symm
    obtain ⟨D, hD, -⟩ := exists_divisor_smul_dX_of_perfectField K hc0
    refine ⟨D, fun v => ?_⟩
    rw [← hc]
    exact hD v

end PerfectInstance


section PerfectExactDivisor

variable [PerfectField K] [DecidableEq (RatFunc K)]

end PerfectExactDivisor


section CharZeroRoutes

variable [CharZero K]

end CharZeroRoutes


end Profile


section FiniteFieldReadings

end FiniteFieldReadings


end AlgebraicCurve


section AxiomAudit

end AxiomAudit


end

end


end


section
section

set_option linter.unusedSectionVars false

noncomputable section

open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.WithZero
open _root_.Module
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.Module
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.IsLocalRing
open _root_.Module.IsLocalRing
open _root_.KaehlerDifferential
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.KaehlerDifferential
open _root_.Polynomial
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.Polynomial

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Place.ord Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential diagonalHom diagonalHom_apply diagonal_mem_adeleSpace HasCanonicalDivisor HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTerm kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_support_finite_of_adeleSpace weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK HasCanonicalLocalResidueKStar.dataKStar Place.mem_fiber Place.valuationSubringAlgebra Place.finite_setOf_restrict_eq kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kaehlerCotrace kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt KwHgfV352CompletionTraceSum FiberKaehlerCotraceResidueIdentityK CotraceResidueIdentityOnFiberLocalizedK Place.finiteResidue_of_deg_pos residueTraceCompletionCommute residueTheoremK_ratFunc_of_isAlgClosed)

open _root_.AlgebraicCurve

open scoped _root_.Polynomial _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.Polynomial

open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField

section KernelEngine

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
variable [HasPrincipalDivisors K F]

end KernelEngine


section SimplePoleSeam

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]

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

end SmulReduction


section PerGenerator

variable {K : Type*} [Field K] [CharZero K] [DecidableEq (RatFunc K)]
variable [HasPrincipalDivisors K (RatFunc K)]

end PerGenerator


section Engine

variable {K : Type*} [Field K] [CharZero K] [DecidableEq (RatFunc K)]

end Engine


section AlgClosedDischarge

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] [DecidableEq (RatFunc K)]

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


section S18AliasT2
namespace AlgebraicCurve
export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Place.ord Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential diagonalHom diagonalHom_apply diagonal_mem_adeleSpace HasCanonicalDivisor HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTerm kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_support_finite_of_adeleSpace weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK HasCanonicalLocalResidueKStar.dataKStar Place.mem_fiber Place.valuationSubringAlgebra Place.finite_setOf_restrict_eq kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kaehlerCotrace kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt KwHgfV352CompletionTraceSum FiberKaehlerCotraceResidueIdentityK CotraceResidueIdentityOnFiberLocalizedK Place.finiteResidue_of_deg_pos residueTraceCompletionCommute residueTheoremK_ratFunc_of_isAlgClosed)
end AlgebraicCurve
open scoped _root_.AlgebraicCurve in
theorem AlgebraicCurve.p0n22_cpf_residueTheoremK_ratFunc_of_isAlgClosed
    (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar K (RatFunc K)]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := RatFunc K)]
    [∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates] :
    AlgebraicCurve.ResidueTheoremK K (RatFunc K) :=
  AlgebraicCurve.residueTheoremK_ratFunc_of_isAlgClosed K
end S18AliasT2


section
section

set_option maxHeartbeats 6400000
set_option linter.unusedSectionVars false

noncomputable section

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Place.ord Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential diagonalHom diagonalHom_apply diagonal_mem_adeleSpace HasCanonicalDivisor HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTerm kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_support_finite_of_adeleSpace weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK HasCanonicalLocalResidueKStar.dataKStar Place.mem_fiber Place.valuationSubringAlgebra Place.finite_setOf_restrict_eq kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kaehlerCotrace kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt KwHgfV352CompletionTraceSum FiberKaehlerCotraceResidueIdentityK CotraceResidueIdentityOnFiberLocalizedK Place.finiteResidue_of_deg_pos residueTraceCompletionCommute residueTheoremK_ratFunc_of_isAlgClosed)

open _root_.AlgebraicCurve

open scoped _root_.Polynomial _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.Polynomial
open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField

section KCurrencyRow

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]
variable [Algebra.IsIntegral E F]

end KCurrencyRow


section Engine

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)]
variable [∀ w : Place K F, w.DCoordGenerates]
variable {E : Type*} [Field E] [Algebra K E]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalDivisor (K := K) (F := E)]
variable [∀ v : Place K E, v.DCoordGenerates]
variable [Algebra E F] [IsScalarTower K E F] [Algebra.IsIntegral E F]

theorem residueTheoremK_of_cotraceResidueIdentityK
    [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]
    (hE : ResidueTheoremK K E)
    {ωE₀ : Ω[E⁄K]} (hωE₀ : ωE₀ ≠ 0) (hgen : kaehlerPullback K F E ωE₀ ≠ 0)
    (hIdentK : FiberKaehlerCotraceResidueIdentityK K F E) :
    ResidueTheoremK K F := by
  intro RfamF _ ωF hωF f
  haveI : Nontrivial Ω[F⁄K] := ⟨ωF, 0, hωF⟩
  rcases isEmpty_or_nonempty (Place K F) with hempty | hne
  ·
    rw [weilOfKaehlerK_apply]
    exact finsum_eq_zero_of_forall_eq_zero fun w => (hempty.false w).elim
  obtain ⟨w₀⟩ := hne

  obtain ⟨RfamE, hident⟩ := hIdentK RfamF hωE₀ hgen

  have hcoeff : w₀.differentialCoeff (kaehlerPullback K F E ωE₀) ≠ 0 :=
    w₀.differentialCoeff_ne_zero hgen
  have hωF_eq : ωF = (w₀.differentialCoeff ωF
      * (w₀.differentialCoeff (kaehlerPullback K F E ωE₀))⁻¹)
        • kaehlerPullback K F E ωE₀ := by
    have key : (w₀.differentialCoeff ωF
        * (w₀.differentialCoeff (kaehlerPullback K F E ωE₀))⁻¹)
          • kaehlerPullback K F E ωE₀ = ωF := by
      calc (w₀.differentialCoeff ωF
            * (w₀.differentialCoeff (kaehlerPullback K F E ωE₀))⁻¹)
              • kaehlerPullback K F E ωE₀
          = (w₀.differentialCoeff ωF
              * (w₀.differentialCoeff (kaehlerPullback K F E ωE₀))⁻¹)
                • (w₀.differentialCoeff (kaehlerPullback K F E ωE₀) • w₀.dCoord) := by
            rw [w₀.differentialCoeff_smul_dCoord]
        _ = ((w₀.differentialCoeff ωF
              * (w₀.differentialCoeff (kaehlerPullback K F E ωE₀))⁻¹)
                * w₀.differentialCoeff (kaehlerPullback K F E ωE₀)) • w₀.dCoord := by
            rw [smul_smul]
        _ = w₀.differentialCoeff ωF • w₀.dCoord := by
            rw [mul_assoc, inv_mul_cancel₀ hcoeff, mul_one]
        _ = ωF := w₀.differentialCoeff_smul_dCoord ωF
    exact key.symm

  have hterm : ∀ w : Place K F,
      kaehlerResidueTermKFam RfamF ωF (diagonalHom K F f) w
        = kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE₀)
            (diagonalHom K F ((w₀.differentialCoeff ωF
              * (w₀.differentialCoeff (kaehlerPullback K F E ωE₀))⁻¹) * f)) w := by
    intro w
    conv_lhs => rw [hωF_eq]
    exact kaehlerResidueTermKFam_smul_diagonal RfamF _ (kaehlerPullback K F E ωE₀) f w

  have hsup : (Function.support (kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE₀)
      (diagonalHom K F ((w₀.differentialCoeff ωF
        * (w₀.differentialCoeff (kaehlerPullback K F E ωE₀))⁻¹) * f)))).Finite :=
    kaehlerResidueTermKFam_support_finite_of_adeleSpace RfamF hgen
      (diagonal_mem_adeleSpace _)

  calc weilOfKaehlerK RfamF hωF ⟨diagonalHom K F f, diagonal_mem_adeleSpace f⟩
      = ∑ᶠ w : Place K F, kaehlerResidueTermKFam RfamF ωF (diagonalHom K F f) w :=
        weilOfKaehlerK_apply RfamF hωF _
    _ = ∑ᶠ w : Place K F, kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE₀)
          (diagonalHom K F ((w₀.differentialCoeff ωF
            * (w₀.differentialCoeff (kaehlerPullback K F E ωE₀))⁻¹) * f)) w :=
        finsum_congr hterm
    _ = ∑ᶠ v : Place K E, ∑ w ∈ v.fiber F,
          kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE₀)
            (diagonalHom K F ((w₀.differentialCoeff ωF
              * (w₀.differentialCoeff (kaehlerPullback K F E ωE₀))⁻¹) * f)) w :=
        finsum_place_eq_finsum_fiber_sum (E := E) _ hsup
    _ = ∑ᶠ v : Place K E, kaehlerResidueTermKFam RfamE ωE₀
          (diagonalHom K E (Algebra.trace E F ((w₀.differentialCoeff ωF
            * (w₀.differentialCoeff (kaehlerPullback K F E ωE₀))⁻¹) * f))) v :=
        finsum_congr fun v => hident v _
    _ = 0 := by
        have h0 := hE RfamE hωE₀ (Algebra.trace E F ((w₀.differentialCoeff ωF
          * (w₀.differentialCoeff (kaehlerPullback K F E ωE₀))⁻¹) * f))
        rw [weilOfKaehlerK_apply] at h0
        exact h0

end Engine


section RatFuncFloorSupply

variable {K F : Type*} [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)]
variable [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [HasCanonicalDivisor (K := K) (F := F)] [∀ w : Place K F, w.DCoordGenerates]
variable [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
variable [Algebra.IsIntegral (RatFunc K) F]

theorem residueTheoremK_of_cotraceResidueIdentityK_ratFunc_isAlgClosed
    [HasPrincipalDivisors K F]
    (hgen : kaehlerPullback K F (RatFunc K) (dX K) ≠ 0)
    (hIdentK : FiberKaehlerCotraceResidueIdentityK K F (RatFunc K)) :
    ResidueTheoremK K F :=
  residueTheoremK_of_cotraceResidueIdentityK
    (p0n22_cpf_residueTheoremK_ratFunc_of_isAlgClosed K)
    (dX_ne_zero K) hgen hIdentK

end RatFuncFloorSupply


section SelfGate

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]

variable [HasCanonicalDivisor (K := K) (F := F)] [∀ w : Place K F, w.DCoordGenerates]

end SelfGate


end AlgebraicCurve


end


end


end


section
section

noncomputable section

open _root_.Polynomial
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.Polynomial
open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve
open _root_.WeierstrassCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.WeierstrassCurve
open _root_.ModularCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.ModularCurve
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.IsLocalRing

open scoped _root_.WeierstrassCurve.Affine _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.WeierstrassCurve.Affine

namespace Cotpk43T3

open ModularCurve.ElevenA1



set_option linter.unusedSectionVars false

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

section DVRSandwich

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

theorem cotpk43_t3_toValuationSubring_eq_of_dedekind_le
    (O : ValuationSubring F) (hO : IsDedekindDomain O)
    (v : Place k F) (hle : O ≤ v.toValuationSubring) :
    v.toValuationSubring = O := by
  haveI := hO
  have hSP : O.ofPrime (O.idealOfLE v.toValuationSubring hle) = v.toValuationSubring :=
    ValuationSubring.ofPrime_idealOfLE O v.toValuationSubring hle
  rcases eq_or_ne (O.idealOfLE v.toValuationSubring hle) ⊥ with hP | hP
  ·
    exfalso
    apply v.ne_top'
    have h2 : O.ofPrime ⊥ ≤ O.ofPrime (O.idealOfLE v.toValuationSubring hle) :=
      ValuationSubring.ofPrime_le_of_le (h := hP.le)
    rw [ValuationSubring.ofPrime_bot] at h2
    exact top_le_iff.mp (le_trans h2 hSP.le)
  ·
    have hPmax : (O.idealOfLE v.toValuationSubring hle).IsMaximal :=
      Ideal.IsPrime.isMaximal inferInstance hP
    have hPeq : O.idealOfLE v.toValuationSubring hle = IsLocalRing.maximalIdeal O :=
      IsLocalRing.eq_maximalIdeal hPmax
    have h3 : O.ofPrime (O.idealOfLE v.toValuationSubring hle)
        = O.ofPrime (IsLocalRing.maximalIdeal O) :=
      le_antisymm (ValuationSubring.ofPrime_le_of_le (h := hPeq.ge))
        (ValuationSubring.ofPrime_le_of_le (h := hPeq.le))
    rw [ValuationSubring.ofPrime_top] at h3
    rw [hSP] at h3
    exact h3

theorem cotpk43_t3_place_eq_of_dedekind_le
    (O : ValuationSubring F) (hO : IsDedekindDomain O)
    (v w : Place k F) (hv : O ≤ v.toValuationSubring) (hw : O ≤ w.toValuationSubring) :
    v = w :=
  Place.ext ((cotpk43_t3_toValuationSubring_eq_of_dedekind_le O hO v hv).trans
    (cotpk43_t3_toValuationSubring_eq_of_dedekind_le O hO w hw).symm)

theorem cotpk43_t3_place_eq_of_toValuationSubring_le
    (v w : Place k F) (h : v.toValuationSubring ≤ w.toValuationSubring) : v = w :=
  cotpk43_t3_place_eq_of_dedekind_le v.toValuationSubring inferInstance v w le_rfl h

end DVRSandwich


section CentreWitness

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]

variable {K N}

end CentreWitness


section ProductionDescent

end ProductionDescent


end Cotpk43T3


end


end


end


section
section

set_option linter.unusedSectionVars false

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.WithZero

namespace ModularCurve

export _root_.ModularCurve (KwF4R1V391a.KwF4R1V391aResidueTraceCompletionCommute)

namespace GF24a9RRDx
open _root_.ModularCurve

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve
open _root_.KaehlerDifferential
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.KaehlerDifferential
open _root_.IntermediateField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.IntermediateField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.RibetEndgame
open _root_.CongruenceSubgroup
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.CongruenceSubgroup

section Toolkit

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem gf24a9r_ord_neg (v : Place K F) (g : F) : v.ord (-g) = v.ord g := by
  simp only [Place.ord, Valuation.map_neg]

theorem gf24a9r_ord_pow (v : Place K F) (g : F) (m : ℕ) :
    v.ord (g ^ m) = (m : ℤ) * v.ord g := by
  rw [show (g ^ m : F) = g ^ (m : ℤ) from (zpow_natCast g m).symm, v.ord_zpow]

theorem gf24a9r_one_add_ne_zero_of_ord_pos (v : Place K F) {g : F}
    (h : 0 < v.ord g) : (1 : F) + g ≠ 0 := by
  intro hcon
  have hg1 : g = -(1 : F) := by
    rw [add_comm] at hcon
    exact eq_neg_of_add_eq_zero_left hcon
  have h0 : v.ord g = 0 := by rw [hg1, gf24a9r_ord_neg, v.ord_one]
  omega

theorem gf24a9r_ord_one_add_of_ord_pos (v : Place K F) {g : F} (hg : g ≠ 0)
    (h : 0 < v.ord g) : v.ord (1 + g) = 0 := by
  have hmin := v.ord_add_eq_min (f := (1 : F)) one_ne_zero hg
    (by rw [v.ord_one]; omega)
  rw [v.ord_one] at hmin
  rw [hmin, min_eq_left h.le]

theorem gf24a9r_ord_one_add_of_ord_neg (v : Place K F) {g : F} (hg : g ≠ 0)
    (h : v.ord g < 0) : v.ord (1 + g) = v.ord g := by
  have hmin := v.ord_add_eq_min (f := (1 : F)) one_ne_zero hg
    (by rw [v.ord_one]; omega)
  rw [v.ord_one] at hmin
  rw [hmin, min_eq_right h.le]

theorem gf24a9r_exists_ord_pos_ord_neg {w₁ w₂ : Place K F} (h : w₁ ≠ w₂) :
    ∃ u : F, u ≠ 0 ∧ 0 < w₁.ord u ∧ w₂.ord u < 0 := by
  have h12 : ¬(w₁.toValuationSubring ≤ w₂.toValuationSubring) := fun hle =>
    h (Cotpk43T3.cotpk43_t3_place_eq_of_toValuationSubring_le w₁ w₂ hle)
  have h21 : ¬(w₂.toValuationSubring ≤ w₁.toValuationSubring) := fun hle =>
    h.symm (Cotpk43T3.cotpk43_t3_place_eq_of_toValuationSubring_le w₂ w₁ hle)
  obtain ⟨x, hx1, hx2⟩ := SetLike.not_le_iff_exists.mp h12
  obtain ⟨y, hy2, hy1⟩ := SetLike.not_le_iff_exists.mp h21
  have hx0 : x ≠ 0 := by rintro rfl; exact hx2 (zero_mem _)
  have hy0 : y ≠ 0 := by rintro rfl; exact hy1 (zero_mem _)
  have hx1o : 0 ≤ w₁.ord x := w₁.ord_nonneg_of_mem hx1
  have hy2o : 0 ≤ w₂.ord y := w₂.ord_nonneg_of_mem hy2
  have hx2o : w₂.ord x < 0 := by
    by_contra hcon
    rw [not_lt] at hcon
    exact hx2 (w₂.mem_of_ord_nonneg hx0 hcon)
  have hy1o : w₁.ord y < 0 := by
    by_contra hcon
    rw [not_lt] at hcon
    exact hy1 (w₁.mem_of_ord_nonneg hy0 hcon)
  refine ⟨x * y⁻¹, mul_ne_zero hx0 (inv_ne_zero hy0), ?_, ?_⟩
  · rw [w₁.ord_mul hx0 (inv_ne_zero hy0), w₁.ord_inv]
    omega
  · rw [w₂.ord_mul hx0 (inv_ne_zero hy0), w₂.ord_inv]
    omega

theorem gf24a9r_exists_separator (w : Place K F) (S : Finset (Place K F)) (hw : w ∉ S) :
    ∃ u : F, u ≠ 0 ∧ 0 < w.ord u ∧ ∀ w' ∈ S, w'.ord u < 0 := by
  classical
  revert hw
  induction S using Finset.induction_on with
  | empty =>
    intro _
    obtain ⟨g, hg0, hgord⟩ := w.exists_ord_pos
    exact ⟨g, hg0, hgord, fun w' hw' => absurd hw' (Finset.notMem_empty w')⟩
  | @insert a S' ha ih =>
    intro hw
    have hwa : w ≠ a := fun hcon => hw (hcon ▸ Finset.mem_insert_self a S')
    have hwS' : w ∉ S' := fun hcon => hw (Finset.mem_insert_of_mem hcon)
    obtain ⟨y, hy0, hyw, hyS'⟩ := ih hwS'
    obtain ⟨z, hz0, hzw, hza⟩ := gf24a9r_exists_ord_pos_ord_neg hwa
    rcases lt_trichotomy (a.ord y) 0 with hneg | hzero | hpos
    ·
      refine ⟨y, hy0, hyw, fun w' hw' => ?_⟩
      rcases Finset.mem_insert.mp hw' with rfl | hw'S'
      · exact hneg
      · exact hyS' w' hw'S'
    ·
      obtain ⟨r, hr1, hrB⟩ : ∃ r : ℕ, 1 ≤ r ∧ ∀ w' ∈ S', w'.ord z < (r : ℤ) := by
        refine ⟨S'.sup (fun w' => (w'.ord z).toNat) + 1, Nat.le_add_left 1 _,
          fun w' hw' => ?_⟩
        have hle : (w'.ord z).toNat ≤ S'.sup (fun p => (p.ord z).toNat) :=
          Finset.le_sup (f := fun p => (p.ord z).toNat) hw'
        have h1 : w'.ord z ≤ ((w'.ord z).toNat : ℤ) := Int.self_le_toNat _
        have h2 : ((w'.ord z).toNat : ℤ)
            ≤ ((S'.sup (fun p => (p.ord z).toNat) : ℕ) : ℤ) := by exact_mod_cast hle
        omega
      have hyr0 : y ^ r ≠ 0 := pow_ne_zero r hy0
      have hordeq : ∀ p : Place K F, p.ord (y ^ r * z) = (r : ℤ) * p.ord y + p.ord z :=
        fun p => by rw [p.ord_mul hyr0 hz0, gf24a9r_ord_pow]
      refine ⟨y ^ r * z, mul_ne_zero hyr0 hz0, ?_, fun w' hw' => ?_⟩
      · rw [hordeq w]
        have hnn : 0 ≤ (r : ℤ) * w.ord y := mul_nonneg (by omega) hyw.le
        linarith
      · rcases Finset.mem_insert.mp hw' with rfl | hw'S'
        · rw [hordeq w', hzero, mul_zero, zero_add]
          exact hza
        · rw [hordeq w']
          have h1 : w'.ord y ≤ -1 := by have := hyS' w' hw'S'; omega
          have h2 : (r : ℤ) * w'.ord y ≤ (r : ℤ) * (-1) :=
            mul_le_mul_of_nonneg_left h1 (by omega)
          have h3 := hrB w' hw'S'
          linarith
    ·
      obtain ⟨r, hr1, hrB⟩ : ∃ r : ℕ, 1 ≤ r ∧ ∀ w' ∈ S', w'.ord z < (r : ℤ) := by
        refine ⟨S'.sup (fun w' => (w'.ord z).toNat) + 1, Nat.le_add_left 1 _,
          fun w' hw' => ?_⟩
        have hle : (w'.ord z).toNat ≤ S'.sup (fun p => (p.ord z).toNat) :=
          Finset.le_sup (f := fun p => (p.ord z).toNat) hw'
        have h1 : w'.ord z ≤ ((w'.ord z).toNat : ℤ) := Int.self_le_toNat _
        have h2 : ((w'.ord z).toNat : ℤ)
            ≤ ((S'.sup (fun p => (p.ord z).toNat) : ℕ) : ℤ) := by exact_mod_cast hle
        omega
      have hyr0 : y ^ r ≠ 0 := pow_ne_zero r hy0
      have hone : (1 : F) + y ^ r ≠ 0 :=
        gf24a9r_one_add_ne_zero_of_ord_pos a
          (by rw [gf24a9r_ord_pow]; exact mul_pos (by omega) hpos)
      have hordw : w.ord (1 + y ^ r) = 0 :=
        gf24a9r_ord_one_add_of_ord_pos w hyr0
          (by rw [gf24a9r_ord_pow]; exact mul_pos (by omega) hyw)
      have horda : a.ord (1 + y ^ r) = 0 :=
        gf24a9r_ord_one_add_of_ord_pos a hyr0
          (by rw [gf24a9r_ord_pow]; exact mul_pos (by omega) hpos)
      refine ⟨z * (1 + y ^ r), mul_ne_zero hz0 hone, ?_, fun w' hw' => ?_⟩
      · rw [w.ord_mul hz0 hone, hordw]
        omega
      · rcases Finset.mem_insert.mp hw' with rfl | hw'S'
        · rw [w'.ord_mul hz0 hone, horda]
          omega
        · have hyneg : w'.ord (y ^ r) < 0 := by
            rw [gf24a9r_ord_pow]
            exact mul_neg_of_pos_of_neg (by omega) (hyS' w' hw'S')
          have hordw' : w'.ord (1 + y ^ r) = (r : ℤ) * w'.ord y := by
            rw [gf24a9r_ord_one_add_of_ord_neg w' hyr0 hyneg, gf24a9r_ord_pow]
          rw [w'.ord_mul hz0 hone, hordw']
          have h1 : w'.ord y ≤ -1 := by have := hyS' w' hw'S'; omega
          have h2 : (r : ℤ) * w'.ord y ≤ (r : ℤ) * (-1) :=
            mul_le_mul_of_nonneg_left h1 (by omega)
          have h3 := hrB w' hw'S'
          linarith

end Toolkit


section RowB

theorem gf24a9r_cotraceFiberLocalizedPolarApprox
    (K F : Type*) [Field K] [Field F] [Algebra K F]
    (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
    [HasLocalResidue K E] [HasCanonicalLocalResidueKStar K E] [HasLocalResidue K F] [HasCanonicalLocalResidueKStar K F]
    [Algebra.IsIntegral E F] :
    CotraceFiberLocalizedPolarApprox K F E := by
  intro _instE _instF ωE _hωE _hgen v w _hwfib n f hf
  classical
  set ωF := kaehlerPullback K F E ωE

  rcases eq_or_ne f 0 with rfl | hf0
  · refine ⟨0, ?_, fun w' _ _ => Submodule.zero_mem _⟩
    rw [sub_zero]
    exact Submodule.zero_mem _

  obtain ⟨u, hu0, huw, huS⟩ :=
    gf24a9r_exists_separator w ((v.fiber F).erase w) (Finset.notMem_erase w _)

  obtain ⟨r, hr1, hrB⟩ : ∃ r : ℕ, 1 ≤ r ∧ ∀ w' ∈ (v.fiber F).erase w,
      -(w'.ord (f * w'.differentialCoeff ωF)) < (r : ℤ) := by
    refine ⟨((v.fiber F).erase w).sup
        (fun w' => (-(w'.ord (f * w'.differentialCoeff ωF))).toNat) + 1,
      Nat.le_add_left 1 _, fun w' hw' => ?_⟩
    have hle : (-(w'.ord (f * w'.differentialCoeff ωF))).toNat
        ≤ ((v.fiber F).erase w).sup
          (fun p => (-(p.ord (f * p.differentialCoeff ωF))).toNat) :=
      Finset.le_sup (f := fun p => (-(p.ord (f * p.differentialCoeff ωF))).toNat) hw'
    have h1 : -(w'.ord (f * w'.differentialCoeff ωF))
        ≤ ((-(w'.ord (f * w'.differentialCoeff ωF))).toNat : ℤ) := Int.self_le_toNat _
    have h2 : ((-(w'.ord (f * w'.differentialCoeff ωF))).toNat : ℤ)
        ≤ ((((v.fiber F).erase w).sup
          (fun p => (-(p.ord (f * p.differentialCoeff ωF))).toNat) : ℕ) : ℤ) := by
      exact_mod_cast hle
    omega
  have hr1' : (1 : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr1
  have hur0 : u ^ r ≠ 0 := pow_ne_zero r hu0
  have hone : (1 : F) + u ^ r ≠ 0 :=
    gf24a9r_one_add_ne_zero_of_ord_pos w
      (by rw [gf24a9r_ord_pow]; exact mul_pos (by omega) huw)
  have hinv0 : ((1 : F) + u ^ r)⁻¹ ≠ 0 := inv_ne_zero hone
  have hordw_one : w.ord (1 + u ^ r) = 0 :=
    gf24a9r_ord_one_add_of_ord_pos w hur0
      (by rw [gf24a9r_ord_pow]; exact mul_pos (by omega) huw)
  refine ⟨f * ((1 : F) + u ^ r)⁻¹, ?_, ?_⟩
  ·
    have hdiff : f - f * ((1 : F) + u ^ r)⁻¹ = f * u ^ r * ((1 : F) + u ^ r)⁻¹ := by
      have hcancel := mul_inv_cancel₀ hone
      calc f - f * ((1 : F) + u ^ r)⁻¹
          = f * (((1 : F) + u ^ r) * ((1 : F) + u ^ r)⁻¹)
            - f * ((1 : F) + u ^ r)⁻¹ := by rw [hcancel, mul_one]
        _ = f * u ^ r * ((1 : F) + u ^ r)⁻¹ := by ring
    rw [hdiff]
    refine (w.mem_regularPoleSubmodule ωF n _).mpr ?_
    rcases eq_or_ne (w.differentialCoeff ωF) 0 with hdc | hdc
    · rw [hdc, mul_zero, mul_zero]
      exact zero_mem _
    ·
      have hin : 0 ≤ w.ord (w.uniformizer ^ (n + 1) * (f * w.differentialCoeff ωF)) :=
        w.ord_nonneg_of_mem ((w.mem_regularPoleSubmodule ωF (n + 1) f).mp hf)
      rw [w.ord_mul (w.uniformizer_pow_ne_zero _) (mul_ne_zero hf0 hdc),
        w.ord_uniformizer_pow, w.ord_mul hf0 hdc] at hin
      have hX0 : f * u ^ r * ((1 : F) + u ^ r)⁻¹ ≠ 0 :=
        mul_ne_zero (mul_ne_zero hf0 hur0) hinv0
      refine w.mem_of_ord_nonneg
        (mul_ne_zero (w.uniformizer_pow_ne_zero n) (mul_ne_zero hX0 hdc)) ?_
      rw [w.ord_mul (w.uniformizer_pow_ne_zero n) (mul_ne_zero hX0 hdc),
        w.ord_uniformizer_pow, w.ord_mul hX0 hdc,
        w.ord_mul (mul_ne_zero hf0 hur0) hinv0, w.ord_mul hf0 hur0,
        w.ord_inv, hordw_one, gf24a9r_ord_pow]
      have hru : (1 : ℤ) ≤ (r : ℤ) * w.ord u := by
        have huw1 : (1 : ℤ) ≤ w.ord u := by omega
        nlinarith [hr1', huw1]
      push_cast at hin ⊢
      linarith
  ·
    intro w' hw'fib hne
    have hw'S : w' ∈ (v.fiber F).erase w := Finset.mem_erase.mpr ⟨hne, hw'fib⟩
    have hu_neg : w'.ord u < 0 := huS w' hw'S
    refine (w'.mem_regularSubmodule ωF _).mpr ?_
    rcases eq_or_ne (w'.differentialCoeff ωF) 0 with hdc | hdc
    · rw [hdc, mul_zero]
      exact zero_mem _
    · have hre : f * ((1 : F) + u ^ r)⁻¹ * w'.differentialCoeff ωF
          = f * w'.differentialCoeff ωF * ((1 : F) + u ^ r)⁻¹ := by ring
      rw [hre]
      have hfdc : f * w'.differentialCoeff ωF ≠ 0 := mul_ne_zero hf0 hdc
      have hurneg : w'.ord (u ^ r) < 0 := by
        rw [gf24a9r_ord_pow]
        exact mul_neg_of_pos_of_neg (by omega) hu_neg
      have hordw' : w'.ord (1 + u ^ r) = (r : ℤ) * w'.ord u := by
        rw [gf24a9r_ord_one_add_of_ord_neg w' hur0 hurneg, gf24a9r_ord_pow]
      refine w'.mem_of_ord_nonneg (mul_ne_zero hfdc hinv0) ?_
      rw [w'.ord_mul hfdc hinv0, w'.ord_inv, hordw']
      have h1 : w'.ord u ≤ -1 := by omega
      have h2 : (r : ℤ) * w'.ord u ≤ (r : ℤ) * (-1) :=
        mul_le_mul_of_nonneg_left h1 (by omega)
      have h3 := hrB w' hw'S
      linarith

end RowB


section CommittedTower

attribute [local instance 2000] RatFunc.instAlgebraOfPolynomial

end CommittedTower


end ModularCurve.GF24a9RRDx



end


end


end


section
section

set_option maxHeartbeats 6400000
set_option linter.unusedSectionVars false

noncomputable section

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Place.ord Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential diagonalHom diagonalHom_apply diagonal_mem_adeleSpace HasCanonicalDivisor HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTerm kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_support_finite_of_adeleSpace weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK HasCanonicalLocalResidueKStar.dataKStar Place.mem_fiber Place.valuationSubringAlgebra Place.finite_setOf_restrict_eq kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kaehlerCotrace kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt KwHgfV352CompletionTraceSum FiberKaehlerCotraceResidueIdentityK CotraceResidueIdentityOnFiberLocalizedK Place.finiteResidue_of_deg_pos residueTraceCompletionCommute residueTheoremK_ratFunc_of_isAlgClosed)

open _root_.AlgebraicCurve

open scoped _root_.Polynomial _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.Polynomial
open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.ModularCurve.GF24a9RRDx

section KCurrencyRowA

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]
variable [Algebra.IsIntegral E F]

end KCurrencyRowA


section Additivity

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]

theorem kaehlerResidueTermKFam_diagonal_add
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK) (ω : Ω[F⁄K])
    (v : Place K F) (g₁ g₂ : F) :
    kaehlerResidueTermKFam Rfam ω (diagonalHom K F (g₁ + g₂)) v
      = kaehlerResidueTermKFam Rfam ω (diagonalHom K F g₁) v
        + kaehlerResidueTermKFam Rfam ω (diagonalHom K F g₂) v := by
  simp only [kaehlerResidueTermKFam_apply, diagonalHom_apply]
  rw [add_mul, map_add, map_add]

theorem kaehlerResidueTermKFam_diagonal_zero
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK) (ω : Ω[F⁄K])
    (v : Place K F) :
    kaehlerResidueTermKFam Rfam ω (diagonalHom K F (0 : F)) v = 0 := by
  rw [kaehlerResidueTermKFam_apply, diagonalHom_apply, zero_mul, _root_.map_zero, _root_.map_zero]

end Additivity


section Engine

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable {E : Type*} [Field E] [Algebra K E] [HasCanonicalLocalResidueKStar K E]
variable [Algebra E F] [IsScalarTower K E F] [Algebra.IsIntegral E F]
variable [HasLocalResidue K E] [HasLocalResidue K F]

theorem cotraceFiberIdentityK_zero
    [HasPrincipalDivisors K F]
    (RfamF : ∀ w : Place K F, w.CanonicalLocalResidueDataK)
    (RfamE : ∀ v : Place K E, v.CanonicalLocalResidueDataK)
    (ωE : Ω[E⁄K]) (v : Place K E) :
    ∑ w ∈ v.fiber F, kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE)
        (diagonalHom K F (0 : F)) w
      = kaehlerResidueTermKFam RfamE ωE (diagonalHom K E (Algebra.trace E F (0 : F))) v := by
  rw [Finset.sum_eq_zero (fun w _ => kaehlerResidueTermKFam_diagonal_zero RfamF _ w),
    _root_.map_zero (Algebra.trace E F), kaehlerResidueTermKFam_diagonal_zero RfamE ωE v]

theorem cotraceFiberIdentityK_add
    [HasPrincipalDivisors K F]
    (RfamF : ∀ w : Place K F, w.CanonicalLocalResidueDataK)
    (RfamE : ∀ v : Place K E, v.CanonicalLocalResidueDataK)
    {ωE : Ω[E⁄K]} (v : Place K E) {g p : F}
    (hg : ∑ w ∈ v.fiber F, kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE)
        (diagonalHom K F g) w
      = kaehlerResidueTermKFam RfamE ωE (diagonalHom K E (Algebra.trace E F g)) v)
    (hp : ∑ w ∈ v.fiber F, kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE)
        (diagonalHom K F p) w
      = kaehlerResidueTermKFam RfamE ωE (diagonalHom K E (Algebra.trace E F p)) v) :
    ∑ w ∈ v.fiber F, kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE)
        (diagonalHom K F (g + p)) w
      = kaehlerResidueTermKFam RfamE ωE (diagonalHom K E (Algebra.trace E F (g + p))) v := by
  calc ∑ w ∈ v.fiber F, kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE)
          (diagonalHom K F (g + p)) w
      = ∑ w ∈ v.fiber F,
          (kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE) (diagonalHom K F g) w
            + kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE)
                (diagonalHom K F p) w) :=
        Finset.sum_congr rfl fun w _ =>
          kaehlerResidueTermKFam_diagonal_add RfamF (kaehlerPullback K F E ωE) w g p
    _ = (∑ w ∈ v.fiber F, kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE)
            (diagonalHom K F g) w)
          + ∑ w ∈ v.fiber F, kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE)
              (diagonalHom K F p) w :=
        Finset.sum_add_distrib
    _ = kaehlerResidueTermKFam RfamE ωE (diagonalHom K E (Algebra.trace E F g)) v
          + kaehlerResidueTermKFam RfamE ωE (diagonalHom K E (Algebra.trace E F p)) v := by
        rw [hg, hp]
    _ = kaehlerResidueTermKFam RfamE ωE
          (diagonalHom K E (Algebra.trace E F g + Algebra.trace E F p)) v :=
        (kaehlerResidueTermKFam_diagonal_add RfamE ωE v _ _).symm
    _ = kaehlerResidueTermKFam RfamE ωE
          (diagonalHom K E (Algebra.trace E F (g + p))) v := by
        rw [← map_add]

theorem cotraceFiberIdentityK_of_uniform_layer
    [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]
    (RfamF : ∀ w : Place K F, w.CanonicalLocalResidueDataK)
    (RfamE : ∀ v : Place K E, v.CanonicalLocalResidueDataK)
    {ωE : Ω[E⁄K]} (hωE : ωE ≠ 0) (hgen : kaehlerPullback K F E ωE ≠ 0)
    (hA' : ∀ (v : Place K E) (p : F),
        (∀ w₁ ∈ v.fiber F, ∀ w₂ ∈ v.fiber F,
          p ∉ w₁.regularSubmodule (kaehlerPullback K F E ωE) →
          p ∉ w₂.regularSubmodule (kaehlerPullback K F E ωE) → w₁ = w₂) →
        ∑ w ∈ v.fiber F, kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE)
            (diagonalHom K F p) w
          = kaehlerResidueTermKFam RfamE ωE (diagonalHom K E (Algebra.trace E F p)) v)
    (hB : CotraceFiberLocalizedPolarApprox K F E)
    (v : Place K E) :
    ∀ (N : ℕ) (f : F),
      (∀ w ∈ v.fiber F, f ∈ w.regularPoleSubmodule (kaehlerPullback K F E ωE) N) →
      ∑ w ∈ v.fiber F, kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE)
          (diagonalHom K F f) w
        = kaehlerResidueTermKFam RfamE ωE (diagonalHom K E (Algebra.trace E F f)) v := by
  intro N
  induction N with
  | zero =>
    intro f hf
    refine hA' v f ?_
    intro w₁ hw₁ w₂ hw₂ hp₁ hp₂
    exfalso
    have hreg := hf w₁ hw₁
    have hEq : w₁.regularPoleSubmodule (kaehlerPullback K F E ωE) 0 =
        w₁.regularSubmodule (kaehlerPullback K F E ωE) :=
      Place.regularPoleSubmodule_zero w₁ (kaehlerPullback K F E ωE)
    rw [hEq] at hreg
    exact hp₁ hreg
  | succ N ih =>
    intro f hf
    classical

    choose! q hq1 hq2 using fun (w : Place K F) (hw : w ∈ v.fiber F) =>
      hB hωE hgen v w hw N f (hf w hw)

    have hrem : ∀ w₀ ∈ v.fiber F,
        f - ∑ w ∈ v.fiber F, q w
          ∈ w₀.regularPoleSubmodule (kaehlerPullback K F E ωE) N := by
      intro w₀ hw₀
      have hsplit : ∑ w ∈ v.fiber F, q w
          = q w₀ + ∑ w ∈ (v.fiber F).erase w₀, q w :=
        (Finset.add_sum_erase _ q hw₀).symm
      have heq : f - ∑ w ∈ v.fiber F, q w
          = (f - q w₀) - ∑ w ∈ (v.fiber F).erase w₀, q w := by
        rw [hsplit]; ring
      rw [heq]
      refine Submodule.sub_mem _ (hq1 w₀ hw₀) (Submodule.sum_mem _ ?_)
      intro w hw
      have hwfib : w ∈ v.fiber F := Finset.mem_of_mem_erase hw
      have hwne : w ≠ w₀ := Finset.ne_of_mem_erase hw
      have hq_reg : q w ∈ w₀.regularSubmodule (kaehlerPullback K F E ωE) :=
        hq2 w hwfib w₀ hw₀ (Ne.symm hwne)
      rw [← Place.regularPoleSubmodule_zero] at hq_reg
      exact w₀.regularPoleSubmodule_mono _ (Nat.zero_le N) hq_reg

    have hrem_ident := ih (f - ∑ w ∈ v.fiber F, q w) hrem

    have happrox_ident : ∀ w ∈ v.fiber F,
        ∑ w' ∈ v.fiber F, kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE)
            (diagonalHom K F (q w)) w'
          = kaehlerResidueTermKFam RfamE ωE
              (diagonalHom K E (Algebra.trace E F (q w))) v := by
      intro w hw
      refine hA' v (q w) ?_
      intro w₁ hw₁ w₂ hw₂ hp₁ hp₂
      have h₁ : w₁ = w := by
        by_contra hne
        exact hp₁ (hq2 w hw w₁ hw₁ hne)
      have h₂ : w₂ = w := by
        by_contra hne
        exact hp₂ (hq2 w hw w₂ hw₂ hne)
      rw [h₁, h₂]

    have hsum_ident :
        ∑ w' ∈ v.fiber F, kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE)
            (diagonalHom K F (∑ w ∈ v.fiber F, q w)) w'
          = kaehlerResidueTermKFam RfamE ωE
              (diagonalHom K E (Algebra.trace E F (∑ w ∈ v.fiber F, q w))) v :=
      Finset.sum_induction q
        (fun x => ∑ w' ∈ v.fiber F, kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE)
            (diagonalHom K F x) w'
          = kaehlerResidueTermKFam RfamE ωE (diagonalHom K E (Algebra.trace E F x)) v)
        (fun a b ha hb => cotraceFiberIdentityK_add RfamF RfamE v ha hb)
        (cotraceFiberIdentityK_zero RfamF RfamE ωE v)
        happrox_ident

    have hcombined := cotraceFiberIdentityK_add RfamF RfamE v hrem_ident hsum_ident
    rwa [sub_add_cancel] at hcombined

theorem fiberKaehlerCotraceResidueIdentityK_of_rowAK_rowB
    (hA : CotraceResidueIdentityOnFiberLocalizedK K F E)
    (hB : CotraceFiberLocalizedPolarApprox K F E) :
    FiberKaehlerCotraceResidueIdentityK K F E := by
  intro instE instF RfamF ωE hωE hgen
  obtain ⟨RfamE, hA'⟩ := hA RfamF hωE hgen
  refine ⟨RfamE, fun v f => ?_⟩
  classical

  choose nfun hnfun using fun w : Place K F =>
    w.exists_mem_regularPoleSubmodule (kaehlerPullback K F E ωE) f

  refine cotraceFiberIdentityK_of_uniform_layer RfamF RfamE hωE hgen hA' hB v
    (∑ w ∈ v.fiber F, nfun w) f (fun w hw => ?_)
  exact w.regularPoleSubmodule_mono _
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hw) (hnfun w)

end Engine


section RowBDischarged

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable {E : Type*} [Field E] [Algebra K E] [HasCanonicalLocalResidueKStar K E]
variable [Algebra E F] [IsScalarTower K E F] [Algebra.IsIntegral E F]
variable [HasLocalResidue K E] [HasLocalResidue K F]

theorem fiberKaehlerCotraceResidueIdentityK_of_rowAK
    (hA : CotraceResidueIdentityOnFiberLocalizedK K F E) :
    FiberKaehlerCotraceResidueIdentityK K F E :=
  fiberKaehlerCotraceResidueIdentityK_of_rowAK_rowB hA
    (gf24a9r_cotraceFiberLocalizedPolarApprox K F E)

end RowBDischarged


section Composite

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)]
variable [∀ w : Place K F, w.DCoordGenerates]
variable {E : Type*} [Field E] [Algebra K E]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalDivisor (K := K) (F := E)]
variable [∀ v : Place K E, v.DCoordGenerates]
variable [Algebra E F] [IsScalarTower K E F] [Algebra.IsIntegral E F]
variable [HasLocalResidue K E] [HasLocalResidue K F]

end Composite


section CompositeRatFunc

variable {K F : Type*} [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)]
variable [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [HasCanonicalDivisor (K := K) (F := F)] [∀ w : Place K F, w.DCoordGenerates]
variable [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
variable [Algebra.IsIntegral (RatFunc K) F] [HasLocalResidue K F]

theorem residueTheoremK_of_rowAK_ratFunc_isAlgClosed
    [HasPrincipalDivisors K F]
    (hgen : kaehlerPullback K F (RatFunc K) (dX K) ≠ 0)
    (hA : CotraceResidueIdentityOnFiberLocalizedK K F (RatFunc K)) :
    ResidueTheoremK K F :=
  residueTheoremK_of_cotraceResidueIdentityK_ratFunc_isAlgClosed hgen
    (fiberKaehlerCotraceResidueIdentityK_of_rowAK hA)

end CompositeRatFunc


section SelfGate

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]

variable [HasLocalResidue K F]

end SelfGate


end AlgebraicCurve


end


end


end


section
section

set_option maxHeartbeats 6400000
set_option linter.unusedSectionVars false

noncomputable section

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Place.ord Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential diagonalHom diagonalHom_apply diagonal_mem_adeleSpace HasCanonicalDivisor HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTerm kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_support_finite_of_adeleSpace weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK HasCanonicalLocalResidueKStar.dataKStar Place.mem_fiber Place.valuationSubringAlgebra Place.finite_setOf_restrict_eq kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kaehlerCotrace kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt KwHgfV352CompletionTraceSum FiberKaehlerCotraceResidueIdentityK CotraceResidueIdentityOnFiberLocalizedK Place.finiteResidue_of_deg_pos residueTraceCompletionCommute residueTheoremK_ratFunc_of_isAlgClosed)

open _root_.AlgebraicCurve

open scoped _root_.Polynomial _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.Polynomial
open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.ModularCurve.GF24a11bRowACurrencyBridge

section DataKStarSeam

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]

theorem kaehlerResidueTermKFam_dataKStar (ω : Ω[F⁄K]) (α : Place K F → F) (v : Place K F) :
    kaehlerResidueTermKFam (HasCanonicalLocalResidueKStar.dataKStar) ω α v
      = kaehlerResidueTerm ω α v := rfl

theorem kaehlerResidueTermKFam_eq_of_subsingleton
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK) (ω : Ω[F⁄K]) (α : Place K F → F)
    (v : Place K F) (hsub : Subsingleton v.CanonicalLocalResidueDataK) :
    kaehlerResidueTermKFam Rfam ω α v = kaehlerResidueTerm ω α v := by
  have hR : Rfam v = HasCanonicalLocalResidueKStar.dataKStar v := hsub.elim _ _
  rw [kaehlerResidueTermKFam_apply, hR]
  rfl

end DataKStarSeam


section AlgClosedSurj

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place
export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue heightOneSpectrum adicValuation adicValuation_ne_zero adicValuation_coe_eq_one_iff adicValuation_coe_irreducible ord ord_zero ord_one ord_mul ord_inv ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ord_smul ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one isEquiv_adicValuation_ofHeightOneSpectrum ord_ofHeightOneSpectrum_ne_zero_iff dCoord DCoordGenerates dCoord_ne_zero differentialCoeff exists_eq_smul_dCoord differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero CanonicalLocalResidueDataK localResidue localResidue_eq_zero_of_ord_nonneg differentialCoeff_ne_zero ramificationIndex ramificationIndex_pos restrict ord_restrict restrictInclusion inertiaDeg deg_restrict_mul_inertiaDeg fiber mem_fiber ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq adicCompletion adicCompletionIntegers kw_ffgc_adicCompletionComap kw_ffgc_valued_adicCompletionComap kw_ffgc_adicCompletionComapIntegers kw_ffgc_adicCompletionComapIntegers_coe kw_ffgc_algebraAdicCompletionComap kw_ffgc_algebraMap_adicCompletionComap_eq kw_ffgc_rankOne_adicCompletion kw_ffgc_absoluteValue kw_ffgc_adicCompletionComap_algebraMap_algebraMap kw_ffgc_completionLinearCombination kw_ffgc_denseRange_completionLinearCombination kw_ffgc_finiteDimensional_adicCompletion kw_ffgc_completionTraceF' regularSubmodule finiteResidue_of_deg_pos poleSubmodule uniformizer_pow_ne_zero ord_uniformizer_pow poleSubmodule_mono iSup_poleSubmodule_eq_top exists_mem_poleSubmodule canonicalLocalResidueDataK_agree_on_poleSubmodule_of_surj)
end Place
namespace Place
open scoped _root_.AlgebraicCurve.Place in
theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.surjective_algebraMap_residueField_of_isAlgClosed_of_finiteResidue
    [IsAlgClosed K] (v : Place K F) [v.FiniteResidue] :
    Function.Surjective (algebraMap K v.ResidueField) := by
  have : Module.Finite K v.ResidueField := Place.FiniteResidue.finite
  have : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K)
    (K := v.ResidueField)).surjective

-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.surjective_algebraMap_residueField_of_isAlgClosed_of_finiteResidue :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.surjective_algebraMap_residueField_of_isAlgClosed_of_finiteResidue
end Place



namespace Place
open scoped _root_.AlgebraicCurve.Place in
theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.subsingleton_canonicalLocalResidueDataK_of_isAlgClosed_of_finiteResidue
    [IsAlgClosed K] (v : Place K F) [v.FiniteResidue] :
    Subsingleton v.CanonicalLocalResidueDataK :=
  v.subsingleton_canonicalLocalResidueDataK_of_surj
    v.surjective_algebraMap_residueField_of_isAlgClosed_of_finiteResidue

-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.subsingleton_canonicalLocalResidueDataK_of_isAlgClosed_of_finiteResidue :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.subsingleton_canonicalLocalResidueDataK_of_isAlgClosed_of_finiteResidue
end Place



end AlgClosedSurj


section SubsingletonBridge

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable {E : Type*} [Field E] [Algebra K E] [HasCanonicalLocalResidueKStar K E]
variable [Algebra E F] [IsScalarTower K E F] [Algebra.IsIntegral E F]

theorem cotraceResidueIdentityOnFiberLocalizedK_of_committed
    (hsubF : ∀ w : Place K F, Subsingleton w.CanonicalLocalResidueDataK)
    (h : CotraceResidueIdentityOnFiberLocalized K F E) :
    CotraceResidueIdentityOnFiberLocalizedK K F E := by
  intro _ _ RfamF ωE hωE hgen
  refine ⟨HasCanonicalLocalResidueKStar.dataKStar, fun v p hloc => ?_⟩
  calc ∑ w ∈ v.fiber F, kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE)
          (diagonalHom K F p) w
      = ∑ w ∈ v.fiber F, kaehlerResidueTerm (kaehlerPullback K F E ωE)
          (diagonalHom K F p) w := by
        refine Finset.sum_congr rfl fun w _ => ?_
        exact kaehlerResidueTermKFam_eq_of_subsingleton RfamF _ _ w (hsubF w)
    _ = kaehlerResidueTerm ωE (diagonalHom K E (Algebra.trace E F p)) v :=
        h hωE hgen v p hloc
    _ = kaehlerResidueTermKFam (HasCanonicalLocalResidueKStar.dataKStar) ωE
          (diagonalHom K E (Algebra.trace E F p)) v :=
        (kaehlerResidueTermKFam_dataKStar ωE _ v).symm

end SubsingletonBridge


section Reduction

variable {K F : Type*} [Field K] [IsAlgClosed K]
variable [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
variable [Algebra.IsIntegral (RatFunc K) F] [Module.Finite (RatFunc K) F]
variable [∀ w : Place K F, w.FiniteResidue]

end Reduction


section ProductionComposite

variable {K F : Type*} [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)]
variable [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [HasCanonicalDivisor (K := K) (F := F)] [∀ w : Place K F, w.DCoordGenerates]
variable [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
variable [Algebra.IsIntegral (RatFunc K) F] [Module.Finite (RatFunc K) F]
variable [HasLocalResidue K F]
variable [∀ w : Place K F, w.FiniteResidue]

end ProductionComposite


section SelfGate

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]

end SelfGate


end AlgebraicCurve


end


end


end


section
section

set_option maxHeartbeats 6400000
set_option linter.unusedSectionVars false

noncomputable section

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Place.ord Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential diagonalHom diagonalHom_apply diagonal_mem_adeleSpace HasCanonicalDivisor HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTerm kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_support_finite_of_adeleSpace weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK HasCanonicalLocalResidueKStar.dataKStar Place.mem_fiber Place.valuationSubringAlgebra Place.finite_setOf_restrict_eq kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kaehlerCotrace kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt KwHgfV352CompletionTraceSum FiberKaehlerCotraceResidueIdentityK CotraceResidueIdentityOnFiberLocalizedK Place.finiteResidue_of_deg_pos residueTraceCompletionCommute residueTheoremK_ratFunc_of_isAlgClosed)

open _root_.AlgebraicCurve

open scoped _root_.Polynomial _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.Polynomial
open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField
open ModularCurve.GF24a11bRowACurrencyBridge ModularCurve.GF24a12CohenSupply
open Ldgr23CohenDefectCorrectionSlice Ldgr24DefectKernelSlice
open Modularity.Ldgr27TraceSemilinearSlice

section SemilinearDefect

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]

end SemilinearDefect


section RefinedAtom

variable (K F : Type*) [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable (E : Type*) [Field E] [Algebra K E] [HasCanonicalLocalResidueKStar K E]
variable [Algebra E F] [IsScalarTower K E F]
variable [HasLocalResidue K E] [HasLocalResidue K F]
variable [Algebra.IsIntegral E F]

end RefinedAtom


section KaehlerPullbackSmul

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]

theorem kw_mlc_hrtCharP7_kaehlerPullback_smul (g : E) (ωE : Ω[E⁄K]) :
    kaehlerPullback K F E (g • ωE) = (algebraMap E F g) • kaehlerPullback K F E ωE := by
  show (KaehlerDifferential.map K K E F) (g • ωE)
    = (algebraMap E F g) • (KaehlerDifferential.map K K E F) ωE
  rw [LinearMap.map_smul, algebra_compatible_smul F g]

end KaehlerPullbackSmul


section OmegaBandBridge

variable (K F : Type*) [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable (E : Type*) [Field E] [Algebra K E] [HasCanonicalLocalResidueKStar K E]
variable [Algebra E F] [IsScalarTower K E F]
variable [HasLocalResidue K E] [HasLocalResidue K F]
variable [Algebra.IsIntegral E F]

end OmegaBandBridge


section Production

variable {K F : Type*} [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)]
variable [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [HasCanonicalDivisor (K := K) (F := F)] [∀ w : Place K F, w.DCoordGenerates]
variable [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
variable [Algebra.IsIntegral (RatFunc K) F] [Module.Finite (RatFunc K) F]
variable [HasLocalResidue K F]
variable [∀ w : Place K F, w.FiniteResidue]

end Production


section SATGate

variable (K F : Type*) [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable (E : Type*) [Field E] [Algebra K E] [HasCanonicalLocalResidueKStar K E]
variable [Algebra E F] [IsScalarTower K E F]
variable [HasLocalResidue K E] [HasLocalResidue K F]
variable [Algebra.IsIntegral E F]

end SATGate


end AlgebraicCurve


end


end


end


section
section

set_option maxHeartbeats 6400000
set_option linter.unusedSectionVars false

noncomputable section

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.ModularCurve.GF24a12CohenSupply
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.Ldgr23CohenDefectCorrectionSlice
open Ldgr24DefectKernelSlice ModularCurve.GF24a11bRowACurrencyBridge

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Place.ord Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential diagonalHom diagonalHom_apply diagonal_mem_adeleSpace HasCanonicalDivisor HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTerm kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_support_finite_of_adeleSpace weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK HasCanonicalLocalResidueKStar.dataKStar Place.mem_fiber Place.valuationSubringAlgebra Place.finite_setOf_restrict_eq kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kaehlerCotrace kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt KwHgfV352CompletionTraceSum FiberKaehlerCotraceResidueIdentityK CotraceResidueIdentityOnFiberLocalizedK Place.finiteResidue_of_deg_pos residueTraceCompletionCommute residueTheoremK_ratFunc_of_isAlgClosed)

open _root_.AlgebraicCurve

section KappaTraceCollapse

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

end KappaTraceCollapse


section ESemilinearDeadEnd

variable (K F : Type*) [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable (E : Type*) [Field E] [Algebra K E] [HasCanonicalLocalResidueKStar K E]
variable [Algebra E F] [IsScalarTower K E F]
variable [HasLocalResidue K E] [HasLocalResidue K F]
variable [Algebra.IsIntegral E F]

end ESemilinearDeadEnd


section FKCRIWire

variable (K F : Type*) [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable (E : Type*) [Field E] [Algebra K E] [HasCanonicalLocalResidueKStar K E]
variable [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

theorem kw_mlc_hrtCharP9_cotraceResidueIdentityOnFiberLocalized_of_fkcri
    (h : FiberKaehlerCotraceResidueIdentity K F E) :
    CotraceResidueIdentityOnFiberLocalized K F E := by
  intro _ _ ωE hωE hgen v p _
  exact h hωE hgen v p

end FKCRIWire


section FKCRIProduction

variable {K F : Type*} [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)]
variable [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [HasCanonicalDivisor (K := K) (F := F)] [∀ w : Place K F, w.DCoordGenerates]
variable [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
variable [Algebra.IsIntegral (RatFunc K) F] [Module.Finite (RatFunc K) F]
variable [HasLocalResidue K F]
variable [∀ w : Place K F, w.FiniteResidue]

theorem residueTheoremK_of_fiberKaehlerCotraceResidueIdentity_ratFunc_isAlgClosed
    [HasPrincipalDivisors K F]
    (hgen : kaehlerPullback K F (RatFunc K) (dX K) ≠ 0)
    (hFKCRI : FiberKaehlerCotraceResidueIdentity K F (RatFunc K)) :
    ResidueTheoremK K F :=
  residueTheoremK_of_rowAK_ratFunc_isAlgClosed hgen
    (cotraceResidueIdentityOnFiberLocalizedK_of_committed
      (fun w => w.subsingleton_canonicalLocalResidueDataK_of_isAlgClosed_of_finiteResidue)
      (kw_mlc_hrtCharP9_cotraceResidueIdentityOnFiberLocalized_of_fkcri K F (RatFunc K)
        hFKCRI))

end FKCRIProduction


section SATGate

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]

end SATGate


section ResidualRecord

end ResidualRecord


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
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.ModularCurve.GF24a9RRDx
open _root_.AlgebraicCurve.Place
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place
open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.IsDedekindDomain

noncomputable section

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Place.ord Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential diagonalHom diagonalHom_apply diagonal_mem_adeleSpace HasCanonicalDivisor HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTerm kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_support_finite_of_adeleSpace weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK HasCanonicalLocalResidueKStar.dataKStar Place.mem_fiber Place.valuationSubringAlgebra Place.finite_setOf_restrict_eq kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kaehlerCotrace kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt KwHgfV352CompletionTraceSum FiberKaehlerCotraceResidueIdentityK CotraceResidueIdentityOnFiberLocalizedK Place.finiteResidue_of_deg_pos residueTraceCompletionCommute residueTheoremK_ratFunc_of_isAlgClosed)

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

theorem kwHgfV352_localResidueCompletion_sum (v : Place K E) {ι : Type*}
    (s : Finset ι) (f : ι → v.adicCompletion) :
    kwHgfV352_localResidueCompletion v (∑ i ∈ s, f i)
      = ∑ i ∈ s, kwHgfV352_localResidueCompletion v (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [show (0 : v.adicCompletion) = algebraMap E v.adicCompletion 0 from (_root_.map_zero _).symm,
      kwHgfV352_localResidueCompletion_algebraMap, _root_.map_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, kwHgfV352_localResidueCompletion_add, ih,
      Finset.sum_insert ha]

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
set_option linter.unusedSectionVars false

noncomputable section

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.ModularCurve.GF24a9RRDx
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.RationalFunctionField
open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Place.ord Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential diagonalHom diagonalHom_apply diagonal_mem_adeleSpace HasCanonicalDivisor HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTerm kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_support_finite_of_adeleSpace weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK HasCanonicalLocalResidueKStar.dataKStar Place.mem_fiber Place.valuationSubringAlgebra Place.finite_setOf_restrict_eq kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kaehlerCotrace kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt KwHgfV352CompletionTraceSum FiberKaehlerCotraceResidueIdentityK CotraceResidueIdentityOnFiberLocalizedK Place.finiteResidue_of_deg_pos residueTraceCompletionCommute residueTheoremK_ratFunc_of_isAlgClosed)

open _root_.AlgebraicCurve

section ChainRule

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Nontrivial Ω[F⁄K]]

open scoped _root_.AlgebraicCurve.Place in
theorem Place.differentialCoeff_kaehlerPullback [Nontrivial Ω[E⁄K]]
    (v : Place K E) [v.DCoordGenerates] (w : Place K F) [w.DCoordGenerates]
    (ωE : Ω[E⁄K]) :
    w.differentialCoeff (kaehlerPullback K F E ωE)
      = algebraMap E F (v.differentialCoeff ωE)
        * w.differentialCoeff (kaehlerPullback K F E v.dCoord) := by
  conv_lhs => rw [← v.differentialCoeff_smul_dCoord ωE,
    kw_mlc_hrtCharP7_kaehlerPullback_smul, w.differentialCoeff_smul]

variable [Algebra.IsIntegral E F]

end ChainRule


section Mints

variable (K F E : Type*) [Field K] [Field F] [Algebra K F]
variable [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

end Mints


section CotrDXEffLift

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
variable [Algebra.IsIntegral (RatFunc K) F]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalLocalResidueKStar K F]
variable [Nontrivial Ω[F⁄K]] [∀ w : Place K F, w.DCoordGenerates]
variable [Nontrivial Ω[(RatFunc K)⁄K]] [∀ v : Place K (RatFunc K), v.DCoordGenerates]

end CotrDXEffLift


section R1

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]
variable [Nontrivial Ω[F⁄K]] [∀ w : Place K F, w.DCoordGenerates]
variable [Nontrivial Ω[E⁄K]] [∀ v : Place K E, v.DCoordGenerates]

end R1


section NewFloor

variable {K F : Type*} [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)]
variable [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [HasCanonicalDivisor (K := K) (F := F)] [∀ w : Place K F, w.DCoordGenerates]
variable [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
variable [Algebra.IsIntegral (RatFunc K) F] [Module.Finite (RatFunc K) F]
variable [HasLocalResidue K F]
variable [∀ w : Place K F, w.FiniteResidue]
variable [Nontrivial Ω[F⁄K]]
variable [Nontrivial Ω[(RatFunc K)⁄K]] [∀ v : Place K (RatFunc K), v.DCoordGenerates]

end NewFloor


section SATGate

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [HasLocalResidue K F]

end SATGate


section W5Probe

end W5Probe


end AlgebraicCurve


end


end


end


section
section

set_option maxHeartbeats 6400000
set_option linter.unusedSectionVars false

noncomputable section

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Place.ord Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential diagonalHom diagonalHom_apply diagonal_mem_adeleSpace HasCanonicalDivisor HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTerm kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_support_finite_of_adeleSpace weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK HasCanonicalLocalResidueKStar.dataKStar Place.mem_fiber Place.valuationSubringAlgebra Place.finite_setOf_restrict_eq kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kaehlerCotrace kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt KwHgfV352CompletionTraceSum FiberKaehlerCotraceResidueIdentityK CotraceResidueIdentityOnFiberLocalizedK Place.finiteResidue_of_deg_pos residueTraceCompletionCommute residueTheoremK_ratFunc_of_isAlgClosed)

open _root_.AlgebraicCurve

open _root_.FunctionField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.FunctionField
open _root_.KaehlerDifferential
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.KaehlerDifferential
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.ModularCurve.GF24a9RRDx

section OmegaShift

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [HasCanonicalLocalResidueKStar K F]
variable [Nontrivial Ω[F⁄K]]

theorem kaehlerResidueTerm_kaehlerPullback_diagonal_eq_dCoord_shift
    [Nontrivial Ω[E⁄K]] (v : Place K E) [v.DCoordGenerates]
    (w : Place K F) [w.DCoordGenerates] (ωE : Ω[E⁄K]) (g : F) :
    kaehlerResidueTerm (kaehlerPullback K F E ωE) (diagonalHom K F g) w
      = kaehlerResidueTerm (kaehlerPullback K F E v.dCoord)
          (diagonalHom K F (g * algebraMap E F (v.differentialCoeff ωE))) w := by
  unfold kaehlerResidueTerm
  congr 2
  show g * w.differentialCoeff (kaehlerPullback K F E ωE)
    = g * algebraMap E F (v.differentialCoeff ωE)
        * w.differentialCoeff (kaehlerPullback K F E v.dCoord)
  rw [Place.differentialCoeff_kaehlerPullback v w ωE, mul_assoc]

variable [HasCanonicalLocalResidueKStar K E]

end OmegaShift


section FPATransfer

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [HasCanonicalLocalResidueKStar K F] [HasPrincipalDivisors K F]
variable [Nontrivial Ω[F⁄K]] [∀ w : Place K F, w.DCoordGenerates]

end FPATransfer


section MainDischarge

variable {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
variable [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
variable [Algebra.IsIntegral (RatFunc K) F]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalLocalResidueKStar K F]
variable [Nontrivial Ω[F⁄K]] [∀ w : Place K F, w.DCoordGenerates]
variable [Nontrivial Ω[(RatFunc K)⁄K]] [∀ v : Place K (RatFunc K), v.DCoordGenerates]
variable [∀ w : Place K F, w.FiniteResidue]

end MainDischarge


section NewFloor

variable {K F : Type*} [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)]
variable [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [HasCanonicalDivisor (K := K) (F := F)] [∀ w : Place K F, w.DCoordGenerates]
variable [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
variable [Algebra.IsIntegral (RatFunc K) F] [Module.Finite (RatFunc K) F]
variable [HasLocalResidue K F]
variable [∀ w : Place K F, w.FiniteResidue]
variable [Nontrivial Ω[F⁄K]]
variable [Nontrivial Ω[(RatFunc K)⁄K]] [∀ v : Place K (RatFunc K), v.DCoordGenerates]

end NewFloor


section W5Probe

end W5Probe


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
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place
open _root_.FunctionField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.FunctionField
open _root_.KaehlerDifferential
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.KaehlerDifferential
open ModularCurve.GF24a9RRDx

noncomputable section

namespace ModularCurve

export _root_.ModularCurve (KwF4R1V391a.KwF4R1V391aResidueTraceCompletionCommute)

namespace KwF4R1V391a

export _root_.ModularCurve.KwF4R1V391a (KwF4R1V391aResidueTraceCompletionCommute)

open _root_.ModularCurve.KwF4R1V391a
open _root_.ModularCurve

section CompletionTraceAtLinear

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F] [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]
variable [FiniteDimensional E F]

theorem kwF4R1V391a_completionTraceF'_mul_algebraMap (w : Place K F) (g : F) (c : E) :
    kw_ffgc_completionTraceF' E w (g * algebraMap E F c)
      = kw_ffgc_completionTraceF' E w g
          * algebraMap E (w.restrict E).adicCompletion c := by
  rw [kw_ffgc_completionTraceF'_apply, kw_ffgc_completionTraceF'_apply, map_mul,
    kw_ffgc_adicCompletionComap_algebraMap_algebraMap E w c,
    mul_comm (algebraMap F w.adicCompletion g) _, ← Algebra.smul_def,
    LinearMap.map_smul, smul_eq_mul, mul_comm]

theorem kwF4R1V391a_completionTraceAt_mul_algebraMap
    (v : Place K E) (w : Place K F) (hw : w ∈ v.fiber F) (g : F) (c : E) :
    kwHgfV352_completionTraceAt v w hw (g * algebraMap E F c)
      = kwHgfV352_completionTraceAt v w hw g * algebraMap E v.adicCompletion c := by
  have hv : w.restrict E = v := Place.mem_fiber.mp hw
  subst hv
  show (Place.mem_fiber.mp hw ▸ kw_ffgc_completionTraceF' E w (g * algebraMap E F c))
    = (Place.mem_fiber.mp hw ▸ kw_ffgc_completionTraceF' E w g)
        * algebraMap E (w.restrict E).adicCompletion c

  rw [kwF4R1V391a_completionTraceF'_mul_algebraMap w g c]

end CompletionTraceAtLinear


section Mint

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]

end Mint


section Engine

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]

end Engine


end ModularCurve.KwF4R1V391a



end

end


end


section
section

set_option maxHeartbeats 1600000

namespace FLT
namespace Gapsw7X3xCrossPlaceTraceDecomposition

open scoped _root_.NumberField _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.NumberField _root_.TensorProduct _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.TensorProduct
open FLT.Gapsw7X1mCompletionCarrier
open FLT.Gapsw7X3jCarrierAlgebraWiring
open FLT.Gapsw7X3mCompletionFieldFiniteDimensional

theorem gapsw7_x3x_trace_pi (R : Type*) [CommRing R] {ι : Type*} [Fintype ι]
    (S : ι → Type*) [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
    [∀ i, Module.Free R (S i)] [∀ i, Module.Finite R (S i)]
    (x : ∀ i, S i) :
    Algebra.trace R (∀ i, S i) x = ∑ i, Algebra.trace R (S i) (x i) := by
  have _em := Classical.em
  classical
  let b : ∀ i, Module.Basis (Module.Free.ChooseBasisIndex R (S i)) R (S i) :=
    fun i => Module.Free.chooseBasis R (S i)
  have key : Algebra.leftMulMatrix (Pi.basis b) x
      = Matrix.blockDiagonal' (fun i => Algebra.leftMulMatrix (b i) (x i)) := by
    refine Matrix.ext fun ji ji' => ?_
    obtain ⟨i, j⟩ := ji
    obtain ⟨i', j'⟩ := ji'
    rcases eq_or_ne i i' with rfl | hne
    · rw [Matrix.blockDiagonal'_apply_eq, Algebra.leftMulMatrix_eq_repr_mul,
        Algebra.leftMulMatrix_eq_repr_mul, Pi.basis_apply, Pi.basis_repr]
      have hx : (x * Pi.single i (b i j')) i = x i * b i j' := by
        simp
      rw [hx]
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hne,
        Algebra.leftMulMatrix_eq_repr_mul, Pi.basis_apply, Pi.basis_repr]
      have hx : (x * Pi.single i' (b i' j')) i = 0 := by
        simp [Pi.single_eq_of_ne hne]
      rw [hx]
      simp
  rw [Algebra.trace_eq_matrix_trace (Pi.basis b), key,
    Matrix.trace_blockDiagonal']
  exact Finset.sum_congr rfl fun i _ =>
    (Algebra.trace_eq_matrix_trace (b i) (x i)).symm

theorem gapsw7_x3x_trace_baseChange (R A B : Type*) [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra R B] [Module.Free R B]
    [Module.Finite R B] (b : B) :
    Algebra.trace A (A ⊗[R] B) ((1 : A) ⊗ₜ[R] b)
      = algebraMap R A (Algebra.trace R B b) := by
  have _em := Classical.em
  have h := LinearMap.trace_baseChange (Algebra.lmul R B b) A
  rw [Algebra.baseChange_lmul] at h
  exact h

theorem gapsw7_x3x_trace_decomposition_of_prod_iso (R A B : Type*)
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Module.Free R B] [Module.Finite R B] {ι : Type*} [Fintype ι]
    (S : ι → Type*) [∀ i, CommRing (S i)] [∀ i, Algebra A (S i)]
    [∀ i, Module.Free A (S i)] [∀ i, Module.Finite A (S i)]
    (e : (A ⊗[R] B) ≃ₐ[A] ∀ i, S i) (b : B) :
    algebraMap R A (Algebra.trace R B b)
      = ∑ i, Algebra.trace A (S i) (e ((1 : A) ⊗ₜ[R] b) i) := by
  have _em := Classical.em
  rw [← gapsw7_x3x_trace_baseChange R A B b,
    ← Algebra.trace_eq_of_algEquiv e ((1 : A) ⊗ₜ[R] b),
    gapsw7_x3x_trace_pi A S]

end FLT.Gapsw7X3xCrossPlaceTraceDecomposition



end


end


section
section

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 3200000
set_option linter.unusedSectionVars false

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place
open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.IsDedekindDomain
open _root_.TensorProduct
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.TensorProduct
open AlgebraicCurve.KwBwnmchRFTDCDischarge

noncomputable section

namespace ModularCurve

export _root_.ModularCurve (KwF4R1V391a.KwF4R1V391aResidueTraceCompletionCommute)

namespace KwF4R1V384a
open _root_.ModularCurve

section FiberAlgebra

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F] [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]

scoped instance kwF4R1V384a_instAlgebraFiberCompletion (v : Place K E) (w' : v.fiber F) :
    Algebra v.adicCompletion w'.1.adicCompletion := by
  rcases w' with ⟨w', hw'⟩
  have hv : w'.restrict E = v := Place.mem_fiber.mp hw'
  subst hv
  exact kw_ffgc_algebraAdicCompletionComap E w'

scoped instance kwF4R1V384a_instIsScalarTowerFiberCompletion (v : Place K E) (w' : v.fiber F) :
    IsScalarTower E v.adicCompletion w'.1.adicCompletion := by
  rcases w' with ⟨w', hw'⟩
  have hv : w'.restrict E = v := Place.mem_fiber.mp hw'
  subst hv
  refine IsScalarTower.of_algebraMap_eq fun e => ?_
  rw [show algebraMap E w'.adicCompletion e = algebraMap F w'.adicCompletion (algebraMap E F e)
    from IsScalarTower.algebraMap_apply E F w'.adicCompletion e]
  exact kw_ffgc_adicCompletionComap_algebraMap_algebraMap E w' e

scoped instance kwF4R1V384a_instFiniteDimensionalFiberCompletion [FiniteDimensional E F]
    (v : Place K E) (w' : v.fiber F) :
    FiniteDimensional v.adicCompletion w'.1.adicCompletion := by
  rcases w' with ⟨w', hw'⟩
  have hv : w'.restrict E = v := Place.mem_fiber.mp hw'
  subst hv
  exact kw_ffgc_finiteDimensional_adicCompletion E w'

end FiberAlgebra


section SemilocalDiag

variable {K : Type*} (F : Type*) [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F] [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]

def kwF4R1V384a_semilocalComponent (v : Place K E) (w' : v.fiber F) :
    v.adicCompletion ⊗[E] F →ₐ[v.adicCompletion] w'.1.adicCompletion :=
  Algebra.TensorProduct.lift (Algebra.ofId v.adicCompletion w'.1.adicCompletion)
    (IsScalarTower.toAlgHom E F w'.1.adicCompletion) (fun _ _ => mul_comm _ _)

@[scoped simp]
theorem kwF4R1V384a_semilocalComponent_tmul (v : Place K E) (w' : v.fiber F)
    (c : v.adicCompletion) (g : F) :
    kwF4R1V384a_semilocalComponent F v w' (c ⊗ₜ[E] g)
      = algebraMap v.adicCompletion w'.1.adicCompletion c
          * algebraMap F w'.1.adicCompletion g := by
  unfold kwF4R1V384a_semilocalComponent
  rw [Algebra.TensorProduct.lift_tmul]
  rfl

def kwF4R1V384a_semilocalDiag (v : Place K E) :
    v.adicCompletion ⊗[E] F →ₐ[v.adicCompletion]
      ((w' : v.fiber F) → w'.1.adicCompletion) :=
  Pi.algHom v.adicCompletion _ (kwF4R1V384a_semilocalComponent F v)

variable {F}

@[scoped simp]
theorem kwF4R1V384a_semilocalDiag_apply (v : Place K E) (x : v.adicCompletion ⊗[E] F)
    (w' : v.fiber F) :
    kwF4R1V384a_semilocalDiag F v x w' = kwF4R1V384a_semilocalComponent F v w' x := rfl

theorem kwF4R1V384a_semilocalDiag_one_tmul (v : Place K E) (g : F) (w' : v.fiber F) :
    kwF4R1V384a_semilocalDiag F v ((1 : v.adicCompletion) ⊗ₜ[E] g) w'
      = algebraMap F w'.1.adicCompletion g := by
  rw [kwF4R1V384a_semilocalDiag_apply, kwF4R1V384a_semilocalComponent_tmul,
    map_one, one_mul]

end SemilocalDiag


section Mint

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

def KwF4R1V384aCompletionSemilocalBij : Prop :=
  ∀ [HasPrincipalDivisors K E] [HasPrincipalDivisors K F] [FiniteDimensional E F]
    (v : Place K E),
    Function.Bijective (kwF4R1V384a_semilocalDiag (K := K) (E := E) F v)

end Mint


section PerComponentSurjective

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F] [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]
variable [FiniteDimensional E F]

theorem kwF4R1V384a_completionLinearCombination_surjective
    (w' : Place K F) {ι : Type*} [Fintype ι] (b : Module.Basis ι E F) :
    Function.Surjective (kw_ffgc_completionLinearCombination E w' b) := by
  letI := kw_ffgc_rankOne_adicCompletion (K := K) (w'.restrict E)
  letI : NontriviallyNormedField (w'.restrict E).adicCompletion :=
    Valued.toNontriviallyNormedField (w'.restrict E).adicCompletion
      (WithZero (Multiplicative ℤ))
  rw [← Set.range_eq_univ, ← LinearMap.coe_range,
    ← (LinearMap.range (kw_ffgc_completionLinearCombination E w' b))
        |>.closed_of_finiteDimensional.closure_eq]
  exact (kw_ffgc_denseRange_completionLinearCombination E w' b).closure_range

theorem kwF4R1V384a_semilocalComponent_surjective (v : Place K E) (w' : v.fiber F) :
    Function.Surjective (kwF4R1V384a_semilocalComponent F v w') := by
  rcases w' with ⟨w', hw'⟩
  have hv : w'.restrict E = v := Place.mem_fiber.mp hw'
  subst hv
  intro y
  let b := Module.finBasis E F
  obtain ⟨c, hc⟩ := kwF4R1V384a_completionLinearCombination_surjective w' b y
  refine ⟨∑ i, c i ⊗ₜ[E] b i, ?_⟩
  rw [map_sum, ← hc]
  unfold kw_ffgc_completionLinearCombination
  rw [Fintype.linearCombination_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [kwF4R1V384a_semilocalComponent_tmul, Algebra.smul_def]

end PerComponentSurjective


section SpecificMints

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

def KwF4R1V384aDistinctKernels : Prop :=
  ∀ [HasPrincipalDivisors K E] [HasPrincipalDivisors K F] [FiniteDimensional E F]
    (v : Place K E) (w' w'' : v.fiber F), w' ≠ w'' →
    RingHom.ker (kwF4R1V384a_semilocalComponent (K := K) (E := E) F v w').toRingHom
      ≠ RingHom.ker (kwF4R1V384a_semilocalComponent (K := K) (E := E) F v w'').toRingHom

def KwF4R1V384aFinrankCompletionEF : Prop :=
  ∀ [HasPrincipalDivisors K E] [HasPrincipalDivisors K F] [FiniteDimensional E F]
    (v : Place K E) (w' : v.fiber F),
    (Module.finrank v.adicCompletion w'.1.adicCompletion : ℤ)
      = (w'.1.ramificationIndex E : ℤ) * (w'.1.inertiaDeg E : ℤ)

end SpecificMints


section BijEngine

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

scoped instance kwF4R1V384a_ker_semilocalComponent_isMaximal
    [HasPrincipalDivisors K E] [HasPrincipalDivisors K F] [FiniteDimensional E F]
    (v : Place K E) (w' : v.fiber F) :
    (RingHom.ker (kwF4R1V384a_semilocalComponent F v w').toRingHom).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (kwF4R1V384a_semilocalComponent F v w').toRingHom
    (kwF4R1V384a_semilocalComponent_surjective v w')

theorem kwF4R1V384a_semilocalDiag_surjective_of_distinctKernels
    [HasPrincipalDivisors K E] [HasPrincipalDivisors K F] [FiniteDimensional E F]
    (hdist : KwF4R1V384aDistinctKernels K F E) (v : Place K E) :
    Function.Surjective (kwF4R1V384a_semilocalDiag F v) := by
  classical
  intro y
  let m : v.fiber F → Ideal (v.adicCompletion ⊗[E] F) :=
    fun w' => RingHom.ker (kwF4R1V384a_semilocalComponent F v w').toRingHom
  haveI : ∀ w', (m w').IsMaximal :=
    kwF4R1V384a_ker_semilocalComponent_isMaximal v
  have hcop : Pairwise (Function.onFun IsCoprime m) := fun i j hij =>
    Ideal.isCoprime_of_isMaximal (I := m i) (J := m j) (hdist v i j hij)
  choose xw hxw using fun w' => kwF4R1V384a_semilocalComponent_surjective v w' (y w')
  obtain ⟨xbar, hxbar⟩ :=
    Ideal.quotientInfToPiQuotient_surj hcop (fun w' => Ideal.Quotient.mk (m w') (xw w'))
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective xbar
  refine ⟨x, funext fun w' => ?_⟩
  show kwF4R1V384a_semilocalComponent F v w' x = y w'
  have hcomp : Ideal.Quotient.mk (m w') x = Ideal.Quotient.mk (m w') (xw w') := by
    have := congrFun hxbar w'
    rwa [Ideal.quotientInfToPiQuotient_mk' m x w'] at this
  have hmod : x - xw w' ∈ m w' := Ideal.Quotient.eq.mp hcomp
  have hzero : kwF4R1V384a_semilocalComponent F v w' (x - xw w') = 0 := hmod
  rw [map_sub, sub_eq_zero] at hzero
  rw [hzero, hxw w']

scoped instance kwF4R1V384a_instModuleFiberCompletion
    [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]
    (v : Place K E) (w' : v.fiber F) :
    Module v.adicCompletion w'.1.adicCompletion :=
  Algebra.toModule

theorem kwF4R1V384a_completionSemilocalBij_of_distinctKernels_finrankEF
    [Algebra.IsSeparable E F]
    (hdist : KwF4R1V384aDistinctKernels K F E)
    (hef : KwF4R1V384aFinrankCompletionEF K F E) :
    KwF4R1V384aCompletionSemilocalBij K F E := by
  intro _ _ _ v
  have hsurj := kwF4R1V384a_semilocalDiag_surjective_of_distinctKernels hdist v
  refine ⟨?_, hsurj⟩

  letI srPi : Semiring ((w' : v.fiber F) → w'.1.adicCompletion) := inferInstance
  letI algPi : Algebra v.adicCompletion ((w' : v.fiber F) → w'.1.adicCompletion) :=
    inferInstance
  letI modPi : Module v.adicCompletion ((w' : v.fiber F) → w'.1.adicCompletion) :=
    @Algebra.toModule _ _ _ srPi algPi

  have hdimcod : Module.finrank v.adicCompletion ((w' : v.fiber F) → w'.1.adicCompletion)
      = Module.finrank E F := by
    have hpi : (Module.finrank v.adicCompletion ((w' : v.fiber F) → w'.1.adicCompletion) : ℕ)
        = ∑ w' : v.fiber F, Module.finrank v.adicCompletion w'.1.adicCompletion := by
      convert Module.finrank_pi_fintype v.adicCompletion using 2 <;>
        exact fun i => inferInstance
    rw [hpi]
    have hsum := Place.sum_ramificationIndex_mul_inertiaDeg (K := K) (F := E) (F' := F) v
    rw [← Nat.cast_inj (R := ℤ), Nat.cast_sum]
    calc ∑ w' : v.fiber F,
          ((Module.finrank v.adicCompletion w'.1.adicCompletion : ℤ))
        = ∑ w' : v.fiber F,
            ((w'.1.ramificationIndex E : ℤ) * (w'.1.inertiaDeg E : ℤ)) :=
          Finset.sum_congr rfl fun w' _ => hef v w'
      _ = ∑ w' ∈ v.fiber F,
            ((w'.ramificationIndex E : ℤ) * (w'.inertiaDeg E : ℤ)) :=
          Finset.sum_attach (v.fiber F)
            (fun w => (w.ramificationIndex E : ℤ) * (w.inertiaDeg E : ℤ))
      _ = (Module.finrank E F : ℤ) := hsum
  have hdimdom : Module.finrank v.adicCompletion (v.adicCompletion ⊗[E] F)
      = Module.finrank E F := by
    rw [Module.finrank_tensorProduct, Module.finrank_self, one_mul]
  have hsurj' : Function.Surjective
      (kwF4R1V384a_semilocalDiag F v).toLinearMap := hsurj

  haveI fdPi : FiniteDimensional v.adicCompletion
      ((w' : v.fiber F) → w'.1.adicCompletion) := inferInstance
  exact (@LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    v.adicCompletion (v.adicCompletion ⊗[E] F) _ _ _
    ((w' : v.fiber F) → w'.1.adicCompletion) _ modPi _ fdPi
    (hdimdom.trans hdimcod.symm)
    (kwF4R1V384a_semilocalDiag F v).toLinearMap).mpr hsurj'

end BijEngine


section Headline

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

open FLT.Gapsw7X3xCrossPlaceTraceDecomposition

theorem kwF4R1V384a_trace_algebraMap_eq_completionTraceAt
    [HasPrincipalDivisors K E] [HasPrincipalDivisors K F] [FiniteDimensional E F]
    (v : Place K E) (w' : v.fiber F) (g : F) :
    Algebra.trace v.adicCompletion w'.1.adicCompletion (algebraMap F w'.1.adicCompletion g)
      = AlgebraicCurve.kwHgfV352_completionTraceAt v w'.1 w'.2 g := by
  rcases w' with ⟨w', hw'⟩
  have hv : w'.restrict E = v := Place.mem_fiber.mp hw'
  subst hv
  rfl

set_option maxHeartbeats 6400000 in

theorem kwF4R1V384a_completionTraceSum_of_semilocalBij
    (hbij : KwF4R1V384aCompletionSemilocalBij K F E) :
    AlgebraicCurve.KwHgfV352CompletionTraceSum K F E := by
  classical
  intro _ _ _ v g
  let e : v.adicCompletion ⊗[E] F ≃ₐ[v.adicCompletion]
      ((w' : v.fiber F) → w'.1.adicCompletion) :=
    AlgEquiv.ofBijective (kwF4R1V384a_semilocalDiag F v) (hbij v)
  rw [gapsw7_x3x_trace_decomposition_of_prod_iso E v.adicCompletion F
        (fun w' : v.fiber F => w'.1.adicCompletion) e g]
  refine Finset.sum_congr rfl fun w' _ => ?_
  rw [show e ((1 : v.adicCompletion) ⊗ₜ[E] g) w'
      = kwF4R1V384a_semilocalDiag F v ((1 : v.adicCompletion) ⊗ₜ[E] g) w' from rfl,
    kwF4R1V384a_semilocalDiag_one_tmul,
    kwF4R1V384a_trace_algebraMap_eq_completionTraceAt]

theorem kwF4R1V384a_completionTraceSum_of_distinctKernels_finrankEF
    [Algebra.IsSeparable E F]
    (hdist : KwF4R1V384aDistinctKernels K F E)
    (hef : KwF4R1V384aFinrankCompletionEF K F E) :
    AlgebraicCurve.KwHgfV352CompletionTraceSum K F E :=
  kwF4R1V384a_completionTraceSum_of_semilocalBij
    (kwF4R1V384a_completionSemilocalBij_of_distinctKernels_finrankEF hdist hef)

end Headline


end ModularCurve.KwF4R1V384a



end

end


end

end P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed
