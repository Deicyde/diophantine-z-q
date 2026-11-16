/-
Copyright 2026 Anthropic, PBC. Released under Apache License 2.0.
Source: https://github.com/anthropics/fermats-last-theorem
Revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.lean; source lines 1735-3202.
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
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.RRSplit.residueTheoremK_of_isAlgClosed_Part01

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


section
section

@[expose] public section

noncomputable section

open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.WithZero
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.IsLocalRing

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Place.ord Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential diagonalHom diagonalHom_apply diagonal_mem_adeleSpace HasCanonicalDivisor HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTerm kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_support_finite_of_adeleSpace weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK HasCanonicalLocalResidueKStar.dataKStar Place.mem_fiber Place.valuationSubringAlgebra Place.finite_setOf_restrict_eq kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kaehlerCotrace kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt KwHgfV352CompletionTraceSum FiberKaehlerCotraceResidueIdentityK CotraceResidueIdentityOnFiberLocalizedK Place.finiteResidue_of_deg_pos residueTraceCompletionCommute residueTheoremK_ratFunc_of_isAlgClosed)

open _root_.AlgebraicCurve

namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue heightOneSpectrum adicValuation adicValuation_ne_zero adicValuation_coe_eq_one_iff adicValuation_coe_irreducible ord ord_zero ord_one ord_mul ord_inv ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ord_smul ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one isEquiv_adicValuation_ofHeightOneSpectrum ord_ofHeightOneSpectrum_ne_zero_iff dCoord DCoordGenerates dCoord_ne_zero differentialCoeff exists_eq_smul_dCoord differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero CanonicalLocalResidueDataK localResidue localResidue_eq_zero_of_ord_nonneg differentialCoeff_ne_zero ramificationIndex ramificationIndex_pos restrict ord_restrict restrictInclusion inertiaDeg deg_restrict_mul_inertiaDeg fiber mem_fiber ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq adicCompletion adicCompletionIntegers kw_ffgc_adicCompletionComap kw_ffgc_valued_adicCompletionComap kw_ffgc_adicCompletionComapIntegers kw_ffgc_adicCompletionComapIntegers_coe kw_ffgc_algebraAdicCompletionComap kw_ffgc_algebraMap_adicCompletionComap_eq kw_ffgc_rankOne_adicCompletion kw_ffgc_absoluteValue kw_ffgc_adicCompletionComap_algebraMap_algebraMap kw_ffgc_completionLinearCombination kw_ffgc_denseRange_completionLinearCombination kw_ffgc_finiteDimensional_adicCompletion kw_ffgc_completionTraceF' regularSubmodule finiteResidue_of_deg_pos poleSubmodule uniformizer_pow_ne_zero ord_uniformizer_pow poleSubmodule_mono iSup_poleSubmodule_eq_top exists_mem_poleSubmodule canonicalLocalResidueDataK_agree_on_poleSubmodule_of_surj)

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

export _root_.AlgebraicCurve.RationalFunctionField (heightOneSpectrumOfIrreducible heightOneSpectrumOfIrreducible_asIdeal exists_irreducible_span finitePlace finitePlace_def algebraMap_mem_ofHeightOneSpectrum deg_ofHeightOneSpectrum deg_finitePlace)

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

open _root_.Polynomial
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.Polynomial
open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.IsDedekindDomain

open scoped _root_.Polynomial.Bivariate _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.Polynomial.Bivariate

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Place.ord Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential diagonalHom diagonalHom_apply diagonal_mem_adeleSpace HasCanonicalDivisor HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTerm kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_support_finite_of_adeleSpace weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK HasCanonicalLocalResidueKStar.dataKStar Place.mem_fiber Place.valuationSubringAlgebra Place.finite_setOf_restrict_eq kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kaehlerCotrace kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt KwHgfV352CompletionTraceSum FiberKaehlerCotraceResidueIdentityK CotraceResidueIdentityOnFiberLocalizedK Place.finiteResidue_of_deg_pos residueTraceCompletionCommute residueTheoremK_ratFunc_of_isAlgClosed)

namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue heightOneSpectrum adicValuation adicValuation_ne_zero adicValuation_coe_eq_one_iff adicValuation_coe_irreducible ord ord_zero ord_one ord_mul ord_inv ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ord_smul ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one isEquiv_adicValuation_ofHeightOneSpectrum ord_ofHeightOneSpectrum_ne_zero_iff dCoord DCoordGenerates dCoord_ne_zero differentialCoeff exists_eq_smul_dCoord differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero CanonicalLocalResidueDataK localResidue localResidue_eq_zero_of_ord_nonneg differentialCoeff_ne_zero ramificationIndex ramificationIndex_pos restrict ord_restrict restrictInclusion inertiaDeg deg_restrict_mul_inertiaDeg fiber mem_fiber ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq adicCompletion adicCompletionIntegers kw_ffgc_adicCompletionComap kw_ffgc_valued_adicCompletionComap kw_ffgc_adicCompletionComapIntegers kw_ffgc_adicCompletionComapIntegers_coe kw_ffgc_algebraAdicCompletionComap kw_ffgc_algebraMap_adicCompletionComap_eq kw_ffgc_rankOne_adicCompletion kw_ffgc_absoluteValue kw_ffgc_adicCompletionComap_algebraMap_algebraMap kw_ffgc_completionLinearCombination kw_ffgc_denseRange_completionLinearCombination kw_ffgc_finiteDimensional_adicCompletion kw_ffgc_completionTraceF' regularSubmodule finiteResidue_of_deg_pos poleSubmodule uniformizer_pow_ne_zero ord_uniformizer_pow poleSubmodule_mono iSup_poleSubmodule_eq_top exists_mem_poleSubmodule canonicalLocalResidueDataK_agree_on_poleSubmodule_of_surj)

open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.ord_add_eq_min {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (h : v.ord f ≠ v.ord g) :
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
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.ord_add_eq_min
end AlgebraicCurve.Place



namespace WeierstrassCurve

export _root_.WeierstrassCurve (Affine map mk isIntegral_iff IsIntegral baseChange j)

namespace Affine

export _root_.WeierstrassCurve.Affine (CoordinateRing map baseChange FunctionField)

open _root_.WeierstrassCurve.Affine
open _root_.WeierstrassCurve

open _root_.WeierstrassCurve.Affine.CoordinateRing
open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve

variable {F : Type*} [Field F] {W : Affine F}

variable (v : AlgebraicCurve.Place F W.FunctionField)

end WeierstrassCurve.Affine



end

end


end


section
section

set_option synthInstance.maxHeartbeats 3200000
set_option maxHeartbeats 6400000

noncomputable section

open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.IsDedekindDomain
open _root_.IsDedekindDomain.HeightOneSpectrum
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.IsDedekindDomain.HeightOneSpectrum
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.IsLocalRing
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.WithZero
open _root_.MonoidWithZeroHom
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.MonoidWithZeroHom

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Place.ord Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential diagonalHom diagonalHom_apply diagonal_mem_adeleSpace HasCanonicalDivisor HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTerm kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_support_finite_of_adeleSpace weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK HasCanonicalLocalResidueKStar.dataKStar Place.mem_fiber Place.valuationSubringAlgebra Place.finite_setOf_restrict_eq kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kaehlerCotrace kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt KwHgfV352CompletionTraceSum FiberKaehlerCotraceResidueIdentityK CotraceResidueIdentityOnFiberLocalizedK Place.finiteResidue_of_deg_pos residueTraceCompletionCommute residueTheoremK_ratFunc_of_isAlgClosed)

namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue heightOneSpectrum adicValuation adicValuation_ne_zero adicValuation_coe_eq_one_iff adicValuation_coe_irreducible ord ord_zero ord_one ord_mul ord_inv ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ord_smul ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one isEquiv_adicValuation_ofHeightOneSpectrum ord_ofHeightOneSpectrum_ne_zero_iff dCoord DCoordGenerates dCoord_ne_zero differentialCoeff exists_eq_smul_dCoord differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero CanonicalLocalResidueDataK localResidue localResidue_eq_zero_of_ord_nonneg differentialCoeff_ne_zero ramificationIndex ramificationIndex_pos restrict ord_restrict restrictInclusion inertiaDeg deg_restrict_mul_inertiaDeg fiber mem_fiber ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq adicCompletion adicCompletionIntegers kw_ffgc_adicCompletionComap kw_ffgc_valued_adicCompletionComap kw_ffgc_adicCompletionComapIntegers kw_ffgc_adicCompletionComapIntegers_coe kw_ffgc_algebraAdicCompletionComap kw_ffgc_algebraMap_adicCompletionComap_eq kw_ffgc_rankOne_adicCompletion kw_ffgc_absoluteValue kw_ffgc_adicCompletionComap_algebraMap_algebraMap kw_ffgc_completionLinearCombination kw_ffgc_denseRange_completionLinearCombination kw_ffgc_finiteDimensional_adicCompletion kw_ffgc_completionTraceF' regularSubmodule finiteResidue_of_deg_pos poleSubmodule uniformizer_pow_ne_zero ord_uniformizer_pow poleSubmodule_mono iSup_poleSubmodule_eq_top exists_mem_poleSubmodule canonicalLocalResidueDataK_agree_on_poleSubmodule_of_surj)

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
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.IsDedekindDomain
open _root_.IsDedekindDomain.HeightOneSpectrum
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.IsDedekindDomain.HeightOneSpectrum
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.IsLocalRing
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.WithZero
open _root_.MonoidWithZeroHom
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.MonoidWithZeroHom

section HenselUniqueness

variable {R : Type*} [CommRing R] [IsLocalRing R]

end HenselUniqueness


namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Place.ord Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential diagonalHom diagonalHom_apply diagonal_mem_adeleSpace HasCanonicalDivisor HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTerm kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_support_finite_of_adeleSpace weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK HasCanonicalLocalResidueKStar.dataKStar Place.mem_fiber Place.valuationSubringAlgebra Place.finite_setOf_restrict_eq kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kaehlerCotrace kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt KwHgfV352CompletionTraceSum FiberKaehlerCotraceResidueIdentityK CotraceResidueIdentityOnFiberLocalizedK Place.finiteResidue_of_deg_pos residueTraceCompletionCommute residueTheoremK_ratFunc_of_isAlgClosed)

namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue heightOneSpectrum adicValuation adicValuation_ne_zero adicValuation_coe_eq_one_iff adicValuation_coe_irreducible ord ord_zero ord_one ord_mul ord_inv ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ord_smul ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one isEquiv_adicValuation_ofHeightOneSpectrum ord_ofHeightOneSpectrum_ne_zero_iff dCoord DCoordGenerates dCoord_ne_zero differentialCoeff exists_eq_smul_dCoord differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero CanonicalLocalResidueDataK localResidue localResidue_eq_zero_of_ord_nonneg differentialCoeff_ne_zero ramificationIndex ramificationIndex_pos restrict ord_restrict restrictInclusion inertiaDeg deg_restrict_mul_inertiaDeg fiber mem_fiber ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq adicCompletion adicCompletionIntegers kw_ffgc_adicCompletionComap kw_ffgc_valued_adicCompletionComap kw_ffgc_adicCompletionComapIntegers kw_ffgc_adicCompletionComapIntegers_coe kw_ffgc_algebraAdicCompletionComap kw_ffgc_algebraMap_adicCompletionComap_eq kw_ffgc_rankOne_adicCompletion kw_ffgc_absoluteValue kw_ffgc_adicCompletionComap_algebraMap_algebraMap kw_ffgc_completionLinearCombination kw_ffgc_denseRange_completionLinearCombination kw_ffgc_finiteDimensional_adicCompletion kw_ffgc_completionTraceF' regularSubmodule finiteResidue_of_deg_pos poleSubmodule uniformizer_pow_ne_zero ord_uniformizer_pow poleSubmodule_mono iSup_poleSubmodule_eq_top exists_mem_poleSubmodule canonicalLocalResidueDataK_agree_on_poleSubmodule_of_surj)

open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve

section IntegerComap

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

theorem kw_ffgc_adicCompletionComapIntegers_mem_maximalIdeal
    {x : (W.restrict F).adicCompletionIntegers}
    (hx : x ∈ maximalIdeal (W.restrict F).adicCompletionIntegers) :
    kw_ffgc_adicCompletionComapIntegers F W x ∈ maximalIdeal W.adicCompletionIntegers := by
  have hrpos := W.ramificationIndex_pos (F := F)
  rw [show maximalIdeal (W.restrict F).adicCompletionIntegers
      = (W.restrict F).heightOneSpectrum.completionIdeal F from rfl,
    HeightOneSpectrum.mem_completionIdeal_iff] at hx
  rw [show maximalIdeal W.adicCompletionIntegers
      = W.heightOneSpectrum.completionIdeal F' from rfl,
    HeightOneSpectrum.mem_completionIdeal_iff, kw_ffgc_adicCompletionComapIntegers_coe,
    kw_ffgc_valued_adicCompletionComap]
  calc Valued.v (x : (W.restrict F).adicCompletion) ^ W.ramificationIndex F
      < 1 ^ W.ramificationIndex F := pow_lt_pow_left₀ hx (WithZero.zero_le _) hrpos.ne'
    _ = 1 := one_pow _

scoped instance kw_ffgc_isLocalHom_adicCompletionComapIntegers :
    IsLocalHom (kw_ffgc_adicCompletionComapIntegers F W) where
  map_nonunit x hx := by
    by_contra hnu
    exact (IsLocalRing.notMem_maximalIdeal.mpr hx)
      (kw_ffgc_adicCompletionComapIntegers_mem_maximalIdeal F W
        ((IsLocalRing.mem_maximalIdeal x).mpr hnu))

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

noncomputable section

open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.WithZero
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.IsLocalRing
open scoped _root_.Polynomial _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.Polynomial

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Place.ord Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential diagonalHom diagonalHom_apply diagonal_mem_adeleSpace HasCanonicalDivisor HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTerm kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_support_finite_of_adeleSpace weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK HasCanonicalLocalResidueKStar.dataKStar Place.mem_fiber Place.valuationSubringAlgebra Place.finite_setOf_restrict_eq kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kaehlerCotrace kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt KwHgfV352CompletionTraceSum FiberKaehlerCotraceResidueIdentityK CotraceResidueIdentityOnFiberLocalizedK Place.finiteResidue_of_deg_pos residueTraceCompletionCommute residueTheoremK_ratFunc_of_isAlgClosed)

open _root_.AlgebraicCurve

namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue heightOneSpectrum adicValuation adicValuation_ne_zero adicValuation_coe_eq_one_iff adicValuation_coe_irreducible ord ord_zero ord_one ord_mul ord_inv ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ord_smul ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one isEquiv_adicValuation_ofHeightOneSpectrum ord_ofHeightOneSpectrum_ne_zero_iff dCoord DCoordGenerates dCoord_ne_zero differentialCoeff exists_eq_smul_dCoord differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero CanonicalLocalResidueDataK localResidue localResidue_eq_zero_of_ord_nonneg differentialCoeff_ne_zero ramificationIndex ramificationIndex_pos restrict ord_restrict restrictInclusion inertiaDeg deg_restrict_mul_inertiaDeg fiber mem_fiber ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq adicCompletion adicCompletionIntegers kw_ffgc_adicCompletionComap kw_ffgc_valued_adicCompletionComap kw_ffgc_adicCompletionComapIntegers kw_ffgc_adicCompletionComapIntegers_coe kw_ffgc_algebraAdicCompletionComap kw_ffgc_algebraMap_adicCompletionComap_eq kw_ffgc_rankOne_adicCompletion kw_ffgc_absoluteValue kw_ffgc_adicCompletionComap_algebraMap_algebraMap kw_ffgc_completionLinearCombination kw_ffgc_denseRange_completionLinearCombination kw_ffgc_finiteDimensional_adicCompletion kw_ffgc_completionTraceF' regularSubmodule finiteResidue_of_deg_pos poleSubmodule uniformizer_pow_ne_zero ord_uniformizer_pow poleSubmodule_mono iSup_poleSubmodule_eq_top exists_mem_poleSubmodule canonicalLocalResidueDataK_agree_on_poleSubmodule_of_surj)

open _root_.AlgebraicCurve.Place

section DegPos

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

end DegPos


end Place


namespace RationalFunctionField

export _root_.AlgebraicCurve.RationalFunctionField (heightOneSpectrumOfIrreducible heightOneSpectrumOfIrreducible_asIdeal exists_irreducible_span finitePlace finitePlace_def algebraMap_mem_ofHeightOneSpectrum deg_ofHeightOneSpectrum deg_finitePlace)

open _root_.AlgebraicCurve.RationalFunctionField

variable (K : Type*) [Field K]

scoped instance instFiniteResidueOfHeightOneSpectrum (w : HeightOneSpectrum K[X]) :
    (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).FiniteResidue := by
  obtain ⟨p, hp, hw⟩ := exists_irreducible_span K w
  refine Place.finiteResidue_of_deg_pos _ ?_
  rw [deg_ofHeightOneSpectrum K hw]
  exact hp.natDegree_pos

scoped instance instFiniteResiduePlaceInfty [DecidableEq (RatFunc K)] :
    (placeInfty K).FiniteResidue :=
  Place.finiteResidue_of_deg_pos _ (by rw [deg_placeInfty K]; exact one_pos)

variable {K} in

scoped instance instFiniteResidue (v : Place K (RatFunc K)) : v.FiniteResidue := by
  classical
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
  · exact instFiniteResidueOfHeightOneSpectrum K w
  · exact instFiniteResiduePlaceInfty K

end RationalFunctionField


namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue heightOneSpectrum adicValuation adicValuation_ne_zero adicValuation_coe_eq_one_iff adicValuation_coe_irreducible ord ord_zero ord_one ord_mul ord_inv ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ord_smul ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one isEquiv_adicValuation_ofHeightOneSpectrum ord_ofHeightOneSpectrum_ne_zero_iff dCoord DCoordGenerates dCoord_ne_zero differentialCoeff exists_eq_smul_dCoord differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero CanonicalLocalResidueDataK localResidue localResidue_eq_zero_of_ord_nonneg differentialCoeff_ne_zero ramificationIndex ramificationIndex_pos restrict ord_restrict restrictInclusion inertiaDeg deg_restrict_mul_inertiaDeg fiber mem_fiber ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq adicCompletion adicCompletionIntegers kw_ffgc_adicCompletionComap kw_ffgc_valued_adicCompletionComap kw_ffgc_adicCompletionComapIntegers kw_ffgc_adicCompletionComapIntegers_coe kw_ffgc_algebraAdicCompletionComap kw_ffgc_algebraMap_adicCompletionComap_eq kw_ffgc_rankOne_adicCompletion kw_ffgc_absoluteValue kw_ffgc_adicCompletionComap_algebraMap_algebraMap kw_ffgc_completionLinearCombination kw_ffgc_denseRange_completionLinearCombination kw_ffgc_finiteDimensional_adicCompletion kw_ffgc_completionTraceF' regularSubmodule finiteResidue_of_deg_pos poleSubmodule uniformizer_pow_ne_zero ord_uniformizer_pow poleSubmodule_mono iSup_poleSubmodule_eq_top exists_mem_poleSubmodule canonicalLocalResidueDataK_agree_on_poleSubmodule_of_surj)

open _root_.AlgebraicCurve.Place

section Restrict

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F'] [Algebra F F'] [Algebra K F] [IsScalarTower K F F']
  [Algebra.IsIntegral F F'] (w : Place K F')

end Restrict


end Place


end AlgebraicCurve


end

end


end


section
section

set_option synthInstance.maxHeartbeats 3200000
set_option maxHeartbeats 6400000

noncomputable section

open _root_.Polynomial
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.Polynomial
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.IsLocalRing
open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.IsDedekindDomain

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Place.ord Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential diagonalHom diagonalHom_apply diagonal_mem_adeleSpace HasCanonicalDivisor HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTerm kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_support_finite_of_adeleSpace weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK HasCanonicalLocalResidueKStar.dataKStar Place.mem_fiber Place.valuationSubringAlgebra Place.finite_setOf_restrict_eq kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kaehlerCotrace kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt KwHgfV352CompletionTraceSum FiberKaehlerCotraceResidueIdentityK CotraceResidueIdentityOnFiberLocalizedK Place.finiteResidue_of_deg_pos residueTraceCompletionCommute residueTheoremK_ratFunc_of_isAlgClosed)

namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue heightOneSpectrum adicValuation adicValuation_ne_zero adicValuation_coe_eq_one_iff adicValuation_coe_irreducible ord ord_zero ord_one ord_mul ord_inv ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ord_smul ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one isEquiv_adicValuation_ofHeightOneSpectrum ord_ofHeightOneSpectrum_ne_zero_iff dCoord DCoordGenerates dCoord_ne_zero differentialCoeff exists_eq_smul_dCoord differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero CanonicalLocalResidueDataK localResidue localResidue_eq_zero_of_ord_nonneg differentialCoeff_ne_zero ramificationIndex ramificationIndex_pos restrict ord_restrict restrictInclusion inertiaDeg deg_restrict_mul_inertiaDeg fiber mem_fiber ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq adicCompletion adicCompletionIntegers kw_ffgc_adicCompletionComap kw_ffgc_valued_adicCompletionComap kw_ffgc_adicCompletionComapIntegers kw_ffgc_adicCompletionComapIntegers_coe kw_ffgc_algebraAdicCompletionComap kw_ffgc_algebraMap_adicCompletionComap_eq kw_ffgc_rankOne_adicCompletion kw_ffgc_absoluteValue kw_ffgc_adicCompletionComap_algebraMap_algebraMap kw_ffgc_completionLinearCombination kw_ffgc_denseRange_completionLinearCombination kw_ffgc_finiteDimensional_adicCompletion kw_ffgc_completionTraceF' regularSubmodule finiteResidue_of_deg_pos poleSubmodule uniformizer_pow_ne_zero ord_uniformizer_pow poleSubmodule_mono iSup_poleSubmodule_eq_top exists_mem_poleSubmodule canonicalLocalResidueDataK_agree_on_poleSubmodule_of_surj)

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

end CompletionAlgebra


section IrreducibleValuation

open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.WithZero

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (V : Place K F)

end IrreducibleValuation


section SpectralSetup

open scoped _root_.Valued _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.Valued _root_.NNReal _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.NNReal _root_.WithZero _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.WithZero

open _root_.WithZeroMulInt
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.WithZeroMulInt
open _root_.Valuation.IsRankOneDiscrete
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.Valuation.IsRankOneDiscrete

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

open scoped _root_.Valued _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.Valued _root_.NNReal _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.NNReal _root_.WithZero _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.WithZero

open _root_.WithZeroMulInt
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.WithZeroMulInt
open _root_.Valuation.IsRankOneDiscrete
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.Valuation.IsRankOneDiscrete

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

open scoped _root_.Valued _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.Valued _root_.NNReal _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.NNReal _root_.WithZero _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.WithZero

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

open scoped _root_.Valued _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.Valued _root_.NNReal _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.NNReal _root_.WithZero _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.WithZero

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
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.IsDedekindDomain
open _root_.IsDedekindDomain.HeightOneSpectrum
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.IsDedekindDomain.HeightOneSpectrum
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.IsLocalRing
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.WithZero

open scoped _root_.Valued _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.Valued _root_.WithZero _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.WithZero

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Place.ord Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential diagonalHom diagonalHom_apply diagonal_mem_adeleSpace HasCanonicalDivisor HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTerm kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_support_finite_of_adeleSpace weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK HasCanonicalLocalResidueKStar.dataKStar Place.mem_fiber Place.valuationSubringAlgebra Place.finite_setOf_restrict_eq kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kaehlerCotrace kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt KwHgfV352CompletionTraceSum FiberKaehlerCotraceResidueIdentityK CotraceResidueIdentityOnFiberLocalizedK Place.finiteResidue_of_deg_pos residueTraceCompletionCommute residueTheoremK_ratFunc_of_isAlgClosed)

namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue heightOneSpectrum adicValuation adicValuation_ne_zero adicValuation_coe_eq_one_iff adicValuation_coe_irreducible ord ord_zero ord_one ord_mul ord_inv ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ord_smul ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one isEquiv_adicValuation_ofHeightOneSpectrum ord_ofHeightOneSpectrum_ne_zero_iff dCoord DCoordGenerates dCoord_ne_zero differentialCoeff exists_eq_smul_dCoord differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero CanonicalLocalResidueDataK localResidue localResidue_eq_zero_of_ord_nonneg differentialCoeff_ne_zero ramificationIndex ramificationIndex_pos restrict ord_restrict restrictInclusion inertiaDeg deg_restrict_mul_inertiaDeg fiber mem_fiber ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq adicCompletion adicCompletionIntegers kw_ffgc_adicCompletionComap kw_ffgc_valued_adicCompletionComap kw_ffgc_adicCompletionComapIntegers kw_ffgc_adicCompletionComapIntegers_coe kw_ffgc_algebraAdicCompletionComap kw_ffgc_algebraMap_adicCompletionComap_eq kw_ffgc_rankOne_adicCompletion kw_ffgc_absoluteValue kw_ffgc_adicCompletionComap_algebraMap_algebraMap kw_ffgc_completionLinearCombination kw_ffgc_denseRange_completionLinearCombination kw_ffgc_finiteDimensional_adicCompletion kw_ffgc_completionTraceF' regularSubmodule finiteResidue_of_deg_pos poleSubmodule uniformizer_pow_ne_zero ord_uniformizer_pow poleSubmodule_mono iSup_poleSubmodule_eq_top exists_mem_poleSubmodule canonicalLocalResidueDataK_agree_on_poleSubmodule_of_surj)

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

def kw_ffgc_residueFieldEquivCompletionResidueField :
    V.ResidueField ≃+* IsLocalRing.ResidueField V.adicCompletionIntegers :=
  ResidueFieldEquivCompletionResidueField F V.heightOneSpectrum

end ResidueCompletion


end AlgebraicCurve.Place



end

end


end


section
section

noncomputable section

open _root_.KaehlerDifferential
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.KaehlerDifferential

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Place.ord Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential diagonalHom diagonalHom_apply diagonal_mem_adeleSpace HasCanonicalDivisor HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTerm kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_support_finite_of_adeleSpace weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK HasCanonicalLocalResidueKStar.dataKStar Place.mem_fiber Place.valuationSubringAlgebra Place.finite_setOf_restrict_eq kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kaehlerCotrace kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt KwHgfV352CompletionTraceSum FiberKaehlerCotraceResidueIdentityK CotraceResidueIdentityOnFiberLocalizedK Place.finiteResidue_of_deg_pos residueTraceCompletionCommute residueTheoremK_ratFunc_of_isAlgClosed)

open _root_.AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

namespace IsCurveOver

export _root_.AlgebraicCurve.IsCurveOver (instFiniteResidue mk finiteResidue kaehler_free_rank_one)

open _root_.AlgebraicCurve.IsCurveOver

variable {K F}

end IsCurveOver


namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue heightOneSpectrum adicValuation adicValuation_ne_zero adicValuation_coe_eq_one_iff adicValuation_coe_irreducible ord ord_zero ord_one ord_mul ord_inv ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ord_smul ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one isEquiv_adicValuation_ofHeightOneSpectrum ord_ofHeightOneSpectrum_ne_zero_iff dCoord DCoordGenerates dCoord_ne_zero differentialCoeff exists_eq_smul_dCoord differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero CanonicalLocalResidueDataK localResidue localResidue_eq_zero_of_ord_nonneg differentialCoeff_ne_zero ramificationIndex ramificationIndex_pos restrict ord_restrict restrictInclusion inertiaDeg deg_restrict_mul_inertiaDeg fiber mem_fiber ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq adicCompletion adicCompletionIntegers kw_ffgc_adicCompletionComap kw_ffgc_valued_adicCompletionComap kw_ffgc_adicCompletionComapIntegers kw_ffgc_adicCompletionComapIntegers_coe kw_ffgc_algebraAdicCompletionComap kw_ffgc_algebraMap_adicCompletionComap_eq kw_ffgc_rankOne_adicCompletion kw_ffgc_absoluteValue kw_ffgc_adicCompletionComap_algebraMap_algebraMap kw_ffgc_completionLinearCombination kw_ffgc_denseRange_completionLinearCombination kw_ffgc_finiteDimensional_adicCompletion kw_ffgc_completionTraceF' regularSubmodule finiteResidue_of_deg_pos poleSubmodule uniformizer_pow_ne_zero ord_uniformizer_pow poleSubmodule_mono iSup_poleSubmodule_eq_top exists_mem_poleSubmodule canonicalLocalResidueDataK_agree_on_poleSubmodule_of_surj)

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

export _root_.ModularCurve (KwF4R1V391a.KwF4R1V391aResidueTraceCompletionCommute)

open _root_.ModularCurve

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve

end ModularCurve


namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Place.ord Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential diagonalHom diagonalHom_apply diagonal_mem_adeleSpace HasCanonicalDivisor HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTerm kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_support_finite_of_adeleSpace weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK HasCanonicalLocalResidueKStar.dataKStar Place.mem_fiber Place.valuationSubringAlgebra Place.finite_setOf_restrict_eq kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kaehlerCotrace kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt KwHgfV352CompletionTraceSum FiberKaehlerCotraceResidueIdentityK CotraceResidueIdentityOnFiberLocalizedK Place.finiteResidue_of_deg_pos residueTraceCompletionCommute residueTheoremK_ratFunc_of_isAlgClosed)

open _root_.AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

end AlgebraicCurve


namespace ModularCurve

export _root_.ModularCurve (KwF4R1V391a.KwF4R1V391aResidueTraceCompletionCommute)

open _root_.ModularCurve

end ModularCurve


end

end


end


section
section

noncomputable section

open _root_.Polynomial
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.Polynomial
open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.WithZero
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.IsLocalRing
open _root_.IntermediateField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.IntermediateField

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Place.ord Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential diagonalHom diagonalHom_apply diagonal_mem_adeleSpace HasCanonicalDivisor HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTerm kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_support_finite_of_adeleSpace weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK HasCanonicalLocalResidueKStar.dataKStar Place.mem_fiber Place.valuationSubringAlgebra Place.finite_setOf_restrict_eq kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kaehlerCotrace kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt KwHgfV352CompletionTraceSum FiberKaehlerCotraceResidueIdentityK CotraceResidueIdentityOnFiberLocalizedK Place.finiteResidue_of_deg_pos residueTraceCompletionCommute residueTheoremK_ratFunc_of_isAlgClosed)

namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue heightOneSpectrum adicValuation adicValuation_ne_zero adicValuation_coe_eq_one_iff adicValuation_coe_irreducible ord ord_zero ord_one ord_mul ord_inv ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ord_smul ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one isEquiv_adicValuation_ofHeightOneSpectrum ord_ofHeightOneSpectrum_ne_zero_iff dCoord DCoordGenerates dCoord_ne_zero differentialCoeff exists_eq_smul_dCoord differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero CanonicalLocalResidueDataK localResidue localResidue_eq_zero_of_ord_nonneg differentialCoeff_ne_zero ramificationIndex ramificationIndex_pos restrict ord_restrict restrictInclusion inertiaDeg deg_restrict_mul_inertiaDeg fiber mem_fiber ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq adicCompletion adicCompletionIntegers kw_ffgc_adicCompletionComap kw_ffgc_valued_adicCompletionComap kw_ffgc_adicCompletionComapIntegers kw_ffgc_adicCompletionComapIntegers_coe kw_ffgc_algebraAdicCompletionComap kw_ffgc_algebraMap_adicCompletionComap_eq kw_ffgc_rankOne_adicCompletion kw_ffgc_absoluteValue kw_ffgc_adicCompletionComap_algebraMap_algebraMap kw_ffgc_completionLinearCombination kw_ffgc_denseRange_completionLinearCombination kw_ffgc_finiteDimensional_adicCompletion kw_ffgc_completionTraceF' regularSubmodule finiteResidue_of_deg_pos poleSubmodule uniformizer_pow_ne_zero ord_uniformizer_pow poleSubmodule_mono iSup_poleSubmodule_eq_top exists_mem_poleSubmodule canonicalLocalResidueDataK_agree_on_poleSubmodule_of_surj)

open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve

section Ultrametric

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.ord_add_eq_left {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (h : v.ord f < v.ord g) :
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
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.ord_add_eq_left
end Ultrametric


section SumLeFinrank

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

attribute [local instance 0] valuationSubringAlgebra

end SumLeFinrank


end AlgebraicCurve.Place



namespace ModularCurve

export _root_.ModularCurve (KwF4R1V391a.KwF4R1V391aResidueTraceCompletionCommute)

open _root_.ModularCurve

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve

section RationalFunctionFieldInfty

end RationalFunctionFieldInfty


section Tower

variable (p : ℕ) [NeZero p]

end Tower


attribute [local instance 0] AlgebraicCurve.Place.valuationSubringAlgebra

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
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.WithZero
open _root_.Module
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.Module
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.IsLocalRing
open _root_.Module.IsLocalRing

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Place.ord Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential diagonalHom diagonalHom_apply diagonal_mem_adeleSpace HasCanonicalDivisor HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTerm kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_support_finite_of_adeleSpace weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK HasCanonicalLocalResidueKStar.dataKStar Place.mem_fiber Place.valuationSubringAlgebra Place.finite_setOf_restrict_eq kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kaehlerCotrace kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt KwHgfV352CompletionTraceSum FiberKaehlerCotraceResidueIdentityK CotraceResidueIdentityOnFiberLocalizedK Place.finiteResidue_of_deg_pos residueTraceCompletionCommute residueTheoremK_ratFunc_of_isAlgClosed)

open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue heightOneSpectrum adicValuation adicValuation_ne_zero adicValuation_coe_eq_one_iff adicValuation_coe_irreducible ord ord_zero ord_one ord_mul ord_inv ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ord_smul ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one isEquiv_adicValuation_ofHeightOneSpectrum ord_ofHeightOneSpectrum_ne_zero_iff dCoord DCoordGenerates dCoord_ne_zero differentialCoeff exists_eq_smul_dCoord differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero CanonicalLocalResidueDataK localResidue localResidue_eq_zero_of_ord_nonneg differentialCoeff_ne_zero ramificationIndex ramificationIndex_pos restrict ord_restrict restrictInclusion inertiaDeg deg_restrict_mul_inertiaDeg fiber mem_fiber ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq adicCompletion adicCompletionIntegers kw_ffgc_adicCompletionComap kw_ffgc_valued_adicCompletionComap kw_ffgc_adicCompletionComapIntegers kw_ffgc_adicCompletionComapIntegers_coe kw_ffgc_algebraAdicCompletionComap kw_ffgc_algebraMap_adicCompletionComap_eq kw_ffgc_rankOne_adicCompletion kw_ffgc_absoluteValue kw_ffgc_adicCompletionComap_algebraMap_algebraMap kw_ffgc_completionLinearCombination kw_ffgc_denseRange_completionLinearCombination kw_ffgc_finiteDimensional_adicCompletion kw_ffgc_completionTraceF' regularSubmodule finiteResidue_of_deg_pos poleSubmodule uniformizer_pow_ne_zero ord_uniformizer_pow poleSubmodule_mono iSup_poleSubmodule_eq_top exists_mem_poleSubmodule canonicalLocalResidueDataK_agree_on_poleSubmodule_of_surj)

open _root_.AlgebraicCurve.Place

variable (v : Place K F)

end Place


namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue heightOneSpectrum adicValuation adicValuation_ne_zero adicValuation_coe_eq_one_iff adicValuation_coe_irreducible ord ord_zero ord_one ord_mul ord_inv ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ord_smul ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one isEquiv_adicValuation_ofHeightOneSpectrum ord_ofHeightOneSpectrum_ne_zero_iff dCoord DCoordGenerates dCoord_ne_zero differentialCoeff exists_eq_smul_dCoord differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero CanonicalLocalResidueDataK localResidue localResidue_eq_zero_of_ord_nonneg differentialCoeff_ne_zero ramificationIndex ramificationIndex_pos restrict ord_restrict restrictInclusion inertiaDeg deg_restrict_mul_inertiaDeg fiber mem_fiber ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq adicCompletion adicCompletionIntegers kw_ffgc_adicCompletionComap kw_ffgc_valued_adicCompletionComap kw_ffgc_adicCompletionComapIntegers kw_ffgc_adicCompletionComapIntegers_coe kw_ffgc_algebraAdicCompletionComap kw_ffgc_algebraMap_adicCompletionComap_eq kw_ffgc_rankOne_adicCompletion kw_ffgc_absoluteValue kw_ffgc_adicCompletionComap_algebraMap_algebraMap kw_ffgc_completionLinearCombination kw_ffgc_denseRange_completionLinearCombination kw_ffgc_finiteDimensional_adicCompletion kw_ffgc_completionTraceF' regularSubmodule finiteResidue_of_deg_pos poleSubmodule uniformizer_pow_ne_zero ord_uniformizer_pow poleSubmodule_mono iSup_poleSubmodule_eq_top exists_mem_poleSubmodule canonicalLocalResidueDataK_agree_on_poleSubmodule_of_surj)

open _root_.AlgebraicCurve.Place

variable (v : Place K F)

theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.subsingleton_canonicalLocalResidueDataK_of_surj
    (hsurj : Function.Surjective (algebraMap K v.ResidueField)) :
    Subsingleton v.CanonicalLocalResidueDataK := by
  constructor
  intro R₁ R₂
  have hres : R₁.res = R₂.res := by
    ext f
    obtain ⟨n, hn⟩ := v.exists_mem_poleSubmodule f
    exact v.canonicalLocalResidueDataK_agree_on_poleSubmodule_of_surj hsurj R₁ R₂ n hn
  obtain ⟨⟨r₁, h₁a, h₁b⟩, h₁c⟩ := R₁
  obtain ⟨⟨r₂, h₂a, h₂b⟩, h₂c⟩ := R₂
  congr 2




-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.subsingleton_canonicalLocalResidueDataK_of_surj :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.subsingleton_canonicalLocalResidueDataK_of_surj
end Place


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
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.WithZero
open _root_.Module
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.Module
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.IsLocalRing
open _root_.Module.IsLocalRing

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Place.ord Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential diagonalHom diagonalHom_apply diagonal_mem_adeleSpace HasCanonicalDivisor HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTerm kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_support_finite_of_adeleSpace weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK HasCanonicalLocalResidueKStar.dataKStar Place.mem_fiber Place.valuationSubringAlgebra Place.finite_setOf_restrict_eq kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kaehlerCotrace kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt KwHgfV352CompletionTraceSum FiberKaehlerCotraceResidueIdentityK CotraceResidueIdentityOnFiberLocalizedK Place.finiteResidue_of_deg_pos residueTraceCompletionCommute residueTheoremK_ratFunc_of_isAlgClosed)

open _root_.AlgebraicCurve

section FiberReindex

variable {K E F : Type*} [Field K] [Field E] [Field F]
variable [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F] [HasPrincipalDivisors K F]

variable {M : Type*} [AddCommMonoid M]

theorem finsum_place_eq_finsum_fiber_sum (g : Place K F → M)
    (hg : (Function.support g).Finite) :
    ∑ᶠ w, g w = ∑ᶠ v : Place K E, ∑ w ∈ v.fiber F, g w := by
  classical
  set S := hg.toFinset with hS
  set T := S.image (fun w => w.restrict E) with hT

  rw [finsum_eq_finsetSum_of_support_subset g
    (s := S) (fun w hw => (hS ▸ hg.mem_toFinset.mpr hw))]

  have hsup : Function.support (fun v : Place K E => ∑ w ∈ v.fiber F, g w) ⊆ ↑T := by
    intro v hv
    simp only [Function.mem_support] at hv
    obtain ⟨w, hwfib, hwne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv
    exact Finset.mem_coe.mpr (hT ▸ Finset.mem_image.mpr
      ⟨w, hS ▸ hg.mem_toFinset.mpr hwne, Place.mem_fiber.mp hwfib⟩)
  rw [finsum_eq_finsetSum_of_support_subset _ hsup]

  have hfib : ∀ v ∈ T, ∑ w ∈ v.fiber F, g w
      = ∑ w ∈ S with w.restrict E = v, g w := by
    intro v _
    refine (Finset.sum_subset ?_ ?_).symm
    · intro w hw
      exact Place.mem_fiber.mpr (Finset.mem_filter.mp hw).2
    · intro w hwfib hwfilt

      by_contra hgw
      exact hwfilt (Finset.mem_filter.mpr
        ⟨hS ▸ hg.mem_toFinset.mpr hgw, Place.mem_fiber.mp hwfib⟩)
  rw [Finset.sum_congr rfl hfib]

  exact (Finset.sum_fiberwise_of_maps_to
    (fun w hw => hT ▸ Finset.mem_image.mpr ⟨w, hw, rfl⟩) g).symm

end FiberReindex


section FiberRow

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)]
variable [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

variable (K F)
variable (E : Type*) [Field E] [Algebra K E]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalDivisor (K := K) (F := E)]
variable [∀ v : Place K E, v.DCoordGenerates] [Nontrivial Ω[E⁄K]]
variable [Algebra E F] [IsScalarTower K E F] [Algebra.IsIntegral E F]

end FiberRow


section Engine

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)]
variable [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

variable {E : Type*} [Field E] [Algebra K E]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalDivisor (K := K) (F := E)]
variable [∀ v : Place K E, v.DCoordGenerates] [Nontrivial Ω[E⁄K]]
variable [Algebra E F] [IsScalarTower K E F] [Algebra.IsIntegral E F]

end Engine


end AlgebraicCurve


section AxiomAudit

end AxiomAudit


end


end


end


section
section

noncomputable section

open _root_.Polynomial
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.Polynomial
open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.WithZero
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.IsLocalRing

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Place.ord Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential diagonalHom diagonalHom_apply diagonal_mem_adeleSpace HasCanonicalDivisor HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTerm kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_support_finite_of_adeleSpace weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK HasCanonicalLocalResidueKStar.dataKStar Place.mem_fiber Place.valuationSubringAlgebra Place.finite_setOf_restrict_eq kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kaehlerCotrace kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt KwHgfV352CompletionTraceSum FiberKaehlerCotraceResidueIdentityK CotraceResidueIdentityOnFiberLocalizedK Place.finiteResidue_of_deg_pos residueTraceCompletionCommute residueTheoremK_ratFunc_of_isAlgClosed)

open _root_.AlgebraicCurve

section SubsingletonCriterion

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

end SubsingletonCriterion


namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue heightOneSpectrum adicValuation adicValuation_ne_zero adicValuation_coe_eq_one_iff adicValuation_coe_irreducible ord ord_zero ord_one ord_mul ord_inv ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ord_smul ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one isEquiv_adicValuation_ofHeightOneSpectrum ord_ofHeightOneSpectrum_ne_zero_iff dCoord DCoordGenerates dCoord_ne_zero differentialCoeff exists_eq_smul_dCoord differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero CanonicalLocalResidueDataK localResidue localResidue_eq_zero_of_ord_nonneg differentialCoeff_ne_zero ramificationIndex ramificationIndex_pos restrict ord_restrict restrictInclusion inertiaDeg deg_restrict_mul_inertiaDeg fiber mem_fiber ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq adicCompletion adicCompletionIntegers kw_ffgc_adicCompletionComap kw_ffgc_valued_adicCompletionComap kw_ffgc_adicCompletionComapIntegers kw_ffgc_adicCompletionComapIntegers_coe kw_ffgc_algebraAdicCompletionComap kw_ffgc_algebraMap_adicCompletionComap_eq kw_ffgc_rankOne_adicCompletion kw_ffgc_absoluteValue kw_ffgc_adicCompletionComap_algebraMap_algebraMap kw_ffgc_completionLinearCombination kw_ffgc_denseRange_completionLinearCombination kw_ffgc_finiteDimensional_adicCompletion kw_ffgc_completionTraceF' regularSubmodule finiteResidue_of_deg_pos poleSubmodule uniformizer_pow_ne_zero ord_uniformizer_pow poleSubmodule_mono iSup_poleSubmodule_eq_top exists_mem_poleSubmodule canonicalLocalResidueDataK_agree_on_poleSubmodule_of_surj)

open _root_.AlgebraicCurve.Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

end Place


namespace RationalFunctionField

export _root_.AlgebraicCurve.RationalFunctionField (heightOneSpectrumOfIrreducible heightOneSpectrumOfIrreducible_asIdeal exists_irreducible_span finitePlace finitePlace_def algebraMap_mem_ofHeightOneSpectrum deg_ofHeightOneSpectrum deg_finitePlace)

open _root_.AlgebraicCurve.RationalFunctionField

variable (K : Type*) [Field K]

section PlaceInfty

variable [DecidableEq (RatFunc K)]

theorem ord_placeInfty_eq_zero_of_intDegree_eq_zero {f : RatFunc K} (hf : f ≠ 0)
    (h : f.intDegree = 0) : (placeInfty K).ord f = 0 := by
  rw [(placeInfty K).ord_eq_zero_iff_adicValuation_eq_one hf,
    ← (inftyValuation_isEquiv_adicValuation K).eq_one_iff_eq_one,
    RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero K hf, h]
  rfl

theorem ord_placeInfty_eq_intDegree_mul {f : RatFunc K} (hf : f ≠ 0) :
    (placeInfty K).ord f = f.intDegree * (placeInfty K).ord (RatFunc.X) := by
  have hinj := IsFractionRing.injective K[X] (RatFunc K)

  have hpoly : ∀ q : K[X], q ≠ 0 →
      (placeInfty K).ord (algebraMap K[X] (RatFunc K) q)
        = (q.natDegree : ℤ) * (placeInfty K).ord (RatFunc.X) := by
    intro q hq
    have hq' : algebraMap K[X] (RatFunc K) q ≠ 0 := (map_ne_zero_iff _ hinj).mpr hq
    have hX : (RatFunc.X : RatFunc K) ≠ 0 := RatFunc.X_ne_zero
    have hXpow : (RatFunc.X : RatFunc K) ^ q.natDegree ≠ 0 := pow_ne_zero _ hX

    have hXpoly : (RatFunc.X : RatFunc K) ^ q.natDegree
        = algebraMap K[X] (RatFunc K) (Polynomial.X ^ q.natDegree) := by
      rw [map_pow, RatFunc.algebraMap_X]
    have hdeg : (algebraMap K[X] (RatFunc K) q / RatFunc.X ^ q.natDegree).intDegree = 0 := by
      rw [RatFunc.intDegree_div hq' hXpow, RatFunc.intDegree_polynomial, hXpoly,
        RatFunc.intDegree_polynomial, natDegree_X_pow, sub_self]
    have hne : algebraMap K[X] (RatFunc K) q / RatFunc.X ^ q.natDegree ≠ 0 :=
      div_ne_zero hq' hXpow
    have h0 := ord_placeInfty_eq_zero_of_intDegree_eq_zero K hne hdeg
    have hsplit : algebraMap K[X] (RatFunc K) q
        = (algebraMap K[X] (RatFunc K) q / RatFunc.X ^ q.natDegree)
          * RatFunc.X ^ q.natDegree :=
      (div_mul_cancel₀ _ hXpow).symm
    rw [hsplit, (placeInfty K).ord_mul hne hXpow, h0, zero_add, ← zpow_natCast,
      (placeInfty K).ord_zpow]
  have hnum' : algebraMap K[X] (RatFunc K) f.num ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr (RatFunc.num_ne_zero hf)
  have hden' : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr f.denom_ne_zero
  rw [show f = algebraMap K[X] (RatFunc K) f.num * (algebraMap K[X] (RatFunc K) f.denom)⁻¹ by
      rw [← div_eq_mul_inv, f.num_div_denom],
    (placeInfty K).ord_mul hnum' (inv_ne_zero hden'), (placeInfty K).ord_inv,
    hpoly _ (RatFunc.num_ne_zero hf), hpoly _ f.denom_ne_zero, ← div_eq_mul_inv,
    RatFunc.intDegree_div hnum' hden', RatFunc.intDegree_polynomial,
    RatFunc.intDegree_polynomial]
  ring

theorem ord_placeInfty_X : (placeInfty K).ord (RatFunc.X : RatFunc K) = -1 := by
  have hX : (RatFunc.X : RatFunc K) ≠ 0 := RatFunc.X_ne_zero

  have hneg : (placeInfty K).ord (RatFunc.X : RatFunc K) < 0 := by
    by_contra h
    have hmem : (RatFunc.X : RatFunc K) ∈ (placeInfty K).toValuationSubring :=
      (placeInfty K).mem_of_ord_nonneg hX (not_lt.mp h)
    rw [placeInfty_toValuationSubring, Valuation.mem_valuationSubring_iff,
      RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero K hX,
      RatFunc.intDegree_X, show (1 : ℤᵐ⁰) = exp 0 from rfl, exp_le_exp] at hmem
    omega

  obtain ⟨π, hπ⟩ :=
    IsDiscreteValuationRing.exists_irreducible (placeInfty K).toValuationSubring
  have hπ0 : (π : RatFunc K) ≠ 0 := by
    simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  have hdvd : (placeInfty K).ord (RatFunc.X : RatFunc K) ∣ 1 := by
    rw [← (placeInfty K).ord_coe_irreducible hπ, ord_placeInfty_eq_intDegree_mul K hπ0]
    exact Dvd.intro_left _ rfl
  rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd) with h | h <;> omega

end PlaceInfty


section Principal

variable {K}

end Principal


end RationalFunctionField


namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue heightOneSpectrum adicValuation adicValuation_ne_zero adicValuation_coe_eq_one_iff adicValuation_coe_irreducible ord ord_zero ord_one ord_mul ord_inv ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ord_smul ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one isEquiv_adicValuation_ofHeightOneSpectrum ord_ofHeightOneSpectrum_ne_zero_iff dCoord DCoordGenerates dCoord_ne_zero differentialCoeff exists_eq_smul_dCoord differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero CanonicalLocalResidueDataK localResidue localResidue_eq_zero_of_ord_nonneg differentialCoeff_ne_zero ramificationIndex ramificationIndex_pos restrict ord_restrict restrictInclusion inertiaDeg deg_restrict_mul_inertiaDeg fiber mem_fiber ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq adicCompletion adicCompletionIntegers kw_ffgc_adicCompletionComap kw_ffgc_valued_adicCompletionComap kw_ffgc_adicCompletionComapIntegers kw_ffgc_adicCompletionComapIntegers_coe kw_ffgc_algebraAdicCompletionComap kw_ffgc_algebraMap_adicCompletionComap_eq kw_ffgc_rankOne_adicCompletion kw_ffgc_absoluteValue kw_ffgc_adicCompletionComap_algebraMap_algebraMap kw_ffgc_completionLinearCombination kw_ffgc_denseRange_completionLinearCombination kw_ffgc_finiteDimensional_adicCompletion kw_ffgc_completionTraceF' regularSubmodule finiteResidue_of_deg_pos poleSubmodule uniformizer_pow_ne_zero ord_uniformizer_pow poleSubmodule_mono iSup_poleSubmodule_eq_top exists_mem_poleSubmodule canonicalLocalResidueDataK_agree_on_poleSubmodule_of_surj)

open _root_.AlgebraicCurve.Place

section Congr

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (e : F ≃+* F')

variable (he : ∀ a : K, e (algebraMap K F a) = algebraMap K F' a)
include he

end Congr


end Place


namespace Pic0

export _root_.AlgebraicCurve.Pic0 (mk mk_surjective)

open _root_.AlgebraicCurve.Pic0

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (e : F ≃+* F') (he : ∀ a : K, e (algebraMap K F a) = algebraMap K F' a)
include e he

end Pic0


end AlgebraicCurve


namespace ModularCurve

export _root_.ModularCurve (KwF4R1V391a.KwF4R1V391aResidueTraceCompletionCommute)

open _root_.ModularCurve

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve
open _root_.IntermediateField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.IntermediateField

end ModularCurve


end

end


end


section
section

noncomputable section

open _root_.KaehlerDifferential
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.KaehlerDifferential

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Place.ord Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential diagonalHom diagonalHom_apply diagonal_mem_adeleSpace HasCanonicalDivisor HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTerm kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_support_finite_of_adeleSpace weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK HasCanonicalLocalResidueKStar.dataKStar Place.mem_fiber Place.valuationSubringAlgebra Place.finite_setOf_restrict_eq kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kaehlerCotrace kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt KwHgfV352CompletionTraceSum FiberKaehlerCotraceResidueIdentityK CotraceResidueIdentityOnFiberLocalizedK Place.finiteResidue_of_deg_pos residueTraceCompletionCommute residueTheoremK_ratFunc_of_isAlgClosed)

open _root_.AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

def KaehlerRankOne : Prop :=
  Module.Free F Ω[F⁄K] ∧ Module.finrank F Ω[F⁄K] = 1

variable {K F}

namespace IsCurveOver
export _root_.AlgebraicCurve.IsCurveOver (instFiniteResidue mk finiteResidue kaehler_free_rank_one)
end IsCurveOver
open scoped _root_.AlgebraicCurve.IsCurveOver in
theorem IsCurveOver.of_finiteResidue_of_kaehlerRankOne
    [HasPrincipalDivisors K F] [∀ v : Place K F, v.FiniteResidue]
    (hΩ : KaehlerRankOne K F) : IsCurveOver K F where
  finiteResidue v := Place.FiniteResidue.finite (v := v)
  kaehler_free_rank_one := hΩ

namespace RationalFunctionField

export _root_.AlgebraicCurve.RationalFunctionField (heightOneSpectrumOfIrreducible heightOneSpectrumOfIrreducible_asIdeal exists_irreducible_span finitePlace finitePlace_def algebraMap_mem_ofHeightOneSpectrum deg_ofHeightOneSpectrum deg_finitePlace)

open _root_.AlgebraicCurve.RationalFunctionField

variable (K : Type*) [Field K]

theorem isCurveOver_of_kaehlerRankOne (hΩ : KaehlerRankOne K (RatFunc K)) :
    IsCurveOver K (RatFunc K) :=
  IsCurveOver.of_finiteResidue_of_kaehlerRankOne hΩ

end RationalFunctionField


variable (K F)

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
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.Polynomial
open _root_.IntermediateField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.IntermediateField
open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Place.ord Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential diagonalHom diagonalHom_apply diagonal_mem_adeleSpace HasCanonicalDivisor HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTerm kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_support_finite_of_adeleSpace weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK HasCanonicalLocalResidueKStar.dataKStar Place.mem_fiber Place.valuationSubringAlgebra Place.finite_setOf_restrict_eq kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kaehlerCotrace kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt KwHgfV352CompletionTraceSum FiberKaehlerCotraceResidueIdentityK CotraceResidueIdentityOnFiberLocalizedK Place.finiteResidue_of_deg_pos residueTraceCompletionCommute residueTheoremK_ratFunc_of_isAlgClosed)

open _root_.AlgebraicCurve

variable {K : Type*} [Field K]

end AlgebraicCurve


namespace ModularCurve

export _root_.ModularCurve (KwF4R1V391a.KwF4R1V391aResidueTraceCompletionCommute)

open _root_.ModularCurve

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


section
section

noncomputable section

open _root_.IntermediateField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.IntermediateField
open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve
open _root_.Polynomial
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.Polynomial
open _root_.TensorProduct
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.TensorProduct
open _root_.Module
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.Module

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Place.ord Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential diagonalHom diagonalHom_apply diagonal_mem_adeleSpace HasCanonicalDivisor HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTerm kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_support_finite_of_adeleSpace weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK HasCanonicalLocalResidueKStar.dataKStar Place.mem_fiber Place.valuationSubringAlgebra Place.finite_setOf_restrict_eq kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kaehlerCotrace kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt KwHgfV352CompletionTraceSum FiberKaehlerCotraceResidueIdentityK CotraceResidueIdentityOnFiberLocalizedK Place.finiteResidue_of_deg_pos residueTraceCompletionCommute residueTheoremK_ratFunc_of_isAlgClosed)

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

export _root_.ModularCurve (KwF4R1V391a.KwF4R1V391aResidueTraceCompletionCommute)

open _root_.ModularCurve

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]

end ModularCurve


end

end


end


section
section

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

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Place.ord Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential diagonalHom diagonalHom_apply diagonal_mem_adeleSpace HasCanonicalDivisor HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTerm kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_support_finite_of_adeleSpace weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK HasCanonicalLocalResidueKStar.dataKStar Place.mem_fiber Place.valuationSubringAlgebra Place.finite_setOf_restrict_eq kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kaehlerCotrace kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt KwHgfV352CompletionTraceSum FiberKaehlerCotraceResidueIdentityK CotraceResidueIdentityOnFiberLocalizedK Place.finiteResidue_of_deg_pos residueTraceCompletionCommute residueTheoremK_ratFunc_of_isAlgClosed)

open _root_.AlgebraicCurve

namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue heightOneSpectrum adicValuation adicValuation_ne_zero adicValuation_coe_eq_one_iff adicValuation_coe_irreducible ord ord_zero ord_one ord_mul ord_inv ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ord_smul ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one isEquiv_adicValuation_ofHeightOneSpectrum ord_ofHeightOneSpectrum_ne_zero_iff dCoord DCoordGenerates dCoord_ne_zero differentialCoeff exists_eq_smul_dCoord differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero CanonicalLocalResidueDataK localResidue localResidue_eq_zero_of_ord_nonneg differentialCoeff_ne_zero ramificationIndex ramificationIndex_pos restrict ord_restrict restrictInclusion inertiaDeg deg_restrict_mul_inertiaDeg fiber mem_fiber ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq adicCompletion adicCompletionIntegers kw_ffgc_adicCompletionComap kw_ffgc_valued_adicCompletionComap kw_ffgc_adicCompletionComapIntegers kw_ffgc_adicCompletionComapIntegers_coe kw_ffgc_algebraAdicCompletionComap kw_ffgc_algebraMap_adicCompletionComap_eq kw_ffgc_rankOne_adicCompletion kw_ffgc_absoluteValue kw_ffgc_adicCompletionComap_algebraMap_algebraMap kw_ffgc_completionLinearCombination kw_ffgc_denseRange_completionLinearCombination kw_ffgc_finiteDimensional_adicCompletion kw_ffgc_completionTraceF' regularSubmodule finiteResidue_of_deg_pos poleSubmodule uniformizer_pow_ne_zero ord_uniformizer_pow poleSubmodule_mono iSup_poleSubmodule_eq_top exists_mem_poleSubmodule canonicalLocalResidueDataK_agree_on_poleSubmodule_of_surj)

open _root_.AlgebraicCurve.Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

@[scoped simp]
theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.mem_regularSubmodule (w : Place K F) (ωF : Ω[F⁄K]) (f : F) :
    f ∈ w.regularSubmodule ωF ↔ f * w.differentialCoeff ωF ∈ w.toValuationSubring := Iff.rfl




-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.mem_regularSubmodule :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.mem_regularSubmodule
end Place


namespace FiberKaehlerLocalDatum

section KernelContainments

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]

end KernelContainments


section ModularInvariance

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]

end ModularInvariance


section PolarSpanEngine

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]

end PolarSpanEngine


section ComposedEngine

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)]
variable [∀ w : Place K F, w.DCoordGenerates] [Nontrivial Ω[F⁄K]]
variable {E : Type*} [Field E] [Algebra K E]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalDivisor (K := K) (F := E)]
variable [∀ v : Place K E, v.DCoordGenerates] [Nontrivial Ω[E⁄K]]
variable [Algebra E F] [IsScalarTower K E F] [Algebra.IsIntegral E F]
variable [Module.Finite E F] [∀ v : Place K E, v.FiniteResidue]

end ComposedEngine


end FiberKaehlerLocalDatum


end AlgebraicCurve


section AxiomAudit

end AxiomAudit


end


end


end

end P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed
