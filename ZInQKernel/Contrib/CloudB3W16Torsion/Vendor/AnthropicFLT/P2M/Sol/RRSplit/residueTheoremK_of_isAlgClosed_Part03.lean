/-
Copyright 2026 Anthropic, PBC. Released under Apache License 2.0.
Source: https://github.com/anthropics/fermats-last-theorem
Revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.lean; source lines 3203-5269.
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
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.RRSplit.residueTheoremK_of_isAlgClosed_Part02

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 6400000
set_option maxHeartbeats 12800000

namespace P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed

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

def _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.regularPoleSubmodule (w : Place K F) (ωF : Ω[F⁄K]) (n : ℕ) : Submodule K F :=
  (w.poleSubmodule n).comap (LinearMap.mulRight K (w.differentialCoeff ωF))




@[scoped simp]
theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.mem_regularPoleSubmodule (w : Place K F) (ωF : Ω[F⁄K]) (n : ℕ) (f : F) :
    f ∈ w.regularPoleSubmodule ωF n
      ↔ w.uniformizer ^ n * (f * w.differentialCoeff ωF) ∈ w.toValuationSubring := Iff.rfl




theorem regularPoleSubmodule_zero (w : Place K F) (ωF : Ω[F⁄K]) :
    w.regularPoleSubmodule ωF 0 = w.regularSubmodule ωF := by
  ext f
  simp only [mem_regularPoleSubmodule, pow_zero, one_mul, mem_regularSubmodule]

theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.regularPoleSubmodule_mono (w : Place K F) (ωF : Ω[F⁄K]) :
    Monotone (w.regularPoleSubmodule ωF) :=
  fun _ _ hmn => Submodule.comap_mono (w.poleSubmodule_mono hmn)




theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.iSup_regularPoleSubmodule_eq_top (w : Place K F) (ωF : Ω[F⁄K]) :
    ⨆ n, w.regularPoleSubmodule ωF n = ⊤ := by
  rw [eq_top_iff]
  intro f _
  have hmem : f * w.differentialCoeff ωF ∈ ⨆ n, w.poleSubmodule n :=
    w.iSup_poleSubmodule_eq_top ▸ Submodule.mem_top
  obtain ⟨n, hn⟩ := (Submodule.mem_iSup_of_directed _
    (Monotone.directed_le w.poleSubmodule_mono)).mp hmem
  exact Submodule.mem_iSup_of_mem n hn




theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.exists_mem_regularPoleSubmodule (w : Place K F) (ωF : Ω[F⁄K]) (f : F) :
    ∃ n, f ∈ w.regularPoleSubmodule ωF n := by
  have h : f ∈ ⨆ n, w.regularPoleSubmodule ωF n :=
    (w.iSup_regularPoleSubmodule_eq_top ωF) ▸ Submodule.mem_top
  exact (Submodule.mem_iSup_of_directed _
    (Monotone.directed_le (w.regularPoleSubmodule_mono ωF))).mp h




end Place


namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue heightOneSpectrum adicValuation adicValuation_ne_zero adicValuation_coe_eq_one_iff adicValuation_coe_irreducible ord ord_zero ord_one ord_mul ord_inv ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ord_smul ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one isEquiv_adicValuation_ofHeightOneSpectrum ord_ofHeightOneSpectrum_ne_zero_iff dCoord DCoordGenerates dCoord_ne_zero differentialCoeff exists_eq_smul_dCoord differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero CanonicalLocalResidueDataK localResidue localResidue_eq_zero_of_ord_nonneg differentialCoeff_ne_zero ramificationIndex ramificationIndex_pos restrict ord_restrict restrictInclusion inertiaDeg deg_restrict_mul_inertiaDeg fiber mem_fiber ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq adicCompletion adicCompletionIntegers kw_ffgc_adicCompletionComap kw_ffgc_valued_adicCompletionComap kw_ffgc_adicCompletionComapIntegers kw_ffgc_adicCompletionComapIntegers_coe kw_ffgc_algebraAdicCompletionComap kw_ffgc_algebraMap_adicCompletionComap_eq kw_ffgc_rankOne_adicCompletion kw_ffgc_absoluteValue kw_ffgc_adicCompletionComap_algebraMap_algebraMap kw_ffgc_completionLinearCombination kw_ffgc_denseRange_completionLinearCombination kw_ffgc_finiteDimensional_adicCompletion kw_ffgc_completionTraceF' regularSubmodule finiteResidue_of_deg_pos poleSubmodule uniformizer_pow_ne_zero ord_uniformizer_pow poleSubmodule_mono iSup_poleSubmodule_eq_top exists_mem_poleSubmodule canonicalLocalResidueDataK_agree_on_poleSubmodule_of_surj)

open _root_.AlgebraicCurve.Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

end Place


namespace FiberKaehlerLocalDatum

section LaurentRecursion

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]

variable [∀ w : Place K F, w.DCoordGenerates] [Nontrivial Ω[F⁄K]]

end LaurentRecursion


section LaurentMonomRow

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]

end LaurentMonomRow


section Engine

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]
variable [∀ w : Place K F, w.DCoordGenerates] [Nontrivial Ω[F⁄K]]

end Engine


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

open scoped Polynomial P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.Polynomial
open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]

omit [DecidableEq (RatFunc K)] in

theorem D_ratFuncX_eq_neg_X_sq_smul_D_inv :
    KaehlerDifferential.D K (RatFunc K) RatFunc.X
      = (-(RatFunc.X : RatFunc K) ^ 2) •
          KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)⁻¹ :=
  (KaehlerDifferential.D K (RatFunc K)).leibniz_of_mul_eq_one
    (mul_inv_cancel₀ RatFunc.X_ne_zero)

theorem ord_placeInfty_X_inv : (placeInfty K).ord (RatFunc.X : RatFunc K)⁻¹ = 1 := by
  rw [(placeInfty K).ord_inv, ord_placeInfty_X, neg_neg]

theorem ord_placeInfty_X_pow (n : ℕ) :
    (placeInfty K).ord ((RatFunc.X : RatFunc K) ^ n) = -(n : ℤ) := by
  rw [show ((RatFunc.X : RatFunc K) ^ n) = (RatFunc.X : RatFunc K) ^ (n : ℤ) from
    (zpow_natCast _ n).symm, (placeInfty K).ord_zpow, ord_placeInfty_X]
  ring

section NonVanishing

variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

theorem D_ratFuncX_inv_ne_zero (hwd : OrdDifferentialWellDefined K (RatFunc K)) :
    KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)⁻¹ ≠ 0 := by
  obtain ⟨u, -, hueq⟩ :=
    hwd (placeInfty K) (RatFunc.X : RatFunc K)⁻¹ (placeInfty K).uniformizer
      (ord_placeInfty_X_inv K) (placeInfty K).ord_uniformizer
  intro h0
  refine (placeInfty K).dCoord_ne_zero ?_
  show KaehlerDifferential.D K (RatFunc K) (placeInfty K).uniformizer = 0
  rw [hueq, h0, smul_zero]

end NonVanishing


section DifferentialCoeff

variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

theorem differentialCoeff_placeInfty_D_X_eq :
    (placeInfty K).differentialCoeff (KaehlerDifferential.D K (RatFunc K) RatFunc.X)
      = (-(RatFunc.X : RatFunc K) ^ 2) *
          (placeInfty K).differentialCoeff
            (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)⁻¹) := by
  rw [D_ratFuncX_eq_neg_X_sq_smul_D_inv, (placeInfty K).differentialCoeff_smul]

theorem ord_differentialCoeff_placeInfty_D_X_inv_eq_zero
    (hwd : OrdDifferentialWellDefined K (RatFunc K)) :
    (placeInfty K).ord
        ((placeInfty K).differentialCoeff
          (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)⁻¹)) = 0 := by
  obtain ⟨u, hu0, hueq⟩ :=
    hwd (placeInfty K) (placeInfty K).uniformizer (RatFunc.X : RatFunc K)⁻¹
      (placeInfty K).ord_uniformizer (ord_placeInfty_X_inv K)
  rw [(placeInfty K).differentialCoeff_unique
    (show KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)⁻¹
        = u • (placeInfty K).dCoord from hueq), hu0]

end DifferentialCoeff


section OrdDifferential

variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

theorem ordDifferential_placeInfty_D_ratFuncX
    (hwd : OrdDifferentialWellDefined K (RatFunc K)) :
    (placeInfty K).ordDifferential
        (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)) = -2 := by
  rw [Place.ordDifferential, differentialCoeff_placeInfty_D_X_eq K, neg_mul,
    (placeInfty K).ord_neg,
    (placeInfty K).ord_mul (pow_ne_zero 2 RatFunc.X_ne_zero)
      ((placeInfty K).differentialCoeff_ne_zero (D_ratFuncX_inv_ne_zero K hwd)),
    ord_placeInfty_X_pow K 2, ord_differentialCoeff_placeInfty_D_X_inv_eq_zero K hwd]
  norm_num

end OrdDifferential


section Factorisation

variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

end Factorisation


section NamedSubrow

variable [HasCanonicalLocalResidueKStar K (RatFunc K)]

end NamedSubrow


section Bridge

variable [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

end Bridge


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

open scoped Polynomial P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.Polynomial

open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]

variable (K)

section InftyVanish

variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]

end InftyVanish


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

open scoped Polynomial P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.Polynomial

open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField

variable (K : Type*) [Field K]

abbrev dX : Ω[(RatFunc K)⁄K] := KaehlerDifferential.D K (RatFunc K) RatFunc.X

theorem aeval_ratFuncX_eq_algebraMap (q : K[X]) :
    aeval (RatFunc.X : RatFunc K) q = algebraMap K[X] (RatFunc K) q := by
  rw [← RatFunc.algebraMap_X,
    show algebraMap K[X] (RatFunc K) X = IsScalarTower.toAlgHom K K[X] (RatFunc K) X from rfl,
    aeval_algHom_apply, aeval_X_left_apply]
  rfl

theorem D_algebraMap_polynomial (q : K[X]) :
    KaehlerDifferential.D K (RatFunc K) (algebraMap K[X] (RatFunc K) q)
      = algebraMap K[X] (RatFunc K) q.derivative • dX K := by
  rw [← aeval_ratFuncX_eq_algebraMap K q, (D K (RatFunc K)).map_aeval q RatFunc.X,
    aeval_ratFuncX_eq_algebraMap K q.derivative]

theorem denom_sq_smul_D_eq (f : RatFunc K) :
    (algebraMap K[X] (RatFunc K) f.denom) ^ 2 • KaehlerDifferential.D K (RatFunc K) f
      = algebraMap K[X] (RatFunc K)
          (f.num.derivative * f.denom - f.num * f.denom.derivative) • dX K := by
  have hd : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr f.denom_ne_zero
  have hDf : KaehlerDifferential.D K (RatFunc K) f
      = ((algebraMap K[X] (RatFunc K) f.denom)⁻¹ ^ 2) •
        (algebraMap K[X] (RatFunc K) f.denom • D K (RatFunc K) (algebraMap K[X] (RatFunc K) f.num)
          - algebraMap K[X] (RatFunc K) f.num
              • D K (RatFunc K) (algebraMap K[X] (RatFunc K) f.denom)) := by
    conv_lhs => rw [← f.num_div_denom, (D K (RatFunc K)).leibniz_div]
  rw [hDf, smul_smul, ← mul_pow, mul_inv_cancel₀ hd, one_pow, one_smul,
    D_algebraMap_polynomial K f.num, D_algebraMap_polynomial K f.denom,
    smul_smul, smul_smul, ← sub_smul]
  push_cast
  ring_nf

theorem span_dX_eq_top :
    Submodule.span (RatFunc K) {dX K} = ⊤ := by
  rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation, Submodule.span_le]
  rintro _ ⟨f, rfl⟩
  have hd : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr f.denom_ne_zero

  have hsq : ((algebraMap K[X] (RatFunc K) f.denom) ^ 2)⁻¹
        * (algebraMap K[X] (RatFunc K) f.denom) ^ 2 = 1 :=
    inv_mul_cancel₀ (pow_ne_zero 2 hd)
  refine Submodule.mem_span_singleton.mpr ⟨((algebraMap K[X] (RatFunc K) f.denom) ^ 2)⁻¹
    * algebraMap K[X] (RatFunc K)
        (f.num.derivative * f.denom - f.num * f.denom.derivative), ?_⟩
  rw [mul_smul, ← denom_sq_smul_D_eq K f, smul_smul, hsq, one_smul]

theorem dX_ne_zero [Nontrivial Ω[(RatFunc K)⁄K]] : dX K ≠ 0 := by
  intro h0
  obtain ⟨ω, hω⟩ := exists_ne (0 : Ω[(RatFunc K)⁄K])
  have hω_mem : ω ∈ Submodule.span (RatFunc K) {dX K} :=
    span_dX_eq_top K ▸ Submodule.mem_top
  rw [h0, Submodule.span_zero_singleton] at hω_mem
  exact hω hω_mem

theorem not_dvd_derivative_of_sq_not_dvd {p : K[X]} (hp : Irreducible p) (hsep : p.Separable)
    {q : K[X]} (hpq : p ∣ q) (hpq2 : ¬ p ^ 2 ∣ q) : ¬ p ∣ q.derivative := by
  obtain ⟨m, rfl⟩ := hpq
  have hpm : ¬ p ∣ m := fun ⟨r, hr⟩ => hpq2 ⟨r, by rw [hr]; ring⟩
  intro hpdvd
  rw [derivative_mul] at hpdvd
  have hpdvd' : p ∣ p.derivative * m := by
    have := dvd_sub hpdvd (dvd_mul_right p m.derivative)
    rwa [add_sub_cancel_right] at this
  rcases hp.prime.dvd_mul.mp hpdvd' with hpp' | hpm'
  ·
    exact hp.not_isUnit (hsep.isUnit_of_dvd' dvd_rfl hpp')
  · exact hpm hpm'

variable {K}

theorem not_dvd_derivative_of_ord_eq_one {w : HeightOneSpectrum K[X]} {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) (hsep : p.Separable)
    {q : K[X]} (hq : q ≠ 0)
    (hord : (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord
      (algebraMap K[X] (RatFunc K) q) = 1) :
    ¬ p ∣ q.derivative := by
  have hwmem : ∀ {r : K[X]}, r ≠ 0 →
      ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord
        (algebraMap K[X] (RatFunc K) r) ≠ 0 ↔ p ∣ r) := fun {r} hr => by
    rw [Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w hr,
      hwp, Ideal.mem_span_singleton]
  have hordp : (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord
      (algebraMap K[X] (RatFunc K) p) = 1 :=
    ord_ofHeightOneSpectrum_of_span w hp.ne_zero hwp
  refine not_dvd_derivative_of_sq_not_dvd K hp hsep
    ((hwmem hq).mp (hord ▸ one_ne_zero)) ?_

  rintro ⟨r, rfl⟩
  have hr : r ≠ 0 := fun h => hq (by simp [h])
  have : (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord
      (algebraMap K[X] (RatFunc K) (p ^ 2 * r)) ≥ 2 := by
    have hp0 : algebraMap K[X] (RatFunc K) p ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hp.ne_zero
    have hr0 : algebraMap K[X] (RatFunc K) r ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hr
    rw [map_mul, map_pow,
      (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord_mul (pow_ne_zero 2 hp0) hr0,
      ← zpow_natCast, (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord_zpow,
      hordp, mul_one]
    have : 0 ≤ (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord
        (algebraMap K[X] (RatFunc K) r) :=
      (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord_nonneg_of_mem
        (algebraMap_mem_ofHeightOneSpectrum K w r)
    omega
  omega

section NumDenom

variable {w : HeightOneSpectrum K[X]}



theorem uniformizer_ne_zero' : ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).uniformizer ≠ 0 :=
  ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).uniformizer_ne_zero

theorem ord_algebraMap_denom_uniformizer_eq_zero {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) :
    ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord (algebraMap K[X] (RatFunc K) ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).uniformizer.denom) = 0 := by
  set π := ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).uniformizer with hπ
  have hπne : π ≠ 0 := uniformizer_ne_zero'
  by_contra hne

  have hpd : p ∣ π.denom := by
    rw [← Ideal.mem_span_singleton, ← hwp]
    exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
      π.denom_ne_zero).mp hne
  have hpn : ¬ p ∣ π.num := fun hpn =>
    hp.not_isUnit (π.isCoprime_num_denom.isUnit_of_dvd' hpn hpd)
  have hordn : ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord (algebraMap K[X] (RatFunc K) π.num) = 0 := by
    by_contra h
    exact hpn (by
      rw [← Ideal.mem_span_singleton, ← hwp]
      exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
        (RatFunc.num_ne_zero hπne)).mp h)
  have hordd : 0 < ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord (algebraMap K[X] (RatFunc K) π.denom) :=
    lt_of_le_of_ne (((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord_nonneg_of_mem (algebraMap_mem_ofHeightOneSpectrum K w _)) (Ne.symm hne)

  have hnum0 : algebraMap K[X] (RatFunc K) π.num ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr (RatFunc.num_ne_zero hπne)
  have hden0 : algebraMap K[X] (RatFunc K) π.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr π.denom_ne_zero
  have hordπ : ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord π = 1 := ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord_uniformizer
  rw [← π.num_div_denom, div_eq_mul_inv, ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord_mul hnum0 (inv_ne_zero hden0),
    ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord_inv, hordn] at hordπ
  omega

theorem ord_algebraMap_num_uniformizer_eq_one {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) :
    ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord (algebraMap K[X] (RatFunc K) ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).uniformizer.num) = 1 := by
  set π := ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).uniformizer with hπ
  have hπne : π ≠ 0 := uniformizer_ne_zero'
  have hnum0 : algebraMap K[X] (RatFunc K) π.num ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr (RatFunc.num_ne_zero hπne)
  have hden0 : algebraMap K[X] (RatFunc K) π.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr π.denom_ne_zero
  have hordπ : ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord π = 1 := ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord_uniformizer
  rw [← π.num_div_denom, div_eq_mul_inv, ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord_mul hnum0 (inv_ne_zero hden0),
    ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord_inv, ord_algebraMap_denom_uniformizer_eq_zero hp hwp] at hordπ
  omega

theorem not_dvd_num'denom_sub_numdenom' {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) (hsep : p.Separable) :
    ¬ p ∣ (((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).uniformizer.num.derivative * ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).uniformizer.denom
            - ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).uniformizer.num * ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).uniformizer.denom.derivative) := by
  set π := ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).uniformizer with hπ
  have hπne : π ≠ 0 := uniformizer_ne_zero'
  have hpn' : ¬ p ∣ π.num.derivative :=
    not_dvd_derivative_of_ord_eq_one hp hwp hsep (RatFunc.num_ne_zero hπne)
      (ord_algebraMap_num_uniformizer_eq_one hp hwp)
  have hpd : ¬ p ∣ π.denom := fun hpd => by
    have := ord_algebraMap_denom_uniformizer_eq_zero (w := w) hp hwp
    rw [← Ideal.mem_span_singleton, ← hwp] at hpd
    exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
      π.denom_ne_zero).mpr hpd this
  have hpn : p ∣ π.num := by
    rw [← Ideal.mem_span_singleton, ← hwp]
    refine (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
      (RatFunc.num_ne_zero hπne)).mp ?_
    rw [ord_algebraMap_num_uniformizer_eq_one hp hwp]; exact one_ne_zero
  intro hdvd

  have hpnd' : p ∣ π.num * π.denom.derivative := hpn.mul_right _
  have hpn'd : p ∣ π.num.derivative * π.denom := by
    have := dvd_add hdvd hpnd'
    rwa [sub_add_cancel] at this
  rcases hp.prime.dvd_mul.mp hpn'd with h | h
  · exact hpn' h
  · exact hpd h

end NumDenom


section PerPlace

variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable {w : HeightOneSpectrum K[X]}



theorem ord_differentialCoeff_dX_ofHeightOneSpectrum {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) (hsep : p.Separable) :
    ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord (((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).differentialCoeff (dX K)) = 0 := by
  set π := ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).uniformizer with hπ
  have hπne : π ≠ 0 := uniformizer_ne_zero'
  set ξ : K[X] := π.num.derivative * π.denom - π.num * π.denom.derivative with hξ
  have hd0 : algebraMap K[X] (RatFunc K) π.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr π.denom_ne_zero

  have hcoord : ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).dCoord
      = (algebraMap K[X] (RatFunc K) ξ / (algebraMap K[X] (RatFunc K) π.denom) ^ 2) • dX K := by
    rw [div_eq_mul_inv, mul_comm, mul_smul, ← denom_sq_smul_D_eq K π, smul_smul,
      inv_mul_cancel₀ (pow_ne_zero 2 hd0), one_smul]
    rfl

  have hξ0 : ξ ≠ 0 := by
    intro h; rw [hξ] at h
    exact not_dvd_num'denom_sub_numdenom' hp hwp hsep (h ▸ dvd_zero p)
  have hcoeff0 : algebraMap K[X] (RatFunc K) ξ / (algebraMap K[X] (RatFunc K) π.denom) ^ 2 ≠ 0 :=
    div_ne_zero ((map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hξ0)
      (pow_ne_zero 2 hd0)

  have hcoeff : ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).differentialCoeff (dX K)
      = (algebraMap K[X] (RatFunc K) ξ / (algebraMap K[X] (RatFunc K) π.denom) ^ 2)⁻¹ := by
    refine ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).differentialCoeff_unique ?_
    rw [hcoord, smul_smul, inv_mul_cancel₀ hcoeff0, one_smul]

  have hordξ : ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord (algebraMap K[X] (RatFunc K) ξ) = 0 := by
    by_contra h
    refine not_dvd_num'denom_sub_numdenom' hp hwp hsep ?_
    rw [← Ideal.mem_span_singleton, ← hwp]
    exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w hξ0).mp h
  rw [hcoeff, ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord_inv, div_eq_mul_inv,
    ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord_mul ((map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hξ0)
      (inv_ne_zero (pow_ne_zero 2 hd0)),
    hordξ, ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord_inv, ← zpow_natCast, ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord_zpow,
    ord_algebraMap_denom_uniformizer_eq_zero hp hwp]
  ring

end PerPlace


section Discharge

variable (K)
variable [CharZero K] [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]

end Discharge


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
open _root_.KaehlerDifferential
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.KaehlerDifferential
open _root_.Polynomial
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.Polynomial

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Place.ord Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential diagonalHom diagonalHom_apply diagonal_mem_adeleSpace HasCanonicalDivisor HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTerm kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_support_finite_of_adeleSpace weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK HasCanonicalLocalResidueKStar.dataKStar Place.mem_fiber Place.valuationSubringAlgebra Place.finite_setOf_restrict_eq kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kaehlerCotrace kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt KwHgfV352CompletionTraceSum FiberKaehlerCotraceResidueIdentityK CotraceResidueIdentityOnFiberLocalizedK Place.finiteResidue_of_deg_pos residueTraceCompletionCommute residueTheoremK_ratFunc_of_isAlgClosed)

open _root_.AlgebraicCurve

open scoped Polynomial P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.Polynomial

open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField

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

set_option linter.unusedSectionVars false

set_option synthInstance.maxHeartbeats 3200000
set_option maxHeartbeats 6400000

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

section Helpers

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]

end Helpers


section NoGoEngine

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]

namespace FiberKaehlerLocalDatum

end FiberKaehlerLocalDatum


end NoGoEngine


section FKRINoGo

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [HasCanonicalLocalResidueKStar K F]
variable [∀ w : Place K F, w.DCoordGenerates] [Nontrivial Ω[F⁄K]]
variable {E : Type*} [Field E] [Algebra K E]
variable [HasCanonicalLocalResidueKStar K E]
variable [∀ v : Place K E, v.DCoordGenerates] [Nontrivial Ω[E⁄K]]
variable [Algebra E F] [IsScalarTower K E F] [Algebra.IsIntegral E F]

end FKRINoGo


section CorrectedCarrier

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]

variable {K F E}

variable (K F E)
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]
variable [Algebra.IsIntegral E F]

def FiberKaehlerCotraceResidueIdentity : Prop :=
  ∀ [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]
    {ωE : Ω[E⁄K]} (_ : ωE ≠ 0) (_ : kaehlerPullback K F E ωE ≠ 0)
    (v : Place K E) (f : F),
    ∑ w ∈ v.fiber F, kaehlerResidueTerm (kaehlerPullback K F E ωE) (diagonalHom K F f) w
      = kaehlerResidueTerm ωE (diagonalHom K E (Algebra.trace E F f)) v

end CorrectedCarrier


section CorrectedEngine

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [HasCanonicalLocalResidueKStar K F]
variable [∀ w : Place K F, w.DCoordGenerates] [Nontrivial Ω[F⁄K]]
variable {E : Type*} [Field E] [Algebra K E]
variable [HasCanonicalLocalResidueKStar K E]
variable [∀ v : Place K E, v.DCoordGenerates] [Nontrivial Ω[E⁄K]]
variable [Algebra E F] [IsScalarTower K E F] [Algebra.IsIntegral E F]

end CorrectedEngine


end AlgebraicCurve


namespace ModularCurve

export _root_.ModularCurve (KwF4R1V391a.KwF4R1V391aResidueTraceCompletionCommute)

open _root_.ModularCurve

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve
open _root_.Polynomial
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.Polynomial
open _root_.IntermediateField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.IntermediateField

attribute [local instance 2000] RatFunc.instAlgebraOfPolynomial

section ProductionNondegeneracy

end ProductionNondegeneracy


section ProductionNoGo

end ProductionNoGo


section CorrectedProductionJoin

variable (N : ℕ) [NeZero N]

end CorrectedProductionJoin


end ModularCurve


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

section KaehlerCotrace

variable (K E F : Type*) [Field K] [Field E] [Field F]
  [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F]

variable {K E F}

theorem kaehlerCotrace_D (e : E) :
    kaehlerCotrace K E F (KaehlerDifferential.D K E e)
      = KaehlerDifferential.D K F (algebraMap E F e) :=
  KaehlerDifferential.map_D K K E F e

theorem kaehlerCotrace_smul_algebraMap (e : E) (ωE : Ω[E⁄K]) :
    kaehlerCotrace K E F (e • ωE) = (algebraMap E F e) • kaehlerCotrace K E F ωE := by
  rw [LinearMap.map_smul, algebra_compatible_smul F e]

end KaehlerCotrace


section KaehlerCotraceSelf

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]

end KaehlerCotraceSelf


namespace FiberKaehlerLocalDatum

section KaehlerCotraceDatumCarrier

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable {E : Type*} [Field E] [Algebra K E] [HasCanonicalLocalResidueKStar K E] [Algebra E F] [IsScalarTower K E F]

end KaehlerCotraceDatumCarrier


section KaehlerCotraceDatumEngine

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable {E : Type*} [Field E] [Algebra K E] [HasCanonicalLocalResidueKStar K E] [Algebra E F] [IsScalarTower K E F]

end KaehlerCotraceDatumEngine


section ChainedDischarges

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable {E : Type*} [Field E] [Algebra K E] [HasCanonicalLocalResidueKStar K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]
variable [∀ v : Place K E, v.DCoordGenerates]
variable [∀ w : Place K F, w.DCoordGenerates]

end ChainedDischarges


section ComposedEngine

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable {E : Type*} [Field E] [Algebra K E] [HasCanonicalLocalResidueKStar K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]
variable [∀ w : Place K F, w.DCoordGenerates]
variable [∀ v : Place K E, v.DCoordGenerates]
variable [HasLocalResidue K F] [HasCanonicalDivisor (K := K) (F := F)] [Nontrivial Ω[F⁄K]]
variable [HasLocalResidue K E] [HasCanonicalDivisor (K := K) (F := E)] [Nontrivial Ω[E⁄K]]
variable [Module.Finite E F] [∀ v : Place K E, v.FiniteResidue]

end ComposedEngine


end FiberKaehlerLocalDatum


section StageABKaehlerCotrace

open scoped Polynomial P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.Polynomial
open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)] [CharZero K]
variable [HasLocalResidue K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable {F : Type*} [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [HasLocalResidue K F] [HasCanonicalDivisor (K := K) (F := F)]
variable [∀ w : Place K F, w.DCoordGenerates] [Nontrivial Ω[F⁄K]]
variable [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
variable [Algebra.IsIntegral (RatFunc K) F]
variable [HasPrincipalDivisors K (RatFunc K)]
variable [Module.Finite (RatFunc K) F] [∀ v : Place K (RatFunc K), v.FiniteResidue]

end StageABKaehlerCotrace


section AxiomAudit

end AxiomAudit


end AlgebraicCurve


end


end


end


section
section

set_option linter.unusedSectionVars false

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

section SeparatingWitness

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable {E : Type*} [Field E] [Algebra K E] [HasCanonicalLocalResidueKStar K E] [Algebra E F] [IsScalarTower K E F]

theorem kaehlerCotrace_dCoord_ne_zero_of_exists
    (v : Place K E) [v.DCoordGenerates]
    {ωE₀ : Ω[E⁄K]} (h : kaehlerCotrace K E F ωE₀ ≠ 0) :
    kaehlerCotrace K E F v.dCoord ≠ 0 := by
  intro hdc
  apply h
  rw [← v.differentialCoeff_smul_dCoord ωE₀, kaehlerCotrace_smul_algebraMap, hdc, smul_zero]

theorem exists_kaehlerCotrace_ne_zero_of_D_algebraMap_ne_zero
    {e : E} (he : KaehlerDifferential.D K F (algebraMap E F e) ≠ 0) :
    ∃ ωE : Ω[E⁄K], kaehlerCotrace K E F ωE ≠ 0 :=
  ⟨KaehlerDifferential.D K E e, by rw [kaehlerCotrace_D]; exact he⟩

end SeparatingWitness


section OverAsk

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable {E : Type*} [Field E] [Algebra K E] [HasCanonicalLocalResidueKStar K E] [Algebra E F] [IsScalarTower K E F]

end OverAsk


section JoinKCD

open scoped Polynomial P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.Polynomial
open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)] [CharZero K]
variable [HasLocalResidue K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable {F : Type*} [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [HasLocalResidue K F] [HasCanonicalDivisor (K := K) (F := F)]
variable [∀ w : Place K F, w.DCoordGenerates] [Nontrivial Ω[F⁄K]]
variable [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
variable [Algebra.IsIntegral (RatFunc K) F]
variable [HasPrincipalDivisors K (RatFunc K)]
variable [Module.Finite (RatFunc K) F] [∀ v : Place K (RatFunc K), v.FiniteResidue]

end JoinKCD


section JoinSurj

open scoped Polynomial P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.Polynomial
open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.FiberKaehlerLocalDatum

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)] [CharZero K]
variable [HasLocalResidue K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable {F : Type*} [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [HasLocalResidue K F] [HasCanonicalDivisor (K := K) (F := F)]
variable [∀ w : Place K F, w.DCoordGenerates] [Nontrivial Ω[F⁄K]]
variable [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
variable [Algebra.IsIntegral (RatFunc K) F]
variable [HasPrincipalDivisors K (RatFunc K)]
variable [Module.Finite (RatFunc K) F] [∀ v : Place K (RatFunc K), v.FiniteResidue]

end JoinSurj


end AlgebraicCurve


section AxiomAudit

end AxiomAudit


end


end


section
section

set_option linter.unusedSectionVars false

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

section CotraceInjective

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]

theorem kaehlerCotrace_injective_iff_dCoord_ne_zero
    (v : Place K E) [v.DCoordGenerates] [Nontrivial Ω[E⁄K]] :
    Function.Injective (kaehlerCotrace K E F) ↔ kaehlerCotrace K E F v.dCoord ≠ 0 := by
  constructor
  · intro hinj h0
    exact v.dCoord_ne_zero (hinj (h0.trans (_root_.map_zero _).symm))
  · intro hne ωE ωE' heq
    obtain ⟨e, rfl⟩ := v.exists_eq_smul_dCoord ωE
    obtain ⟨e', rfl⟩ := v.exists_eq_smul_dCoord ωE'
    rw [kaehlerCotrace_smul_algebraMap, kaehlerCotrace_smul_algebraMap] at heq
    have hee' : algebraMap E F e = algebraMap E F e' :=
      smul_left_injective F hne heq
    rw [(algebraMap E F).injective hee']

variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalLocalResidueKStar K E]

theorem kaehlerCotrace_injective_of_exists_ne_zero
    (v : Place K E) [v.DCoordGenerates] [Nontrivial Ω[E⁄K]]
    {ωE₀ : Ω[E⁄K]} (h : kaehlerCotrace K E F ωE₀ ≠ 0) :
    Function.Injective (kaehlerCotrace K E F) :=
  (kaehlerCotrace_injective_iff_dCoord_ne_zero v).mpr
    (kaehlerCotrace_dCoord_ne_zero_of_exists v h)

theorem kaehlerCotrace_injective_of_D_algebraMap_ne_zero
    (v : Place K E) [v.DCoordGenerates] [Nontrivial Ω[E⁄K]]
    {e : E} (he : KaehlerDifferential.D K F (algebraMap E F e) ≠ 0) :
    Function.Injective (kaehlerCotrace K E F) :=
  let ⟨_, hωE⟩ := exists_kaehlerCotrace_ne_zero_of_D_algebraMap_ne_zero he
  kaehlerCotrace_injective_of_exists_ne_zero v hωE

end CotraceInjective


section CotraceRange

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]

end CotraceRange


section ConstDatum

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]

variable [Algebra.IsIntegral E F]
variable [∀ v : Place K E, v.DCoordGenerates] [Nontrivial Ω[E⁄K]]

end ConstDatum


end AlgebraicCurve


section AxiomAudit

end AxiomAudit


end


end


section
section

set_option linter.unusedSectionVars false

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

open scoped Polynomial P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.Polynomial
open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField

section CotraceDX

variable (K : Type*) [Field K]
variable (F : Type*) [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]

theorem kaehlerCotrace_dX_eq :
    kaehlerCotrace K (RatFunc K) F (dX K)
      = KaehlerDifferential.D K F (algebraMap (RatFunc K) F RatFunc.X) :=
  kaehlerCotrace_D RatFunc.X

end CotraceDX


section SeparatingCarrier

variable (K : Type*) [Field K]
variable (F : Type*) [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F] [Algebra (RatFunc K) F]

def IsSeparatingTranscendental : Prop :=
  KaehlerDifferential.D K F (algebraMap (RatFunc K) F RatFunc.X) ≠ 0

end SeparatingCarrier


section SeparatingEngine

variable (K : Type*) [Field K]
variable (F : Type*) [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]

theorem kaehlerCotrace_dX_ne_zero_of_isSeparatingTranscendental
    (hsep : IsSeparatingTranscendental K F) :
    kaehlerCotrace K (RatFunc K) F (dX K) ≠ 0 := by
  rw [kaehlerCotrace_dX_eq]; exact hsep

theorem isSeparatingTranscendental_iff_kaehlerCotrace_dX_ne_zero :
    IsSeparatingTranscendental K F ↔ kaehlerCotrace K (RatFunc K) F (dX K) ≠ 0 := by
  rw [IsSeparatingTranscendental, kaehlerCotrace_dX_eq]

end SeparatingEngine


section JoinTraceDescentAt

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)] [CharZero K]
variable [HasLocalResidue K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable {F : Type*} [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [HasLocalResidue K F] [HasCanonicalDivisor (K := K) (F := F)]
variable [∀ w : Place K F, w.DCoordGenerates] [Nontrivial Ω[F⁄K]]
variable [Algebra (RatFunc K) F] [HasPrincipalDivisors K (RatFunc K)]

end JoinTraceDescentAt


section JoinLocalDatumAt

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)] [CharZero K]
variable [HasLocalResidue K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable {F : Type*} [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [HasLocalResidue K F] [HasCanonicalDivisor (K := K) (F := F)]
variable [∀ w : Place K F, w.DCoordGenerates] [Nontrivial Ω[F⁄K]]
variable [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
variable [Algebra.IsIntegral (RatFunc K) F]
variable [HasPrincipalDivisors K (RatFunc K)]
variable [Module.Finite (RatFunc K) F] [∀ v : Place K (RatFunc K), v.FiniteResidue]

end JoinLocalDatumAt


section JoinCotraceDX

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)] [CharZero K]
variable [HasLocalResidue K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable {F : Type*} [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [HasLocalResidue K F] [HasCanonicalDivisor (K := K) (F := F)]
variable [∀ w : Place K F, w.DCoordGenerates] [Nontrivial Ω[F⁄K]]
variable [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
variable [HasPrincipalDivisors K (RatFunc K)]

end JoinCotraceDX


end AlgebraicCurve


section AxiomAudit

end AxiomAudit


end


end


section
section

set_option linter.unusedSectionVars false

open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.WithZero
open _root_.Module
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.Module
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.IsLocalRing
open _root_.Module.IsLocalRing
open _root_.TensorProduct
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.TensorProduct

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Place.ord Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential diagonalHom diagonalHom_apply diagonal_mem_adeleSpace HasCanonicalDivisor HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTerm kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_support_finite_of_adeleSpace weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK HasCanonicalLocalResidueKStar.dataKStar Place.mem_fiber Place.valuationSubringAlgebra Place.finite_setOf_restrict_eq kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kaehlerCotrace kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt KwHgfV352CompletionTraceSum FiberKaehlerCotraceResidueIdentityK CotraceResidueIdentityOnFiberLocalizedK Place.finiteResidue_of_deg_pos residueTraceCompletionCommute residueTheoremK_ratFunc_of_isAlgClosed)

open _root_.AlgebraicCurve

open scoped Polynomial P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.Polynomial
open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField

section SepIffInjective

variable (K : Type*) [Field K]
variable (F : Type*) [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]

theorem isSeparatingTranscendental_iff_kaehlerCotrace_injective
    [HasCanonicalLocalResidueKStar K (RatFunc K)]
    (v : Place K (RatFunc K)) [v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]] :
    IsSeparatingTranscendental K F ↔ Function.Injective (kaehlerCotrace K (RatFunc K) F) := by
  constructor
  · exact fun hsep => kaehlerCotrace_injective_of_D_algebraMap_ne_zero v hsep
  · intro hinj
    rw [isSeparatingTranscendental_iff_kaehlerCotrace_dX_ne_zero]
    exact fun h0 => dX_ne_zero K (hinj (h0.trans (_root_.map_zero _).symm))

end SepIffInjective


section MapBaseChangeSurj

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable {E : Type*} [Field E] [Algebra K E] [HasCanonicalLocalResidueKStar K E] [Algebra E F] [IsScalarTower K E F]

theorem surjective_mapBaseChange_of_formallyUnramified [Algebra.FormallyUnramified E F] :
    Function.Surjective (KaehlerDifferential.mapBaseChange K E F) := by
  rw [← LinearMap.range_eq_top, KaehlerDifferential.range_mapBaseChange]
  exact LinearMap.ker_eq_top.mpr (Subsingleton.elim _ _)

end MapBaseChangeSurj


section CotraceNeZero

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable {E : Type*} [Field E] [Algebra K E] [HasCanonicalLocalResidueKStar K E] [Algebra E F] [IsScalarTower K E F]

theorem exists_kaehlerCotrace_ne_zero_of_formallyUnramified
    [Algebra.FormallyUnramified E F] [Nontrivial Ω[F⁄K]] :
    ∃ ωE : Ω[E⁄K], kaehlerCotrace K E F ωE ≠ 0 := by
  by_contra h
  simp only [not_exists, not_not] at h

  have hmap0 : ∀ t, KaehlerDifferential.mapBaseChange K E F t = 0 := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact _root_.map_zero _
    | tmul f ωE =>
        rw [KaehlerDifferential.mapBaseChange_tmul]
        show f • kaehlerCotrace K E F ωE = 0
        rw [h ωE, smul_zero]
    | add a b ha hb => rw [map_add, ha, hb, add_zero]

  obtain ⟨ωF, hωF⟩ := exists_ne (0 : Ω[F⁄K])
  obtain ⟨t, ht⟩ := surjective_mapBaseChange_of_formallyUnramified (K := K) (E := E) (F := F) ωF
  exact hωF (ht ▸ hmap0 t)

end CotraceNeZero


section CotraceInjective

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable {E : Type*} [Field E] [Algebra K E] [HasCanonicalLocalResidueKStar K E] [Algebra E F] [IsScalarTower K E F]

theorem kaehlerCotrace_injective_of_formallyUnramified
    (v : Place K E) [v.DCoordGenerates] [Nontrivial Ω[E⁄K]]
    [Algebra.FormallyUnramified E F] [Nontrivial Ω[F⁄K]] :
    Function.Injective (kaehlerCotrace K E F) := by
  obtain ⟨ωE₀, hωE₀⟩ :=
    exists_kaehlerCotrace_ne_zero_of_formallyUnramified (K := K) (E := E) (F := F)
  exact kaehlerCotrace_injective_of_exists_ne_zero v hωE₀

end CotraceInjective


section SepDischarge

variable (K : Type*) [Field K]
variable (F : Type*) [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]

theorem isSeparatingTranscendental_of_formallyUnramified
    [HasCanonicalLocalResidueKStar K (RatFunc K)]
    (v : Place K (RatFunc K)) [v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
    [Algebra.FormallyUnramified (RatFunc K) F] [Nontrivial Ω[F⁄K]] :
    IsSeparatingTranscendental K F :=
  (isSeparatingTranscendental_iff_kaehlerCotrace_injective K F v).mpr
    (kaehlerCotrace_injective_of_formallyUnramified v)

theorem isSeparatingTranscendental_of_isSeparable
    [HasCanonicalLocalResidueKStar K (RatFunc K)]
    (v : Place K (RatFunc K)) [v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
    [Algebra.IsSeparable (RatFunc K) F] [Nontrivial Ω[F⁄K]] :
    IsSeparatingTranscendental K F :=
  haveI := Algebra.FormallyUnramified.of_isSeparable (RatFunc K) F
  isSeparatingTranscendental_of_formallyUnramified K F v

end SepDischarge


section JoinIsSeparable

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)] [CharZero K]
variable [HasLocalResidue K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable {F : Type*} [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [HasLocalResidue K F] [HasCanonicalDivisor (K := K) (F := F)]
variable [∀ w : Place K F, w.DCoordGenerates] [Nontrivial Ω[F⁄K]]
variable [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
variable [HasPrincipalDivisors K (RatFunc K)]
variable [Algebra.IsSeparable (RatFunc K) F]

end JoinIsSeparable


end AlgebraicCurve


section AxiomAudit

end AxiomAudit


end


end


section
section

set_option linter.unusedSectionVars false

open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.WithZero
open _root_.Module
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.Module
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.IsLocalRing
open _root_.Module.IsLocalRing
open _root_.TensorProduct
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.TensorProduct

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Place.ord Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential diagonalHom diagonalHom_apply diagonal_mem_adeleSpace HasCanonicalDivisor HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTerm kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_support_finite_of_adeleSpace weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK HasCanonicalLocalResidueKStar.dataKStar Place.mem_fiber Place.valuationSubringAlgebra Place.finite_setOf_restrict_eq kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kaehlerCotrace kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt KwHgfV352CompletionTraceSum FiberKaehlerCotraceResidueIdentityK CotraceResidueIdentityOnFiberLocalizedK Place.finiteResidue_of_deg_pos residueTraceCompletionCommute residueTheoremK_ratFunc_of_isAlgClosed)

open _root_.AlgebraicCurve

open scoped Polynomial P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.Polynomial
open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField

section CotraceDXSeparable

variable (K : Type*) [Field K]
variable (F : Type*) [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]

theorem kaehlerCotrace_dX_ne_zero_of_isSeparable
    [HasCanonicalLocalResidueKStar K (RatFunc K)]
    (v : Place K (RatFunc K)) [v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
    [Algebra.IsSeparable (RatFunc K) F] [Nontrivial Ω[F⁄K]] :
    kaehlerCotrace K (RatFunc K) F (dX K) ≠ 0 :=
  kaehlerCotrace_dX_ne_zero_of_isSeparatingTranscendental K F
    (isSeparatingTranscendental_of_isSeparable K F v)

end CotraceDXSeparable


section JoinIsSeparableDX

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)] [CharZero K]
variable [HasLocalResidue K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable {F : Type*} [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [HasLocalResidue K F] [HasCanonicalDivisor (K := K) (F := F)]
variable [∀ w : Place K F, w.DCoordGenerates] [Nontrivial Ω[F⁄K]]
variable [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
variable [Algebra.IsIntegral (RatFunc K) F]
variable [HasPrincipalDivisors K (RatFunc K)]
variable [Algebra.IsSeparable (RatFunc K) F]

end JoinIsSeparableDX


section JoinFormallyUnramifiedDX

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)] [CharZero K]
variable [HasLocalResidue K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable {F : Type*} [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [HasLocalResidue K F] [HasCanonicalDivisor (K := K) (F := F)]
variable [∀ w : Place K F, w.DCoordGenerates] [Nontrivial Ω[F⁄K]]
variable [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
variable [Algebra.IsIntegral (RatFunc K) F]
variable [HasPrincipalDivisors K (RatFunc K)]
variable [Algebra.FormallyUnramified (RatFunc K) F]

end JoinFormallyUnramifiedDX


section JoinFiberIdentityIsSeparable

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)] [CharZero K]
variable [HasLocalResidue K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable {F : Type*} [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [HasLocalResidue K F] [HasCanonicalDivisor (K := K) (F := F)]
variable [∀ w : Place K F, w.DCoordGenerates] [Nontrivial Ω[F⁄K]]
variable [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
variable [Algebra.IsIntegral (RatFunc K) F]
variable [HasPrincipalDivisors K (RatFunc K)]
variable [Algebra.IsSeparable (RatFunc K) F]

end JoinFiberIdentityIsSeparable


end AlgebraicCurve


section AxiomAudit

end AxiomAudit


end


end


section
section

set_option linter.unusedSectionVars false

set_option synthInstance.maxHeartbeats 3200000
set_option maxHeartbeats 6400000

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

section CurrencyBridge

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable {E : Type*} [Field E] [Algebra K E] [HasCanonicalLocalResidueKStar K E] [Algebra E F] [IsScalarTower K E F]

theorem kaehlerPullback_eq_kaehlerCotrace (ωE : Ω[E⁄K]) :
    kaehlerPullback K F E ωE = kaehlerCotrace K E F ωE := rfl

end CurrencyBridge


section NamedRows

variable (K F : Type*) [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable (E : Type*) [Field E] [Algebra K E] [HasCanonicalLocalResidueKStar K E] [Algebra E F] [IsScalarTower K E F]
variable [HasLocalResidue K E] [HasLocalResidue K F]
variable [Algebra.IsIntegral E F]

def CotraceResidueIdentityOnFiberLocalized : Prop :=
  ∀ [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]
    {ωE : Ω[E⁄K]} (_ : ωE ≠ 0) (_ : kaehlerPullback K F E ωE ≠ 0)
    (v : Place K E) (p : F),
    (∀ w₁ ∈ v.fiber F, ∀ w₂ ∈ v.fiber F,
      p ∉ w₁.regularSubmodule (kaehlerPullback K F E ωE) →
      p ∉ w₂.regularSubmodule (kaehlerPullback K F E ωE) → w₁ = w₂) →
    ∑ w ∈ v.fiber F, kaehlerResidueTerm (kaehlerPullback K F E ωE) (diagonalHom K F p) w
      = kaehlerResidueTerm ωE (diagonalHom K E (Algebra.trace E F p)) v

def CotraceFiberLocalizedPolarApprox : Prop :=
  ∀ [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]
    {ωE : Ω[E⁄K]} (_ : ωE ≠ 0) (_ : kaehlerPullback K F E ωE ≠ 0)
    (v : Place K E) (w : Place K F) (_ : w ∈ v.fiber F) (n : ℕ) (f : F)
    (_ : f ∈ w.regularPoleSubmodule (kaehlerPullback K F E ωE) (n + 1)),
    ∃ p : F,
      f - p ∈ w.regularPoleSubmodule (kaehlerPullback K F E ωE) n ∧
      ∀ w' ∈ v.fiber F, w' ≠ w → p ∈ w'.regularSubmodule (kaehlerPullback K F E ωE)

end NamedRows


section Engine

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable {E : Type*} [Field E] [Algebra K E] [HasCanonicalLocalResidueKStar K E] [Algebra E F] [IsScalarTower K E F]
variable [HasLocalResidue K E] [HasLocalResidue K F]
variable [Algebra.IsIntegral E F]

end Engine


section DXBridge

open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField

variable (K F : Type*) [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
variable [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasLocalResidue K F]
variable [Algebra.IsIntegral (RatFunc K) F]
variable [∀ w : Place K F, w.DCoordGenerates] [Nontrivial Ω[F⁄K]]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

end DXBridge


end AlgebraicCurve


namespace ModularCurve

export _root_.ModularCurve (KwF4R1V391a.KwF4R1V391aResidueTraceCompletionCommute)

open _root_.ModularCurve

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve
open _root_.Polynomial
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.Polynomial

attribute [local instance 2000] RatFunc.instAlgebraOfPolynomial

section ProductionGapTwo

variable (N : ℕ) [NeZero N]

end ProductionGapTwo


section ProductionJoins

variable (N : ℕ) [NeZero N]

end ProductionJoins


section ProductionGates

end ProductionGates


end ModularCurve


section AxiomAudit

end AxiomAudit


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

open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField

section Uniqueness

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

end Uniqueness


section Profile

variable (K : Type*) [Field K]

theorem exists_smul_dX_eq (ω : Ω[(RatFunc K)⁄K]) : ∃ c : RatFunc K, c • dX K = ω := by
  have hmem : ω ∈ Submodule.span (RatFunc K) {dX K} :=
    span_dX_eq_top K ▸ Submodule.mem_top
  exact Submodule.mem_span_singleton.mp hmem

section ProfileValues

variable [CharZero K] [DecidableEq (RatFunc K)]

end ProfileValues


section Instance

variable [CharZero K]

end Instance


section ExactDivisor

variable [CharZero K] [DecidableEq (RatFunc K)]

end ExactDivisor


end Profile


section RatDiamond

end RatDiamond


end AlgebraicCurve


namespace ModularCurve

export _root_.ModularCurve (KwF4R1V391a.KwF4R1V391aResidueTraceCompletionCommute)

open _root_.ModularCurve

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve
open _root_.IntermediateField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.IntermediateField

end ModularCurve


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
open _root_.KaehlerDifferential
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.KaehlerDifferential
open _root_.Polynomial
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.Polynomial

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Place.ord Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential diagonalHom diagonalHom_apply diagonal_mem_adeleSpace HasCanonicalDivisor HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTerm kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_support_finite_of_adeleSpace weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK HasCanonicalLocalResidueKStar.dataKStar Place.mem_fiber Place.valuationSubringAlgebra Place.finite_setOf_restrict_eq kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kaehlerCotrace kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt KwHgfV352CompletionTraceSum FiberKaehlerCotraceResidueIdentityK CotraceResidueIdentityOnFiberLocalizedK Place.finiteResidue_of_deg_pos residueTraceCompletionCommute residueTheoremK_ratFunc_of_isAlgClosed)

open _root_.AlgebraicCurve

open scoped Polynomial P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.Polynomial

open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField

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

end P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed
