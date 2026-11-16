/-
Copyright 2026 Anthropic, PBC. Released under Apache License 2.0.
Source: https://github.com/anthropics/fermats-last-theorem
Revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.lean; source lines 1890-3722.
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
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.RRSplit.residueTheoremK_ratFunc_of_isAlgClosed_Part01

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 6400000
set_option maxHeartbeats 12800000

namespace P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed

section
section

noncomputable section

open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.WithZero
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsLocalRing
open scoped Polynomial P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq)

open _root_.AlgebraicCurve

namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_ne_zero adicValuation_coe_eq_one_iff adicValuation_coe_irreducible ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ord_smul ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring mk.injEq rec ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk adicValuation_valuationSubring mem_iff_adicValuation_le_one isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one isEquiv_adicValuation_ofHeightOneSpectrum ord_ofHeightOneSpectrum_ne_zero_iff dCoord DCoordGenerates dCoord_ne_zero differentialCoeff differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_dCoord differentialCoeff_zero differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg deg_restrict_mul_inertiaDeg ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq)

open _root_.AlgebraicCurve.Place

section DegPos

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem finiteResidue_of_deg_pos (h : 0 < v.deg) : v.FiniteResidue :=
  ⟨Module.finite_of_finrank_pos h⟩

end DegPos


end Place


namespace RationalFunctionField

export _root_.AlgebraicCurve.RationalFunctionField (heightOneSpectrumOfIrreducible heightOneSpectrumOfIrreducible_asIdeal exists_irreducible_span finitePlace finitePlace_def algebraMap_mem_ofHeightOneSpectrum residueFieldEquivOfHeightOneSpectrum deg_ofHeightOneSpectrum deg_finitePlace)

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

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_ne_zero adicValuation_coe_eq_one_iff adicValuation_coe_irreducible ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ord_smul ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring mk.injEq rec ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk adicValuation_valuationSubring mem_iff_adicValuation_le_one isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one isEquiv_adicValuation_ofHeightOneSpectrum ord_ofHeightOneSpectrum_ne_zero_iff dCoord DCoordGenerates dCoord_ne_zero differentialCoeff differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_dCoord differentialCoeff_zero differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg deg_restrict_mul_inertiaDeg ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq)

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

open scoped Polynomial P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)]
variable [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
variable [HasPrincipalDivisors K F]

section RatFuncIntegrality

open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField

variable (K)
variable [DecidableEq (RatFunc K)]

theorem algebraMap_polynomial_mem_of_ne_placeInfty'
    {v : Place K (RatFunc K)} (hv : v ≠ placeInfty K) (q : K[X]) :
    algebraMap K[X] (RatFunc K) q ∈ v.toValuationSubring := by
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
  · exact algebraMap_mem_ofHeightOneSpectrum K w q
  · exact absurd rfl hv

theorem pow_X_mem_of_ne_placeInfty
    {v : Place K (RatFunc K)} (hv : v ≠ placeInfty K) (n : ℕ) :
    (RatFunc.X : RatFunc K) ^ n ∈ v.toValuationSubring := by
  have h : algebraMap K[X] (RatFunc K) (Polynomial.X ^ n) ∈ v.toValuationSubring :=
    algebraMap_polynomial_mem_of_ne_placeInfty' K hv (Polynomial.X ^ n)
  rwa [map_pow, RatFunc.algebraMap_X] at h

theorem pow_X_mul_mem_of_ne_placeInfty
    {v : Place K (RatFunc K)} (hv : v ≠ placeInfty K) (n : ℕ)
    {g : RatFunc K} (hg : g ∈ v.toValuationSubring) :
    (RatFunc.X : RatFunc K) ^ n * g ∈ v.toValuationSubring :=
  mul_mem (pow_X_mem_of_ne_placeInfty K hv n) hg

end RatFuncIntegrality


section P1PolynomialSubrows

open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField

variable (K)
variable [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]

def P1DifferentialCoeffRegularFinite {ω₀ : Ω[(RatFunc K)⁄K]} (_hω₀ : ω₀ ≠ 0) : Prop :=
  ∀ v : Place K (RatFunc K), v ≠ placeInfty K →
    v.differentialCoeff ω₀ ∈ v.toValuationSubring

variable {K}

end P1PolynomialSubrows


section P1PrincipalPartSubrows

open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField

variable (K)
variable [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]

abbrev p1PrincipalPartAtom (p c : K[X]) (m : ℕ) : RatFunc K :=
  algebraMap K[X] (RatFunc K) c / (algebraMap K[X] (RatFunc K) p) ^ m

variable {K}

omit [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
  [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
  [HasPrincipalDivisors K (RatFunc K)] in

theorem finitePlace_ne_placeInfty {p : K[X]} (hp : Irreducible p) :
    finitePlace K hp ≠ placeInfty K :=
  fun h => placeInfty_ne_ofHeightOneSpectrum K _ h.symm

end P1PrincipalPartSubrows


section P1Composed

open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField

variable [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]

end P1Composed


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
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial
open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.WithZero
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsLocalRing

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq)

open _root_.AlgebraicCurve

section SubsingletonCriterion

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

end SubsingletonCriterion


namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_ne_zero adicValuation_coe_eq_one_iff adicValuation_coe_irreducible ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ord_smul ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring mk.injEq rec ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk adicValuation_valuationSubring mem_iff_adicValuation_le_one isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one isEquiv_adicValuation_ofHeightOneSpectrum ord_ofHeightOneSpectrum_ne_zero_iff dCoord DCoordGenerates dCoord_ne_zero differentialCoeff differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_dCoord differentialCoeff_zero differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg deg_restrict_mul_inertiaDeg ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq)

open _root_.AlgebraicCurve.Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem ord_algebraMap_base (a : K) : v.ord (algebraMap K F a) = 0 := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  have h1 : 0 ≤ v.ord (algebraMap K F a) := v.ord_nonneg_of_mem (v.algebraMap_mem' a)
  have h2 : 0 ≤ v.ord (algebraMap K F a)⁻¹ := by
    rw [← map_inv₀]
    exact v.ord_nonneg_of_mem (v.algebraMap_mem' a⁻¹)
  rw [v.ord_inv] at h2
  omega

end Place


namespace RationalFunctionField

export _root_.AlgebraicCurve.RationalFunctionField (heightOneSpectrumOfIrreducible heightOneSpectrumOfIrreducible_asIdeal exists_irreducible_span finitePlace finitePlace_def algebraMap_mem_ofHeightOneSpectrum residueFieldEquivOfHeightOneSpectrum deg_ofHeightOneSpectrum deg_finitePlace)

open _root_.AlgebraicCurve.RationalFunctionField

variable (K : Type*) [Field K]

theorem exists_ord_finitePlace_eq_nsmul {p : K[X]} (hp : Irreducible p) {q : K[X]}
    (hq : q ≠ 0) :
    ∃ m : ℕ, (finitePlace K hp).ord (algebraMap K[X] (RatFunc K) q)
      = m * (finitePlace K hp).ord (algebraMap K[X] (RatFunc K) p) := by
  obtain ⟨m, b, hb, rfl⟩ := WfDvdMonoid.max_power_factor hq hp
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  have hp0 : p ≠ 0 := hp.ne_zero
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hq (mul_zero _)
  have hordb : (finitePlace K hp).ord (algebraMap K[X] (RatFunc K) b) = 0 := by
    by_contra hcon
    exact hb ((ord_finitePlace_ne_zero_iff K hp hb0).mp hcon)
  refine ⟨m, ?_⟩
  rw [map_mul, map_pow,
    (finitePlace K hp).ord_mul (pow_ne_zero _ ((map_ne_zero_iff _ hinj).mpr hp0))
      ((map_ne_zero_iff _ hinj).mpr hb0),
    hordb, add_zero, ← zpow_natCast, (finitePlace K hp).ord_zpow]

theorem ord_finitePlace_dvd {p : K[X]} (hp : Irreducible p) {f : RatFunc K} (hf : f ≠ 0) :
    (finitePlace K hp).ord (algebraMap K[X] (RatFunc K) p) ∣ (finitePlace K hp).ord f := by
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  obtain ⟨a, ha⟩ := exists_ord_finitePlace_eq_nsmul K hp (RatFunc.num_ne_zero hf)
  obtain ⟨b, hb⟩ := exists_ord_finitePlace_eq_nsmul K hp f.denom_ne_zero
  have hnum' : algebraMap K[X] (RatFunc K) f.num ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr (RatFunc.num_ne_zero hf)
  have hden' : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr f.denom_ne_zero
  rw [show f = algebraMap K[X] (RatFunc K) f.num * (algebraMap K[X] (RatFunc K) f.denom)⁻¹ by
      rw [← div_eq_mul_inv, f.num_div_denom],
    (finitePlace K hp).ord_mul hnum' (inv_ne_zero hden'), (finitePlace K hp).ord_inv, ha, hb]
  exact ⟨(a : ℤ) - b, by ring⟩

theorem ord_finitePlace_self {p : K[X]} (hp : Irreducible p) :
    (finitePlace K hp).ord (algebraMap K[X] (RatFunc K) p) = 1 := by

  have hnonneg : 0 ≤ (finitePlace K hp).ord (algebraMap K[X] (RatFunc K) p) :=
    (finitePlace K hp).ord_nonneg_of_mem (algebraMap_mem_ofHeightOneSpectrum K _ p)

  obtain ⟨π, hπ⟩ :=
    IsDiscreteValuationRing.exists_irreducible (finitePlace K hp).toValuationSubring
  have hπ0 : (π : RatFunc K) ≠ 0 := by
    simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  have hdvd : (finitePlace K hp).ord (algebraMap K[X] (RatFunc K) p) ∣ 1 :=
    (finitePlace K hp).ord_coe_irreducible hπ ▸ ord_finitePlace_dvd K hp hπ0
  rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd) with h | h
  · exact h
  · omega

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

theorem ord_placeInfty_algebraMap' {q : K[X]} (hq : q ≠ 0) :
    (placeInfty K).ord (algebraMap K[X] (RatFunc K) q) = -(q.natDegree : ℤ) := by
  have hq' : algebraMap K[X] (RatFunc K) q ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hq
  rw [ord_placeInfty_eq_intDegree_mul K hq', ord_placeInfty_X, RatFunc.intDegree_polynomial]
  ring

end PlaceInfty


section Principal

variable {K}

end Principal


end RationalFunctionField


namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_ne_zero adicValuation_coe_eq_one_iff adicValuation_coe_irreducible ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ord_smul ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring mk.injEq rec ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk adicValuation_valuationSubring mem_iff_adicValuation_le_one isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one isEquiv_adicValuation_ofHeightOneSpectrum ord_ofHeightOneSpectrum_ne_zero_iff dCoord DCoordGenerates dCoord_ne_zero differentialCoeff differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_dCoord differentialCoeff_zero differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg deg_restrict_mul_inertiaDeg ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq)

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

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve
open _root_.IntermediateField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IntermediateField

end ModularCurve


end

end


end


section
section

noncomputable section

open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsDedekindDomain
open _root_.Polynomial
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq)

open _root_.AlgebraicCurve

namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_ne_zero adicValuation_coe_eq_one_iff adicValuation_coe_irreducible ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ord_smul ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring mk.injEq rec ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk adicValuation_valuationSubring mem_iff_adicValuation_le_one isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one isEquiv_adicValuation_ofHeightOneSpectrum ord_ofHeightOneSpectrum_ne_zero_iff dCoord DCoordGenerates dCoord_ne_zero differentialCoeff differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_dCoord differentialCoeff_zero differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg deg_restrict_mul_inertiaDeg ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq)

open _root_.AlgebraicCurve.Place

section IntegrallyClosed

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)

end IntegrallyClosed


section SupportTransfer

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F'] [Algebra F F']
  [FiniteDimensional F F']

variable (w : Place K F')

omit [FiniteDimensional F F'] in

theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.aeval_mem {Q : Polynomial F} {x : F'}
    (hcoeff : ∀ i, algebraMap F F' (Q.coeff i) ∈ w.toValuationSubring)
    (hx : x ∈ w.toValuationSubring) :
    Polynomial.aeval x Q ∈ w.toValuationSubring := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range]
  exact sum_mem fun i _ => mul_mem (hcoeff i) (pow_mem hx i)




theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.exists_coeff_ord_ne_zero {f : F'} (hf : f ≠ 0) (hford : w.ord f ≠ 0) :
    ∃ i < (minpoly F f).natDegree, (minpoly F f).coeff i ≠ 0 ∧
      w.ord (algebraMap F F' ((minpoly F f).coeff i)) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  set P := minpoly F f with hPdef
  have hint : _root_.IsIntegral F f := Algebra.IsIntegral.isIntegral f
  have hmonic : P.Monic := minpoly.monic hint
  have hdeg : 0 < P.natDegree := minpoly.natDegree_pos hint
  have hc0 : P.coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint hf

  have hcoeff : ∀ i, algebraMap F F' (P.coeff i) ∈ w.toValuationSubring := by
    intro i
    rcases lt_trichotomy i P.natDegree with hi | hi | hi
    · rcases eq_or_ne (P.coeff i) 0 with h0 | h0
      · simp [h0]
      · exact w.mem_of_ord_nonneg (by simpa using h0) (by have := hcon i hi h0; omega)
    · subst hi
      simp [hmonic.coeff_natDegree]
    · simp [Polynomial.coeff_eq_zero_of_natDegree_lt hi]

  have hfmem : f ∈ w.toValuationSubring := by
    refine w.mem_of_eval_monic_eq_zero (P := P.map (algebraMap F F')) (hmonic.map _)
      (fun i => by simpa using hcoeff i) ?_
    rw [Polynomial.eval_map, ← Polynomial.aeval_def, hPdef, minpoly.aeval]

  have hfpos : 0 < w.ord f := lt_of_le_of_ne (w.ord_nonneg_of_mem hfmem) (Ne.symm hford)

  have hkey : algebraMap F F' (P.coeff 0) = -(f * Polynomial.aeval f P.divX) := by
    have hsplit : Polynomial.aeval f (Polynomial.X * P.divX + Polynomial.C (P.coeff 0))
        = (0 : F') := by rw [P.X_mul_divX_add]; exact minpoly.aeval F f
    rw [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at hsplit
    linear_combination hsplit
  have hcof_mem : Polynomial.aeval f P.divX ∈ w.toValuationSubring :=
    w.aeval_mem (fun i => by rw [Polynomial.coeff_divX]; exact hcoeff (i + 1)) hfmem
  have hcof_ne : Polynomial.aeval f P.divX ≠ 0 := by
    intro h
    rw [h, mul_zero, _root_.neg_zero] at hkey
    exact hc0 (by simpa using hkey)

  have hpos0 : 0 < w.ord (algebraMap F F' (P.coeff 0)) := by
    rw [hkey, w.ord_neg, w.ord_mul hf hcof_ne]
    have := w.ord_nonneg_of_mem hcof_mem
    omega
  have := hcon 0 hdeg hc0
  omega




end SupportTransfer


section Chart

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
variable (w : Place K F)

def chartHom (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) :
    R →+* w.toValuationSubring :=
  (algebraMap R F).codRestrict w.toValuationSubring.toSubring hw

omit [IsDedekindDomain R] [IsFractionRing R F] in

theorem inv_algebraMap_mem (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring)
    {s : R} (hs : IsUnit (chartHom w hw s)) :
    (algebraMap R F s)⁻¹ ∈ w.toValuationSubring := by
  obtain ⟨u, hu⟩ := hs
  have hcoe : ((u : w.toValuationSubring) : F) = algebraMap R F s := by rw [hu]; rfl
  have h1 : (((u⁻¹ : w.toValuationSubringˣ) : w.toValuationSubring) : F)
      * algebraMap R F s = 1 := by
    have hmul := congrArg (fun a : w.toValuationSubring => (a : F)) u.inv_mul
    push_cast at hmul
    rwa [hcoe] at hmul
  rw [← eq_inv_of_mul_eq_one_left h1]
  exact SetLike.coe_mem _

end Chart


section FiberFiniteness

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
  [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F']

end FiberFiniteness


end Place


section Assembly

variable {K : Type*} [Field K] {F' : Type*} [Field F'] [Algebra K F']
  [Algebra (RatFunc K) F'] [IsScalarTower K (RatFunc K) F']
  [FiniteDimensional (RatFunc K) F'] [Algebra.IsSeparable (RatFunc K) F']

theorem finite_setOf_ord_ne_zero_of_finiteDimensional {f : F'} (hf : f ≠ 0) :
    {w : Place K F' | w.ord f ≠ 0}.Finite := by
  classical
  set P := minpoly (RatFunc K) f with hPdef

  refine Set.Finite.subset (Set.Finite.biUnion (Set.finite_Iio P.natDegree) (fun i _ =>
    Set.Finite.biUnion (s := {v : Place K (RatFunc K) | v.ord (P.coeff i) ≠ 0})
      ?_ (fun v _ => Place.finite_setOf_restrict_eq v))) ?_
  ·
    rcases eq_or_ne (P.coeff i) 0 with h0 | h0
    · simp [h0]
    · exact RationalFunctionField.finite_setOf_ord_ne_zero h0
  ·
    intro w hw
    obtain ⟨i, hi, hci, hord⟩ := w.exists_coeff_ord_ne_zero (F := RatFunc K) hf hw
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    refine ⟨i, hi, w.restrict (RatFunc K), ?_, rfl⟩
    intro h0
    apply hord
    rw [w.ord_restrict, h0, mul_zero]

end Assembly


end AlgebraicCurve


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

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq)

open _root_.AlgebraicCurve

namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_ne_zero adicValuation_coe_eq_one_iff adicValuation_coe_irreducible ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ord_smul ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring mk.injEq rec ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk adicValuation_valuationSubring mem_iff_adicValuation_le_one isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one isEquiv_adicValuation_ofHeightOneSpectrum ord_ofHeightOneSpectrum_ne_zero_iff dCoord DCoordGenerates dCoord_ne_zero differentialCoeff differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_dCoord differentialCoeff_zero differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg deg_restrict_mul_inertiaDeg ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq)

open _root_.AlgebraicCurve.Place

section CotangentEngine

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

noncomputable def _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.uniformizerSubring'' : v.toValuationSubring :=
  (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose




@[reducible] private noncomputable def _root_.AlgebraicCurve.Place.polynomialAlgebra : Algebra K[X] v.toValuationSubring :=
  (Polynomial.aeval (R := K) v.uniformizerSubring'').toRingHom.toAlgebra


export _root_.AlgebraicCurve.Place (polynomialAlgebra)

theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.polynomialAlgebra_algebraMap_X :
    letI := v.polynomialAlgebra
    algebraMap K[X] v.toValuationSubring X = v.uniformizerSubring'' :=
  aeval_X _




@[reducible] private def _root_.AlgebraicCurve.Place.polynomialIsScalarTower :
    letI := v.polynomialAlgebra
    IsScalarTower K K[X] v.toValuationSubring := by
  letI := v.polynomialAlgebra
  refine IsScalarTower.of_algebraMap_eq fun a => ?_
  show _ = aeval v.uniformizerSubring'' (algebraMap K K[X] a)
  simp [Polynomial.algebraMap_eq, aeval_C]


export _root_.AlgebraicCurve.Place (polynomialIsScalarTower)

theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.range_mapBaseChange_le_span_D_uniformizer :
    letI := v.polynomialAlgebra
    letI := v.polynomialIsScalarTower
    LinearMap.range (KaehlerDifferential.mapBaseChange K K[X] v.toValuationSubring)
      ≤ Submodule.span v.toValuationSubring
          {KaehlerDifferential.D K v.toValuationSubring v.uniformizerSubring''} := by
  letI := v.polynomialAlgebra
  letI := v.polynomialIsScalarTower
  rintro _ ⟨t, rfl⟩
  induction t with
  | zero => simp
  | add x y hx hy => rw [map_add]; exact add_mem hx hy
  | tmul b ω =>
    rw [KaehlerDifferential.mapBaseChange_tmul,
      show ω = (KaehlerDifferential.polynomialEquiv K ω) • (KaehlerDifferential.D K K[X] X) from
        ((KaehlerDifferential.polynomialEquiv K).symm_apply_apply ω).symm.trans
          (KaehlerDifferential.polynomialEquiv_symm K _),
      LinearMap.map_smul, KaehlerDifferential.map_D,
      show algebraMap K[X] v.toValuationSubring X = v.uniformizerSubring'' from aeval_X _,
      ← algebraMap_smul (A := v.toValuationSubring)]
    exact Submodule.smul_mem _ b
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))




theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.range_mapBaseChange_eq_top_of_subsingleton
    (hsub :
      letI := v.polynomialAlgebra
      Subsingleton Ω[v.toValuationSubring⁄K[X]]) :
    letI := v.polynomialAlgebra
    letI := v.polynomialIsScalarTower
    LinearMap.range (KaehlerDifferential.mapBaseChange K K[X] v.toValuationSubring) = ⊤ := by
  letI := v.polynomialAlgebra
  letI := v.polynomialIsScalarTower
  rw [KaehlerDifferential.range_mapBaseChange]
  exact LinearMap.ker_eq_top.mpr (Subsingleton.elim _ _)




theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.span_D_uniformizer_eq_top_of_subsingleton
    (hsub :
      letI := v.polynomialAlgebra
      Subsingleton Ω[v.toValuationSubring⁄K[X]]) :
    Submodule.span v.toValuationSubring
      {KaehlerDifferential.D K v.toValuationSubring v.uniformizerSubring''} = ⊤ := by
  refine top_le_iff.mp ?_
  rw [← v.range_mapBaseChange_eq_top_of_subsingleton hsub]
  exact v.range_mapBaseChange_le_span_D_uniformizer




end CotangentEngine


end Place


variable (K F : Type*) [Field K] [Field F] [Algebra K F]

def ValSubringPolynomialFormallyUnramified : Prop :=
  ∀ v : Place K F,
    letI := v.polynomialAlgebra
    Subsingleton Ω[v.toValuationSubring⁄K[X]]

variable {K F}

theorem valSubringKaehlerSpanTop_of_polynomialFormallyUnramified
    (hfu : ValSubringPolynomialFormallyUnramified K F) :
    ValSubringKaehlerSpanTop K F :=
  fun v => v.span_D_uniformizer_eq_top_of_subsingleton (hfu v)

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

open _root_.Polynomial
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial
open _root_.UniqueFactorizationMonoid
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.UniqueFactorizationMonoid

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq)

open _root_.AlgebraicCurve

open scoped Polynomial P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial

variable {K : Type*} [Field K]

theorem exists_monic_irreducible_factorization {d : K[X]} (hd : d.Monic) :
    ∃ (s : Finset K[X]) (n : K[X] → ℕ),
      (∀ p ∈ s, p.Monic) ∧ (∀ p ∈ s, Irreducible p) ∧
      (Set.Pairwise (s : Set K[X]) fun i j => IsCoprime i j) ∧
      d = ∏ p ∈ s, p ^ n p := by
  classical
  refine ⟨(normalizedFactors d).toFinset,
    fun p => (normalizedFactors d).count p, ?_, ?_, ?_, ?_⟩
  ·
    intro p hp
    exact ((Polynomial.mem_normalizedFactors_iff hd.ne_zero).mp
      (Multiset.mem_toFinset.mp hp)).2.1
  ·
    intro p hp
    exact irreducible_of_normalized_factor p (Multiset.mem_toFinset.mp hp)
  ·

    intro p hp q hq hne
    have hp' := Multiset.mem_toFinset.mp hp
    have hq' := Multiset.mem_toFinset.mp hq
    rw [(irreducible_of_normalized_factor p hp').coprime_iff_not_dvd]
    exact fun hdvd => hne (normalizedFactors_eq_of_dvd d p hp' q hq' hdvd)
  ·

    calc d = (normalizedFactors d).prod := by
            rw [prod_normalizedFactors_eq hd.ne_zero, hd.normalize_eq_self]
      _ = ∏ p ∈ (normalizedFactors d).toFinset, p ^ (normalizedFactors d).count p :=
            Finset.prod_multiset_count _

theorem algebraMap_mem_span_P1PartialFractionGenerators (q : K[X]) :
    algebraMap K[X] (RatFunc K) q ∈ Submodule.span K (P1PartialFractionGenerators K) :=
  Submodule.span_mono Set.subset_union_left
    (gate_algebraMap_polynomial_mem_span_P1PolynomialGenerators q)

theorem div_pow_mem_span_P1PartialFractionGenerators
    {p c : K[X]} (hpmon : p.Monic) (hpirr : Irreducible p)
    (hdeg : c.degree < p.degree) {m : ℕ} (hm : 1 ≤ m) :
    algebraMap K[X] (RatFunc K) c / (algebraMap K[X] (RatFunc K) p) ^ m
      ∈ Submodule.span K (P1PartialFractionGenerators K) := by
  exact Submodule.subset_span (Or.inr ⟨p, c, m, hpmon, hpirr, hdeg, hm, rfl⟩)

theorem ratFunc_mem_span_P1PartialFractionGenerators (f : RatFunc K) :
    f ∈ Submodule.span K (P1PartialFractionGenerators K) := by
  classical

  have hdenmon : f.denom.Monic := RatFunc.monic_denom f

  obtain ⟨s, n, hmon, hirr, hcop, hdfac⟩ :=
    exists_monic_irreducible_factorization hdenmon

  have hginv : ∀ p ∈ s,
      (algebraMap K[X] (RatFunc K) p)⁻¹ * algebraMap K[X] (RatFunc K) p = 1 :=
    fun p hp => inv_mul_cancel₀ (RatFunc.algebraMap_ne_zero (hmon p hp).ne_zero)

  obtain ⟨q, r, hr, hpfrac⟩ :=
    Polynomial.mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse
      (K := RatFunc K) f.num hmon hcop n hginv

  have hLHS : algebraMap K[X] (RatFunc K) f.num *
      ∏ p ∈ s, ((algebraMap K[X] (RatFunc K) p)⁻¹) ^ n p = f := by
    have hprod : ∏ p ∈ s, ((algebraMap K[X] (RatFunc K) p)⁻¹) ^ n p
        = (algebraMap K[X] (RatFunc K) f.denom)⁻¹ := by
      rw [hdfac, map_prod]
      rw [← Finset.prod_inv_distrib]
      exact Finset.prod_congr rfl fun p _ => by rw [map_pow, inv_pow]
    rw [hprod, ← div_eq_mul_inv, RatFunc.num_div_denom]
  rw [← hLHS, hpfrac]

  refine Submodule.add_mem _ (algebraMap_mem_span_P1PartialFractionGenerators q) ?_
  refine Submodule.sum_mem _ fun p hp => ?_
  refine Submodule.sum_mem _ fun j _ => ?_

  rw [inv_pow, ← div_eq_mul_inv]
  exact div_pow_mem_span_P1PartialFractionGenerators (hmon p hp) (hirr p hp)
    (hr p hp j) j.succ_pos

theorem p1PartialFractionSpan_eq_top :
    Submodule.span K (P1PartialFractionGenerators K) = ⊤ :=
  Submodule.eq_top_iff'.mpr ratFunc_mem_span_P1PartialFractionGenerators

end AlgebraicCurve


section AxiomAudit

end AxiomAudit


end


end


end


section
section

set_option maxHeartbeats 3200000

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve.Lg37
open _root_.Polynomial
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial
open _root_.IntermediateField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IntermediateField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Mp72a102T1
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Mp72a102T2

namespace ModularCurve
namespace KwNo6Section

section GenericIso

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

noncomputable def residueFieldAdjoinRootEquiv {ᾱ : v.ResidueField} (hint : _root_.IsIntegral K ᾱ)
    (htop : K⟮ᾱ⟯ = ⊤) :
    AdjoinRoot (minpoly K ᾱ) ≃ₐ[K] v.ResidueField :=
  (adjoinRootEquivAdjoin K hint).trans
    ((IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv)

theorem residueFieldAdjoinRootEquiv_root {ᾱ : v.ResidueField} (hint : _root_.IsIntegral K ᾱ)
    (htop : K⟮ᾱ⟯ = ⊤) :
    residueFieldAdjoinRootEquiv v hint htop (AdjoinRoot.root (minpoly K ᾱ)) = ᾱ := by
  have hgen := adjoinRootEquivAdjoin_apply_root K hint

  simp only [residueFieldAdjoinRootEquiv, AlgEquiv.trans_apply, hgen,
    IntermediateField.topEquiv_apply]
  exact AdjoinSimple.coe_gen K ᾱ

end GenericIso


section GenericSection

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

noncomputable def sectionOfPrimitiveRoot {ᾱ : v.ResidueField} (hint : _root_.IsIntegral K ᾱ)
    (htop : K⟮ᾱ⟯ = ⊤) (αhat : lg37_completion v)
    (hroot : (aeval αhat) (minpoly K ᾱ) = 0)
    (hres : lg37_residueHat v αhat = ᾱ) :
    Lg37CompletionSection v where
  lift :=
    (AdjoinRoot.liftAlgHom (minpoly K ᾱ) (Algebra.ofId K (lg37_completion v)) αhat
      (by rw [aeval_def] at hroot; exact hroot)).comp
      (residueFieldAdjoinRootEquiv v hint htop).symm.toAlgHom
  residueHat_lift a := by

    have hres' : lg37_residueHat v αhat
        = residueFieldAdjoinRootEquiv v hint htop (AdjoinRoot.root (minpoly K ᾱ)) :=
      hres.trans (residueFieldAdjoinRootEquiv_root v hint htop).symm
    have hkey : (mp72a102_t2_residueHatAlgHom v).comp
          (AdjoinRoot.liftAlgHom (minpoly K ᾱ) (Algebra.ofId K (lg37_completion v)) αhat
            (by rw [aeval_def] at hroot; exact hroot))
        = (residueFieldAdjoinRootEquiv v hint htop).toAlgHom := by
      refine AdjoinRoot.algHom_ext ?_
      rw [AlgHom.comp_apply, AdjoinRoot.liftAlgHom_root]
      exact hres'
    have h1 := DFunLike.congr_fun hkey ((residueFieldAdjoinRootEquiv v hint htop).symm a)
    rw [AlgHom.comp_apply] at h1
    have h2 : (residueFieldAdjoinRootEquiv v hint htop).toAlgHom
        ((residueFieldAdjoinRootEquiv v hint htop).symm a) = a :=
      (residueFieldAdjoinRootEquiv v hint htop).apply_symm_apply a
    exact h1.trans h2

end GenericSection


section Modular

end Modular


end ModularCurve.KwNo6Section



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

def _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.poleSubmodule (n : ℕ) : Submodule K F where
  carrier := {f | v.uniformizer ^ n * f ∈ v.toValuationSubring}
  add_mem' {f g} hf hg := by
    simpa only [Set.mem_setOf_eq, mul_add] using add_mem hf hg
  zero_mem' := by simpa only [Set.mem_setOf_eq, mul_zero] using zero_mem _
  smul_mem' c f hf := by
    show v.uniformizer ^ n * (c • f) ∈ v.toValuationSubring
    rw [Algebra.smul_def, mul_left_comm]
    exact mul_mem (v.algebraMap_mem' c) hf




@[scoped simp]
theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.mem_poleSubmodule {n : ℕ} {f : F} :
    f ∈ v.poleSubmodule n ↔ v.uniformizer ^ n * f ∈ v.toValuationSubring := Iff.rfl




theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.uniformizer_pow_ne_zero (n : ℕ) : (v.uniformizer ^ n : F) ≠ 0 :=
  pow_ne_zero n v.uniformizer_ne_zero




theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.ord_uniformizer_pow (n : ℕ) : v.ord (v.uniformizer ^ n) = (n : ℤ) := by
  rw [show (v.uniformizer ^ n : F) = v.uniformizer ^ (n : ℤ) from (zpow_natCast _ n).symm,
    v.ord_zpow, v.ord_uniformizer, mul_one]




theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.coe_poleSubmodule_zero :
    (v.poleSubmodule 0 : Set F) = (v.toValuationSubring : Set F) := by
  ext f; simp [mem_poleSubmodule]




@[scoped simp]
theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.poleSubmodule_one : v.poleSubmodule 1 = v.simplePoleSubmodule := by
  ext f; simp [mem_poleSubmodule, mem_simplePoleSubmodule]




theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.mem_poleSubmodule_iff_ord {n : ℕ} {f : F} (hf : f ≠ 0) :
    f ∈ v.poleSubmodule n ↔ -(n : ℤ) ≤ v.ord f := by
  rw [mem_poleSubmodule, v.mem_iff_ord_nonneg (mul_ne_zero (v.uniformizer_pow_ne_zero n) hf),
    v.ord_mul (v.uniformizer_pow_ne_zero n) hf, v.ord_uniformizer_pow]
  omega




theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.poleSubmodule_mono : Monotone v.poleSubmodule := by
  intro m n hmn f hf
  rcases eq_or_ne f 0 with rfl | hf0
  · exact zero_mem _
  · rw [v.mem_poleSubmodule_iff_ord hf0] at hf ⊢
    have : -(n : ℤ) ≤ -(m : ℤ) := by exact_mod_cast neg_le_neg (Nat.cast_le.mpr hmn)
    omega




def _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.poleMulUniformizerPow (n : ℕ) : v.poleSubmodule n →ₗ[K] v.toValuationSubring where
  toFun f := ⟨v.uniformizer ^ n * f.1, f.2⟩
  map_add' f g := Subtype.ext (mul_add _ _ _)
  map_smul' c f := Subtype.ext <| by
    show v.uniformizer ^ n * ((c • f : v.poleSubmodule n) : F)
        = ((c • ⟨v.uniformizer ^ n * f.1, f.2⟩ : v.toValuationSubring) : F)
    simp only [Algebra.smul_def, MulMemClass.coe_mul, v.coe_algebraMap, Submodule.coe_smul,
      mul_left_comm]




def _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.laurentTailCoeff (n : ℕ) : v.poleSubmodule n →ₗ[K] v.ResidueField :=
  (Ideal.Quotient.mkₐ K (IsLocalRing.maximalIdeal v.toValuationSubring)).toLinearMap
    ∘ₗ v.poleMulUniformizerPow n




theorem laurentTailCoeff_apply {n : ℕ} (f : v.poleSubmodule n) :
    v.laurentTailCoeff n f = IsLocalRing.residue _ ⟨v.uniformizer ^ n * f.1, f.2⟩ := rfl

theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.laurentTail_remainder_mem_poleSubmodule {n : ℕ} {f : F}
    (hf : f ∈ v.poleSubmodule (n + 1)) {c : v.toValuationSubring}
    (hc : IsLocalRing.residue _ c = v.laurentTailCoeff (n + 1) ⟨f, hf⟩) :
    f - (c : F) * (v.uniformizer ^ (n + 1))⁻¹ ∈ v.poleSubmodule n := by

  set a : v.toValuationSubring := ⟨v.uniformizer ^ (n + 1) * f, hf⟩ with ha_def
  have hmem : a - c ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hc, laurentTailCoeff_apply, sub_self]
  rw [v.irreducible_uniformizerSubring.maximalIdeal_eq, Ideal.mem_span_singleton] at hmem
  obtain ⟨d, hd⟩ := hmem

  rw [mem_poleSubmodule]
  have hcoe : v.uniformizer ^ (n + 1) * f - (c : F) = v.uniformizer * (d : F) := by
    have h := congrArg (Subtype.val) hd
    push_cast [coe_uniformizerSubring] at h
    exact h
  have hkey : v.uniformizer ^ n * (f - (c : F) * (v.uniformizer ^ (n + 1))⁻¹) = (d : F) := by
    refine mul_left_cancel₀ v.uniformizer_ne_zero ?_
    calc v.uniformizer * (v.uniformizer ^ n * (f - (c : F) * (v.uniformizer ^ (n + 1))⁻¹))
        = v.uniformizer ^ (n + 1) * f
            - (c : F) * (v.uniformizer ^ (n + 1) * (v.uniformizer ^ (n + 1))⁻¹) := by ring
      _ = v.uniformizer ^ (n + 1) * f - (c : F) := by
          rw [mul_inv_cancel₀ (v.uniformizer_pow_ne_zero (n + 1)), mul_one]
      _ = v.uniformizer * (d : F) := hcoe
  rw [hkey]
  exact d.2




theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.localResidueData_res_eq_simplePoleResidueAux (R : v.LocalResidueData) {f : F}
    (hf : f ∈ v.simplePoleSubmodule) : R.res f = v.simplePoleResidueAux ⟨f, hf⟩ := by
  rw [R.res_simplePole f hf, simplePoleResidueAux_apply]




end Place


theorem gate_poleSubmodule_strictMono (v : Place K F) (n : ℕ) :
    (v.uniformizer ^ (n + 1))⁻¹ ∈ v.poleSubmodule (n + 1) ∧
      (v.uniformizer ^ (n + 1))⁻¹ ∉ v.poleSubmodule n := by
  refine ⟨?_, ?_⟩
  · rw [Place.mem_poleSubmodule, mul_inv_cancel₀ (v.uniformizer_pow_ne_zero (n + 1))]
    exact one_mem _
  · rw [v.mem_poleSubmodule_iff_ord (inv_ne_zero (v.uniformizer_pow_ne_zero (n + 1))),
      v.ord_inv, v.ord_uniformizer_pow]
    omega

theorem gate_localResidueData_uniformizer_inv (v : Place K F) (R : v.LocalResidueData) :
    R.res v.uniformizer⁻¹ = 1 := by
  rw [v.localResidueData_res_eq_simplePoleResidueAux R
      (gate_uniformizer_inv_mem_simplePoleSubmodule v).1,
    Place.simplePoleResidueAux_apply]
  have h1 :
      (⟨v.uniformizer * v.uniformizer⁻¹,
        (gate_uniformizer_inv_mem_simplePoleSubmodule v).1⟩ : v.toValuationSubring) = 1 :=
    Subtype.ext (mul_inv_cancel₀ v.uniformizer_ne_zero)
  rw [h1, map_one]

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
set_option maxRecDepth 8000

noncomputable section

open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsLocalRing
open _root_.Polynomial
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial

open scoped Polynomial P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial

namespace ModularCurve
namespace Mp72a102T3

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve.Lg37

section General

variable {R : Type*} [CommRing R] (I : Ideal R)

theorem mp72a102_t3_evalₐ_zero_depth (z : AdicCompletion I R) :
    AdicCompletion.evalₐ I 0 z = 0 := by
  haveI : Subsingleton (R ⧸ (I ^ 0)) :=
    Ideal.Quotient.subsingleton_iff.mpr (by rw [pow_zero, Ideal.one_eq_top])
  exact Subsingleton.elim _ _

theorem mp72a102_t3_evalₐ_algebraMap (n : ℕ) (r : R) :
    AdicCompletion.evalₐ I n (algebraMap R (AdicCompletion I R) r)
      = Ideal.Quotient.mk (I ^ n) r := by
  rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    AdicCompletion.evalₐ_of]

theorem mp72a102_t3_evalₐ_factor {m n : ℕ} (hmn : m ≤ n) (z : AdicCompletion I R) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn) (AdicCompletion.evalₐ I n z)
      = AdicCompletion.evalₐ I m z := by
  obtain ⟨c, rfl⟩ := AdicCompletion.mk_surjective I R z
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, Ideal.Quotient.factor_mk]
  exact AdicCompletion.Ideal.mk_eq_mk I hmn c

theorem mp72a102_t3_exists_rep_of_evalₐ_eq_zero {n : ℕ} {z : AdicCompletion I R}
    (h : AdicCompletion.evalₐ I n z = 0) :
    ∃ w ∈ I ^ n, AdicCompletion.evalₐ I (n + 1) z = Ideal.Quotient.mk (I ^ (n + 1)) w := by
  obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (n + 1) z)
  refine ⟨w, ?_, hw.symm⟩
  have hfac := mp72a102_t3_evalₐ_factor I (Nat.le_succ n) z
  rw [← hw, Ideal.Quotient.factor_mk, h] at hfac
  exact Ideal.Quotient.eq_zero_iff_mem.mp hfac

theorem mp72a102_t3_evalₐ_succ_mul_eq_zero {n : ℕ} {r : R} (hr : r ∈ I)
    {z : AdicCompletion I R} (h : AdicCompletion.evalₐ I n z = 0) :
    AdicCompletion.evalₐ I (n + 1) (algebraMap R (AdicCompletion I R) r * z) = 0 := by
  obtain ⟨w, hw, hwz⟩ := mp72a102_t3_exists_rep_of_evalₐ_eq_zero I h
  rw [map_mul, mp72a102_t3_evalₐ_algebraMap, hwz, ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem, pow_succ']
  exact Ideal.mul_mem_mul hr hw

theorem mp72a102_t3_evalₐ_one_eq_zero_of_evalOneₐ {z : AdicCompletion I R}
    (h : AdicCompletion.evalOneₐ I z = 0) : AdicCompletion.evalₐ I 1 z = 0 := by
  obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I 1 z)
  have hfac := AdicCompletion.factorₐ_evalₐ_one I z
  rw [← hw, Ideal.Quotient.factor_mk, h] at hfac
  rw [← hw, Ideal.Quotient.eq_zero_iff_mem, pow_one]
  exact Ideal.Quotient.eq_zero_iff_mem.mp hfac

end General


section Carrier

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mp72a102_t3_evalDepth_add (v : Place K F) (n : ℕ)
    (x y : lg37_completion v) :
    AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) n (x + y)
      = AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) n x
        + AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) n y :=
  map_add _ x y

theorem mp72a102_t3_evalDepth_mul (v : Place K F) (n : ℕ)
    (x y : lg37_completion v) :
    AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) n (x * y)
      = AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) n x
        * AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) n y :=
  map_mul _ x y

theorem mp72a102_t3_residueHat_congr_of_depth_one (v : Place K F)
    {x y : lg37_completion v}
    (h : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) 1 x
        = AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) 1 y) :
    lg37_residueHat v x = lg37_residueHat v y := by
  show AdicCompletion.evalOneₐ (maximalIdeal v.toValuationSubring) x
      = AdicCompletion.evalOneₐ (maximalIdeal v.toValuationSubring) y
  rw [← AdicCompletion.factorₐ_evalₐ_one, ← AdicCompletion.factorₐ_evalₐ_one, h]

theorem mp72a102_t3_evalDepth_one_eq_zero_of_residueHat (v : Place K F)
    {x : lg37_completion v} (hx : lg37_residueHat v x = 0) :
    AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) 1 x = 0 :=
  mp72a102_t3_evalₐ_one_eq_zero_of_evalOneₐ _ hx

theorem mp72a102_t3_eq_uniformizer_mul_of_mem_maximalIdeal (v : Place K F)
    {w : v.toValuationSubring} (hw : w ∈ maximalIdeal v.toValuationSubring) :
    ∃ u : v.toValuationSubring, w = v.uniformizerSubring * u := by
  rw [v.irreducible_uniformizerSubring.maximalIdeal_eq, Ideal.mem_span_singleton] at hw
  exact hw

theorem mp72a102_t3_exists_uniformizer_factor (v : Place K F)
    {x : lg37_completion v} (hx : lg37_residueHat v x = 0) (n : ℕ) :
    ∃ u : v.toValuationSubring,
      AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) n
        (x - algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring
          * algebraMap v.toValuationSubring (lg37_completion v) u) = 0 := by
  rcases n with _ | n
  · exact ⟨0, mp72a102_t3_evalₐ_zero_depth _ _⟩
  · obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective
      (AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (n + 1) x)
    have h1 : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) 1 x = 0 :=
      mp72a102_t3_evalDepth_one_eq_zero_of_residueHat v hx
    have hfac := mp72a102_t3_evalₐ_factor (maximalIdeal v.toValuationSubring)
      (Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero n)) x
    rw [← hw, Ideal.Quotient.factor_mk, h1] at hfac
    have hwm : w ∈ maximalIdeal v.toValuationSubring := by
      have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hfac
      rwa [pow_one] at hmem
    obtain ⟨u, hu⟩ := mp72a102_t3_eq_uniformizer_mul_of_mem_maximalIdeal v hwm
    refine ⟨u, ?_⟩
    rw [map_sub, map_mul, mp72a102_t3_evalₐ_algebraMap, mp72a102_t3_evalₐ_algebraMap,
      ← map_mul, ← hu, ← hw, sub_self]

theorem mp72a102_t3_sigma_taylor_expansion (v : Place K F)
    (S : Lg37CompletionSection v) (n : ℕ) (x : lg37_completion v) :
    ∃ a : ℕ → v.ResidueField,
      AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) n
        (x - ∑ i ∈ Finset.range n, S.lift (a i)
          * algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ i) = 0 := by
  induction n generalizing x with
  | zero => exact ⟨fun _ => 0, mp72a102_t3_evalₐ_zero_depth _ _⟩
  | succ n ih =>
    have hres : lg37_residueHat v (x - S.lift (lg37_residueHat v x)) = 0 := by
      rw [map_sub, S.residueHat_lift, sub_self]
    obtain ⟨u, hu⟩ := mp72a102_t3_exists_uniformizer_factor v hres (n + 1)
    obtain ⟨a, ha⟩ := ih (algebraMap v.toValuationSubring (lg37_completion v) u)
    have hshift := mp72a102_t3_evalₐ_succ_mul_eq_zero
      (maximalIdeal v.toValuationSubring) v.uniformizerSubring_mem_maximalIdeal ha
    refine ⟨fun i => Nat.rec (motive := fun _ => v.ResidueField)
      (lg37_residueHat v x) (fun j _ => a j) i, ?_⟩
    rw [Finset.sum_range_succ']
    show AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (n + 1)
        (x - ((∑ i ∈ Finset.range n, S.lift (a i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ (i + 1))
          + S.lift (lg37_residueHat v x)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ 0)) = 0
    have hsum : ∑ i ∈ Finset.range n, S.lift (a i)
          * algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ (i + 1)
        = algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring
          * ∑ i ∈ Finset.range n, S.lift (a i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsum, pow_zero, mul_one]
    have hdecomp : x - (algebraMap v.toValuationSubring (lg37_completion v)
            v.uniformizerSubring
          * ∑ i ∈ Finset.range n, S.lift (a i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i
          + S.lift (lg37_residueHat v x))
        = (x - S.lift (lg37_residueHat v x)
            - algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring
              * algebraMap v.toValuationSubring (lg37_completion v) u)
          + algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring
            * (algebraMap v.toValuationSubring (lg37_completion v) u
              - ∑ i ∈ Finset.range n, S.lift (a i)
                * algebraMap v.toValuationSubring (lg37_completion v)
                    v.uniformizerSubring ^ i) := by
      ring
    rw [hdecomp, map_add, hu, hshift, add_zero]

end Carrier


section RatProduction

open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.RationalFunctionField
open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Mp72a101T2

attribute [local instance 2000] RatFunc.instAlgebraOfPolynomial

variable [HasCanonicalLocalResidueKStar ℚ (RatFunc ℚ)]
variable [HasCanonicalLocalResidueKStar (AlgebraicClosure ℚ) (RatFunc (AlgebraicClosure ℚ))]

end RatProduction


end ModularCurve.Mp72a102T3



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

open scoped Polynomial P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial
open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]

section OrdIntegrand

variable [CharZero K]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

omit [DecidableEq (RatFunc K)] [CharZero K]
  [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]] in

theorem p1PrincipalPartAtom_ne_zero {p : K[X]} (hp : p ≠ 0) {c : K[X]} (hc : c ≠ 0)
    (m : ℕ) : p1PrincipalPartAtom K p c m ≠ 0 := by
  simp only [p1PrincipalPartAtom, ne_eq, div_eq_zero_iff, not_or]
  exact ⟨(map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hc,
    pow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hp)⟩

end OrdIntegrand


section MOneMembership

variable [CharZero K]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

end MOneMembership


section MOneTerm

variable [CharZero K]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

end MOneTerm


section MOneInftyVanish

variable [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates]

end MOneInftyVanish


section FiniteSideRow

variable [HasCanonicalLocalResidueKStar K (RatFunc K)]

end FiniteSideRow


section FiniteSideBridge

variable [CharZero K]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

end FiniteSideBridge


section TwoPlaceCancelFromFinite

variable [CharZero K]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]

end TwoPlaceCancelFromFinite


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
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsLocalRing
open scoped Polynomial P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq)

open _root_.AlgebraicCurve

theorem le_exp_neg_one_of_lt_one {x : ℤᵐ⁰} (hx : x < 1) : x ≤ exp (-1 : ℤ) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact zero_le'
  · rw [← exp_log hx0] at hx ⊢
    rw [show (1 : ℤᵐ⁰) = exp 0 from rfl, exp_lt_exp] at hx
    rw [exp_le_exp]
    omega

namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_ne_zero adicValuation_coe_eq_one_iff adicValuation_coe_irreducible ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ord_smul ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring mk.injEq rec ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk adicValuation_valuationSubring mem_iff_adicValuation_le_one isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one isEquiv_adicValuation_ofHeightOneSpectrum ord_ofHeightOneSpectrum_ne_zero_iff dCoord DCoordGenerates dCoord_ne_zero differentialCoeff differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_dCoord differentialCoeff_zero differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg deg_restrict_mul_inertiaDeg ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq)

open _root_.AlgebraicCurve.Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.isUnit_algebraMap {c : K} (hc : c ≠ 0) :
    IsUnit (algebraMap K v.toValuationSubring c) :=
  (isUnit_iff_ne_zero.mpr hc).map _




theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.adicValuation_algebraMap {c : K} (hc : c ≠ 0) :
    v.adicValuation (algebraMap K F c) = 1 := by
  rw [← v.coe_algebraMap]
  exact (v.adicValuation_coe_eq_one_iff _).mpr (v.isUnit_algebraMap hc)




theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.ord_algebraMap (c : K) : v.ord (algebraMap K F c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [_root_.map_zero, v.ord_zero]
  · simp only [ord, v.adicValuation_algebraMap hc, log_one, _root_.neg_zero]




theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.ord_eq_neg_log_of_valuationSubring_eq (w : Valuation F ℤᵐ⁰)
    (hw : w.valuationSubring = v.toValuationSubring) {π : F} (hπ : w π = exp (-1 : ℤ))
    {f : F} (hf : f ≠ 0) : v.ord f = -log (w f) := by
  have hequiv : w.IsEquiv v.adicValuation :=
    v.isEquiv_adicValuation_of_valuationSubring_eq hw
  have hexp_lt : (exp (-1 : ℤ) : ℤᵐ⁰) < 1 := by
    rw [show (1 : ℤᵐ⁰) = exp 0 from rfl]
    exact exp_lt_exp.mpr (by omega)

  obtain ⟨π₀, hπ₀⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have hadic_π₀ : v.adicValuation (π₀ : F) = exp (-1 : ℤ) := v.adicValuation_coe_irreducible hπ₀

  have hwπ₀ : w (π₀ : F) = exp (-1 : ℤ) := by
    refine le_antisymm (le_exp_neg_one_of_lt_one (hequiv.lt_one_iff_lt_one.mpr ?_)) ?_
    · rw [hadic_π₀]
      exact hexp_lt
    · rw [← hπ]
      refine (hequiv π π₀).mpr ?_
      rw [hadic_π₀]
      refine le_exp_neg_one_of_lt_one (hequiv.lt_one_iff_lt_one.mp ?_)
      rw [hπ]
      exact hexp_lt

  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ₀
  have hwu : w ((u : v.toValuationSubring) : F) = 1 :=
    hequiv.eq_one_iff_eq_one.mpr ((v.adicValuation_coe_eq_one_iff _).mpr u.isUnit)
  set n := v.ord f with hn
  rw [hu, map_mul, map_zpow₀, hwu, hwπ₀, one_mul, log_zpow, log_exp, smul_eq_mul]
  ring




end Place


namespace RationalFunctionField

export _root_.AlgebraicCurve.RationalFunctionField (heightOneSpectrumOfIrreducible heightOneSpectrumOfIrreducible_asIdeal exists_irreducible_span finitePlace finitePlace_def algebraMap_mem_ofHeightOneSpectrum residueFieldEquivOfHeightOneSpectrum deg_ofHeightOneSpectrum deg_finitePlace)

open _root_.AlgebraicCurve.RationalFunctionField

variable {K : Type*} [Field K]

theorem ord_ofHeightOneSpectrum_eq_neg_log (w : HeightOneSpectrum K[X]) {p : K[X]}
    (hp : p ≠ 0) (hw : w.asIdeal = Ideal.span {p}) {f : RatFunc K} (hf : f ≠ 0) :
    (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord f
      = -log (w.valuation (RatFunc K) f) := by
  have hval : w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) p) = exp (-1 : ℤ) := by
    have h := w.intValuation_singleton hp hw
    rw [← h]
    simpa using w.valuation_of_algebraMap (K := RatFunc K) p
  exact (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K)
    w).ord_eq_neg_log_of_valuationSubring_eq (w.valuation (RatFunc K)) rfl hval hf

theorem ord_ofHeightOneSpectrum_of_span (w : HeightOneSpectrum K[X]) {p : K[X]}
    (hp : p ≠ 0) (hw : w.asIdeal = Ideal.span {p}) :
    (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord
      (algebraMap K[X] (RatFunc K) p) = 1 := by
  have hval : w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) p) = exp (-1 : ℤ) := by
    have h := w.intValuation_singleton hp hw
    rw [← h]
    simpa using w.valuation_of_algebraMap (K := RatFunc K) p
  rw [ord_ofHeightOneSpectrum_eq_neg_log w hp hw (RatFunc.algebraMap_ne_zero hp), hval]
  simp [log_exp]

theorem ord_ofHeightOneSpectrum_eq_zero_of_notMem (w : HeightOneSpectrum K[X]) {q : K[X]}
    (hq : q ≠ 0) (hmem : q ∉ w.asIdeal) :
    (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord
      (algebraMap K[X] (RatFunc K) q) = 0 := by
  by_contra h
  exact hmem
    ((Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w hq).mp h)

section PlaceInftyOrd

variable [DecidableEq (RatFunc K)]

theorem ord_placeInfty {f : RatFunc K} (hf : f ≠ 0) :
    (placeInfty K).ord f = -f.intDegree := by
  have hπ : RatFunc.inftyValuation K (RatFunc.X)⁻¹ = exp (-1 : ℤ) := by
    rw [map_inv₀, RatFunc.inftyValuation.X]
    exact (exp_neg (1 : ℤ)).symm
  rw [(placeInfty K).ord_eq_neg_log_of_valuationSubring_eq (RatFunc.inftyValuation K) rfl hπ
      hf,
    RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero K hf, log_exp]

theorem ord_placeInfty_algebraMap {q : K[X]} (hq : q ≠ 0) :
    (placeInfty K).ord (algebraMap K[X] (RatFunc K) q) = -(q.natDegree : ℤ) := by
  rw [ord_placeInfty (RatFunc.algebraMap_ne_zero hq), RatFunc.intDegree_polynomial]

end PlaceInftyOrd


section IrreducibleDivisor

variable [DecidableEq (RatFunc K)]

theorem single_add_single_apply_eq_ord {p : K[X]} (hp : Irreducible p)
    (v : Place K (RatFunc K)) :
    (Finsupp.single (finitePlace K hp) (1 : ℤ)
        + Finsupp.single (placeInfty K) (-(p.natDegree : ℤ))) v
      = v.ord (algebraMap K[X] (RatFunc K) p) := by
  have hp0 : p ≠ 0 := hp.ne_zero
  rw [Finsupp.add_apply]
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
  ·
    rw [Finsupp.single_eq_of_ne (Ne.symm (placeInfty_ne_ofHeightOneSpectrum K w)), add_zero]
    by_cases hcase :
        Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w = finitePlace K hp
    ·
      rw [hcase, Finsupp.single_eq_same]
      exact (ord_ofHeightOneSpectrum_of_span (heightOneSpectrumOfIrreducible K hp) hp0
        (heightOneSpectrumOfIrreducible_asIdeal K hp)).symm
    ·
      rw [Finsupp.single_eq_of_ne hcase]
      refine (ord_ofHeightOneSpectrum_eq_zero_of_notMem w hp0 fun hmem => hcase ?_).symm

      have hspan : Ideal.span {p} = w.asIdeal :=
        (PrincipalIdealRing.isMaximal_of_irreducible hp).eq_of_le w.isPrime.ne_top
          ((Ideal.span_singleton_le_iff_mem _).mpr hmem)
      have hwp : w = heightOneSpectrumOfIrreducible K hp :=
        HeightOneSpectrum.ext
          (hspan.symm.trans (heightOneSpectrumOfIrreducible_asIdeal K hp).symm)
      rw [hwp, finitePlace_def]
  ·
    rw [Finsupp.single_eq_of_ne
        (show placeInfty K ≠ finitePlace K hp from
          placeInfty_ne_ofHeightOneSpectrum K (heightOneSpectrumOfIrreducible K hp)),
      Finsupp.single_eq_same, zero_add]
    exact (ord_placeInfty_algebraMap hp0).symm

theorem degree_single_add_single {p : K[X]} (hp : Irreducible p) :
    Divisor.degree (Finsupp.single (finitePlace K hp) (1 : ℤ)
        + Finsupp.single (placeInfty K) (-(p.natDegree : ℤ))) = 0 := by
  rw [map_add, Divisor.degree_single, Divisor.degree_single, deg_finitePlace, deg_placeInfty]
  push_cast
  ring

end IrreducibleDivisor


theorem degree_eq_zero_of_forall_eq_ord_algebraMap (q : K[X]) :
    ∀ D : Divisor K (RatFunc K),
      (∀ v : Place K (RatFunc K), D v = v.ord (algebraMap K[X] (RatFunc K) q)) →
      Divisor.degree D = 0 := by
  classical
  refine UniqueFactorizationMonoid.induction_on_prime q ?_ ?_ ?_
  ·
    intro D hD
    have hzero : D = 0 := by
      ext v
      simp [hD v]
    rw [hzero, _root_.map_zero]
  ·
    intro x hx D hD
    obtain ⟨r, -, rfl⟩ := Polynomial.isUnit_iff.mp hx
    have hC : (algebraMap K[X] (RatFunc K)) (Polynomial.C r) = algebraMap K (RatFunc K) r := by
      rw [← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    have hzero : D = 0 := by
      ext v
      rw [hD v, hC, v.ord_algebraMap]
      simp
    rw [hzero, _root_.map_zero]
  ·
    intro a p ha hp ih D hD
    have hp' : algebraMap K[X] (RatFunc K) p ≠ 0 := RatFunc.algebraMap_ne_zero hp.ne_zero
    have ha' : algebraMap K[X] (RatFunc K) a ≠ 0 := RatFunc.algebraMap_ne_zero ha
    set Dp : Divisor K (RatFunc K) :=
      Finsupp.single (finitePlace K hp.irreducible) (1 : ℤ)
        + Finsupp.single (placeInfty K) (-(p.natDegree : ℤ)) with hDp_def
    have hDp : ∀ v : Place K (RatFunc K), Dp v = v.ord (algebraMap K[X] (RatFunc K) p) :=
      fun v => single_add_single_apply_eq_ord hp.irreducible v

    have hDa : ∀ v : Place K (RatFunc K),
        (D - Dp) v = v.ord (algebraMap K[X] (RatFunc K) a) := by
      intro v
      rw [Finsupp.sub_apply, hD v, hDp v, map_mul, v.ord_mul hp' ha']
      ring
    have hdeg_p : Divisor.degree Dp = 0 := degree_single_add_single hp.irreducible
    have hdeg_a : Divisor.degree (D - Dp) = 0 := ih (D - Dp) hDa
    have hsplit : D = Dp + (D - Dp) := by abel
    rw [hsplit, map_add, hdeg_p, zero_add]
    exact hdeg_a

def principalDivisor {f : RatFunc K} (hf : f ≠ 0) : Divisor K (RatFunc K) :=
  ⟨(finite_setOf_ord_ne_zero hf).toFinset, fun v => v.ord f, fun v => by
    simp [Set.Finite.mem_toFinset]⟩

@[scoped simp]
theorem principalDivisor_apply {f : RatFunc K} (hf : f ≠ 0) (v : Place K (RatFunc K)) :
    principalDivisor hf v = v.ord f := rfl

theorem degree_eq_zero_of_forall_eq_ord {f : RatFunc K} (D : Divisor K (RatFunc K))
    (hD : ∀ v : Place K (RatFunc K), D v = v.ord f) : Divisor.degree D = 0 := by
  rcases eq_or_ne f 0 with rfl | hf
  · have hzero : D = 0 := by
      ext v
      simp [hD v]
    rw [hzero, _root_.map_zero]
  · have hden : f.denom ≠ 0 := f.denom_ne_zero
    have hdenF : algebraMap K[X] (RatFunc K) f.denom ≠ 0 := RatFunc.algebraMap_ne_zero hden

    have hsplit : ∀ v : Place K (RatFunc K),
        (D + principalDivisor hdenF) v = v.ord (algebraMap K[X] (RatFunc K) f.num) := by
      intro v
      rw [Finsupp.add_apply, hD v, principalDivisor_apply]
      have hmul : f * algebraMap K[X] (RatFunc K) f.denom
          = algebraMap K[X] (RatFunc K) f.num :=
        ((div_eq_iff hdenF).mp f.num_div_denom).symm
      have h2 := v.ord_mul hf hdenF
      rw [hmul] at h2
      exact h2.symm
    have h1 := degree_eq_zero_of_forall_eq_ord_algebraMap f.num
      (D + principalDivisor hdenF) hsplit
    have h2 := degree_eq_zero_of_forall_eq_ord_algebraMap f.denom
      (principalDivisor hdenF) fun _ => rfl
    rw [map_add, h2, add_zero] at h1
    exact h1

theorem degree_principalDivisor {f : RatFunc K} (hf : f ≠ 0) :
    Divisor.degree (principalDivisor hf) = 0 :=
  degree_eq_zero_of_forall_eq_ord (principalDivisor hf) fun _ => rfl

scoped instance instHasPrincipalDivisors : HasPrincipalDivisors K (RatFunc K) where
  exists_divisor _ hf := ⟨principalDivisor hf, fun _ => rfl, degree_principalDivisor hf⟩

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

open scoped Polynomial P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial
open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField

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

end P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed
