/-
Copyright 2026 Anthropic, PBC. Released under Apache License 2.0.
Source: https://github.com/anthropics/fermats-last-theorem
Revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.lean; source lines 2813-4221.
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
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.RRSplit.functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed_Part02

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 6400000
set_option maxHeartbeats 12800000

namespace P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed

section
section
noncomputable section
namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic)

open _root_.AlgebraicCurve
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_coe_eq_one_iff ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ofHeightOneSpectrum mk.injEq rec ne_top' algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict mem_restrict_iff ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg fiber mem_fiber mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one DCoordGenerates differentialCoeff ordDifferential uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero)

open _root_.AlgebraicCurve.Place
variable [HasPrincipalDivisors K F]

theorem eq_algebraMap_of_forall_ord_nonneg (v₀ : Place K F) (hrat : v₀.IsRational)
    (hdeg : v₀.deg ≠ 0) {g : F} (hg : g ≠ 0) (hord : ∀ v : Place K F, 0 ≤ v.ord g) :
    ∃ c : K, g = algebraMap K F c := by
  have hg₀ : g ∈ v₀.toValuationSubring := v₀.mem_of_ord_nonneg hg (hord v₀)
  refine ⟨v₀.evalAt g, ?_⟩
  by_contra hne

  set t : F := g - algebraMap K F (v₀.evalAt g) with ht
  have htne : t ≠ 0 := sub_ne_zero.mpr hne
  have hzero : 0 < v₀.ord t := v₀.ord_sub_evalAt_pos hrat hg₀ htne
  have hpole : ∀ v : Place K F, 0 ≤ v.ord t := fun v =>
    v.ord_nonneg_of_mem (sub_mem (v.mem_of_ord_nonneg hg (hord v)) (v.algebraMap_mem' _))

  obtain ⟨D, hD, hdeg0⟩ := HasPrincipalDivisors.exists_divisor (K := K) t htne
  have hDpos : 0 < D v₀ := by rw [hD v₀]; exact hzero
  have hDnonneg : ∀ v, 0 ≤ D v := fun v => by rw [hD v]; exact hpole v
  have hmem : v₀ ∈ D.support := Finsupp.mem_support_iff.mpr hDpos.ne'
  have hpos : 0 < Divisor.degree D := by
    rw [Divisor.degree_eq_sum_support]
    calc (0 : ℤ) < D v₀ * (v₀.deg : ℤ) :=
          mul_pos hDpos (by exact_mod_cast Nat.pos_of_ne_zero hdeg)
      _ ≤ ∑ v ∈ D.support, D v * (v.deg : ℤ) :=
          Finset.single_le_sum
            (fun v _ => mul_nonneg (hDnonneg v) (Int.natCast_nonneg _)) hmem
  omega
end Place

end AlgebraicCurve

end


noncomputable section
namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic)

open _root_.AlgebraicCurve
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem constantsAreBase_of_exists_isRational [HasPrincipalDivisors K F]
    (v₀ : Place K F) (hrat : v₀.IsRational) (hdeg : v₀.deg ≠ 0) :
    ConstantsAreBase K F := by
  refine le_antisymm (fun f hf => ?_) (fun f ⟨c, hc⟩ => hc ▸ algebraMap_mem_lSpace_zero c)
  rcases eq_or_ne f 0 with rfl | hf0
  · exact zero_mem _
  · have hord : ∀ v : Place K F, 0 ≤ v.ord f := by
      have h := (mem_lSpace_iff_ord.mp hf).resolve_left hf0
      simpa using h
    obtain ⟨c, hc⟩ := Place.eq_algebraMap_of_forall_ord_nonneg v₀ hrat hdeg hf0 hord
    exact ⟨c, hc.symm⟩
end AlgebraicCurve

end


noncomputable section
namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic)

open _root_.AlgebraicCurve
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem constantsAreBase_of_deg_eq_one [HasPrincipalDivisors K F]
    (v₀ : Place K F) (hdeg : v₀.deg = 1) :
    ConstantsAreBase K F :=
  constantsAreBase_of_exists_isRational v₀ (v₀.isRational_of_deg_eq_one hdeg)
    (hdeg ▸ one_ne_zero)
end AlgebraicCurve

end


end


end


section
section

noncomputable section

open _root_.Module
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsLocalRing
open _root_.Module.IsLocalRing
open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero

namespace Submodule

export _root_.Submodule (quotEquivOfEq Quotient.eq inclusion factor span_singleton_le_iff_mem coe_smul smul_mem' mk smul_mem mem_bot subtype_injective mk.injEq coe_mem Quotient.subsingleton_iff Quotient.mk span restrictScalars mem_map_of_mem inclusion_injective topEquiv_apply comapSubtypeEquivOfLe neg_le mem_comap finrank_quotient_add_finrank mem_top Quotient.equiv mem_span_singleton mul_mem_mul mem_dualAnnihilator mkQ mem_map coe_subtype map_smul' zero map_span quotientQuotientEquivQuotient coe_eq_zero range_subtype Quotient.mk_surjective map rec mem_inf mem_sup neg_le_neg Quotient.mk_eq_zero subset_span topEquiv map_injective_of_injective comap_subtype_self mapQ subsingleton_iff smul_def mk_eq_zero coe_add mkQ_apply ext factor_mk ker_mkQ map_comap_subtype comap comap_mono map_sup coe_zero map_le_iff_le_comap)

open _root_.Submodule

variable {K X : Type*} [Field K] [AddCommGroup X] [Module K X]

def nestedComapMapMkQEquiv {A B C : Submodule K X} (_hAB : A ≤ B) (hBC : B ≤ C) :
    ((B.comap C.subtype).map (A.comap C.subtype).mkQ : Submodule K _)
      ≃ₗ[K] B ⧸ A.comap B.subtype := by
  set S := A.comap C.subtype with hS
  set T := B.comap C.subtype with hT

  let ψ : (T : Type _) →ₗ[K] (C ⧸ S) := S.mkQ ∘ₗ T.subtype
  have hker : LinearMap.ker ψ = S.comap T.subtype := by
    simp only [ψ, LinearMap.ker_comp, ker_mkQ]
  have hran : LinearMap.range ψ = T.map S.mkQ := by
    simp only [ψ, LinearMap.range_comp, range_subtype]
  let e1 : (T ⧸ S.comap T.subtype) ≃ₗ[K] (T.map S.mkQ : Submodule K _) :=
    (Submodule.Quotient.equiv _ (LinearMap.ker ψ) (LinearEquiv.refl K T)
        (by rw [hker]; simp)).trans
      (ψ.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hran))

  have hmap : (S.comap T.subtype).map
      (Submodule.comapSubtypeEquivOfLe hBC : (T : Type _) →ₗ[K] B) = A.comap B.subtype := by
    ext ⟨b, hb⟩
    simp only [mem_map, mem_comap, Submodule.coe_subtype, hS]
    constructor
    · rintro ⟨⟨⟨x, hxC⟩, hxB⟩, hxA, hxeq⟩
      have hx : x = b := congrArg Subtype.val hxeq
      subst hx; exact hxA
    · intro hbA
      exact ⟨⟨⟨b, hBC hb⟩, hb⟩, hbA, rfl⟩
  let e2 : (T ⧸ S.comap T.subtype) ≃ₗ[K] (B ⧸ A.comap B.subtype) :=
    Submodule.Quotient.equiv _ _ (Submodule.comapSubtypeEquivOfLe hBC) hmap
  exact e1.symm.trans e2

theorem finrank_quotient_chain {A B C : Submodule K X} (hAB : A ≤ B) (hBC : B ≤ C)
    [hCB : Module.Finite K (C ⧸ B.comap C.subtype)]
    [hBA : Module.Finite K (B ⧸ A.comap B.subtype)] :
    Module.Finite K (C ⧸ A.comap C.subtype) ∧
      finrank K (C ⧸ A.comap C.subtype)
        = finrank K (C ⧸ B.comap C.subtype) + finrank K (B ⧸ A.comap B.subtype) := by
  set S := A.comap C.subtype
  set T := B.comap C.subtype
  have hST : S ≤ T := comap_mono hAB

  have e3 := Submodule.quotientQuotientEquivQuotient S T hST

  have eK := nestedComapMapMkQEquiv (K := K) hAB hBC
  haveI : Module.Finite K (T.map S.mkQ : Submodule K _) := Module.Finite.equiv eK.symm
  haveI : Module.Finite K ((C ⧸ S) ⧸ T.map S.mkQ) := Module.Finite.equiv e3.symm
  haveI hfin : Module.Finite K (C ⧸ S) := Module.Finite.of_submodule_quotient (T.map S.mkQ)
  refine ⟨hfin, ?_⟩
  have h := Submodule.finrank_quotient_add_finrank (R := K) (T.map S.mkQ)
  rw [LinearEquiv.finrank_eq e3, LinearEquiv.finrank_eq eK] at h
  omega

end Submodule


namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic)

open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

def adeleBddQuotSingleEquivResidueField (D : Divisor K F) (P : Place K F) :
    (adeleBdd D ⧸ (adeleBdd (D - Finsupp.single P 1)).comap (adeleBdd D).subtype)
      ≃ₗ[K] P.ResidueField := by
  classical
  set E : Divisor K F := D - Finsupp.single P 1 with hE
  have hEP : E P = D P - 1 := by rw [hE, Finsupp.sub_apply, Finsupp.single_eq_same]
  have hEv : ∀ v, v ≠ P → E v = D v := by
    intro v hv; rw [hE, Finsupp.sub_apply, Finsupp.single_eq_of_ne hv, sub_zero]

  let π : P.toValuationSubring :=
    (IsDiscreteValuationRing.exists_irreducible P.toValuationSubring).choose
  have hπ : Irreducible π :=
    (IsDiscreteValuationRing.exists_irreducible P.toValuationSubring).choose_spec
  set t : F := (π : F) with ht
  have ht0 : t ≠ 0 := by simpa [ht, ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  have ht1 : P.ord t = 1 := P.ord_coe_irreducible hπ
  have htn0 : t ^ (D P) ≠ 0 := zpow_ne_zero _ ht0

  have hordmul : ∀ {g : F}, g ≠ 0 → P.ord (t ^ (D P) * g) = D P + P.ord g := fun {g} hg => by
    rw [P.ord_mul htn0 hg, P.ord_zpow, ht1, mul_one]

  have hmem : ∀ α : Place K F → F, α ∈ adeleBdd D → t ^ (D P) * α P ∈ P.toValuationSubring := by
    intro α hα
    rcases eq_or_ne (α P) 0 with hg0 | hg0
    · simp [hg0]
    · refine P.mem_of_ord_nonneg (mul_ne_zero htn0 hg0) ?_
      rw [hordmul hg0]
      have h := hα P
      rw [P.adicValuation_eq_exp_neg_ord hg0, WithZero.exp_le_exp] at h
      linarith

  let ψ : adeleBdd D →ₗ[K] P.toValuationSubring :=
    { toFun := fun α => ⟨t ^ (D P) * (α : Place K F → F) P, hmem _ α.2⟩
      map_add' := by
        intro α β; apply Subtype.ext
        simp only [Submodule.coe_add, Pi.add_apply]
        push_cast; ring
      map_smul' := by
        intro c α; apply Subtype.ext
        simp only [RingHom.id_apply, SetLike.val_smul, Algebra.smul_def, MulMemClass.coe_mul,
          Place.coe_algebraMap, Pi.smul_apply]
        ring }
  have hψ_apply : ∀ α : adeleBdd D,
      (ψ α : F) = t ^ (D P) * (α : Place K F → F) P := fun α => rfl

  let res : P.toValuationSubring →ₗ[K] P.ResidueField :=
    (Algebra.linearMap P.toValuationSubring P.ResidueField).restrictScalars K
  have hres : ∀ x : P.toValuationSubring, res x = IsLocalRing.residue _ x := by
    intro x
    show (Algebra.linearMap P.toValuationSubring P.ResidueField).restrictScalars K x = _
    rw [LinearMap.restrictScalars_apply, Algebra.linearMap_apply,
      IsLocalRing.ResidueField.algebraMap_eq]
  let φ : adeleBdd D →ₗ[K] P.ResidueField := res ∘ₗ ψ

  have hphi : ∀ α : adeleBdd D, φ α = 0 ↔
      (⟨t ^ (D P) * (α : Place K F → F) P, hmem _ α.2⟩ : P.toValuationSubring)
        ∈ IsLocalRing.maximalIdeal P.toValuationSubring := fun α => by
    rw [show φ α = IsLocalRing.residue P.toValuationSubring
            ⟨t ^ (D P) * (α : Place K F → F) P, hmem _ α.2⟩ from hres (ψ α),
      IsLocalRing.residue_eq_zero_iff]

  have hker : LinearMap.ker φ = (adeleBdd E).comap (adeleBdd D).subtype := by
    ext α
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.coe_subtype]
    rw [hphi α, P.mk_mem_maximalIdeal_iff, mem_adeleBdd]
    have hαD := α.2
    constructor
    · rintro (h | h) v
      ·
        have hα0 : (α : Place K F → F) P = 0 := by
          rcases mul_eq_zero.mp h with h' | h'
          · exact absurd h' htn0
          · exact h'
        by_cases hv : v = P
        · subst v; rw [hα0, Valuation.map_zero]; exact zero_le'
        · rw [hEv v hv]; exact hαD v
      · by_cases hv : v = P
        · subst v
          rcases eq_or_ne ((α : Place K F → F) P) 0 with hα0 | hα0
          · rw [hα0, Valuation.map_zero]; exact zero_le'
          · rw [P.adicValuation_eq_exp_neg_ord hα0, WithZero.exp_le_exp, hEP]
            rw [hordmul hα0] at h; omega
        · rw [hEv v hv]; exact hαD v
    · intro h
      rcases eq_or_ne ((α : Place K F → F) P) 0 with hα0 | hα0
      · left; rw [hα0, mul_zero]
      · right
        have hP := h P
        rw [P.adicValuation_eq_exp_neg_ord hα0, WithZero.exp_le_exp, hEP] at hP
        rw [hordmul hα0]; omega

  have hsurj : Function.Surjective φ := by
    intro c

    obtain ⟨cl, hcl⟩ := IsLocalRing.residue_surjective (R := P.toValuationSubring) c

    set f : F := (cl : F) * t ^ (-(D P)) with hf
    have hαD : Pi.single P f ∈ adeleBdd D := by
      intro v
      by_cases hv : v = P
      · subst v
        simp only [Pi.single_eq_same]
        rcases eq_or_ne (cl : F) 0 with hc0 | hc0
        · rw [hf, hc0, zero_mul, Valuation.map_zero]; exact zero_le'
        · have hf0 : f ≠ 0 := by rw [hf]; exact mul_ne_zero hc0 (zpow_ne_zero _ ht0)
          rw [P.adicValuation_eq_exp_neg_ord hf0, WithZero.exp_le_exp]
          rw [hf, P.ord_mul hc0 (zpow_ne_zero _ ht0), P.ord_zpow, ht1, mul_one]
          have hclnn := P.ord_nonneg_of_mem cl.2
          linarith
      · rw [Pi.single_eq_of_ne hv, Valuation.map_zero]; exact zero_le'
    refine ⟨⟨Pi.single P f, hαD⟩, ?_⟩

    show res (ψ ⟨Pi.single P f, hαD⟩) = c
    rw [hres]
    rw [show (ψ ⟨Pi.single P f, hαD⟩ : P.toValuationSubring) = cl from ?_, hcl]
    apply Subtype.ext
    rw [hψ_apply]
    show t ^ (D P) * (Pi.single P f : Place K F → F) P = (cl : F)
    rw [show (Pi.single P f : Place K F → F) P = f from Pi.single_eq_same _ _, hf,
      mul_comm (cl : F), ← mul_assoc, ← zpow_add₀ ht0, add_neg_cancel, zpow_zero, one_mul]

  exact (Submodule.Quotient.equiv _ _ (LinearEquiv.refl K _) (by rw [← hker]; simp)).trans
    (φ.quotKerEquivOfSurjective hsurj)

theorem finrank_adeleBdd_quotient_single [IsCurveOver K F] (D : Divisor K F) (P : Place K F) :
    Module.Finite K
        (adeleBdd D ⧸ (adeleBdd (D - Finsupp.single P 1)).comap (adeleBdd D).subtype) ∧
      finrank K
          (adeleBdd D ⧸ (adeleBdd (D - Finsupp.single P 1)).comap (adeleBdd D).subtype)
        = P.deg := by
  haveI := IsCurveOver.finite_residueField (K := K) P
  exact ⟨Module.Finite.equiv (adeleBddQuotSingleEquivResidueField D P).symm,
    (adeleBddQuotSingleEquivResidueField D P).finrank_eq⟩

theorem finrank_adeleBdd_quotient [IsCurveOver K F] {D₁ D₂ : Divisor K F} (hD : D₁ ≤ D₂) :
    Module.Finite K (adeleBdd D₂ ⧸ (adeleBdd D₁).comap (adeleBdd D₂).subtype) ∧
      (finrank K (adeleBdd D₂ ⧸ (adeleBdd D₁).comap (adeleBdd D₂).subtype) : ℤ)
        = Divisor.degree D₂ - Divisor.degree D₁ := by
  classical

  suffices H : ∀ m : ℕ, ∀ D₁ D₂ : Divisor K F, D₁ ≤ D₂ →
      (Divisor.degree (D₂ - D₁)).toNat = m →
      Module.Finite K (adeleBdd D₂ ⧸ (adeleBdd D₁).comap (adeleBdd D₂).subtype) ∧
        (finrank K (adeleBdd D₂ ⧸ (adeleBdd D₁).comap (adeleBdd D₂).subtype) : ℤ)
          = Divisor.degree D₂ - Divisor.degree D₁ from
    H _ D₁ D₂ hD rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro D₁ D₂ hD hm
    have hEeff : ∀ v, 0 ≤ (D₂ - D₁) v := fun v => by
      rw [Finsupp.sub_apply]; have := hD v; omega
    by_cases hD0 : D₂ - D₁ = 0
    ·
      have hD12 : D₁ = D₂ := (sub_eq_zero.mp hD0).symm
      subst hD12
      rw [Submodule.comap_subtype_self]
      haveI : Subsingleton (adeleBdd D₁ ⧸ (⊤ : Submodule K (adeleBdd D₁))) :=
        Submodule.Quotient.subsingleton_iff.mpr rfl
      exact ⟨Module.Finite.of_finite, by simp [Module.finrank_zero_of_subsingleton]⟩
    ·
      obtain ⟨P, hP⟩ := Finsupp.support_nonempty_iff.mpr hD0
      have hPpos : 1 ≤ (D₂ - D₁) P := by
        have hne : (D₂ - D₁) P ≠ 0 := Finsupp.mem_support_iff.mp hP
        have := hEeff P; omega
      set D₂' : Divisor K F := D₂ - Finsupp.single P 1 with hD₂'
      have h12' : D₁ ≤ D₂' := by
        intro v; rw [hD₂', Finsupp.sub_apply]
        by_cases hv : v = P
        · subst v; rw [Finsupp.single_eq_same]
          have := hPpos; rw [Finsupp.sub_apply] at this; omega
        · rw [Finsupp.single_eq_of_ne hv, sub_zero]; exact hD v
      have h2'2 : D₂' ≤ D₂ := by
        intro v; rw [hD₂', Finsupp.sub_apply]
        by_cases hv : v = P
        · subst v; rw [Finsupp.single_eq_same]; omega
        · rw [Finsupp.single_eq_of_ne hv, sub_zero]

      have hdegD₂' : Divisor.degree D₂' = Divisor.degree D₂ - P.deg := by
        rw [hD₂', map_sub, Divisor.degree_single, one_mul]
      have hPdeg1 : 1 ≤ (P.deg : ℤ) := by exact_mod_cast one_le_deg P
      have hEnn : 0 ≤ Divisor.degree (D₂ - D₁) := Divisor.degree_nonneg_of_nonneg hEeff
      have hE'nn : 0 ≤ Divisor.degree (D₂' - D₁) := Divisor.degree_nonneg_of_nonneg
        (fun v => by rw [Finsupp.sub_apply]; have := h12' v; omega)
      have hdegdiff : Divisor.degree (D₂' - D₁) = Divisor.degree (D₂ - D₁) - P.deg := by
        simp only [hD₂', map_sub, Divisor.degree_single, one_mul]; ring

      have hmlt : (Divisor.degree (D₂' - D₁)).toNat < m := by rw [← hm]; omega
      obtain ⟨hfin', hrank'⟩ := IH _ hmlt D₁ D₂' h12' rfl

      obtain ⟨hfinS, hrankS⟩ := finrank_adeleBdd_quotient_single (K := K) D₂ P
      rw [← hD₂'] at hfinS hrankS

      haveI := hfin'; haveI := hfinS
      obtain ⟨hfin, hrank⟩ := Submodule.finrank_quotient_chain
        (A := adeleBdd D₁) (B := adeleBdd D₂') (C := adeleBdd D₂)
        (adeleBdd_mono h12') (adeleBdd_mono h2'2)
      refine ⟨hfin, ?_⟩
      rw [hrank, hrankS]
      push_cast
      linarith [hrank', hdegD₂']

theorem module_finite_adeleBdd_quotient [IsCurveOver K F] {D₁ D₂ : Divisor K F} (hD : D₁ ≤ D₂) :
    Module.Finite K (adeleBdd D₂ ⧸ (adeleBdd D₁).comap (adeleBdd D₂).subtype) :=
  (finrank_adeleBdd_quotient hD).1

theorem finrank_adeleBdd_quotient_eq [IsCurveOver K F] {D₁ D₂ : Divisor K F} (hD : D₁ ≤ D₂) :
    (finrank K (adeleBdd D₂ ⧸ (adeleBdd D₁).comap (adeleBdd D₂).subtype) : ℤ)
      = Divisor.degree D₂ - Divisor.degree D₁ :=
  (finrank_adeleBdd_quotient hD).2

def lSpaceQuotientToAdeleBddQuotient {D₁ D₂ : Divisor K F} (_hD : D₁ ≤ D₂) :
    (LSpace D₂ ⧸ (LSpace D₁).comap (LSpace D₂).subtype)
      →ₗ[K] (adeleBdd D₂ ⧸ (adeleBdd D₁).comap (adeleBdd D₂).subtype) :=
  Submodule.mapQ _ _
    ((diagonalHom K F).restrict
      (p := (LSpace D₂ : Submodule K F)) (q := (adeleBdd D₂ : Submodule K _))
      (fun f hf => diagonal_mem_adeleBdd_iff.mpr hf))
    (fun f hf => by
      simp only [Submodule.mem_comap, Submodule.coe_subtype] at hf ⊢
      exact diagonal_mem_adeleBdd_iff.mpr hf)

theorem lSpaceQuotientToAdeleBddQuotient_injective {D₁ D₂ : Divisor K F} (hD : D₁ ≤ D₂) :
    Function.Injective (lSpaceQuotientToAdeleBddQuotient hD) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype]

  rw [show (lSpaceQuotientToAdeleBddQuotient hD) (Submodule.Quotient.mk f)
        = Submodule.Quotient.mk ((diagonalHom K F).restrict
            (fun g hg => diagonal_mem_adeleBdd_iff.mpr hg) f) from rfl,
    Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype] at hx
  exact diagonal_mem_adeleBdd_iff.mp hx

set_option maxHeartbeats 1600000 in

theorem ell_sub_ell_le_degree_sub_degree [IsCurveOver K F] {D₁ D₂ : Divisor K F} (hD : D₁ ≤ D₂)
    [FiniteDimensional K (LSpace D₂)] :
    (ell D₂ : ℤ) - (ell D₁ : ℤ) ≤ Divisor.degree D₂ - Divisor.degree D₁ := by
  haveI := module_finite_adeleBdd_quotient hD

  have hℓ₁ : ell D₁ = finrank K ((LSpace D₁).comap (LSpace D₂).subtype) :=
    (LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe (lSpace_mono hD))).symm
  have hL : ell D₂
      = finrank K (LSpace D₂ ⧸ (LSpace D₁).comap (LSpace D₂).subtype) + ell D₁ := by
    rw [hℓ₁]; exact (Submodule.finrank_quotient_add_finrank _).symm

  have hemb : finrank K (LSpace D₂ ⧸ (LSpace D₁).comap (LSpace D₂).subtype)
      ≤ finrank K (adeleBdd D₂ ⧸ (adeleBdd D₁).comap (adeleBdd D₂).subtype) :=
    LinearMap.finrank_le_finrank_of_injective (lSpaceQuotientToAdeleBddQuotient_injective hD)
  have hloc := finrank_adeleBdd_quotient_eq hD
  have : (ell D₂ : ℤ) - (ell D₁ : ℤ)
      = (finrank K (LSpace D₂ ⧸ (LSpace D₁).comap (LSpace D₂).subtype) : ℤ) := by
    rw [hL]; push_cast; ring
  rw [this, ← hloc]
  exact_mod_cast hemb

theorem adeleBdd_inf_sup_globalSub {D₁ D₂ : Divisor K F} (hD : D₁ ≤ D₂) :
    adeleBdd D₂ ⊓ (adeleBdd D₁ ⊔ globalSub K F)
      = adeleBdd D₁ ⊔ adeleBdd D₂ ⊓ globalSub K F := by
  rw [inf_comm, sup_inf_assoc_of_le _ (adeleBdd_mono hD), inf_comm]

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
open _root_.Module
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module
namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic)

open _root_.AlgebraicCurve
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable (K F)

theorem weilDualityAdelic_of_residueRows (hΩℓ : WeilOmegaEllAgrees K F) :
    WeilDualityAdelic K F := by
  intro _ _ _ ω hω D
  rw [← finrank_omegaSpace_eq_indexOfSpecialty]
  exact hΩℓ hω D
end AlgebraicCurve

end


end


end


section
section

noncomputable section

open _root_.Module
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module
open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero

namespace Submodule

export _root_.Submodule (quotEquivOfEq Quotient.eq inclusion factor span_singleton_le_iff_mem coe_smul smul_mem' mk smul_mem mem_bot subtype_injective mk.injEq coe_mem Quotient.subsingleton_iff Quotient.mk span restrictScalars mem_map_of_mem inclusion_injective topEquiv_apply comapSubtypeEquivOfLe neg_le mem_comap finrank_quotient_add_finrank mem_top Quotient.equiv mem_span_singleton mul_mem_mul mem_dualAnnihilator mkQ mem_map coe_subtype map_smul' zero map_span quotientQuotientEquivQuotient coe_eq_zero range_subtype Quotient.mk_surjective map rec mem_inf mem_sup neg_le_neg Quotient.mk_eq_zero subset_span topEquiv map_injective_of_injective comap_subtype_self mapQ subsingleton_iff smul_def mk_eq_zero coe_add mkQ_apply ext factor_mk ker_mkQ map_comap_subtype comap comap_mono map_sup coe_zero map_le_iff_le_comap)

open _root_.Submodule

variable {K X : Type*} [Field K] [AddCommGroup X] [Module K X]

theorem comap_subtype_sup_of_le_of_le {S T C : Submodule K X} (hS : S ≤ C) (hT : T ≤ C) :
    S.comap C.subtype ⊔ T.comap C.subtype = (S ⊔ T).comap C.subtype := by
  apply Submodule.map_injective_of_injective (f := C.subtype) C.subtype_injective
  rw [Submodule.map_sup, Submodule.map_comap_subtype, Submodule.map_comap_subtype,
    Submodule.map_comap_subtype, inf_eq_right.mpr hS, inf_eq_right.mpr hT,
    inf_eq_right.mpr (sup_le hS hT)]

end Submodule


namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic)

open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem globalSub_le_adeleSpace [HasPrincipalDivisors K F] :
    globalSub K F ≤ adeleSpace K F := by
  rintro _ ⟨f, rfl⟩
  exact diagonal_mem_adeleSpace f

theorem adeleBdd_sup_globalSub_le_adeleSpace [HasPrincipalDivisors K F] (D : Divisor K F) :
    adeleBdd D ⊔ globalSub K F ≤ adeleSpace K F :=
  sup_le adeleBdd_le_adeleSpace globalSub_le_adeleSpace

theorem adeleBddPrincipal_eq_comap [HasPrincipalDivisors K F] (D : Divisor K F) :
    adeleBddPrincipal K F D = (adeleBdd D ⊔ globalSub K F).comap (adeleSpace K F).subtype :=
  Submodule.comap_subtype_sup_of_le_of_le adeleBdd_le_adeleSpace globalSub_le_adeleSpace

section FiniteLSpace

variable [IsCurveOver K F] [Nonempty (Place K F)]

omit [Nonempty (Place K F)] in

theorem finiteDimensional_lSpace [hL0 : FiniteDimensional K (LSpace (0 : Divisor K F))]
    (D : Divisor K F) : FiniteDimensional K (LSpace D) := by

  have h0D : (0 : Divisor K F) ≤ D ⊔ 0 := le_sup_right
  have hDD : D ≤ D ⊔ 0 := le_sup_left
  suffices h : FiniteDimensional K (LSpace (D ⊔ 0)) by
    exact Module.Finite.of_injective (Submodule.inclusion (lSpace_mono hDD))
      (Submodule.inclusion_injective _)

  haveI := module_finite_adeleBdd_quotient (K := K) h0D
  haveI hfinQ : FiniteDimensional K
      (LSpace (D ⊔ 0) ⧸ (LSpace (0 : Divisor K F)).comap (LSpace (D ⊔ 0)).subtype) :=
    Module.Finite.of_injective _ (lSpaceQuotientToAdeleBddQuotient_injective h0D)
  haveI : FiniteDimensional K
      ((LSpace (0 : Divisor K F)).comap (LSpace (D ⊔ 0)).subtype : Submodule K _) :=
    Module.Finite.equiv (Submodule.comapSubtypeEquivOfLe (lSpace_mono h0D)).symm
  exact Module.Finite.of_submodule_quotient
    ((LSpace (0 : Divisor K F)).comap (LSpace (D ⊔ 0)).subtype)

end FiniteLSpace


set_option maxHeartbeats 3200000 in

theorem range_lSpaceQuotientToAdeleBddQuotient {D₁ D₂ : Divisor K F} (hD : D₁ ≤ D₂) :
    LinearMap.range (lSpaceQuotientToAdeleBddQuotient hD)
      = ((adeleBdd D₁ ⊔ globalSub K F).comap (adeleBdd D₂).subtype).map
          ((adeleBdd D₁).comap (adeleBdd D₂).subtype).mkQ := by
  classical
  ext z
  obtain ⟨α, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  simp only [LinearMap.mem_range, Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype,
    Submodule.mkQ_apply]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x

    have hxeq : Submodule.Quotient.mk
        ((diagonalHom K F).restrict (fun g hg => diagonal_mem_adeleBdd_iff.mpr hg) f)
        = (Submodule.Quotient.mk α :
            adeleBdd D₂ ⧸ (adeleBdd D₁).comap (adeleBdd D₂).subtype) := hx
    refine ⟨α, ?_, rfl⟩

    have hdiag2 : (diagonalHom K F (f : F)) ∈ adeleBdd D₂ := diagonal_mem_adeleBdd_iff.mpr f.2
    have hsub : (α : Place K F → F) - diagonalHom K F (f : F) ∈ adeleBdd D₁ := by
      have hq := (Submodule.Quotient.eq _).mp hxeq.symm
      simpa using hq
    refine Submodule.mem_sup.mpr ⟨(α : Place K F → F) - diagonalHom K F (f : F), hsub,
      diagonalHom K F (f : F), diagonal_mem_globalSub _, ?_⟩
    abel
  · rintro ⟨β, hβ, hβeq⟩

    have hβ' : (β : Place K F → F) ∈ adeleBdd D₂ ⊓ (adeleBdd D₁ ⊔ globalSub K F) :=
      Submodule.mem_inf.mpr ⟨β.2, hβ⟩
    rw [adeleBdd_inf_sup_globalSub hD, ← map_diagonal_lSpace] at hβ'
    obtain ⟨γ, hγ, δ, ⟨f, hf, hfδ⟩, hsum⟩ := Submodule.mem_sup.mp hβ'
    refine ⟨Submodule.Quotient.mk ⟨f, hf⟩, ?_⟩
    rw [show (lSpaceQuotientToAdeleBddQuotient hD) (Submodule.Quotient.mk ⟨f, hf⟩)
          = Submodule.Quotient.mk ((diagonalHom K F).restrict
              (fun g hg => diagonal_mem_adeleBdd_iff.mpr hg) ⟨f, hf⟩) from rfl,
      ← hβeq, Submodule.Quotient.eq]

    refine Submodule.mem_comap.mpr ?_
    show diagonalHom K F f - (β : Place K F → F) ∈ adeleBdd D₁
    have hβsub : diagonalHom K F f - (β : Place K F → F) = -γ := by
      rw [← hsum, hfδ]; ring
    rw [hβsub]; exact (adeleBdd D₁).neg_mem hγ

set_option maxHeartbeats 3200000 in

theorem finrank_adeleBddSup_quotient [IsCurveOver K F] [Nonempty (Place K F)]
    {D₁ D₂ : Divisor K F} (hD : D₁ ≤ D₂) [hL : FiniteDimensional K (LSpace D₂)] :
    Module.Finite K (↥(adeleBdd D₂ ⊔ globalSub K F)
        ⧸ (adeleBdd D₁ ⊔ globalSub K F).comap (adeleBdd D₂ ⊔ globalSub K F).subtype) ∧
      (finrank K (↥(adeleBdd D₂ ⊔ globalSub K F)
          ⧸ (adeleBdd D₁ ⊔ globalSub K F).comap (adeleBdd D₂ ⊔ globalSub K F).subtype) : ℤ)
        = (Divisor.degree D₂ - ell D₂) - (Divisor.degree D₁ - ell D₁) := by
  classical

  let A : Submodule K (adeleBdd D₂) := (adeleBdd D₁).comap (adeleBdd D₂).subtype
  let B : Submodule K (adeleBdd D₂) :=
    (adeleBdd D₁ ⊔ globalSub K F).comap (adeleBdd D₂).subtype
  have hAB : A ≤ B := Submodule.comap_mono le_sup_left

  haveI hfinA : Module.Finite K (adeleBdd D₂ ⧸ A) := module_finite_adeleBdd_quotient hD
  have hdimA : (finrank K (adeleBdd D₂ ⧸ A) : ℤ) = Divisor.degree D₂ - Divisor.degree D₁ :=
    finrank_adeleBdd_quotient_eq hD

  have hran : LinearMap.range (lSpaceQuotientToAdeleBddQuotient hD) = B.map A.mkQ :=
    range_lSpaceQuotientToAdeleBddQuotient hD
  have hℓ₁ : ell D₁ = finrank K ((LSpace D₁).comap (LSpace D₂).subtype) :=
    (LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe (lSpace_mono hD))).symm
  have hdimL : ell D₂
      = finrank K (LSpace D₂ ⧸ (LSpace D₁).comap (LSpace D₂).subtype) + ell D₁ := by
    have h := Submodule.finrank_quotient_add_finrank (R := K)
      ((LSpace D₁).comap (LSpace D₂).subtype)
    rw [← hℓ₁] at h; exact h.symm
  have hdimB : ell D₂ = finrank K (B.map A.mkQ : Submodule K (adeleBdd D₂ ⧸ A)) + ell D₁ := by
    rw [← hran, LinearMap.finrank_range_of_inj
      (lSpaceQuotientToAdeleBddQuotient_injective hD)]
    exact hdimL

  have e3 := Submodule.quotientQuotientEquivQuotient A B hAB
  haveI hfinB : Module.Finite K (adeleBdd D₂ ⧸ B) := Module.Finite.equiv e3
  have hdim2 : finrank K (adeleBdd D₂ ⧸ A)
      = finrank K (adeleBdd D₂ ⧸ B) + finrank K (B.map A.mkQ : Submodule K _) := by
    have h := Submodule.finrank_quotient_add_finrank (R := K) (M := adeleBdd D₂ ⧸ A)
      (B.map A.mkQ)
    rw [LinearEquiv.finrank_eq e3] at h; omega

  have e2 := LinearMap.quotientInfEquivSupQuotient (R := K)
    (adeleBdd D₂) (adeleBdd D₁ ⊔ globalSub K F)

  have hsup : adeleBdd D₂ ⊔ (adeleBdd D₁ ⊔ globalSub K F) = adeleBdd D₂ ⊔ globalSub K F := by
    rw [← sup_assoc, sup_eq_left.mpr (adeleBdd_mono hD)]
  have hB' : (adeleBdd D₂).comap (adeleBdd D₂).subtype ⊓
      (adeleBdd D₁ ⊔ globalSub K F).comap (adeleBdd D₂).subtype = B := by
    rw [Submodule.comap_subtype_self, top_inf_eq]
  let eL : (adeleBdd D₂ ⧸ B) ≃ₗ[K]
      (adeleBdd D₂ ⧸ ((adeleBdd D₂).comap (adeleBdd D₂).subtype ⊓
        (adeleBdd D₁ ⊔ globalSub K F).comap (adeleBdd D₂).subtype)) :=
    Submodule.quotEquivOfEq _ _ hB'.symm

  have hfin_iso : Module.Finite K (↥(adeleBdd D₂ ⊔ (adeleBdd D₁ ⊔ globalSub K F)) ⧸
        (adeleBdd D₁ ⊔ globalSub K F).comap
          (adeleBdd D₂ ⊔ (adeleBdd D₁ ⊔ globalSub K F)).subtype) :=
    Module.Finite.equiv (eL.trans e2)
  have hdim_iso : finrank K (↥(adeleBdd D₂ ⊔ (adeleBdd D₁ ⊔ globalSub K F)) ⧸
        (adeleBdd D₁ ⊔ globalSub K F).comap
          (adeleBdd D₂ ⊔ (adeleBdd D₁ ⊔ globalSub K F)).subtype)
      = finrank K (adeleBdd D₂ ⧸ B) :=
    (LinearEquiv.finrank_eq (eL.trans e2)).symm

  have hcast : (finrank K (adeleBdd D₂ ⧸ A) : ℤ)
      = (finrank K (adeleBdd D₂ ⧸ B) : ℤ) + ((ell D₂ : ℤ) - (ell D₁ : ℤ)) := by
    have hb : (ell D₂ : ℤ)
        = (finrank K (B.map A.mkQ : Submodule K (adeleBdd D₂ ⧸ A)) : ℤ) + (ell D₁ : ℤ) := by
      exact_mod_cast hdimB
    push_cast [hdim2]; linarith
  have hgoal : (finrank K (adeleBdd D₂ ⧸ B) : ℤ)
      = Divisor.degree D₂ - ↑(ell D₂) - (Divisor.degree D₁ - ↑(ell D₁)) := by
    linarith [hdimA, hcast]

  clear_value eL
  exact hsup ▸ ⟨hfin_iso, by rw [hdim_iso]; exact hgoal⟩

section Index

variable [IsCurveOver K F] [Nonempty (Place K F)]

theorem adeleBddSup_eq_of_degree_sub_ell_eq {D₁ D₂ : Divisor K F} (hD : D₁ ≤ D₂)
    [FiniteDimensional K (LSpace D₂)]
    (heq : Divisor.degree D₂ - ell D₂ = Divisor.degree D₁ - ell D₁) :
    adeleBdd D₂ ⊔ globalSub K F = adeleBdd D₁ ⊔ globalSub K F := by
  obtain ⟨hfin, hdim⟩ := finrank_adeleBddSup_quotient hD
  rw [heq, sub_self] at hdim

  refine le_antisymm ?_ (sup_le_sup_right (adeleBdd_mono hD) _)
  haveI := hfin
  have hd0 : finrank K (↥(adeleBdd D₂ ⊔ globalSub K F)
      ⧸ (adeleBdd D₁ ⊔ globalSub K F).comap (adeleBdd D₂ ⊔ globalSub K F).subtype) = 0 := by
    exact_mod_cast hdim
  have hsub : Subsingleton (↥(adeleBdd D₂ ⊔ globalSub K F)
      ⧸ (adeleBdd D₁ ⊔ globalSub K F).comap (adeleBdd D₂ ⊔ globalSub K F).subtype) :=
    Module.finrank_zero_iff.mp hd0
  have htop := Submodule.Quotient.subsingleton_iff.mp hsub
  intro x hx
  have hxc : (⟨x, hx⟩ : ↥(adeleBdd D₂ ⊔ globalSub K F)) ∈
      (adeleBdd D₁ ⊔ globalSub K F).comap (adeleBdd D₂ ⊔ globalSub K F).subtype := by
    rw [htop]; exact Submodule.mem_top
  exact hxc

end Index


namespace RiemannGenusReachedAt
export _root_.AlgebraicCurve.RiemannGenusReachedAt (mk eq isMax rec)
end RiemannGenusReachedAt
namespace RiemannGenusReachedAt
open scoped AlgebraicCurve.RiemannGenusReachedAt in
theorem _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RiemannGenusReachedAt.eq_of_ge [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    {D : Divisor K F} (hD : D₀ ≤ D) :
    Divisor.degree D - ell D = γ - 1 := by
  haveI := finiteDimensional_lSpace (K := K) D
  have hge : Divisor.degree D₀ - (ell D₀ : ℤ) ≤ Divisor.degree D - ell D := by
    have := ell_sub_ell_le_degree_sub_degree (K := K) hD
    linarith
  exact le_antisymm (h.isMax D) (h.eq ▸ hge)

end RiemannGenusReachedAt



set_option maxHeartbeats 1600000 in

theorem adeleSpace_eq_of_genusReached [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) :
    adeleSpace K F = adeleBdd D₀ ⊔ globalSub K F := by
  refine le_antisymm ?_ (adeleBdd_sup_globalSub_le_adeleSpace D₀)

  rw [adeleSpace, iSup_le_iff]
  intro D
  refine le_trans (adeleBdd_mono (le_sup_left : D ≤ D ⊔ D₀)) ?_
  haveI := finiteDimensional_lSpace (K := K) (D ⊔ D₀)
  have heq : Divisor.degree (D ⊔ D₀) - ell (D ⊔ D₀) = Divisor.degree D₀ - ell D₀ :=
    (h.eq_of_ge le_sup_right).trans h.eq.symm
  have hsup := adeleBddSup_eq_of_degree_sub_ell_eq (K := K)
    (le_sup_right : D₀ ≤ D ⊔ D₀) heq
  rw [← hsup]
  exact le_sup_left

set_option maxHeartbeats 2400000 in

theorem indexOfSpecialty_eq_of_genusReached [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) (D : Divisor K F) :
    Module.Finite K (adeleSpace K F ⧸ adeleBddPrincipal K F D) ∧
      (indexOfSpecialty D : ℤ) = (ell D : ℤ) - (Divisor.degree D + 1 - γ) := by
  classical

  have hDD' : D ≤ D ⊔ D₀ := le_sup_left
  have hD0D' : D₀ ≤ D ⊔ D₀ := le_sup_right
  haveI := finiteDimensional_lSpace (K := K) (D ⊔ D₀)

  have heqD' : Divisor.degree (D ⊔ D₀) - ell (D ⊔ D₀) = γ - 1 := h.eq_of_ge hD0D'
  have hsa : adeleSpace K F = adeleBdd (D ⊔ D₀) ⊔ globalSub K F := by
    refine le_antisymm ?_ (adeleBdd_sup_globalSub_le_adeleSpace _)
    rw [adeleSpace_eq_of_genusReached h]
    exact sup_le_sup_right (adeleBdd_mono hD0D') _

  have hABsub : adeleBdd D ⊔ globalSub K F ≤ adeleBdd (D ⊔ D₀) ⊔ globalSub K F :=
    sup_le_sup_right (adeleBdd_mono hDD') _
  have hBCsub : adeleBdd (D ⊔ D₀) ⊔ globalSub K F ≤ adeleSpace K F :=
    adeleBdd_sup_globalSub_le_adeleSpace _

  have hCB : (adeleBdd (D ⊔ D₀) ⊔ globalSub K F).comap (adeleSpace K F).subtype = ⊤ := by
    rw [← hsa, Submodule.comap_subtype_self]
  haveI hfinCB : Module.Finite K (adeleSpace K F ⧸
      (adeleBdd (D ⊔ D₀) ⊔ globalSub K F).comap (adeleSpace K F).subtype) := by
    rw [hCB]
    haveI : Subsingleton (adeleSpace K F ⧸ (⊤ : Submodule K (adeleSpace K F))) :=
      Submodule.Quotient.subsingleton_iff.mpr rfl
    exact Module.Finite.of_finite
  have hdimCB : finrank K (adeleSpace K F ⧸
      (adeleBdd (D ⊔ D₀) ⊔ globalSub K F).comap (adeleSpace K F).subtype) = 0 := by
    rw [hCB]
    haveI : Subsingleton (adeleSpace K F ⧸ (⊤ : Submodule K (adeleSpace K F))) :=
      Submodule.Quotient.subsingleton_iff.mpr rfl
    exact Module.finrank_zero_of_subsingleton

  obtain ⟨hfinBA, hdimBA⟩ := finrank_adeleBddSup_quotient (K := K) hDD'

  haveI := hfinBA
  obtain ⟨hfinCA, hdimCA⟩ := Submodule.finrank_quotient_chain
    (A := adeleBdd D ⊔ globalSub K F) (B := adeleBdd (D ⊔ D₀) ⊔ globalSub K F)
    (C := adeleSpace K F) hABsub hBCsub

  have hieq : indexOfSpecialty D
      = finrank K (adeleSpace K F ⧸
        (adeleBdd D ⊔ globalSub K F).comap (adeleSpace K F).subtype) := by
    rw [indexOfSpecialty_eq, adeleBddPrincipal_eq_comap]
  rw [adeleBddPrincipal_eq_comap]
  refine ⟨hfinCA, ?_⟩
  rw [hieq]
  push_cast [hdimCA, hdimCB]
  linarith [hdimBA, heqD']

theorem riemannIndexFormula_of_genusReached
    (hg : ∀ [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)],
      RiemannGenusReached K F (genus K F)) :
    RiemannIndexFormula K F := by
  intro _ _ D
  obtain ⟨hne, hL0, D₀, hD₀⟩ := hg
  haveI := hne; haveI := hL0
  exact (indexOfSpecialty_eq_of_genusReached hD₀ D).2

theorem gate_riemannInequality_of_genusReached [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) (D : Divisor K F) :
    Divisor.degree D + 1 - γ ≤ (ell D : ℤ) := by
  have heq := (indexOfSpecialty_eq_of_genusReached h D).2
  have hnn : (0 : ℤ) ≤ indexOfSpecialty D := Int.natCast_nonneg _
  linarith

end AlgebraicCurve


end


end


end


section
section

noncomputable section

open _root_.Module
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module
open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic)

open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem adeleSpaceMul_add [HasPrincipalDivisors K F] (f g : F) :
    adeleSpaceMul K F (f + g) = adeleSpaceMul K F f + adeleSpaceMul K F g := by
  refine LinearMap.ext fun α => Subtype.ext (funext fun v => ?_)
  simp only [adeleSpaceMul_coe, mulAdele_apply, LinearMap.add_apply, Submodule.coe_add,
    Pi.add_apply, add_mul]

theorem adeleSpaceMul_zero [HasPrincipalDivisors K F] :
    adeleSpaceMul K F (0 : F) = 0 := by
  refine LinearMap.ext fun α => Subtype.ext (funext fun v => ?_)
  simp only [adeleSpaceMul_coe, mulAdele_apply, zero_mul, LinearMap.zero_apply,
    Submodule.coe_zero, Pi.zero_apply]

theorem weilSmul_add_left [HasPrincipalDivisors K F] (f g : F)
    (φ : Module.Dual K (adeleSpace K F)) :
    weilSmul K F (f + g) φ = weilSmul K F f φ + weilSmul K F g φ := by
  ext α
  simp only [weilSmul_apply, adeleSpaceMul_add, LinearMap.add_apply, map_add]

theorem weilSmul_zero_left [HasPrincipalDivisors K F]
    (φ : Module.Dual K (adeleSpace K F)) :
    weilSmul K F (0 : F) φ = 0 := by
  ext α
  simp only [weilSmul_apply, adeleSpaceMul_zero, LinearMap.zero_apply, _root_.map_zero]

theorem weilSmul_neg_left [HasPrincipalDivisors K F] (f : F)
    (φ : Module.Dual K (adeleSpace K F)) :
    weilSmul K F (-f) φ = -weilSmul K F f φ := by
  have h := weilSmul_add_left (K := K) (F := F) f (-f) φ
  rw [add_neg_cancel, weilSmul_zero_left] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

theorem weilSmul_sub_left [HasPrincipalDivisors K F] (f g : F)
    (φ : Module.Dual K (adeleSpace K F)) :
    weilSmul K F (f - g) φ = weilSmul K F f φ - weilSmul K F g φ := by
  rw [sub_eq_add_neg, weilSmul_add_left, weilSmul_neg_left, sub_eq_add_neg]

theorem weilSmul_eq_zero_iff_left [HasPrincipalDivisors K F]
    {f : F} {φ : Module.Dual K (adeleSpace K F)} (hφ : φ ≠ 0) :
    weilSmul K F f φ = 0 ↔ f = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ weilSmul_zero_left φ⟩
  by_contra hf
  exact hφ (weilSmul_injective hf (h.trans (_root_.map_zero (weilSmul K F f)).symm))

theorem weilSmul_left_injective [HasPrincipalDivisors K F]
    {φ : Module.Dual K (adeleSpace K F)} (hφ : φ ≠ 0) :
    Function.Injective (fun f : F => weilSmul K F f φ) := by
  intro f g hfg
  have hsub : weilSmul K F (f - g) φ = 0 := by
    rw [weilSmul_sub_left, sub_eq_zero]; exact hfg
  exact sub_eq_zero.mp ((weilSmul_eq_zero_iff_left hφ).mp hsub)

variable (K F) in

def doubleResiduePairing [HasPrincipalDivisors K F] (W D : Divisor K F)
    {φ μ : Module.Dual K (adeleSpace K F)}
    (hφ : φ ∈ omegaSpace W) (hμ : μ ∈ omegaSpace W) :
    LSpace (W - D) × LSpace (W - D) →ₗ[K] omegaSpace D :=
  (residuePairing K F W D hφ).coprod (residuePairing K F W D hμ)

theorem doubleResiduePairing_apply_coe [HasPrincipalDivisors K F] (W D : Divisor K F)
    {φ μ : Module.Dual K (adeleSpace K F)}
    (hφ : φ ∈ omegaSpace W) (hμ : μ ∈ omegaSpace W) (g h : LSpace (W - D)) :
    (doubleResiduePairing K F W D hφ hμ (g, h) : Module.Dual K (adeleSpace K F))
      = weilSmul K F (g : F) φ + weilSmul K F (h : F) μ := by
  simp only [doubleResiduePairing, LinearMap.coprod_apply, Submodule.coe_add,
    residuePairing_apply_coe]

theorem doubleResiduePairing_injective [HasPrincipalDivisors K F] (W D : Divisor K F)
    {φ μ : Module.Dual K (adeleSpace K F)}
    (hφ : φ ∈ omegaSpace W) (hμ : μ ∈ omegaSpace W)
    (hφ0 : φ ≠ 0) (hindep : ∀ f : F, μ ≠ weilSmul K F f φ) :
    Function.Injective (doubleResiduePairing K F W D hφ hμ) := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨g, h⟩ heq

  have heq' : weilSmul K F (g : F) φ + weilSmul K F (h : F) μ = 0 := by
    have hcoe := congrArg Subtype.val heq
    rwa [doubleResiduePairing_apply_coe, Submodule.coe_zero] at hcoe

  rcases eq_or_ne (h : F) 0 with hh0 | hh0
  ·
    rw [hh0, weilSmul_zero_left, add_zero] at heq'
    have hg0 : (g : F) = 0 := (weilSmul_eq_zero_iff_left hφ0).mp heq'
    exact Prod.ext (Subtype.ext hg0) (Subtype.ext hh0)
  ·
    exfalso

    have hμeq : weilSmul K F (h : F) μ = -weilSmul K F (g : F) φ := by
      have h2 : weilSmul K F (h : F) μ + weilSmul K F (g : F) φ = 0 := by
        rw [add_comm]; exact heq'
      exact eq_neg_of_add_eq_zero_left h2

    have hLHS : weilSmul K F (h : F)⁻¹ (weilSmul K F (h : F) μ) = μ := by
      rw [← LinearMap.comp_apply, ← weilSmul_mul, mul_inv_cancel₀ hh0, weilSmul_one,
        LinearMap.id_apply]
    have hRHS : weilSmul K F (h : F)⁻¹ (-weilSmul K F (g : F) φ)
        = weilSmul K F (-(g : F) * (h : F)⁻¹) φ := by
      rw [_root_.map_neg, ← LinearMap.comp_apply, ← weilSmul_mul, neg_mul, weilSmul_neg_left]
    exact hindep (-(g : F) * (h : F)⁻¹) (by rw [← hLHS, hμeq, hRHS])

theorem two_mul_ell_le_indexOfSpecialty [HasPrincipalDivisors K F] (W D : Divisor K F)
    {φ μ : Module.Dual K (adeleSpace K F)}
    (hφ : φ ∈ omegaSpace W) (hμ : μ ∈ omegaSpace W)
    (hφ0 : φ ≠ 0) (hindep : ∀ f : F, μ ≠ weilSmul K F f φ)
    [Module.Finite K (omegaSpace (K := K) (F := F) D)]
    [Module.Finite K (LSpace (K := K) (F := F) (W - D))] :
    2 * ell (W - D) ≤ indexOfSpecialty D := by
  have hinj := doubleResiduePairing_injective W D hφ hμ hφ0 hindep
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_prod] at hle
  rw [← finrank_omegaSpace_eq_indexOfSpecialty, two_mul]
  exact hle

theorem degree_add_one_sub_genus_le_ell_of_riemannIndexFormula
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    (hRI : RiemannIndexFormula K F) (D : Divisor K F) :
    Divisor.degree D + 1 - (genus K F : ℤ) ≤ (ell D : ℤ) := by
  have hi := hRI D
  have hi0 : (0 : ℤ) ≤ (indexOfSpecialty D : ℤ) := Int.natCast_nonneg _
  linarith

theorem omegaSpace_finite_of_riemannIndexFormula
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    (hRI : RiemannIndexFormula K F) {D : Divisor K F}
    (hpos : 0 < (ell D : ℤ) - Divisor.degree D - 1 + (genus K F : ℤ)) :
    Module.Finite K (omegaSpace (K := K) (F := F) D) := by

  have h0 : 0 < finrank K (adeleSpace K F ⧸ adeleBddPrincipal K F D) := by
    rw [← indexOfSpecialty_eq]
    have hi := hRI D
    have h0' : (0 : ℤ) < (indexOfSpecialty D : ℤ) := by linarith
    exact_mod_cast h0'
  haveI : Module.Finite K (adeleSpace K F ⧸ adeleBddPrincipal K F D) :=
    FiniteDimensional.of_finrank_pos h0
  exact Module.Finite.equiv (omegaSpaceEquivIndexDual D).symm

theorem lSpace_finite_of_riemannIndexFormula
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    (hRI : RiemannIndexFormula K F) {D : Divisor K F}
    (hpos : 0 < Divisor.degree D + 1 - (genus K F : ℤ)) :
    Module.Finite K (LSpace (K := K) (F := F) D) := by
  have h0 : (0 : ℤ) < (ell D : ℤ) :=
    lt_of_lt_of_le hpos (degree_add_one_sub_genus_le_ell_of_riemannIndexFormula hRI D)
  exact FiniteDimensional.of_finrank_pos (by exact_mod_cast h0)

theorem exists_weilSmul_eq_of_riemannIndexFormula
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)] [Nonempty (Place K F)]
    (hRI : RiemannIndexFormula K F)
    {φ μ : Module.Dual K (adeleSpace K F)} {W : Divisor K F}
    (hφ : φ ∈ omegaSpace W) (hμ : μ ∈ omegaSpace W) (hφ0 : φ ≠ 0) :
    ∃ f : F, μ = weilSmul K F f φ := by
  by_contra hcon
  push Not at hcon

  obtain ⟨P⟩ := ‹Nonempty (Place K F)›
  set n : ℕ := 3 * genus K F + 2 * (Divisor.degree W).natAbs + 4 with hn

  set D : Divisor K F := -Finsupp.single P (n : ℤ) with hD
  have hdegD : Divisor.degree D = -(n : ℤ) * (P.deg : ℤ) := by
    rw [hD, _root_.map_neg, Divisor.degree_single]; ring
  have hdegWD : Divisor.degree (W - D) = Divisor.degree W + (n : ℤ) * (P.deg : ℤ) := by
    rw [map_sub, hdegD]; ring
  have hPdeg1 : 1 ≤ (P.deg : ℤ) := by exact_mod_cast one_le_deg P

  have hg0 : (0 : ℤ) ≤ (genus K F : ℤ) := Int.natCast_nonneg _
  have habs0 : (0 : ℤ) ≤ |Divisor.degree W| := abs_nonneg _
  have habsW : -|Divisor.degree W| ≤ Divisor.degree W := neg_abs_le _
  have habsW' : Divisor.degree W ≤ |Divisor.degree W| := le_abs_self _

  have hn_ge : 3 * (genus K F : ℤ) + 2 * |Divisor.degree W| + 4 ≤ (n : ℤ) := by
    rw [hn]; push_cast [Int.natCast_natAbs]; ring_nf; omega
  have hndegP : (n : ℤ) ≤ (n : ℤ) * (P.deg : ℤ) := by
    nlinarith [Int.natCast_nonneg n]
  have hndegP_pos : 0 < (n : ℤ) * (P.deg : ℤ) := by nlinarith

  have hellD : ell D = 0 := ell_eq_zero_of_degree_neg (by rw [hdegD]; linarith)

  have hiD : (indexOfSpecialty D : ℤ) = (n : ℤ) * (P.deg : ℤ) - 1 + (genus K F : ℤ) := by
    have h := hRI D
    rw [hellD, hdegD] at h; push_cast at h; linarith

  have hlowerWD : Divisor.degree W + (n : ℤ) * (P.deg : ℤ) + 1 - (genus K F : ℤ)
      ≤ (ell (W - D) : ℤ) := by
    have h := degree_add_one_sub_genus_le_ell_of_riemannIndexFormula hRI (W - D)
    rw [hdegWD] at h; exact h

  have hiDpos : 0 < (ell D : ℤ) - Divisor.degree D - 1 + (genus K F : ℤ) := by
    rw [hellD, hdegD]; push_cast; nlinarith
  have hellWDpos : 0 < Divisor.degree (W - D) + 1 - (genus K F : ℤ) := by
    rw [hdegWD]; nlinarith
  haveI := omegaSpace_finite_of_riemannIndexFormula hRI hiDpos
  haveI := lSpace_finite_of_riemannIndexFormula hRI hellWDpos

  have hdbl : (2 * ell (W - D) : ℤ) ≤ (indexOfSpecialty D : ℤ) := by
    exact_mod_cast two_mul_ell_le_indexOfSpecialty W D hφ hμ hφ0 hcon

  rw [hiD] at hdbl
  nlinarith

theorem weilDifferentialRankOne_of_riemannIndexFormula
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)] [Nonempty (Place K F)]
    (hRI : RiemannIndexFormula K F) :
    WeilDifferentialRankOne K F := by
  intro φ hφmem hφ0 μ hμmem

  obtain ⟨W₁, hφW₁⟩ := mem_weilDifferentialModule_iff.mp hφmem
  obtain ⟨W₂, hμW₂⟩ := mem_weilDifferentialModule_iff.mp hμmem
  have hφW : φ ∈ omegaSpace (W₁ ⊓ W₂) := omegaSpace_antitone inf_le_left hφW₁
  have hμW : μ ∈ omegaSpace (W₁ ⊓ W₂) := omegaSpace_antitone inf_le_right hμW₂

  obtain ⟨f, hf⟩ := exists_weilSmul_eq_of_riemannIndexFormula hRI hφW hμW hφ0
  exact ⟨f, hf, fun f' hf' => weilSmul_left_injective hφ0 (hf'.symm.trans hf)⟩

end AlgebraicCurve


section AxiomAudit

end AxiomAudit


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
open _root_.Module
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsLocalRing
open _root_.Module.IsLocalRing
namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic)

open _root_.AlgebraicCurve
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [HasCanonicalLocalResidueKStar K F]
variable [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
  [Nontrivial Ω[F⁄K]]
variable (K F)
variable {K F}
variable (K F)
variable {K F}
variable (K F)

def ResiduePairingSurjective : Prop :=
  ∀ [HasPrincipalDivisors K F] (W D : Divisor K F)
    {φ : Module.Dual K (adeleSpace K F)} (hφ : φ ∈ omegaSpace W) (_hφ0 : φ ≠ 0)
    (_hWmax : ∀ E : Divisor K F, φ ∈ omegaSpace E → E ≤ W),
    Function.Surjective (residuePairing K F W D hφ)
end AlgebraicCurve

end


end


end


section
section

noncomputable section

open _root_.Module
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module
open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic)

open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

section Finiteness

variable [IsCurveOver K F] [Nonempty (Place K F)]
  [FiniteDimensional K (LSpace (0 : Divisor K F))]

theorem omegaSpace_finite_of_genusReached
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) (D : Divisor K F) :
    Module.Finite K (omegaSpace (K := K) (F := F) D) := by
  haveI := (indexOfSpecialty_eq_of_genusReached h D).1
  exact Module.Finite.equiv (omegaSpaceEquivIndexDual D).symm

end Finiteness


section ParametricRankOne

variable [IsCurveOver K F] [Nonempty (Place K F)]
  [FiniteDimensional K (LSpace (0 : Divisor K F))]

set_option maxHeartbeats 2400000 in

theorem exists_weilSmul_eq_of_genusReached
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    {φ μ : Module.Dual K (adeleSpace K F)} {W : Divisor K F}
    (hφ : φ ∈ omegaSpace W) (hμ : μ ∈ omegaSpace W) (hφ0 : φ ≠ 0) :
    ∃ f : F, μ = weilSmul K F f φ := by
  by_contra hcon
  push Not at hcon

  obtain ⟨P⟩ := ‹Nonempty (Place K F)›
  set n : ℕ := 3 * γ.natAbs + 2 * (Divisor.degree W).natAbs + 4 with hn
  set D : Divisor K F := -Finsupp.single P (n : ℤ) with hD
  have hdegD : Divisor.degree D = -(n : ℤ) * (P.deg : ℤ) := by
    rw [hD, _root_.map_neg, Divisor.degree_single]; ring
  have hdegWD : Divisor.degree (W - D) = Divisor.degree W + (n : ℤ) * (P.deg : ℤ) := by
    rw [map_sub, hdegD]; ring
  have hPdeg1 : 1 ≤ (P.deg : ℤ) := by exact_mod_cast one_le_deg P
  have habsγ : -(|γ|) ≤ γ ∧ γ ≤ |γ| := ⟨neg_abs_le _, le_abs_self _⟩
  have habsW : -|Divisor.degree W| ≤ Divisor.degree W ∧
      Divisor.degree W ≤ |Divisor.degree W| := ⟨neg_abs_le _, le_abs_self _⟩
  have hn_ge : 3 * |γ| + 2 * |Divisor.degree W| + 4 ≤ (n : ℤ) := by
    rw [hn]; push_cast [Int.natCast_natAbs]; ring_nf; omega
  have hndegP : (n : ℤ) ≤ (n : ℤ) * (P.deg : ℤ) := by nlinarith [Int.natCast_nonneg n]

  have hellD : ell D = 0 := ell_eq_zero_of_degree_neg (by rw [hdegD]; nlinarith)

  have hiD : (indexOfSpecialty D : ℤ) = (n : ℤ) * (P.deg : ℤ) - 1 + γ := by
    have hidx := (indexOfSpecialty_eq_of_genusReached h D).2
    rw [hellD, hdegD] at hidx; push_cast at hidx; linarith

  have hlowerWD : Divisor.degree W + (n : ℤ) * (P.deg : ℤ) + 1 - γ
      ≤ (ell (W - D) : ℤ) := by
    have hlow := gate_riemannInequality_of_genusReached h (W - D)
    rw [hdegWD] at hlow; exact hlow

  haveI := omegaSpace_finite_of_genusReached h D
  haveI := finiteDimensional_lSpace (K := K) (W - D)

  have hdbl : (2 * ell (W - D) : ℤ) ≤ (indexOfSpecialty D : ℤ) := by
    exact_mod_cast two_mul_ell_le_indexOfSpecialty W D hφ hμ hφ0 hcon
  rw [hiD] at hdbl
  nlinarith [habsγ.1, habsγ.2, habsW.1, habsW.2]

theorem weilDifferentialRankOne_of_genusReached
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) :
    WeilDifferentialRankOne K F := by
  intro φ hφmem hφ0 μ hμmem
  obtain ⟨W₁, hφW₁⟩ := mem_weilDifferentialModule_iff.mp hφmem
  obtain ⟨W₂, hμW₂⟩ := mem_weilDifferentialModule_iff.mp hμmem
  have hφW : φ ∈ omegaSpace (W₁ ⊓ W₂) := omegaSpace_antitone inf_le_left hφW₁
  have hμW : μ ∈ omegaSpace (W₁ ⊓ W₂) := omegaSpace_antitone inf_le_right hμW₂
  obtain ⟨f, hf⟩ := exists_weilSmul_eq_of_genusReached h hφW hμW hφ0
  exact ⟨f, hf, fun f' hf' => weilSmul_left_injective hφ0 (hf'.symm.trans hf)⟩

end ParametricRankOne


theorem residuePairing_surjective_of_rankOne_max [HasPrincipalDivisors K F]
    (hRankOne : WeilDifferentialRankOne K F)
    {W : Divisor K F} {φ : Module.Dual K (adeleSpace K F)}
    (hφ : φ ∈ omegaSpace W) (hφ0 : φ ≠ 0)
    (hWmax : ∀ E : Divisor K F, φ ∈ omegaSpace E → E ≤ W) (D : Divisor K F) :
    Function.Surjective (residuePairing K F W D hφ) := by
  rintro ⟨μ, hμD⟩
  have hφmem : φ ∈ weilDifferentialModule K F := omegaSpace_le_weilDifferentialModule W hφ
  have hμmem : μ ∈ weilDifferentialModule K F := omegaSpace_le_weilDifferentialModule D hμD
  obtain ⟨f, hf, -⟩ := hRankOne hφmem hφ0 hμmem
  rcases eq_or_ne f 0 with rfl | hf0
  ·
    have hμ0 : (⟨μ, hμD⟩ : omegaSpace D) = 0 :=
      Subtype.ext (hf.trans (weilSmul_zero_left φ))
    exact ⟨0, (_root_.map_zero _).trans hμ0.symm⟩
  ·

    obtain ⟨P, hPord, _⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0
    have hPinv : ∀ v, (-P) v = v.ord f⁻¹ := fun v => by
      rw [Finsupp.neg_apply, hPord v, v.ord_inv]
    have hinv : weilSmul K F f⁻¹ μ = φ := by
      rw [hf, ← LinearMap.comp_apply, ← weilSmul_mul, mul_inv_cancel₀ hf0, weilSmul_one,
        LinearMap.id_apply]
    have hφD : φ ∈ omegaSpace (D + -P) := by
      rw [← hinv]; exact weilSmul_mem_omegaSpace_add (inv_ne_zero hf0) hPinv hμD
    have hDP : D + -P ≤ W := hWmax _ hφD
    have hfL : f ∈ LSpace (W - D) := by
      rw [mem_lSpace_iff_ord]; refine Or.inr fun v => ?_
      have hv := hDP v
      rw [Finsupp.add_apply, Finsupp.neg_apply, hPord v] at hv
      rw [Finsupp.sub_apply]; linarith
    exact ⟨⟨f, hfL⟩, Subtype.ext hf.symm⟩

section Identification

variable [IsCurveOver K F] [Nonempty (Place K F)]
  [FiniteDimensional K (LSpace (0 : Divisor K F))]
  [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
  [HasCanonicalLocalResidueKStar K F]

omit [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
  [HasCanonicalLocalResidueKStar K F] in

theorem stichtenothGenus_nonneg
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    (hC : ConstantsAreBase K F) : 0 ≤ γ := by
  have hi0 := (indexOfSpecialty_eq_of_genusReached h 0).2
  rw [_root_.map_zero, ell_zero_eq_one_of_constantsAreBase hC] at hi0
  have h0 : (0 : ℤ) ≤ (indexOfSpecialty (0 : Divisor K F) : ℤ) := Int.natCast_nonneg _
  push_cast at hi0; linarith

omit [Nonempty (Place K F)] [FiniteDimensional K (LSpace (0 : Divisor K F))]
  [∀ v : Place K F, v.DCoordGenerates] [HasCanonicalLocalResidueKStar K F] in

theorem genus_eq_degree_div :
    ∃ (ω₀ : Ω[F⁄K]) (hω₀ : ω₀ ≠ 0),
      genus K F = (Divisor.degree (canonicalDivisorOf hω₀) + 2).toNat / 2 := by
  have hne : ∃ ω : Ω[F⁄K], ω ≠ 0 := exists_ne 0
  refine ⟨hne.choose, hne.choose_spec, ?_⟩
  rw [genus, dif_pos hne]

end Identification


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

theorem _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.uniformizer_pow_inv_mem_poleSubmodule_self (m : ℕ) :
    (v.uniformizer ^ (m + 2))⁻¹ ∈ v.poleSubmodule (m + 2) :=
  (gate_poleSubmodule_strictMono v (m + 1)).1




theorem _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.higherPoleMonomial_sum_mem_poleSubmodule {s : Finset ℕ} {N : ℕ}
    (hs : ∀ m ∈ s, m < N) (c : ℕ → K) :
    ∑ m ∈ s, c m • (v.uniformizer ^ (m + 2))⁻¹ ∈ v.poleSubmodule (N + 1) :=
  Submodule.sum_mem _ fun m hm =>
    Submodule.smul_mem _ _ <|
      v.poleSubmodule_mono (by have := hs m hm; omega)
        (v.uniformizer_pow_inv_mem_poleSubmodule_self m)




theorem _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.higherPoleMonomial_coeff_eq_zero_of_mem (s : Finset ℕ) (c : ℕ → K)
    (hmem : ∑ m ∈ s, c m • (v.uniformizer ^ (m + 2))⁻¹ ∈ v.poleSubmodule 1) :
    ∀ m ∈ s, c m = 0 := by
  induction s using Finset.induction_on_max with
  | empty => intro m hm; exact absurd hm (Finset.notMem_empty m)
  | insert N s hN ih =>
    have hNs : N ∉ s := fun h => absurd (hN N h) (lt_irrefl N)
    rw [Finset.sum_insert hNs] at hmem

    have hrest : ∑ m ∈ s, c m • (v.uniformizer ^ (m + 2))⁻¹ ∈ v.poleSubmodule (N + 1) :=
      v.higherPoleMonomial_sum_mem_poleSubmodule hN c

    have hwhole := v.poleSubmodule_mono (Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero N)) hmem

    have htop : c N • (v.uniformizer ^ (N + 2))⁻¹ ∈ v.poleSubmodule (N + 1) := by
      have hsub := (v.poleSubmodule (N + 1)).sub_mem hwhole hrest
      rwa [add_sub_cancel_right] at hsub

    have hcN : c N = 0 := by
      by_contra hcN
      exact (gate_poleSubmodule_strictMono v (N + 1)).2 <|
        (inv_smul_smul₀ hcN ((v.uniformizer ^ (N + 2))⁻¹)) ▸
          (v.poleSubmodule (N + 1)).smul_mem (c N)⁻¹ htop

    intro m hm
    rcases Finset.mem_insert.mp hm with rfl | hm'
    · exact hcN
    · refine ih ?_ m hm'
      rwa [hcN, zero_smul, zero_add] at hmem




theorem _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.linearIndependent_higherPoleMonomial_mkQ :
    LinearIndependent K
      (fun m : ℕ => (v.poleSubmodule 1).mkQ ((v.uniformizer ^ (m + 2))⁻¹)) := by
  rw [linearIndependent_iff']
  intro s c hsum m hm
  refine v.higherPoleMonomial_coeff_eq_zero_of_mem s c ?_ m hm
  have h := hsum
  simp only [← map_smul, ← map_sum] at h
  rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h




def _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.higherPoleCorrectionAux :
    Submodule.span K
        (Set.range fun m : ℕ => (v.poleSubmodule 1).mkQ ((v.uniformizer ^ (m + 2))⁻¹))
      →ₗ[K] v.ResidueField :=
  (Basis.span v.linearIndependent_higherPoleMonomial_mkQ).constr K
    (fun m => v.localResidueExtend ((v.uniformizer ^ (m + 2))⁻¹))




def _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.higherPoleCorrection : F →ₗ[K] v.ResidueField :=
  v.higherPoleCorrectionAux.exists_extend.choose ∘ₗ (v.poleSubmodule 1).mkQ




theorem _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.higherPoleCorrection_apply_of_mem {f : F} (hf : f ∈ v.poleSubmodule 1) :
    v.higherPoleCorrection f = 0 := by
  unfold higherPoleCorrection
  rw [LinearMap.comp_apply, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).mpr hf,
    _root_.map_zero]




theorem _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.higherPoleCorrection_uniformizer_pow_inv (m : ℕ) :
    v.higherPoleCorrection ((v.uniformizer ^ (m + 2))⁻¹)
      = v.localResidueExtend ((v.uniformizer ^ (m + 2))⁻¹) := by

  have hmem : (v.poleSubmodule 1).mkQ ((v.uniformizer ^ (m + 2))⁻¹)
      ∈ Submodule.span K
          (Set.range fun m : ℕ => (v.poleSubmodule 1).mkQ ((v.uniformizer ^ (m + 2))⁻¹)) :=
    Submodule.subset_span ⟨m, rfl⟩
  have hext := DFunLike.congr_fun v.higherPoleCorrectionAux.exists_extend.choose_spec
    ⟨(v.poleSubmodule 1).mkQ ((v.uniformizer ^ (m + 2))⁻¹), hmem⟩

  refine hext.trans ?_

  unfold higherPoleCorrectionAux
  have hb := (Basis.span v.linearIndependent_higherPoleMonomial_mkQ).constr_basis K
    (fun m => v.localResidueExtend ((v.uniformizer ^ (m + 2))⁻¹)) m
  rwa [Basis.span_apply] at hb




def _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.canonicalLocalResidueDataKOfExtend : v.CanonicalLocalResidueDataK where
  res := v.localResidueExtend - v.higherPoleCorrection
  res_of_mem f hf := by
    have h1 : f ∈ v.poleSubmodule 1 :=
      v.poleSubmodule_one ▸ v.mem_simplePoleSubmodule_of_mem hf
    rw [LinearMap.sub_apply, v.higherPoleCorrection_apply_of_mem h1, sub_zero,
      v.localResidueExtend_apply_of_mem (v.mem_simplePoleSubmodule_of_mem hf),
      v.simplePoleResidueAux_eq_zero_of_mem hf]
  res_simplePole f hf := by
    have h1 : f ∈ v.poleSubmodule 1 := v.poleSubmodule_one ▸ hf
    rw [LinearMap.sub_apply, v.higherPoleCorrection_apply_of_mem h1, sub_zero,
      v.localResidueExtend_apply_of_mem hf, simplePoleResidueAux_apply]
  res_higherPoleMonomial n hn := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [show 1 + m + 1 = m + 2 from by omega, LinearMap.sub_apply,
      v.higherPoleCorrection_uniformizer_pow_inv m, sub_self]




end Place


namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_coe_eq_one_iff ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ofHeightOneSpectrum mk.injEq rec ne_top' algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict mem_restrict_iff ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg fiber mem_fiber mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one DCoordGenerates differentialCoeff ordDifferential uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero)

open _root_.AlgebraicCurve.Place

variable (v : Place K F)

end Place


end AlgebraicCurve


section AxiomAudit

end AxiomAudit


end


end


end

end P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed
