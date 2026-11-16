/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicCurve_Place_exists_not_mem_and_forall_ne_mem. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_one_le_deg
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicCurve_Place_exists_not_mem_and_forall_ne_mem
open AlgebraicCurve
open P2MW.S_AlgebraicCurve_Place_exists_not_mem_and_forall_ne_mem.AlgebraicCurve

namespace AlgebraicCurve
export AlgebraicCurve (Place Divisor Divisor.degree Divisor.degree_single IsCurveOver LSpace ell ConstantsAreBase ell_zero_eq_one_of_constantsAreBase stichtenothGenusExists_of_isCurveOver one_le_deg)
namespace Place
export AlgebraicCurve.Place (deg heightOneSpectrum heightOneSpectrum_asIdeal adicValuation adicValuation_ne_zero adicValuation_coe toValuationSubring adicValuation_le_one_of_mem)
open AlgebraicCurve.Place
open AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem _root_.AlgebraicCurve.Place.adicValuation_le_one_iff_mem (v : Place K F) {f : F} :
    v.adicValuation f ≤ 1 ↔ f ∈ v.toValuationSubring := by
  refine ⟨fun h => ?_, v.adicValuation_le_one_of_mem⟩
  by_contra hf
  have hf0 : f ≠ 0 := fun h0 => hf (h0 ▸ v.toValuationSubring.zero_mem)
  have hinv : f⁻¹ ∈ v.toValuationSubring :=
    (v.toValuationSubring.mem_or_inv_mem f).resolve_left hf

  have hmax : (⟨f⁻¹, hinv⟩ : v.toValuationSubring) ∈
      IsLocalRing.maximalIdeal v.toValuationSubring := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    apply hf
    have h1 : (((u⁻¹ : (v.toValuationSubring)ˣ) : v.toValuationSubring) : F) * f⁻¹ = 1 := by
      have h := congrArg (fun a : v.toValuationSubring => (a : F)) u.inv_mul
      simpa [hu] using h
    have h2 : (((u⁻¹ : (v.toValuationSubring)ˣ) : v.toValuationSubring) : F) = f := by
      rw [eq_inv_of_mul_eq_one_left h1, inv_inv]
    rw [← h2]
    exact SetLike.coe_mem _

  have hlt : v.adicValuation f⁻¹ < 1 := by
    have := (IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem v.heightOneSpectrum
      (⟨f⁻¹, hinv⟩ : v.toValuationSubring)).mpr (by rwa [heightOneSpectrum_asIdeal])
    rwa [← v.adicValuation_coe] at this
  rw [map_inv₀] at hlt
  have hpos : 0 < v.adicValuation f := zero_lt_iff.mpr (v.adicValuation_ne_zero hf0)
  have : 1 < v.adicValuation f := (inv_lt_one₀ hpos).mp hlt
  exact absurd h (not_le.mpr this)
export AlgebraicCurve.Place (adicValuation_le_one_iff_mem)
end AlgebraicCurve.Place
open AlgebraicCurve
open P2MW.S_AlgebraicCurve_Place_exists_not_mem_and_forall_ne_mem.AlgebraicCurve
open AlgebraicCurve.Place
open P2MW.S_AlgebraicCurve_Place_exists_not_mem_and_forall_ne_mem.AlgebraicCurve.Place

theorem solution
    {K F : Type*} [Field K] [PerfectField K] [Field F] [Algebra K F]
    [AlgebraicCurve.IsCurveOver K F] [Algebra.EssFiniteType K F]
    (hC : AlgebraicCurve.ConstantsAreBase K F) (v : AlgebraicCurve.Place K F) :
    ∃ f : F, f ∉ v.toValuationSubring ∧
      ∀ w : AlgebraicCurve.Place K F, w ≠ v → f ∈ w.toValuationSubring := by
  classical
  obtain ⟨_, hfin0, γ, D₀, hR⟩ :=
    AlgebraicCurve.stichtenothGenusExists_of_isCurveOver (K := K) (F := F) hC

  set n : ℕ := γ.toNat + 1 with hn
  set D : Divisor K F := Finsupp.single v (n : ℤ) with hD
  have hdeg : Divisor.degree D = (n : ℤ) * v.deg := Divisor.degree_single v n
  have hvdeg : (1 : ℤ) ≤ v.deg := by exact_mod_cast AlgebraicCurve.one_le_deg v
  have hmax := hR.isMax D
  have hnγ : γ + 1 ≤ (n : ℤ) := by
    have := Int.self_le_toNat γ
    simp only [hn]; push_cast; omega
  have hell : (2 : ℤ) ≤ (ell D : ℤ) := by
    have : (n : ℤ) ≤ Divisor.degree D := by rw [hdeg]; nlinarith
    linarith
  have hell0 : ell (0 : Divisor K F) = 1 := ell_zero_eq_one_of_constantsAreBase hC

  have hnot : ¬ (LSpace D ≤ LSpace (0 : Divisor K F)) := by
    intro hle
    haveI := hfin0
    have hle' : Module.finrank K (LSpace D) ≤ Module.finrank K (LSpace (0 : Divisor K F)) :=
      LinearMap.finrank_le_finrank_of_injective (f := Submodule.inclusion hle)
        (Submodule.inclusion_injective hle)
    have : (ell D : ℤ) ≤ (ell (0 : Divisor K F) : ℤ) := by exact_mod_cast hle'
    rw [hell0] at this
    push_cast at this
    linarith
  obtain ⟨f, hfD, hf0⟩ := Set.not_subset.mp hnot
  have hfD' : f ∈ LSpace D := hfD
  refine ⟨f, ?_, ?_⟩
  ·
    intro hfv
    apply hf0
    show f ∈ LSpace (0 : Divisor K F)
    intro w
    rw [Finsupp.coe_zero, Pi.zero_apply, WithZero.exp_zero]
    by_cases hw : w = v
    · subst hw; exact w.adicValuation_le_one_of_mem hfv
    · have h := hfD' w
      have hDw : D w = 0 := by rw [hD, Finsupp.single_apply, if_neg (Ne.symm hw)]
      rwa [hDw, WithZero.exp_zero] at h
  · intro w hw
    have h := hfD' w
    have hDw : D w = 0 := by rw [hD, Finsupp.single_apply, if_neg (Ne.symm hw)]
    rw [hDw, WithZero.exp_zero] at h
    exact (w.adicValuation_le_one_iff_mem).mp h
