/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_Pic0_exists_nsmul_eq (git blob 1e25f735edcd54d05e08dd4b224e7a6c62c50e8c, sha256 8c081a339ff3ee42371fd9a072dad43c0060064481830304018774ad44b6dada).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_exists_natCast_dvd_ord_sub_single_sub_single

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace AlgebraicCurve
end AlgebraicCurve
namespace P2MW.S_AlgebraicCurve_Pic0_exists_nsmul_eq.AlgebraicCurve
end P2MW.S_AlgebraicCurve_Pic0_exists_nsmul_eq.AlgebraicCurve
namespace AlgebraicCurve.Pic0
end AlgebraicCurve.Pic0

namespace P2MW.S_AlgebraicCurve_Pic0_exists_nsmul_eq

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_Pic0_exists_nsmul_eq.AlgebraicCurve

namespace AlgebraicCurve
export _root_.AlgebraicCurve (Place Divisor Divisor.degree Divisor.degree_single Divisor.degZero Divisor.mem_degZero Divisor.principal HasPrincipalDivisors Pic Pic0 Pic0.mk Pic0.mk_surjective Pic0.mk_zero HasPrincipalDivisors.exists_divisor IsCurveOver IsCurveOver.hasPrincipalDivisors IsCurveOver.deg_eq_one_of_isAlgClosed Place.exists_natCast_dvd_ord_sub_single_sub_single)
namespace Pic0
export _root_.AlgebraicCurve.Pic0 (mk mk_surjective mk_zero torsion)
namespace DivisibleReduction
open _root_.AlgebraicCurve.Pic0
open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

def nMulModPrincipal (K F : Type*) [Field K] [Field F] [Algebra K F] (n : ℕ) :
    AddSubgroup (Divisor K F) where
  carrier := {D | ∃ E : Divisor K F, D - n • E ∈ Divisor.principal (K := K) (F := F)}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro D D' ⟨E, hE⟩ ⟨E', hE'⟩
    refine ⟨E + E', ?_⟩
    have h := add_mem hE hE'
    convert h using 1
    simp only [smul_add]
    abel
  neg_mem' := by
    rintro D ⟨E, hE⟩
    refine ⟨-E, ?_⟩
    have h := neg_mem hE
    convert h using 1
    simp only [smul_neg]
    abel

theorem mem_nMulModPrincipal {n : ℕ} {D : Divisor K F} :
    D ∈ nMulModPrincipal K F n ↔ ∃ E : Divisor K F, D - n • E ∈ Divisor.principal (K := K) (F := F) :=
  Iff.rfl

theorem degree_eq_zero_of_mem_principal [HasPrincipalDivisors K F] {D : Divisor K F}
    (hD : D ∈ Divisor.principal (K := K) (F := F)) : Divisor.degree D = 0 := by
  obtain ⟨f, hf, hDf⟩ := hD
  obtain ⟨D', hD', hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf
  have : D = D' := Finsupp.ext fun v => by rw [hDf v, hD' v]
  rw [this, hdeg]

theorem single_sub_single_mem [HasPrincipalDivisors K F] {n : ℕ} (P Q : Place K F)
    (h : ∃ f : F, f ≠ 0 ∧ ∀ v : Place K F,
      (n : ℤ) ∣ v.ord f - (Finsupp.single P 1 - Finsupp.single Q 1 : Divisor K F) v) :
    (Finsupp.single P 1 - Finsupp.single Q 1 : Divisor K F) ∈ nMulModPrincipal K F n := by
  obtain ⟨f, hf, hcong⟩ := h
  obtain ⟨Df, hDf, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf
  set A : Divisor K F := Finsupp.single P 1 - Finsupp.single Q 1 with hA
  have hdvd : ∀ v, (n : ℤ) ∣ (A - Df) v := fun v => by
    rw [Finsupp.sub_apply, hDf v, ← dvd_neg, neg_sub]
    exact hcong v
  refine ⟨Finsupp.mapRange (fun k : ℤ => k / n) (by simp) (A - Df), ⟨f, hf, fun v => ?_⟩⟩
  simp only [Finsupp.sub_apply, Finsupp.smul_apply, Finsupp.mapRange_apply, nsmul_eq_mul]
  rw [Int.mul_ediv_cancel' (by simpa using hdvd v), hDf v]
  ring

theorem sub_degree_smul_single_mem {n : ℕ} (hdeg1 : ∀ v : Place K F, v.deg = 1) (P₀ : Place K F)
    (hgen : ∀ v : Place K F,
      (Finsupp.single v 1 - Finsupp.single P₀ 1 : Divisor K F) ∈ nMulModPrincipal K F n)
    (D : Divisor K F) :
    D - (Divisor.degree D) • (Finsupp.single P₀ 1 : Divisor K F) ∈ nMulModPrincipal K F n := by
  induction D using Finsupp.induction with
  | zero => simp
  | single_add v k D _ _ ih =>
    have hv : (v.deg : ℤ) = 1 := by exact_mod_cast hdeg1 v
    have key : (Finsupp.single v k + D : Divisor K F)
          - (Divisor.degree (Finsupp.single v k + D)) • (Finsupp.single P₀ 1 : Divisor K F)
        = k • ((Finsupp.single v 1 - Finsupp.single P₀ 1 : Divisor K F))
          + (D - (Divisor.degree D) • (Finsupp.single P₀ 1 : Divisor K F)) := by
      rw [map_add, Divisor.degree_single, hv, mul_one, add_smul, smul_sub,
        ← Finsupp.smul_single_one v k]
      abel
    rw [key]
    exact add_mem (AddSubgroup.zsmul_mem _ (hgen v) k) ih

theorem exists_nsmul_eq_mk [HasPrincipalDivisors K F] {n : ℕ} (hn : n ≠ 0)
    (D : Divisor.degZero (K := K) (F := F)) (hD : (D : Divisor K F) ∈ nMulModPrincipal K F n) :
    ∃ y : Pic0 K F, n • y = Pic0.mk D := by
  obtain ⟨E, hE⟩ := hD
  have hdegE : Divisor.degree E = 0 := by
    have h0 : Divisor.degree ((D : Divisor K F) - n • E) = 0 := degree_eq_zero_of_mem_principal hE
    rw [map_sub, (Divisor.mem_degZero).mp D.2, zero_sub, neg_eq_zero, map_nsmul, nsmul_eq_mul,
      mul_eq_zero] at h0
    exact h0.resolve_left (by exact_mod_cast hn)
  refine ⟨Pic0.mk ⟨E, (Divisor.mem_degZero).mpr hdegE⟩, ?_⟩
  show n • (QuotientAddGroup.mk _ : Pic0 K F) = QuotientAddGroup.mk _
  rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
  have : ((-(n • (⟨E, (Divisor.mem_degZero).mpr hdegE⟩ : Divisor.degZero (K := K) (F := F))) + D :
      Divisor.degZero (K := K) (F := F)) : Divisor K F) = (D : Divisor K F) - n • E := by
    simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg, AddSubgroup.coe_nsmul]
    abel
  rw [this]
  exact hE

end AlgebraicCurve.Pic0.DivisibleReduction

open AlgebraicCurve.Pic0.DivisibleReduction in
theorem solution (K F : Type*) [Field K] [Field F] [Algebra K F]
    [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    [IsCurveOver K F]
    (n : ℕ) (hn : n ≠ 0) (x : Pic0 K F) :
    ∃ y : Pic0 K F, n • y = x := by
  haveI : HasPrincipalDivisors K F := IsCurveOver.hasPrincipalDivisors
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rcases isEmpty_or_nonempty (Place K F) with hE | ⟨⟨P₀⟩⟩
  ·
    refine ⟨0, ?_⟩
    have hD : D = 0 := Subtype.ext (Subsingleton.elim _ _)
    rw [hD, Pic0.mk_zero, nsmul_zero]
  · refine exists_nsmul_eq_mk hn D ?_
    have hgen : ∀ v : Place K F,
        (Finsupp.single v 1 - Finsupp.single P₀ 1 : Divisor K F) ∈ nMulModPrincipal K F n :=
      fun v => single_sub_single_mem v P₀
        (AlgebraicCurve.Place.exists_natCast_dvd_ord_sub_single_sub_single K F hfg n hn v P₀)
    have h := sub_degree_smul_single_mem IsCurveOver.deg_eq_one_of_isAlgClosed P₀ hgen (D : Divisor K F)
    rwa [(Divisor.mem_degZero).mp D.2, zero_smul, sub_zero] at h
