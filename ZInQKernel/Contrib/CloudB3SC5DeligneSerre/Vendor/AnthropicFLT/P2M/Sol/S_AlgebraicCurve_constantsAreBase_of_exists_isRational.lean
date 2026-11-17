/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_constantsAreBase_of_exists_isRational (git blob 563581125502e3fa84885909fc3bf048e85a02f6, sha256 58b943669c1a60b0edcc98f7148884c0c6b5f9a5d8661e010672ba61dce81448).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlaceEvaluation
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_mem_of_ord_nonneg
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_ord_nonneg_of_mem
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Divisor_degree_eq_sum_support
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_evalAt_ne_zero
import Batteries.Tactic.Alias

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace AlgebraicCurve
end AlgebraicCurve
namespace P2MW.S_AlgebraicCurve_constantsAreBase_of_exists_isRational.AlgebraicCurve
end P2MW.S_AlgebraicCurve_constantsAreBase_of_exists_isRational.AlgebraicCurve
namespace AlgebraicCurve.Place
end AlgebraicCurve.Place

namespace P2MW.S_AlgebraicCurve_constantsAreBase_of_exists_isRational

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_constantsAreBase_of_exists_isRational.AlgebraicCurve

namespace AlgebraicCurve
export _root_.AlgebraicCurve (mem_lSpace_iff_ord algebraMap_mem_lSpace_zero ConstantsAreBase Place Place.coe_algebraMap Divisor Divisor.degree HasPrincipalDivisors HasPrincipalDivisors.exists_divisor Divisor.degree_eq_sum_support)
open _root_.AlgebraicCurve

namespace Place
export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg ord algebraMap_mem' toValuationSubring IsRational evalAt algebraMap_evalAt mem_of_ord_nonneg ord_nonneg_of_mem evalAt_ne_zero)
open _root_.AlgebraicCurve.Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

open IsLocalRing in

private theorem _root_.AlgebraicCurve.Place.ord_sub_evalAt_pos_s17 (hrat : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring)
    (hne : f - algebraMap K F (v.evalAt f) ≠ 0) :
    0 < v.ord (f - algebraMap K F (v.evalAt f)) := by
  have hmem : f - algebraMap K F (v.evalAt f) ∈ v.toValuationSubring :=
    sub_mem hf (v.algebraMap_mem' _)
  rcases eq_or_ne (v.ord (f - algebraMap K F (v.evalAt f))) 0 with h0 | h0
  · exfalso
    refine v.evalAt_ne_zero hrat hne h0 ?_
    have hres : algebraMap K v.ResidueField
        (v.evalAt (f - algebraMap K F (v.evalAt f))) = 0 := by
      rw [v.algebraMap_evalAt hrat hmem]
      have hcoe : (⟨f - algebraMap K F (v.evalAt f), hmem⟩ : v.toValuationSubring)
          = ⟨f, hf⟩ - algebraMap K v.toValuationSubring (v.evalAt f) := by
        refine Subtype.ext ?_
        show f - algebraMap K F (v.evalAt f)
          = f - (algebraMap K v.toValuationSubring (v.evalAt f) : F)
        rw [Place.coe_algebraMap]
      rw [hcoe, map_sub, sub_eq_zero, ← v.algebraMap_evalAt hrat hf,
        IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField,
        IsLocalRing.ResidueField.algebraMap_eq]
    exact (map_eq_zero_iff _ (algebraMap K v.ResidueField).injective).mp hres
  · have hnonneg := v.ord_nonneg_of_mem hmem
    omega

alias ord_sub_evalAt_pos_s17 := _root_.AlgebraicCurve.Place.ord_sub_evalAt_pos_s17
variable [HasPrincipalDivisors K F]

theorem eq_algebraMap_of_forall_ord_nonneg_s17 (v₀ : Place K F) (hrat : v₀.IsRational)
    (hdeg : v₀.deg ≠ 0) {g : F} (hg : g ≠ 0) (hord : ∀ v : Place K F, 0 ≤ v.ord g) :
    ∃ c : K, g = algebraMap K F c := by
  have hg₀ : g ∈ v₀.toValuationSubring := v₀.mem_of_ord_nonneg hg (hord v₀)
  refine ⟨v₀.evalAt g, ?_⟩
  by_contra hne
  set t : F := g - algebraMap K F (v₀.evalAt g) with ht
  have htne : t ≠ 0 := sub_ne_zero.mpr hne
  have hzero : 0 < v₀.ord t := v₀.ord_sub_evalAt_pos_s17 hrat hg₀ htne
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

theorem constantsAreBase_of_exists_isRational_s17 {K F : Type*} [Field K] [Field F] [Algebra K F]
    [HasPrincipalDivisors K F]
    (v₀ : Place K F) (hrat : v₀.IsRational) (hdeg : v₀.deg ≠ 0) :
    ConstantsAreBase K F := by
  refine le_antisymm (fun f hf => ?_) (fun f ⟨c, hc⟩ => hc ▸ algebraMap_mem_lSpace_zero c)
  rcases eq_or_ne f 0 with rfl | hf0
  · exact zero_mem _
  · have hord : ∀ v : Place K F, 0 ≤ v.ord f := by
      have h := (mem_lSpace_iff_ord.mp hf).resolve_left hf0
      simpa using h
    obtain ⟨c, hc⟩ := Place.eq_algebraMap_of_forall_ord_nonneg_s17 v₀ hrat hdeg hf0 hord
    exact ⟨c, hc.symm⟩

end AlgebraicCurve

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F]
    [AlgebraicCurve.HasPrincipalDivisors K F]
    (v₀ : AlgebraicCurve.Place K F) (hrat : v₀.IsRational) (hdeg : v₀.deg ≠ 0) :
    AlgebraicCurve.ConstantsAreBase K F :=
  AlgebraicCurve.constantsAreBase_of_exists_isRational_s17 v₀ hrat hdeg
