/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_lSpace_eq_bot_of_degree_neg (git blob 5cc3a204f1746460d37480a724acd496b685ed1b, sha256 3d46c2c56738fd741274be49db58b4e1b05d32a8fea3fcf82d0e4ae400f67e3d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import Batteries.Tactic.Alias

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace AlgebraicCurve
end AlgebraicCurve
namespace AlgebraicCurve.Place
end AlgebraicCurve.Place
namespace AlgebraicCurve.Divisor
end AlgebraicCurve.Divisor

namespace P2MW.S_AlgebraicCurve_lSpace_eq_bot_of_degree_neg

set_option autoImplicit false
set_option maxHeartbeats 3200000

namespace AlgebraicCurve
export _root_.AlgebraicCurve (Place Divisor Divisor.degree HasPrincipalDivisors HasPrincipalDivisors.exists_divisor IsCurveOver LSpace ell mem_lSpace_iff_ord WeilDifferentialRankOne StichtenothGenusExists)
open _root_.AlgebraicCurve
namespace Place
export _root_.AlgebraicCurve.Place (deg ord ord_unit_smul_zpow exists_unit_mul_zpow toValuationSubring)
open _root_.AlgebraicCurve.Place
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
private theorem _root_.AlgebraicCurve.Place.ord_nonneg_of_mem {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
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
alias ord_nonneg_of_mem := _root_.AlgebraicCurve.Place.ord_nonneg_of_mem
private theorem _root_.AlgebraicCurve.Place.mem_of_ord_nonneg {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)
alias mem_of_ord_nonneg := _root_.AlgebraicCurve.Place.mem_of_ord_nonneg
theorem mem_iff_ord_nonneg {f : F} (hf : f ≠ 0) :
    f ∈ v.toValuationSubring ↔ 0 ≤ v.ord f :=
  ⟨v.ord_nonneg_of_mem, v.mem_of_ord_nonneg hf⟩
end Place
end AlgebraicCurve

namespace AlgebraicCurve
export _root_.AlgebraicCurve (Place Divisor Divisor.degree HasPrincipalDivisors HasPrincipalDivisors.exists_divisor IsCurveOver LSpace ell mem_lSpace_iff_ord WeilDifferentialRankOne StichtenothGenusExists)
open _root_.AlgebraicCurve
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
namespace Divisor export _root_.AlgebraicCurve.Divisor (degree) end Divisor
open scoped _root_.AlgebraicCurve.Divisor in
theorem Divisor.degree_eq_sum_support (D : Divisor K F) :
    Divisor.degree D = ∑ v ∈ D.support, D v * (v.deg : ℤ) := by
  rw [Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum]
  rfl
variable {D : Divisor K F}
open scoped _root_.AlgebraicCurve.Divisor in

theorem Divisor.degree_nonneg_of_nonneg [IsCurveOver K F]
    {D : Divisor K F} (hD : ∀ v, 0 ≤ D v) : 0 ≤ Divisor.degree D := by
  rw [Divisor.degree_eq_sum_support]
  exact Finset.sum_nonneg fun v _ => mul_nonneg (hD v) (Int.natCast_nonneg _)
theorem lSpace_eq_bot_of_degree_neg_port [IsCurveOver K F]
    (hD : Divisor.degree D < 0) : LSpace D = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  rw [Submodule.mem_bot]
  by_contra hf0
  obtain ⟨P, hPord, hPdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0
  have heff : ∀ v : Place K F, 0 ≤ (P + D) v := by
    intro v
    rw [Finsupp.add_apply, hPord]
    rcases mem_lSpace_iff_ord.mp hf with rfl | h
    · exact absurd rfl hf0
    · linarith [h v]
  have hdegPD : 0 ≤ Divisor.degree (P + D) := Divisor.degree_nonneg_of_nonneg heff
  rw [map_add, hPdeg, zero_add] at hdegPD
  exact absurd hdegPD (not_le.mpr hD)
theorem ell_eq_zero_of_degree_neg [IsCurveOver K F] (hD : Divisor.degree D < 0) :
    ell D = 0 := by
  rw [ell, lSpace_eq_bot_of_degree_neg_port hD, finrank_bot]
end AlgebraicCurve

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_lSpace_eq_bot_of_degree_neg.AlgebraicCurve in
theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] {D : Divisor K F} [IsCurveOver K F]
    (hD : Divisor.degree D < 0) : LSpace D = ⊥ :=
  AlgebraicCurve.lSpace_eq_bot_of_degree_neg_port (K := K) (F := F) (D := D) (hD := hD)
