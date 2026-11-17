/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularForm_finiteDimensional_of_isArithmetic (git blob 7bd847d5af80fc0295927e70e468621b19e6e087, sha256 bb16b17d8daa85d403e887a2b8e9834f4675989af423a44eda59b78918624b7a).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.PowerSeries.Order
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_Subgroup_IsArithmetic_exists_nat_mem_strictPeriods_conj
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularForm_eq_zero_of_lt_order_qExpansion_of_isArithmetic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace UpperHalfPlane
end UpperHalfPlane
namespace ModularForm
end ModularForm
namespace P2MW.S_ModularForm_finiteDimensional_of_isArithmetic.ModularForm
end P2MW.S_ModularForm_finiteDimensional_of_isArithmetic.ModularForm
namespace SlashInvariantForm
end SlashInvariantForm
namespace Matrix.SpecialLinearGroup
end Matrix.SpecialLinearGroup
namespace ConjAct
end ConjAct
namespace MatrixGroups
end MatrixGroups
namespace Topology
end Topology
namespace Manifold
end Manifold
namespace Pointwise
end Pointwise

namespace P2MW.S_ModularForm_finiteDimensional_of_isArithmetic

open _root_.UpperHalfPlane
open _root_.ModularForm
open _root_.P2MW.S_ModularForm_finiteDimensional_of_isArithmetic.ModularForm
open _root_.SlashInvariantForm
open _root_.Matrix.SpecialLinearGroup
open _root_.ConjAct
open scoped _root_.MatrixGroups _root_.ModularForm _root_.P2MW.S_ModularForm_finiteDimensional_of_isArithmetic.ModularForm _root_.Topology _root_.Manifold _root_.Pointwise

noncomputable section

namespace ModularForm export _root_.ModularForm (ext eq_zero_of_lt_order_qExpansion_of_isArithmetic) end ModularForm
open scoped _root_.ModularForm in

def ModularForm.qExpansionCoeffs_W2D {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.HasDetOne] (k : ℤ) {h : ℝ}
    (hh : 0 < h) (h𝒢 : h ∈ 𝒢.strictPeriods) (B : ℕ) : ModularForm 𝒢 k →ₗ[ℂ] (Fin B → ℂ) where
  toFun f n := (qExpansion h f).coeff n
  map_add' f g := by
    ext n
    simp [ModularForm.qExpansion_add hh h𝒢]
  map_smul' a f := by
    ext n
    simp [ModularForm.qExpansion_smul hh h𝒢]

open scoped _root_.ModularForm in
lemma ModularForm.le_order_of_qExpansionCoeffs_eq_zero_W2D {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.HasDetOne]
    {k : ℤ} {h : ℝ} (hh : 0 < h) (h𝒢 : h ∈ 𝒢.strictPeriods) {B : ℕ} {f : ModularForm 𝒢 k}
    (hf : ModularForm.qExpansionCoeffs_W2D k hh h𝒢 B f = 0) : (B : ℕ∞) ≤ (qExpansion h f).order :=
  PowerSeries.nat_le_order _ _ fun n hn ↦ by have h__af := congr_fun hf ⟨n, hn⟩; simp at h__af; exact h__af

theorem solution (𝒢 : Subgroup (GL (Fin 2) ℝ)) [𝒢.IsArithmetic] [𝒢.HasDetOne] (k : ℤ) : FiniteDimensional ℂ (ModularForm 𝒢 k) := by
  obtain ⟨M, hM, hconj⟩ := Subgroup.IsArithmetic.exists_nat_mem_strictPeriods_conj 𝒢
  have hM𝒢 : (M : ℝ) ∈ 𝒢.strictPeriods := by simpa using hconj 1
  set B := M * ((k * 𝒢.relIndex 𝒮ℒ).toNat / 12) + 1 with hB
  refine Module.Finite.of_injective (ModularForm.qExpansionCoeffs_W2D k (Nat.cast_pos.mpr hM) hM𝒢 B) ?_
  rw [injective_iff_map_eq_zero]
  intro f hf
  refine f.eq_zero_of_lt_order_qExpansion_of_isArithmetic hM hconj (lt_of_lt_of_le ?_
    (ModularForm.le_order_of_qExpansionCoeffs_eq_zero_W2D _ hM𝒢 hf))
  exact_mod_cast Nat.lt_succ_self _
end
