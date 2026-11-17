/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularForm_eq_zero_of_lt_order_qExpansion_of_isArithmetic (git blob 5d79affe0208918f897ee1c7a2af64d2bdc19775, sha256 ec58c4bb9b4eade32a3e62104490da96a710724b76a69faa54ff0f0132055249).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.RingTheory.PowerSeries.Order
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_UpperHalfPlane_qExpansion_prod
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularForm_levelOne_eq_zero_of_lt_order_qExpansion
import Batteries.Tactic.Alias

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace UpperHalfPlane
end UpperHalfPlane
namespace ModularForm
end ModularForm
namespace P2MW.S_ModularForm_eq_zero_of_lt_order_qExpansion_of_isArithmetic.ModularForm
end P2MW.S_ModularForm_eq_zero_of_lt_order_qExpansion_of_isArithmetic.ModularForm
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

namespace P2MW.S_ModularForm_eq_zero_of_lt_order_qExpansion_of_isArithmetic

open _root_.UpperHalfPlane
open _root_.ModularForm
open _root_.P2MW.S_ModularForm_eq_zero_of_lt_order_qExpansion_of_isArithmetic.ModularForm
open _root_.SlashInvariantForm
open _root_.Matrix.SpecialLinearGroup
open _root_.ConjAct
open scoped _root_.MatrixGroups _root_.ModularForm _root_.P2MW.S_ModularForm_eq_zero_of_lt_order_qExpansion_of_isArithmetic.ModularForm _root_.Topology _root_.Manifold _root_.Pointwise

noncomputable section

namespace ModularForm export _root_.ModularForm (coe_norm translate norm_eq_zero_iff coe_zero levelOne_eq_zero_of_lt_order_qExpansion) end ModularForm
namespace ModularForm
open scoped _root_.ModularForm in

private theorem _root_.ModularForm.analyticAt_cuspFunction_quotientFunc_W2D {𝒢 : Subgroup (GL (Fin 2) ℝ)}
    {k : ℤ} (f : ModularForm 𝒢 k) {M : ℕ} (hM : 0 < M)
    (hconj : ∀ γ : SL(2, ℤ), (M : ℝ) ∈ (toConjAct (mapGL ℝ γ) • 𝒢).strictPeriods)
    (q : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) :
    AnalyticAt ℂ (cuspFunction M (quotientFunc f q)) 0 := by
  induction q using Quotient.inductionOn with
  | h r =>
    obtain ⟨γ, hγ⟩ := r.2
    have hp : (M : ℝ) ∈ (toConjAct (r.1⁻¹)⁻¹ • 𝒢).strictPeriods := by
      rw [inv_inv, ← hγ]
      exact hconj γ
    exact ModularFormClass.analyticAt_cuspFunction_zero (ModularForm.translate f r.1⁻¹)
      (Nat.cast_pos.mpr hM) hp

end ModularForm
alias ModularForm.analyticAt_cuspFunction_quotientFunc_W2D := _root_.ModularForm.analyticAt_cuspFunction_quotientFunc_W2D
theorem solution {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsArithmetic] {k : ℤ} (f : ModularForm 𝒢 k) {M : ℕ} (hM : 0 < M) (hconj : ∀ γ : SL(2, ℤ), (M : ℝ) ∈ (ConjAct.toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ γ) • 𝒢).strictPeriods) (h : ((M * ((k * 𝒢.relIndex 𝒮ℒ).toNat / 12) : ℕ) : ℕ∞) < (qExpansion M f).order) : f = 0 := by

  set F := ModularForm.norm 𝒮ℒ f with hF
  have hanalytic := f.analyticAt_cuspFunction_quotientFunc_W2D hM hconj
  let _ : Fintype (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) := Fintype.ofFinite _

  have hprod : qExpansion M F = ∏ q : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ, qExpansion M (quotientFunc f q) := by
    rw [hF, ModularForm.coe_norm]
    exact UpperHalfPlane.qExpansion_prod Finset.univ fun q _ ↦ hanalytic q

  have hone : quotientFunc f (⟦1⟧ : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) = ⇑f := by
    rw [quotientFunc_mk]
    simp
  have horder : (qExpansion M f).order ≤ (qExpansion M F).order := by
    rw [hprod, PowerSeries.order_prod, ← hone]
    exact Finset.single_le_sum (f := fun q ↦ (qExpansion M (quotientFunc f q)).order)
      (fun _ _ ↦ zero_le) (Finset.mem_univ _)
  have hrel : 𝒢.relIndex 𝒮ℒ = Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) := rfl
  have hF0 : F = 0 := by
    refine ModularForm.levelOne_eq_zero_of_lt_order_qExpansion M hM F (lt_of_lt_of_le ?_ horder)
    simpa [hrel] using h
  rw [hF, ModularForm.norm_eq_zero_iff] at hF0
  exact DFunLike.coe_injective (hF0.trans ModularForm.coe_zero.symm)
end
