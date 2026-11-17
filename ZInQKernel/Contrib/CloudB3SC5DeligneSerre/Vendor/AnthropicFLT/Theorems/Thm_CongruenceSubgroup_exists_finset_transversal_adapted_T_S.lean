/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CongruenceSubgroup_exists_finset_transversal_adapted_T_S (git blob 14a1049b6b2614e445eb58abd907e33022f80e14, sha256 8fb220658108fc27c7ed540d31cdae17e496295226d3e0b1aee75720985ea1f1).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CongruenceSubgroup_exists_finset_transversal_adapted_T_S

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped MatrixGroups in

theorem CongruenceSubgroup.exists_finset_transversal_adapted_T_S
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (hS₀ : ∀ j : ℤ, ModularGroup.S * ModularGroup.T ^ j ∉ Γ ∧ -(ModularGroup.S * ModularGroup.T ^ j) ∉ Γ)
    (h₀ : ℕ) (hh₀ : 0 < h₀) (hT : ModularGroup.T ^ h₀ ∈ Γ ∨ -(ModularGroup.T ^ h₀) ∈ Γ)
    (hmin : ∀ j : ℕ, 0 < j → j < h₀ → ModularGroup.T ^ j ∉ Γ ∧ -(ModularGroup.T ^ j) ∉ Γ) :
    ∃ s : Finset SL(2, ℤ),
      (∀ g : SL(2, ℤ), ∃ x ∈ s, g * x⁻¹ ∈ Γ ∨ -(g * x⁻¹) ∈ Γ) ∧
      (∀ x ∈ s, ∀ y ∈ s, (x * y⁻¹ ∈ Γ ∨ -(x * y⁻¹) ∈ Γ) → x = y) ∧
      (∀ j : ℕ, j < h₀ → ModularGroup.T ^ j ∈ s) ∧ ModularGroup.S ∈ s ∧
      (∀ x ∈ s, (∀ j : ℕ, j < h₀ → x ≠ ModularGroup.T ^ j) → x ≠ ModularGroup.S →
        (∀ j : ℤ, x * ModularGroup.T ^ j ∉ Γ ∧ -(x * ModularGroup.T ^ j) ∉ Γ) ∧
        (x * ModularGroup.S⁻¹ ∉ Γ ∧ -(x * ModularGroup.S⁻¹) ∉ Γ)) := by
  revert Γ hS₀ h₀ hh₀ hT hmin
  exact @_root_.P2MW.S_CongruenceSubgroup_exists_finset_transversal_adapted_T_S.solution
