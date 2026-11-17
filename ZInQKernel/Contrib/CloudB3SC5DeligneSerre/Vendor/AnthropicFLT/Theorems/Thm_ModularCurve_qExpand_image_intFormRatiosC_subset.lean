/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_qExpand_image_intFormRatiosC_subset (git blob 2682365be6a219ba8fa1407752ff3588e7d3613b, sha256 70897cab06bf3b232dd3350cd9d22b3a91dcffe22ea9950d5f93b4f50f0b41a8).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_qExpand_image_intFormRatiosC_subset

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open scoped MatrixGroups in

theorem ModularCurve.qExpand_image_intFormRatiosC_subset (K : Type*) [Field K]
    {Γ Γ' : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ) (ℓ : ℕ) [NeZero ℓ]
    (hΓ' : ∀ γ ∈ Γ', ∃ γ₁ ∈ Γ,
      γ₁ 0 0 = γ 0 0 ∧ γ₁ 0 1 = (ℓ : ℤ) * γ 0 1 ∧ (ℓ : ℤ) * γ₁ 1 0 = γ 1 0 ∧ γ₁ 1 1 = γ 1 1) :
    ModularCurve.qExpand K ℓ '' ModularCurve.intFormRatiosC K Γ ⊆
      ModularCurve.intFormRatiosC K Γ' := by
  revert K Γ Γ' hT ℓ hΓ'
  exact @_root_.P2MW.S_ModularCurve_qExpand_image_intFormRatiosC_subset.solution
