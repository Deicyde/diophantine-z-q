/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_linearEquiv_cuspForm_sup_zpowers_neg_one_dualMap_periodOf (git blob e0195d7c7630debd4a63838ff8aabdfa9dc1eec7, sha256 761470935e3d02e05c575bfad121a6fb8f7e7afda727d13dc6bfbc1ea363ce22).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_linearEquiv_cuspForm_sup_zpowers_neg_one_dualMap_periodOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.exists_linearEquiv_cuspForm_sup_zpowers_neg_one_dualMap_periodOf
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    ∃ e : CuspForm ((Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ))) 2 ≃ₗ[ℂ] CuspForm Γ 2,
      (∀ f : CuspForm ((Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ))) 2, ∀ τ : UpperHalfPlane, e f τ = f τ) ∧
      (∀ g : CuspForm Γ 2, ∀ τ : UpperHalfPlane, e.symm g τ = g τ) ∧
      (∀ τ₀ τ₁ : UpperHalfPlane,
        e.toLinearMap.dualMap (ModularCurve.periodAlongOf Γ τ₀ τ₁) =
          ModularCurve.periodAlongOf (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) τ₀ τ₁) ∧
      (∀ γ : Γ, e.toLinearMap.dualMap (ModularCurve.periodOf Γ γ) =
          ModularCurve.periodOf (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) ⟨γ, Subgroup.mem_sup_left γ.2⟩) ∧
      (∀ (γ : SL(2, ℤ)) (h₁ : γ ∈ Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)))
          (h₂ : -γ ∈ Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))),
        ModularCurve.periodOf (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) ⟨-γ, h₂⟩ = ModularCurve.periodOf (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) ⟨γ, h₁⟩) ∧
      (∀ φ : Module.Dual ℂ (CuspForm Γ 2),
        φ ∈ ModularCurve.periodLatticeOf Γ ↔
          e.toLinearMap.dualMap φ ∈ ModularCurve.periodLatticeOf (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)))) := by
  revert Γ
  exact @_root_.P2MW.S_ModularCurve_exists_linearEquiv_cuspForm_sup_zpowers_neg_one_dualMap_periodOf.solution
