/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_Period_existsUnique_isParabolicHom_sup_zpowers_neg_one_apply_eq (git blob e3e36a0b422b3da2216dc3c2cfbe8a27dea5844b, sha256 e4b9973fd3fa5edcef7c36f53699b52114d3ddac1a8f05a2afb2377e5e1255bf).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodMap
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_Period_existsUnique_isParabolicHom_sup_zpowers_neg_one_apply_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.Period.existsUnique_isParabolicHom_sup_zpowers_neg_one_apply_eq
    (Γ : Subgroup SL(2, ℤ)) (A : Type*) [AddCommGroup A]
    (ψ : Additive Γ →+ A) (hψ : ModularCurve.Period.IsParabolicHom Γ ψ) :
    ∃! φ : Additive ↥(Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) →+ A,
      ModularCurve.Period.IsParabolicHom (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) φ ∧
        ∀ γ : Γ, φ (Additive.ofMul ⟨(γ : SL(2, ℤ)), Subgroup.mem_sup_left γ.2⟩) = ψ (Additive.ofMul γ) := by
  revert Γ A ψ hψ
  exact @_root_.P2MW.S_ModularCurve_Period_existsUnique_isParabolicHom_sup_zpowers_neg_one_apply_eq.solution
