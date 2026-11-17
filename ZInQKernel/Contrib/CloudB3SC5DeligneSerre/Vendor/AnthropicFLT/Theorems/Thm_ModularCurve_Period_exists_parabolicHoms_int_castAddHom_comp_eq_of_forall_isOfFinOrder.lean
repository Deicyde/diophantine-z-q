/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_Period_exists_parabolicHoms_int_castAddHom_comp_eq_of_forall_isOfFinOrder (git blob 438b7b3ed5aa600c84c1be0c58d0d001c413be78, sha256 efbd2e7666db129d47bbabdb362f1af352e9fbd143cd2f899d1a2bb8fb772286).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodMap
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_Period_exists_parabolicHoms_int_castAddHom_comp_eq_of_forall_isOfFinOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.Period.exists_parabolicHoms_int_castAddHom_comp_eq_of_forall_isOfFinOrder
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (n : ℕ)
    (φ : ModularCurve.Period.parabolicHoms (ZMod n) Γ (ZMod n))
    (hφ : ∀ γ : Γ, IsOfFinOrder γ → (φ : Additive Γ →+ ZMod n) (Additive.ofMul γ) = 0) :
    ∃ x : ModularCurve.Period.parabolicHoms ℤ Γ ℤ,
      (Int.castAddHom (ZMod n)).comp (x : Additive Γ →+ ℤ) = (φ : Additive Γ →+ ZMod n) := by
  revert Γ n φ hφ
  exact @_root_.P2MW.S_ModularCurve_Period_exists_parabolicHoms_int_castAddHom_comp_eq_of_forall_isOfFinOrder.solution
