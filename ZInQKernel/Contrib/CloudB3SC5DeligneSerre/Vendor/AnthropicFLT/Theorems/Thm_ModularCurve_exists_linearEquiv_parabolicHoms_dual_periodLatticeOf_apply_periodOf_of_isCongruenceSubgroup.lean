/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_linearEquiv_parabolicHoms_dual_periodLatticeOf_apply_periodOf_of_isCongruenceSubgroup (git blob 8255196b6deb4cd3a4bce4f82a57d795c1a668fa, sha256 c0b68e9ee930a211ec786f7939321d14c967cdefa81af2130511c0ada7f5c5ae).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_linearEquiv_parabolicHoms_dual_periodLatticeOf_apply_periodOf_of_isCongruenceSubgroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.exists_linearEquiv_parabolicHoms_dual_periodLatticeOf_apply_periodOf_of_isCongruenceSubgroup
    (Γ : Subgroup SL(2, ℤ)) (hΓ : CongruenceSubgroup.IsCongruenceSubgroup Γ) :
    ∃ EV : ModularCurve.Period.parabolicHoms ℤ Γ ℤ ≃ₗ[ℤ] Module.Dual ℤ (ModularCurve.periodLatticeOf Γ),
      ∀ (ψ : ModularCurve.Period.parabolicHoms ℤ Γ ℤ) (δ : Γ),
        EV ψ ⟨ModularCurve.periodOf Γ δ, ModularCurve.periodOf_mem_periodLatticeOf Γ δ⟩ =
          (ψ : Additive Γ →+ ℤ) (Additive.ofMul δ) := by
  revert Γ hΓ
  exact @_root_.P2MW.S_ModularCurve_exists_linearEquiv_parabolicHoms_dual_periodLatticeOf_apply_periodOf_of_isCongruenceSubgroup.solution
