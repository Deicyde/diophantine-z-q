/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_periodMapOf_apply_eq_periodOf (git blob f538273c50f51b618daf1ee732019c2b1643399b, sha256 818f6347b242541f97c34c129deaec5ea01e7ffa27da6c4551874f8cab2bfa78).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_exists_hasEquivariantPrimitiveOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_periodOf_apply_eq_sub_of_hasEquivariantPrimitiveOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ModularCurve_periodMapOf_apply_eq_periodOf

set_option autoImplicit false

open scoped MatrixGroups

theorem solution (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (f : CuspForm Γ 2) (γ : Γ) :
    ModularCurve.periodMapOf Γ f (Additive.ofMul γ) = ModularCurve.periodOf Γ γ f := by
  obtain ⟨F, hF⟩ := ModularCurve.exists_hasEquivariantPrimitiveOf Γ f
  obtain ⟨F₀, h₀, hp⟩ := ModularCurve.periodMapOf_def Γ f hF
  rw [hp, ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply,
    ModularCurve.periodOf_apply_eq_sub_of_hasEquivariantPrimitiveOf Γ f h₀ γ]
  rfl
