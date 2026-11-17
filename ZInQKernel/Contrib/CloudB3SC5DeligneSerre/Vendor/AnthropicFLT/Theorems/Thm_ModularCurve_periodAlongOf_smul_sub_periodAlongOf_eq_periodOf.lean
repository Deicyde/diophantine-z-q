/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_periodAlongOf_smul_sub_periodAlongOf_eq_periodOf (git blob e5aa74a1649ca2bdca57c91e9302b64324abc588, sha256 78a63a556b1a130daee2c5c1645be2be9934fe812795c8ffb92ed747ff5df810).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_periodAlongOf_smul_sub_periodAlongOf_eq_periodOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open UpperHalfPlane
open scoped MatrixGroups

theorem ModularCurve.periodAlongOf_smul_sub_periodAlongOf_eq_periodOf
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (γ : Γ) (τ : UpperHalfPlane) :
    ModularCurve.periodAlongOf Γ UpperHalfPlane.I ((γ : SL(2, ℤ)) • τ) -
      ModularCurve.periodAlongOf Γ UpperHalfPlane.I τ = ModularCurve.periodOf Γ γ := by
  revert Γ γ τ
  exact @_root_.P2MW.S_ModularCurve_periodAlongOf_smul_sub_periodAlongOf_eq_periodOf.solution
