/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_periodAlongOf_apply_eq_sub_of_hasDerivAt (git blob 8d1f18f945a8ebee6951d314a7e30dbfd3ce8b11, sha256 a851bfc28c01eeca701533286723d4966af3956a43cda3dbef0a2ca047547083).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_periodAlongOf_apply_eq_sub_of_hasDerivAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open UpperHalfPlane
open scoped MatrixGroups

theorem ModularCurve.periodAlongOf_apply_eq_sub_of_hasDerivAt (Γ : Subgroup SL(2, ℤ))
    (f : CuspForm Γ 2) {F : UpperHalfPlane → ℂ}
    (hF : ∀ τ : UpperHalfPlane, HasDerivAt (F ∘ ofComplex) (f τ) (τ : ℂ)) (τ₀ τ₁ : UpperHalfPlane) :
    ModularCurve.periodAlongOf Γ τ₀ τ₁ f = F τ₁ - F τ₀ := by
  revert Γ f F hF τ₀ τ₁
  exact @_root_.P2MW.S_ModularCurve_periodAlongOf_apply_eq_sub_of_hasDerivAt.solution
