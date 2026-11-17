/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_realizeOf_eq_div (git blob 79aadbfbad25a40cb40eeb92a687b4030264337c, sha256 9af840e3a76ccb460d09c2c7beda71dc47e1d55a259c2f4622ac0ddeaee95e69).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_realizeOf_eq_div

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.realizeOf_eq_div
    (Γ : Subgroup SL(2, ℤ)) (hT : ModularGroup.T ∈ Γ) {k : ℤ}
    (g h : ModularForm Γ k) (x : LaurentSeries ℂ)
    (hx : x * ((UpperHalfPlane.qExpansion 1 (h : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
      ((UpperHalfPlane.qExpansion 1 (g : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ))
    (τ : UpperHalfPlane) (hτ : (h : UpperHalfPlane → ℂ) τ ≠ 0) :
    ModularCurve.realizeOf Γ x τ = (g : UpperHalfPlane → ℂ) τ / (h : UpperHalfPlane → ℂ) τ := by
  revert Γ hT k g h x hx τ hτ
  exact @_root_.P2MW.S_ModularCurve_realizeOf_eq_div.solution
