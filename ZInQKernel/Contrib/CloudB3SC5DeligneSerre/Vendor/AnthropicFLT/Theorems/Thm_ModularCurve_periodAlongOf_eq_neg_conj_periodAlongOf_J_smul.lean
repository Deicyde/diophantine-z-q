/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_periodAlongOf_eq_neg_conj_periodAlongOf_J_smul (git blob f0c26452d02b06e3a0ec0adafdbe4f0dac11f740, sha256 539bc5501a9da5a47360dfa5b17bdee2ba8a4bfded02a60fc580fd62d2116ffd).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_periodAlongOf_eq_neg_conj_periodAlongOf_J_smul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.periodAlongOf_eq_neg_conj_periodAlongOf_J_smul
    (Γ : Subgroup SL(2, ℤ)) (f g : CuspForm Γ 2)
    (hg : ∀ τ : UpperHalfPlane, g τ = (starRingEnd ℂ) (f (UpperHalfPlane.J • τ)))
    (τ₀ τ₁ : UpperHalfPlane) :
    ModularCurve.periodAlongOf Γ τ₀ τ₁ g =
      -(starRingEnd ℂ) (ModularCurve.periodAlongOf Γ (UpperHalfPlane.J • τ₀) (UpperHalfPlane.J • τ₁) f) := by
  revert Γ f g hg τ₀ τ₁
  exact @_root_.P2MW.S_ModularCurve_periodAlongOf_eq_neg_conj_periodAlongOf_J_smul.solution
