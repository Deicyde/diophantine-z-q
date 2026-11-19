/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_EisensteinSeries_weierstrassZeta_add_one_and_add_tau_and_smul (git blob d5b27224f82ca46584157fd1ad168285e0030bf0, sha256 f6775e33d93c9748e3b5e69d142c71bc39d59060ccf19b6b37cecbc623d7aa68).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_EisensteinSeries_WeierstrassZeta
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_EisensteinSeries_weierstrassZeta_add_one_and_add_tau_and_smul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped Real MatrixGroups

theorem EisensteinSeries.weierstrassZeta_add_one_and_add_tau_and_smul (τ : UpperHalfPlane) :
    (∀ z : ℂ, (∀ v : Fin 2 → ℤ, z ≠ (v 0 : ℂ) * τ + v 1) →
        EisensteinSeries.weierstrassZeta τ (z + 1) =
          EisensteinSeries.weierstrassZeta τ z + EisensteinSeries.G2 τ) ∧
    (∀ z : ℂ, (∀ v : Fin 2 → ℤ, z ≠ (v 0 : ℂ) * τ + v 1) →
        EisensteinSeries.weierstrassZeta τ (z + τ) =
          EisensteinSeries.weierstrassZeta τ z +
            ((τ : ℂ) * EisensteinSeries.G2 τ - 2 * π * Complex.I)) ∧
    (∀ (γ : SL(2, ℤ)) (z : ℂ),
        EisensteinSeries.weierstrassZeta (γ • τ) (z / UpperHalfPlane.denom γ τ) =
          UpperHalfPlane.denom γ τ * EisensteinSeries.weierstrassZeta τ z) := by
  revert τ
  exact @_root_.P2MW.S_EisensteinSeries_weierstrassZeta_add_one_and_add_tau_and_smul.solution
