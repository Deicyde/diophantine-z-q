/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_smul_eq_of_E4_cube_div_discriminant_eq (git blob d9baefe3ac480d8436a61581524de9cb778cd819, sha256 a3c021d598985dff3da43821a36a7d76c8eacd11ffc9a501f03d0431ea976f4d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_smul_eq_of_E4_cube_div_discriminant_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open UpperHalfPlane
open scoped MatrixGroups

theorem ModularCurve.exists_smul_eq_of_E4_cube_div_discriminant_eq (τ τ' : ℍ)
    (h : (ModularForm.E₄ : ℍ → ℂ) τ ^ 3 / ModularForm.discriminant τ =
      (ModularForm.E₄ : ℍ → ℂ) τ' ^ 3 / ModularForm.discriminant τ') :
    ∃ γ : SL(2, ℤ), γ • τ = τ' := by
  revert τ τ' h
  exact @_root_.P2MW.S_ModularCurve_exists_smul_eq_of_E4_cube_div_discriminant_eq.solution
