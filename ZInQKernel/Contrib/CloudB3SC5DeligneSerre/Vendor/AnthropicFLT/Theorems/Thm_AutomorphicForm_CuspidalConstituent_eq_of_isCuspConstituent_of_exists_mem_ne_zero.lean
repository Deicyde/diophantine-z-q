/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_CuspidalConstituent_eq_of_isCuspConstituent_of_exists_mem_ne_zero (git blob 0038b108722c1553cb5a7ed06f3a8ac73e5471d3, sha256 2e08ebbb9a7e4b39c5f685ead75058ec6a516ec8c2da755a1f8928408e8b2cd2).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalConstituent
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_CuspidalConstituent_eq_of_isCuspConstituent_of_exists_mem_ne_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open MeasureTheory NumberField
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

theorem AutomorphicForm.CuspidalConstituent.eq_of_isCuspConstituent_of_exists_mem_ne_zero
    (F : Type) [Field F] [NumberField F] (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    (V₁ V₂ : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (h₁ : AutomorphicForm.CuspidalConstituent.IsCuspConstituent F pins ξ V₁)
    (h₂ : AutomorphicForm.CuspidalConstituent.IsCuspConstituent F pins ξ V₂)
    (h : ∃ φ ∈ V₁ ⊓ V₂, φ ≠ 0) : V₁ = V₂ := by
  revert F pins ξ V₁ V₂ h₁ h₂ h
  exact @_root_.P2MW.S_AutomorphicForm_CuspidalConstituent_eq_of_isCuspConstituent_of_exists_mem_ne_zero.solution
