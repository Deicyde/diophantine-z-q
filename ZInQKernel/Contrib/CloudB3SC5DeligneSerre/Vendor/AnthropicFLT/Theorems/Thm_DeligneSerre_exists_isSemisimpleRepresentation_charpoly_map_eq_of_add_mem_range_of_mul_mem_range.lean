/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_DeligneSerre_exists_isSemisimpleRepresentation_charpoly_map_eq_of_add_mem_range_of_mul_mem_range (git blob c5e5dca3168640ce6d8281cd156f673baebe62df, sha256 2c9add233230e30e2a4f8bfc63951f716f0f8fa87c815e0a2be9f95808dc8b5c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_Deformations_MatrixRepresentation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_DeligneSerre_exists_isSemisimpleRepresentation_charpoly_map_eq_of_add_mem_range_of_mul_mem_range

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open Polynomial

theorem DeligneSerre.exists_isSemisimpleRepresentation_charpoly_map_eq_of_add_mem_range_of_mul_mem_range
    {G : Type} [Group G] {κ : Type} [Field κ] [Finite κ] {Ω : Type} [Field Ω]
    (ι : κ →+* Ω) (χ₁ χ₂ : G →* Ωˣ)
    (hadd : ∀ g : G, (χ₁ g : Ω) + χ₂ g ∈ ι.range) (hmul : ∀ g : G, (χ₁ g : Ω) * χ₂ g ∈ ι.range) :
    ∃ ρ : G →* GL (Fin 2) κ,
      (Deformation.matrixRepresentation ρ).IsSemisimpleRepresentation ∧
      (∀ g : G, χ₁ g = 1 → χ₂ g = 1 → ρ g = 1) ∧
      ∀ g : G, (((ρ g : GL (Fin 2) κ) : Matrix (Fin 2) (Fin 2) κ).map ι).charpoly =
        (X - C (χ₁ g : Ω)) * (X - C (χ₂ g : Ω)) := by
  revert G κ Ω ι χ₁ χ₂ hadd hmul
  exact @_root_.P2MW.S_DeligneSerre_exists_isSemisimpleRepresentation_charpoly_map_eq_of_add_mem_range_of_mul_mem_range.solution
