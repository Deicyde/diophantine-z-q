/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Matrix_GeneralLinearGroup_exists_natCard_le_of_isSemisimpleRepresentation_of_card_image_charpoly_le (git blob 4f8ec1a50663179478ef6d918646d07ef7c1fbfc, sha256 fc2589e6bc5d6c7d70e22258728733cfe86714554c089132e50a9e0e667ae849).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_Deformations_MatrixRepresentation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Matrix_GeneralLinearGroup_exists_natCard_le_of_isSemisimpleRepresentation_of_card_image_charpoly_le

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open scoped MatrixGroups

theorem Matrix.GeneralLinearGroup.exists_natCard_le_of_isSemisimpleRepresentation_of_card_image_charpoly_le
    (η : ℝ) (hη : η < 1 / 2) (M : ℕ) :
    ∃ A : ℕ, ∀ (ℓ : ℕ) [Fact ℓ.Prime] (G : Subgroup (GL (Fin 2) (ZMod ℓ))),
      (Deformation.matrixRepresentation G.subtype).IsSemisimpleRepresentation →
      ∀ H : Finset (GL (Fin 2) (ZMod ℓ)), (↑H : Set (GL (Fin 2) (ZMod ℓ))) ⊆ G →
        (1 - η) * (Nat.card G : ℝ) ≤ H.card →
        (H.image fun h : GL (Fin 2) (ZMod ℓ) =>
            (h : Matrix (Fin 2) (Fin 2) (ZMod ℓ)).charpoly).card ≤ M →
          Nat.card G ≤ A := by
  revert η hη M
  exact @_root_.P2MW.S_Matrix_GeneralLinearGroup_exists_natCard_le_of_isSemisimpleRepresentation_of_card_image_charpoly_le.solution
