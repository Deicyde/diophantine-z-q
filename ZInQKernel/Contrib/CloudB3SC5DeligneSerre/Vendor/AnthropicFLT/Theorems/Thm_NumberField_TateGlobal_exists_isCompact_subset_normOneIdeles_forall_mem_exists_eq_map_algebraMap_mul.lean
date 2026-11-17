/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul (git blob f28659c45f474b5f0619bc1e8548ac93a9a5c182, sha256 38241b02d563b8c668f467be439866d9bcb6bccd3f271f51932a909e5126a330).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_TateGlobalZeta
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open NumberField

theorem NumberField.TateGlobal.exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul
    (F : Type) [Field F] [NumberField F] :
    ∃ K : Set (AdeleRing (𝓞 F) F)ˣ, IsCompact K ∧ K ⊆ (NumberField.TateGlobal.normOneIdeles F : Set _) ∧
      ∀ x ∈ NumberField.TateGlobal.normOneIdeles F, ∃ (η : Fˣ) (κ : (AdeleRing (𝓞 F) F)ˣ), κ ∈ K ∧
        x = Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom η * κ := by
  revert F
  exact @_root_.P2MW.S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.solution
