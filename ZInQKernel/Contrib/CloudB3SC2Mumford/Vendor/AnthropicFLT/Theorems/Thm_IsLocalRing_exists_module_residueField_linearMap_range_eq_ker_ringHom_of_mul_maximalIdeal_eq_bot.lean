/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_IsLocalRing_exists_module_residueField_linearMap_range_eq_ker_ringHom_of_mul_maximalIdeal_eq_bot
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_IsLocalRing_exists_module_residueField_linearMap_range_eq_ker_ringHom_of_mul_maximalIdeal_eq_bot

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open IsLocalRing

universe u

theorem IsLocalRing.exists_module_residueField_linearMap_range_eq_ker_ringHom_of_mul_maximalIdeal_eq_bot
    {B B₁ : Type u} [CommRing B] [IsLocalRing B] [IsArtinianRing B] [CommRing B₁] (π : B →+* B₁)
    (hsmall : RingHom.ker π * maximalIdeal B = ⊥) :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module (ResidueField B) V) (_ : Module.Finite (ResidueField B) V)
      (_ : Module B V) (_ : IsScalarTower B (ResidueField B) V)
      (_ : Module (ResidueField B)ᵐᵒᵖ V) (_ : IsCentralScalar (ResidueField B) V) (ι : V →ₗ[B] B),
      Function.Injective ι ∧ LinearMap.range ι = Submodule.restrictScalars B (RingHom.ker π) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_module_residueField_linearMap_range_eq_ker_ringHom_of_mul_maximalIdeal_eq_bot.solution
