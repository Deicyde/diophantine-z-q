/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AdicCompletion_exists_ringHom_comp_algebraMap_eq_and_flat_of_flat_of_finiteType
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_AdicCompletion_exists_ringHom_comp_algebraMap_eq_and_flat_of_flat_of_finiteType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe u

theorem AdicCompletion.exists_ringHom_comp_algebraMap_eq_and_flat_of_flat_of_finiteType
    {B₀ : Type u} [CommRing B₀] [IsNoetherianRing B₀] {B : Type u} [CommRing B] [Algebra B₀ B]
    [Module.Flat B₀ B] [Algebra.FiniteType B₀ B] (I₀ : Ideal B₀) :
    ∃ f : AdicCompletion I₀ B₀ →+* AdicCompletion (I₀.map (algebraMap B₀ B)) B,
      (∀ b : B₀, f (algebraMap B₀ (AdicCompletion I₀ B₀) b)
        = algebraMap B (AdicCompletion (I₀.map (algebraMap B₀ B)) B) (algebraMap B₀ B b)) ∧
      (letI := f.toAlgebra; Module.Flat (AdicCompletion I₀ B₀) (AdicCompletion (I₀.map (algebraMap B₀ B)) B)) := by p2m_exact_reverting @_root_.P2MW.S_AdicCompletion_exists_ringHom_comp_algebraMap_eq_and_flat_of_flat_of_finiteType.solution
