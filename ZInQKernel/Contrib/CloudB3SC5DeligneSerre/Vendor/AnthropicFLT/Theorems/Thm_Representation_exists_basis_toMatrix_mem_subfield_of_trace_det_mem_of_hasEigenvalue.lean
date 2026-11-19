/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Representation_exists_basis_toMatrix_mem_subfield_of_trace_det_mem_of_hasEigenvalue (git blob c7b5cb0d3fa3cfa1e7527c9bfa580de45d364ee8, sha256 de201fb5cb5ac887e6445a1b55691dc1abaeec6fa6ce30ef3f927b4e14fb46ea).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Representation_exists_basis_toMatrix_mem_subfield_of_trace_det_mem_of_hasEigenvalue

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem Representation.exists_basis_toMatrix_mem_subfield_of_trace_det_mem_of_hasEigenvalue
    {Ω : Type*} [Field Ω] {V : Type*} [AddCommGroup V] [Module Ω V] {G : Type*} [Group G]
    (F : Subfield Ω) (ρ : G →* (V ≃ₗ[Ω] V)) (hV : Module.finrank Ω V = 2)
    (hirr : ∀ W : Submodule Ω V, (∀ g, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = ⊤)
    (htr : ∀ g, LinearMap.trace Ω V (ρ g).toLinearMap ∈ F)
    (hdet : ∀ g, LinearMap.det (ρ g).toLinearMap ∈ F)
    (g₀ : G) (a : Ω) (haF : a ∈ F) (hev : Module.End.HasEigenvalue (ρ g₀).toLinearMap a)
    (hns : (ρ g₀).toLinearMap ≠ a • LinearMap.id) :
    ∃ b : Module.Basis (Fin 2) Ω V,
      ∀ g (i j : Fin 2), LinearMap.toMatrix b b (ρ g).toLinearMap i j ∈ F := by
  revert Ω V G F ρ hV hirr htr hdet g₀ a haF hev hns
  exact @_root_.P2MW.S_Representation_exists_basis_toMatrix_mem_subfield_of_trace_det_mem_of_hasEigenvalue.solution
