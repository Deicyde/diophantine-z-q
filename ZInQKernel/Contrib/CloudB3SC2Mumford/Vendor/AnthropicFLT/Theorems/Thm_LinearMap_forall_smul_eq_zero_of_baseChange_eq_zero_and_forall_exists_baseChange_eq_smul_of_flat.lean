/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_LinearMap_forall_smul_eq_zero_of_baseChange_eq_zero_and_forall_exists_baseChange_eq_smul_of_flat
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_LinearMap_forall_smul_eq_zero_of_baseChange_eq_zero_and_forall_exists_baseChange_eq_smul_of_flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe u v w w'

open TensorProduct

theorem LinearMap.forall_smul_eq_zero_of_baseChange_eq_zero_and_forall_exists_baseChange_eq_smul_of_flat
    {R₀ : Type u} [CommRing R₀] {R : Type v} [CommRing R] [Algebra R₀ R] [Module.Flat R₀ R]
    {M : Type w} [AddCommGroup M] [Module R₀ M] {N : Type w'} [AddCommGroup N] [Module R₀ N]
    (u : M →ₗ[R₀] N) (J : Ideal R₀)
    (hk : ∀ x : M, u x = 0 → ∀ a ∈ J, a • x = 0)
    (hc : ∀ (y : N), ∀ a ∈ J, ∃ x : M, u x = a • y) :
    (∀ x : R ⊗[R₀] M, u.baseChange R x = 0 → ∀ a ∈ J.map (algebraMap R₀ R), a • x = 0) ∧
    (∀ (y : R ⊗[R₀] N), ∀ a ∈ J.map (algebraMap R₀ R), ∃ x : R ⊗[R₀] M, u.baseChange R x = a • y) := by p2m_exact_reverting @_root_.P2MW.S_LinearMap_forall_smul_eq_zero_of_baseChange_eq_zero_and_forall_exists_baseChange_eq_smul_of_flat.solution
