/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_LinearMap_forall_smul_eq_zero_and_forall_exists_eq_smul_of_ker_of_equiv_baseChange_of_flat
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_LinearMap_forall_smul_eq_zero_and_forall_exists_eq_smul_of_ker_of_equiv_baseChange_of_flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped TensorProduct

universe u v w w'

theorem LinearMap.forall_smul_eq_zero_and_forall_exists_eq_smul_of_ker_of_equiv_baseChange_of_flat
    {R₀ : Type u} [CommRing R₀] {R : Type v} [CommRing R] [Algebra R₀ R] [Module.Flat R₀ R]
    {L₀ : Type w} [AddCommGroup L₀] [Module R₀ L₀] {C₀ : Type w} [AddCommGroup C₀] [Module R₀ C₀]
    {D₀ : Type w} [AddCommGroup D₀] [Module R₀ D₀]
    (u₀ : L₀ →ₗ[R₀] C₀) (d₀ : C₀ →ₗ[R₀] D₀) (hdu₀ : ∀ x : L₀, d₀ (u₀ x) = 0) (J : Ideal R₀)
    (hk : ∀ x : L₀, u₀ x = 0 → ∀ a ∈ J, a • x = 0)
    (hc : ∀ y : C₀, d₀ y = 0 → ∀ a ∈ J, ∃ x : L₀, u₀ x = a • y)
    {L : Type w'} [AddCommGroup L] [Module R L] {C : Type w'} [AddCommGroup C] [Module R C]
    {D : Type w'} [AddCommGroup D] [Module R D]
    (u : L →ₗ[R] C) (d : C →ₗ[R] D)
    (eL : R ⊗[R₀] L₀ ≃ₗ[R] L) (eC : R ⊗[R₀] C₀ ≃ₗ[R] C) (eD : R ⊗[R₀] D₀ ≃ₗ[R] D)
    (hu : ∀ x : L₀, u (eL ((1 : R) ⊗ₜ x)) = eC ((1 : R) ⊗ₜ u₀ x))
    (hd : ∀ y : C₀, d (eC ((1 : R) ⊗ₜ y)) = eD ((1 : R) ⊗ₜ d₀ y)) :
    (∀ x : L, u x = 0 → ∀ a ∈ J.map (algebraMap R₀ R), a • x = 0) ∧
    (∀ y : C, d y = 0 → ∀ a ∈ J.map (algebraMap R₀ R), ∃ x : L, u x = a • y) := by p2m_exact_reverting @_root_.P2MW.S_LinearMap_forall_smul_eq_zero_and_forall_exists_eq_smul_of_ker_of_equiv_baseChange_of_flat.solution
