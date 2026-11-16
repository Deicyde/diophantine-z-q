/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_LinearMap_exists_forall_sub_mem_pow_smul_top_and_mkQ_comp_eq_of_compatible
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_LinearMap_exists_forall_sub_mem_pow_smul_top_and_mkQ_comp_eq_of_compatible

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe u v w

theorem LinearMap.exists_forall_sub_mem_pow_smul_top_and_mkQ_comp_eq_of_compatible
    {B : Type u} [CommRing B] [IsNoetherianRing B] (I : Ideal B)
    {M : Type v} [AddCommGroup M] [Module B M] [Module.Finite B M]
    {N : Type w} [AddCommGroup N] [Module B N] [Module.Finite B N]
    (J : ℕ → Submodule B N) (hJ : ∀ k, J (k + 1) ≤ J k)
    (hIJ : ∀ k, I ^ (k + 1) • (⊤ : Submodule B N) ≤ J k)
    (c : ℕ) (hJI : ∀ k, J (k + c) ≤ I ^ (k + 1) • (⊤ : Submodule B N))
    (f : ∀ k, M →ₗ[B] N ⧸ J k)
    (hf : ∀ k, Submodule.factor (hJ k) ∘ₗ f (k + 1) = f k) :
    ∃ g : ℕ → (M →ₗ[B] N),
      (∀ k, g (k + 1) - g k ∈ I ^ (k + 1) • (⊤ : Submodule B (M →ₗ[B] N))) ∧
      (∀ k, (J k).mkQ ∘ₗ g k = f k) := by p2m_exact_reverting @_root_.P2MW.S_LinearMap_exists_forall_sub_mem_pow_smul_top_and_mkQ_comp_eq_of_compatible.solution
