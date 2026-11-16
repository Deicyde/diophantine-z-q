/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_LinearMap_exists_forall_exists_mkQ_comp_eq_factor_comp
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_LinearMap_exists_forall_exists_mkQ_comp_eq_factor_comp

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe u v w

theorem LinearMap.exists_forall_exists_mkQ_comp_eq_factor_comp
    {B : Type u} [CommRing B] [IsNoetherianRing B] (I : Ideal B)
    {M : Type v} [AddCommGroup M] [Module B M] [Module.Finite B M]
    {N : Type w} [AddCommGroup N] [Module B N] [Module.Finite B N] :
    ∃ c : ℕ, ∀ (n : ℕ) (f : M →ₗ[B] N ⧸ (I ^ (n + c) • (⊤ : Submodule B N))),
      ∃ g : M →ₗ[B] N,
        (I ^ n • (⊤ : Submodule B N)).mkQ ∘ₗ g =
          Submodule.factor (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_add_right n c))) ∘ₗ f := by p2m_exact_reverting @_root_.P2MW.S_LinearMap_exists_forall_exists_mkQ_comp_eq_factor_comp.solution
