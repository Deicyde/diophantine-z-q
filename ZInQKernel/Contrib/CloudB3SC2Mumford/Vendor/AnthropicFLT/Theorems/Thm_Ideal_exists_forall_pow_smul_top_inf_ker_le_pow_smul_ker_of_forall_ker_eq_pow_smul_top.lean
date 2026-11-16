/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Ideal_exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_Ideal_exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe u v w

theorem Ideal.exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top
    {B : Type u} [CommRing B] [IsNoetherianRing B] (J : Ideal B)
    (G : ℕ → Type v) (F : ℕ → Type w)
    [∀ k, AddCommGroup (G k)] [∀ k, Module B (G k)] [Module.Finite B (G 0)]
    [∀ k, AddCommGroup (F k)] [∀ k, Module B (F k)]
    (γ : ∀ k, G (k + 1) →ₗ[B] G k) (hγs : ∀ k, Function.Surjective (γ k))
    (hγk : ∀ k, LinearMap.ker (γ k) = J ^ (k + 1) • (⊤ : Submodule B (G (k + 1))))
    (φ : ∀ k, F (k + 1) →ₗ[B] F k)
    (hφk : ∀ k, LinearMap.ker (φ k) ≤ J ^ (k + 1) • (⊤ : Submodule B (F (k + 1))))
    (θ : ∀ k, G k →ₗ[B] F k) (hθs : ∀ k, Function.Surjective (θ k))
    (hθc : ∀ k, φ k ∘ₗ θ (k + 1) = θ k ∘ₗ γ k) :
    ∃ c : ℕ, ∀ k n : ℕ, k + c ≤ n →
      (J ^ n • (⊤ : Submodule B (G n))) ⊓ LinearMap.ker (θ n) ≤ J ^ k • LinearMap.ker (θ n) := by p2m_exact_reverting @_root_.P2MW.S_Ideal_exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top.solution
