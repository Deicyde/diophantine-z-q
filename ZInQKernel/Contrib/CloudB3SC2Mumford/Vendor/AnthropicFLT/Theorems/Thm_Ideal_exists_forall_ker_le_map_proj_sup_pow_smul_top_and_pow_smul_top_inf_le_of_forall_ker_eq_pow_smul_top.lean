/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Ideal_exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_Ideal_exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe u v

theorem Ideal.exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top
    {B : Type u} [CommRing B] [IsNoetherianRing B] (J : Ideal B)
    (F P : ℕ → Type v)
    [∀ n, AddCommGroup (F n)] [∀ n, Module B (F n)] [∀ n, Module.Finite B (F n)]
    [∀ n, AddCommGroup (P n)] [∀ n, Module B (P n)] [∀ n, Module.Finite B (P n)]
    (φ : ∀ n, F (n + 1) →ₗ[B] F n) (hφs : ∀ n, Function.Surjective (φ n))
    (hφk : ∀ n, LinearMap.ker (φ n) = J ^ (n + 1) • (⊤ : Submodule B (F (n + 1))))
    (π : ∀ n, P (n + 1) →ₗ[B] P n) (hπs : ∀ n, Function.Surjective (π n))
    (hπk : ∀ n, LinearMap.ker (π n) = J ^ (n + 1) • (⊤ : Submodule B (P (n + 1))))
    (u : ∀ n, F n →ₗ[B] P n) (hu : ∀ n, π n ∘ₗ u (n + 1) = u n ∘ₗ φ n)
    (K : Submodule B (∀ n, F n))
    (hK : ∀ x : ∀ n, F n, x ∈ K ↔ (∀ n, φ n (x (n + 1)) = x n) ∧ ∀ n, u n (x n) = 0) :
    ∃ c : ℕ, ∀ k n : ℕ, k + c ≤ n →
      LinearMap.ker (u n) ≤ K.map (LinearMap.proj n) ⊔ J ^ (k + 1) • (⊤ : Submodule B (F n)) ∧
      J ^ n • (⊤ : Submodule B (F n)) ⊓ K.map (LinearMap.proj n) ≤ J ^ k • K.map (LinearMap.proj n) := by p2m_exact_reverting @_root_.P2MW.S_Ideal_exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top.solution
