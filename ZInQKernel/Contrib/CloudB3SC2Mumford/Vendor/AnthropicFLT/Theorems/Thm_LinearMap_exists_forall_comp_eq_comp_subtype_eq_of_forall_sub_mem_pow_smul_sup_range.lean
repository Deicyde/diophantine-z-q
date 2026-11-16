/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_LinearMap_exists_forall_comp_eq_comp_subtype_eq_of_forall_sub_mem_pow_smul_sup_range
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_LinearMap_exists_forall_comp_eq_comp_subtype_eq_of_forall_sub_mem_pow_smul_sup_range

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe u

theorem LinearMap.exists_forall_comp_eq_comp_subtype_eq_of_forall_sub_mem_pow_smul_sup_range
    {B : Type u} [CommRing B] [IsNoetherianRing B] (J : Ideal B)
    {GE GK : Type u} [AddCommGroup GE] [Module B GE] [AddCommGroup GK] [Module B GK] [Module.Finite B GK]
    {r : ℕ} (p : (Fin r → B) →ₗ[B] GE) (hp : Function.Surjective p)
    (F E : ℕ → Type u) [∀ k, AddCommGroup (F k)] [∀ k, Module B (F k)] [∀ k, AddCommGroup (E k)] [∀ k, Module B (E k)]
    (φ : ∀ k, F (k + 1) →ₗ[B] F k) (hφs : ∀ k, Function.Surjective (φ k))
    (hφk : ∀ k, LinearMap.ker (φ k) = J ^ (k + 1) • (⊤ : Submodule B (F (k + 1))))
    (ε : ∀ k, F k →ₗ[B] E k) (ψE : ∀ k, GE →ₗ[B] E k) (lam : ∀ k, GK →ₗ[B] F k)
    (hlamc : ∀ k, φ k ∘ₗ lam (k + 1) = lam k) (hlamr : ∀ k, LinearMap.range (lam k) = LinearMap.ker (ε k))

    (ℓ : ∀ n, (Fin r → B) →ₗ[B] F n) (hℓε : ∀ n, ε n ∘ₗ ℓ n = ψE n ∘ₗ p) (hℓφ : ∀ n, φ n ∘ₗ ℓ (n + 1) = ℓ n)
    (δs : ∀ n, ↥(LinearMap.ker p) →ₗ[B] GK) (hδs : ∀ n, lam n ∘ₗ δs n = ℓ n ∘ₗ (LinearMap.ker p).subtype)
    (hδsc : ∀ n, δs (n + 1) - δs n ∈ J ^ (n + 1) • (⊤ : Submodule B (↥(LinearMap.ker p) →ₗ[B] GK)))

    (δ : ↥(LinearMap.ker p) →ₗ[B] GK)
    (hδ : ∀ n, δ - δs n ∈ J ^ (n + 1) • (⊤ : Submodule B (↥(LinearMap.ker p) →ₗ[B] GK)) ⊔
      LinearMap.range (LinearMap.lcomp B GK (LinearMap.ker p).subtype)) :
    ∃ ℓ' : ∀ k, (Fin r → B) →ₗ[B] F k,
      (∀ k, φ k ∘ₗ ℓ' (k + 1) = ℓ' k) ∧
      (∀ k, ε k ∘ₗ ℓ' k = ψE k ∘ₗ p) ∧
      (∀ k, ℓ' k ∘ₗ (LinearMap.ker p).subtype = lam k ∘ₗ δ) := by p2m_exact_reverting @_root_.P2MW.S_LinearMap_exists_forall_comp_eq_comp_subtype_eq_of_forall_sub_mem_pow_smul_sup_range.solution
