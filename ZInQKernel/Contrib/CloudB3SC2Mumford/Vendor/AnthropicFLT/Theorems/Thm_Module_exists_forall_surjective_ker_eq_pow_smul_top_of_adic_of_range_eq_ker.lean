/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Module_exists_forall_surjective_ker_eq_pow_smul_top_of_adic_of_range_eq_ker
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_Module_exists_forall_surjective_ker_eq_pow_smul_top_of_adic_of_range_eq_ker

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe u

theorem Module.exists_forall_surjective_ker_eq_pow_smul_top_of_adic_of_range_eq_ker
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    {M N K : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] [AddCommGroup K] [Module R K]
    (ρ : M →ₗ[R] N) (ι : K →ₗ[R] M) (hι : Function.Injective ι) (hιr : LinearMap.range ι = LinearMap.ker ρ)
    (E : ℕ → Type u) [∀ k, AddCommGroup (E k)] [∀ k, Module R (E k)]
    (τ : ∀ k, E (k + 1) →ₗ[R] E k) (hτs : ∀ k, Function.Surjective (τ k))
    (hτk : ∀ k, LinearMap.ker (τ k) = I ^ (k + 1) • (⊤ : Submodule R (E (k + 1))))
    (P : ℕ → Type u) [∀ k, AddCommGroup (P k)] [∀ k, Module R (P k)] (π : ∀ k, P (k + 1) →ₗ[R] P k)
    (ψP : ∀ k, M →ₗ[R] P k) (hψPs : ∀ k, Function.Surjective (ψP k))
    (hψPk : ∀ k, LinearMap.ker (ψP k) = I ^ (k + 1) • (⊤ : Submodule R M))
    (hψPc : ∀ k, π k ∘ₗ ψP (k + 1) = ψP k)
    (C : ℕ → Type u) [∀ k, AddCommGroup (C k)] [∀ k, Module R (C k)] (γ : ∀ k, C (k + 1) →ₗ[R] C k)
    (ψC : ∀ k, N →ₗ[R] C k) (hψCs : ∀ k, Function.Surjective (ψC k))
    (hψCk : ∀ k, LinearMap.ker (ψC k) = I ^ (k + 1) • (⊤ : Submodule R N))
    (hψCc : ∀ k, γ k ∘ₗ ψC (k + 1) = ψC k)
    (θ : ∀ k, P k →ₗ[R] C k) (hθ : ∀ k, θ k ∘ₗ ψP k = ψC k ∘ₗ ρ)
    (u : ∀ k, E k →ₗ[R] P k) (huc : ∀ k, π k ∘ₗ u (k + 1) = u k ∘ₗ τ k)
    (hur : ∀ k, LinearMap.range (u k) = LinearMap.ker (θ k))
    (hui : ∃ c : ℕ, ∀ k : ℕ, LinearMap.ker (u (k + c)) ≤ I ^ (k + 1) • (⊤ : Submodule R (E (k + c)))) :
    ∃ ψ : ∀ k, K →ₗ[R] E k,
      (∀ k, Function.Surjective (ψ k)) ∧
      (∀ k, LinearMap.ker (ψ k) = I ^ (k + 1) • (⊤ : Submodule R K)) ∧
      (∀ k, τ k ∘ₗ ψ (k + 1) = ψ k) ∧
      (∀ k, u k ∘ₗ ψ k = ψP k ∘ₗ ι) := by p2m_exact_reverting @_root_.P2MW.S_Module_exists_forall_surjective_ker_eq_pow_smul_top_of_adic_of_range_eq_ker.solution
