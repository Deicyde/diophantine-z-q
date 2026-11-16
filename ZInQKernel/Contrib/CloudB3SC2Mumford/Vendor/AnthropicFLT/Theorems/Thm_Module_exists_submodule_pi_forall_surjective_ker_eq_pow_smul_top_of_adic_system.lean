/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Module_exists_submodule_pi_forall_surjective_ker_eq_pow_smul_top_of_adic_system
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_Module_exists_submodule_pi_forall_surjective_ker_eq_pow_smul_top_of_adic_system

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe u

theorem Module.exists_submodule_pi_forall_surjective_ker_eq_pow_smul_top_of_adic_system
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG)
    (E : ℕ → Type u) [∀ k, AddCommGroup (E k)] [∀ k, Module R (E k)]
    (τ : ∀ k, E (k + 1) →ₗ[R] E k) (hτs : ∀ k, Function.Surjective (τ k))
    (hτk : ∀ k, LinearMap.ker (τ k) = I ^ (k + 1) • (⊤ : Submodule R (E (k + 1)))) :
    ∃ L : Submodule R (∀ k, E k),
      (∀ e : ∀ k, E k, e ∈ L ↔ ∀ k, τ k (e (k + 1)) = e k) ∧
      (∀ k, Function.Surjective ((LinearMap.proj k).comp L.subtype : L →ₗ[R] E k)) ∧
      (∀ k, LinearMap.ker ((LinearMap.proj k).comp L.subtype : L →ₗ[R] E k) =
        I ^ (k + 1) • (⊤ : Submodule R L)) := by p2m_exact_reverting @_root_.P2MW.S_Module_exists_submodule_pi_forall_surjective_ker_eq_pow_smul_top_of_adic_system.solution
