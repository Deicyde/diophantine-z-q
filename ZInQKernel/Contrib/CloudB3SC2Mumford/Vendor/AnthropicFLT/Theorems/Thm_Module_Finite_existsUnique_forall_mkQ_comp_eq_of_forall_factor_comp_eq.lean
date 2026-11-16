/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Module_Finite_existsUnique_forall_mkQ_comp_eq_of_forall_factor_comp_eq
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_Module_Finite_existsUnique_forall_mkQ_comp_eq_of_forall_factor_comp_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe u

theorem Module.Finite.existsUnique_forall_mkQ_comp_eq_of_forall_factor_comp_eq
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {M N : Type u} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [Module.Finite A M] [Module.Finite A N]
    (ψ : ∀ n : ℕ, M →ₗ[A] N ⧸ (I ^ (n + 1) • (⊤ : Submodule A N)))
    (hψ : ∀ n : ℕ,
      Submodule.factor (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))) ∘ₗ ψ (n + 1) = ψ n) :
    ∃! Φ : ∀ n : ℕ, (M →ₗ[A] N) ⧸ (I ^ (n + 1) • (⊤ : Submodule A (M →ₗ[A] N))),
      (∀ n : ℕ, Submodule.factor (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))) (Φ (n + 1)) = Φ n) ∧
      (∀ (n : ℕ) (g : M →ₗ[A] N), Submodule.Quotient.mk g = Φ n →
        (Submodule.mkQ (I ^ (n + 1) • (⊤ : Submodule A N))) ∘ₗ g = ψ n) := by p2m_exact_reverting @_root_.P2MW.S_Module_Finite_existsUnique_forall_mkQ_comp_eq_of_forall_factor_comp_eq.solution
