/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Module_exists_pow_smul_ker_eq_zero_and_pow_smul_le_range_of_forall_exists_pow_smul
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_Module_exists_pow_smul_ker_eq_zero_and_pow_smul_le_range_of_forall_exists_pow_smul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe u v w

theorem Module.exists_pow_smul_ker_eq_zero_and_pow_smul_le_range_of_forall_exists_pow_smul
    {R : Type u} [CommRing R] (S : Finset R) (J : Ideal R) (hJ : Ideal.span (S : Set R) = J)
    {M : Type v} [AddCommGroup M] [Module R M] {N : Type w} [AddCommGroup N] [Module R N]
    (u : M →ₗ[R] N)
    (hker : (LinearMap.ker u).FG) (hcoker : Module.Finite R (N ⧸ LinearMap.range u))
    (hk : ∀ a ∈ S, ∀ x : M, u x = 0 → ∃ k : ℕ, a ^ k • x = 0)
    (hc : ∀ a ∈ S, ∀ y : N, ∃ (k : ℕ) (x : M), u x = a ^ k • y) :
    ∃ N₀ : ℕ,
      (∀ x : M, u x = 0 → ∀ a ∈ J ^ N₀, a • x = 0) ∧
      (∀ (y : N), ∀ a ∈ J ^ N₀, ∃ x : M, u x = a • y) := by p2m_exact_reverting @_root_.P2MW.S_Module_exists_pow_smul_ker_eq_zero_and_pow_smul_le_range_of_forall_exists_pow_smul.solution
