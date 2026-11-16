/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_IsAdicComplete_finite_and_surjective_and_apply_eq_zero_iff_of_forall_ker_le_pow_smul_top
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_IsAdicComplete_finite_and_surjective_and_apply_eq_zero_iff_of_forall_ker_le_pow_smul_top

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe u v

theorem IsAdicComplete.finite_and_surjective_and_apply_eq_zero_iff_of_forall_ker_le_pow_smul_top
    {R : Type u} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (M : ℕ → Type v) [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
    (t : ∀ n : ℕ, M (n + 1) →ₗ[R] M n)
    (hI : ∀ n : ℕ, I ^ (n + 1) • (⊤ : Submodule R (M n)) = ⊥)
    (ht : ∀ n : ℕ, Function.Surjective (t n))
    (hker : ∀ n : ℕ, LinearMap.ker (t n) ≤ I ^ (n + 1) • ⊤)
    [Module.Finite R (M 0)]
    (L : Submodule R (∀ n, M n)) (hL : ∀ x, x ∈ L ↔ ∀ n, t n (x (n + 1)) = x n) :
    Module.Finite R L ∧
      (∀ (n : ℕ) (y : M n), ∃ x ∈ L, x n = y) ∧
      (∀ (n : ℕ) (x : ∀ n, M n), x ∈ L → (x n = 0 ↔ x ∈ I ^ (n + 1) • L)) := by p2m_exact_reverting @_root_.P2MW.S_IsAdicComplete_finite_and_surjective_and_apply_eq_zero_iff_of_forall_ker_le_pow_smul_top.solution
