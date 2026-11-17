/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_DoubleComplex_Convergence_finite_E2_q0
Modification notice (2026-11-14, Cloud Worker 2): local import paths are relocated;
mathematical definitions, theorem statements, and proof bodies are unchanged.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_DoubleComplex
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Sol.S_DoubleComplex_Convergence_finite_E2_q0

set_option autoImplicit false

universe u

theorem DoubleComplex.Convergence.finite_E2_q0 {R : Type u} [CommRing R] [IsNoetherianRing R]
    {E₂ : ℕ → ℕ → Type u} [∀ p q, AddCommGroup (E₂ p q)] [∀ p q, Module R (E₂ p q)]
    {H : ℕ → Type u} [∀ n, AddCommGroup (H n)] [∀ n, Module R (H n)] {N : ℕ}
    (conv : DoubleComplex.Convergence R E₂ H N)
    (hH : ∀ n, Module.Finite R (H n)) (hE₂ : ∀ p q, 1 ≤ q → Module.Finite R (E₂ p q))
    (p : ℕ) (hp : p ≤ N) : Module.Finite R (E₂ p 0) := by p2m_exact_reverting @_root_.P2MW.S_DoubleComplex_Convergence_finite_E2_q0.solution
