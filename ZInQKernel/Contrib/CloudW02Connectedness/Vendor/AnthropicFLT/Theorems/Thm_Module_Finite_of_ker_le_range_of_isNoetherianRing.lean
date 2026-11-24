/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Module_Finite_of_ker_le_range_of_isNoetherianRing
Modification notice (2026-11-14, Cloud Worker 2): local import paths are relocated;
mathematical definitions, theorem statements, and proof bodies are unchanged.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.RingTheory.Noetherian.Basic
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Sol.S_Module_Finite_of_ker_le_range_of_isNoetherianRing

theorem Module.Finite.of_ker_le_range_of_isNoetherianRing {R : Type*} [CommRing R] [IsNoetherianRing R] {M N₁ N₂ : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₂] [Module R N₂] [Module.Finite R N₁] [Module.Finite R N₂] (α : N₁ →ₗ[R] M) (β : M →ₗ[R] N₂) (h : LinearMap.ker β ≤ LinearMap.range α) : Module.Finite R M := by p2m_exact_reverting @_root_.P2MW.S_Module_Finite_of_ker_le_range_of_isNoetherianRing.solution
