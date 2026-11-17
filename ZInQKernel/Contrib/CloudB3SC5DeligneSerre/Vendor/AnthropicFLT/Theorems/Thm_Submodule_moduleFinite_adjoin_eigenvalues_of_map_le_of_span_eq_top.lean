/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Submodule_moduleFinite_adjoin_eigenvalues_of_map_le_of_span_eq_top (git blob 4c961ace99be91d8ae01890ab96fbc558d837831, sha256 4721866ac015901552d715acea6032e67a3b10b867f436cd7be0cf6a1f27e4c0).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Submodule_moduleFinite_adjoin_eigenvalues_of_map_le_of_span_eq_top

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem Submodule.moduleFinite_adjoin_eigenvalues_of_map_le_of_span_eq_top
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (Λ : Submodule ℤ V) (hΛfg : Λ.FG) (hΛspan : Submodule.span ℂ (Λ : Set V) = ⊤)
    {J : Type*} (S : J → V →ₗ[ℂ] V) (hS : ∀ (j : J), ∀ x ∈ Λ, S j x ∈ Λ)
    (lam : J → ℂ) (v : V) (hv0 : v ≠ 0) (hv : ∀ j : J, S j v = lam j • v) :
    Module.Finite ℤ (Algebra.adjoin ℤ (Set.range lam)) := by
  revert V Λ hΛfg hΛspan J S hS lam v hv0 hv
  exact @_root_.P2MW.S_Submodule_moduleFinite_adjoin_eigenvalues_of_map_le_of_span_eq_top.solution
