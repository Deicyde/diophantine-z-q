/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_equiv_algHom_modularFunctionFieldFullC_isRoot_of_transcendental (git blob bdec72103c0efe8e7c78c6b196fb30d15a7f5a9a, sha256 5ee5603dd4bcb0d1f5c402238ada1af9a0aa43263cf8ee3f7fcaece93c23351c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0ModL
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_equiv_algHom_modularFunctionFieldFullC_isRoot_of_transcendental

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open ModularCurve

theorem ModularCurve.exists_equiv_algHom_modularFunctionFieldFullC_isRoot_of_transcendental
    (K : Type*) [Field K] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0) (data : ModularPolynomialData N)
    (Ω : Type*) [Field Ω] [Algebra K Ω] (j₀ : Ω) (hj₀ : Transcendental K j₀) :
    ∃ e : {ψ : modularFunctionFieldFullC K N →ₐ[K] Ω // ψ ⟨jqModC K, jqModC_mem_full K N⟩ = j₀} ≃
        {y : Ω // (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom Ω) j₀)).IsRoot y},
      ∀ ψ, ((e ψ : {y : Ω //
          (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom Ω) j₀)).IsRoot y}) : Ω) =
        ψ.1 ⟨qExpand K N (jqModC K), jqModCd_mem_full K N dvd_rfl⟩ := by
  revert K N hN data Ω j₀ hj₀
  exact @_root_.P2MW.S_ModularCurve_exists_equiv_algHom_modularFunctionFieldFullC_isRoot_of_transcendental.solution
