/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_LevelN_exists_linearMap_regularDifferentials_mdifferentiable (git blob 549f64f9f96c6e57da916819c11f25fc0800fb75, sha256 b3f9de23afdf89804d0f8886ec327eeb784b70165918817971074c5ecb44c6ca).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_LevelNFunctionField
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RegularDifferentials
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_LevelN_exists_linearMap_regularDifferentials_mdifferentiable

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped Manifold

theorem ModularCurve.LevelN.exists_linearMap_regularDifferentials_mdifferentiable
    (N : ℕ) [NeZero N]
    (K : Type*) [Field K] [Algebra ℂ K] [Algebra (ModularCurve.LevelN.ring N) K]
    [IsScalarTower ℂ (ModularCurve.LevelN.ring N) K]
    [IsFractionRing (ModularCurve.LevelN.ring N) K] :
    (∀ ω ∈ AlgebraicCurve.regularDifferentials ℂ K,
      ∃ (a b c e : UpperHalfPlane → ℂ) (ha : a ∈ ModularCurve.LevelN.ring N)
        (hb : b ∈ ModularCurve.LevelN.ring N) (hc : c ∈ ModularCurve.LevelN.ring N)
        (he : e ∈ ModularCurve.LevelN.ring N), b ≠ 0 ∧ e ≠ 0 ∧
        ω = (algebraMap (ModularCurve.LevelN.ring N) K ⟨a, ha⟩ /
              algebraMap (ModularCurve.LevelN.ring N) K ⟨b, hb⟩) •
            KaehlerDifferential.D ℂ K (algebraMap (ModularCurve.LevelN.ring N) K ⟨c, hc⟩ /
              algebraMap (ModularCurve.LevelN.ring N) K ⟨e, he⟩)) ∧
    ∃ Ψ : AlgebraicCurve.regularDifferentials ℂ K →ₗ[ℂ] (UpperHalfPlane → ℂ),
      Function.Injective Ψ ∧
      (∀ ω, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Ψ ω)) ∧
      ∀ (ω : AlgebraicCurve.regularDifferentials ℂ K) (a b c e : UpperHalfPlane → ℂ)
        (ha : a ∈ ModularCurve.LevelN.ring N) (hb : b ∈ ModularCurve.LevelN.ring N)
        (hc : c ∈ ModularCurve.LevelN.ring N) (he : e ∈ ModularCurve.LevelN.ring N),
        b ≠ 0 → e ≠ 0 →
        (ω : KaehlerDifferential ℂ K) =
          (algebraMap (ModularCurve.LevelN.ring N) K ⟨a, ha⟩ /
              algebraMap (ModularCurve.LevelN.ring N) K ⟨b, hb⟩) •
            KaehlerDifferential.D ℂ K (algebraMap (ModularCurve.LevelN.ring N) K ⟨c, hc⟩ /
              algebraMap (ModularCurve.LevelN.ring N) K ⟨e, he⟩) →
        ∀ τ : UpperHalfPlane, Ψ ω τ * b τ * e τ ^ 2 =
          a τ * (e τ * deriv (c ∘ UpperHalfPlane.ofComplex) τ -
            c τ * deriv (e ∘ UpperHalfPlane.ofComplex) τ) := by
  revert N K
  exact @_root_.P2MW.S_ModularCurve_LevelN_exists_linearMap_regularDifferentials_mdifferentiable.solution
