/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_natural_diamond_algHom_qExpFunctionFieldC_gammaH_bot_of_transcendental_j (git blob a078fee73a5658a14f5092db7218591f183b24d7, sha256 804308c7c0f82020370643b0995fc2ff11c17900af1ac14b2863a2d332a6a54f).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XH
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_JqCoeff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XHDiamondModL
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_natural_diamond_algHom_qExpFunctionFieldC_gammaH_bot_of_transcendental_j

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve ModularCurve WeierstrassCurve WeierstrassCurve.Affine
open scoped MatrixGroups

universe u v in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_natural_diamond_algHom_qExpFunctionFieldC_gammaH_bot_of_transcendental_j
    (K : Type u) [Field K] [IsAlgClosed K] (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0)
    (x : qExpFunctionFieldC K (CohCarrier.GammaH M ⊥)) (hx : (x : LaurentSeries K) = jqModC K)
    (k Ω : Type v) [Field k] [Field Ω] [DecidableEq Ω] [Algebra K k] [Algebra K Ω] [Algebra k Ω]
    [IsScalarTower K k Ω] (E : WeierstrassCurve k) [E.IsElliptic]
    (hE : Transcendental K E.j)
    (hfull : Nat.card {P : (E.baseChange Ω).toAffine.Point // M • P = 0} = M ^ 2) :
    ∃ Ψ : {P : (E.baseChange Ω).toAffine.Point // addOrderOf P = M} →
        {ψ : qExpFunctionFieldC K (CohCarrier.GammaH M ⊥) →ₐ[K] Ω // ψ x = algebraMap k Ω E.j},
      (∀ (σ : Ω ≃ₐ[k] Ω) (P P' : {P : (E.baseChange Ω).toAffine.Point // addOrderOf P = M}),
        P'.1 = WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω) P.1 →
          ((Ψ P').1 : qExpFunctionFieldC K (CohCarrier.GammaH M ⊥) →ₐ[K] Ω) =
            ((σ : Ω →ₐ[k] Ω).restrictScalars K).comp (Ψ P).1) ∧
      (∀ (ρ : CongruenceSubgroup.Gamma0 M →*
          (qExpFunctionFieldC K (CohCarrier.GammaH M ⊥) ≃ₐ[K]
            qExpFunctionFieldC K (CohCarrier.GammaH M ⊥))),
        IsDiamondPullbackModL K M ⊥ ρ →
        ∀ (γ : CongruenceSubgroup.Gamma0 M)
          (P P' : {P : (E.baseChange Ω).toAffine.Point // addOrderOf P = M}),
          P'.1 = ((((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M).val) • P.1 →
            ((Ψ P').1 : qExpFunctionFieldC K (CohCarrier.GammaH M ⊥) →ₐ[K] Ω) =
              ((Ψ P).1 : qExpFunctionFieldC K (CohCarrier.GammaH M ⊥) →ₐ[K] Ω).comp
                (ρ γ : qExpFunctionFieldC K (CohCarrier.GammaH M ⊥) →ₐ[K]
                  qExpFunctionFieldC K (CohCarrier.GammaH M ⊥))) ∧
      (∀ P P' : {P : (E.baseChange Ω).toAffine.Point // addOrderOf P = M},
        P'.1 = -P.1 → Ψ P' = Ψ P) ∧
      (∀ P P' : {P : (E.baseChange Ω).toAffine.Point // addOrderOf P = M},
        Ψ P' = Ψ P → P'.1 = P.1 ∨ P'.1 = -P.1) := by
  revert K M hM x hx k Ω E hE hfull
  exact @_root_.P2MW.S_ModularCurve_exists_natural_diamond_algHom_qExpFunctionFieldC_gammaH_bot_of_transcendental_j.solution
