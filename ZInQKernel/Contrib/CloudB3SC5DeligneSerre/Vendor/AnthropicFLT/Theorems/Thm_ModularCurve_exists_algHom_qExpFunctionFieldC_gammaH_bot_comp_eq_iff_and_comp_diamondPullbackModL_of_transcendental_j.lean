/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_algHom_qExpFunctionFieldC_gammaH_bot_comp_eq_iff_and_comp_diamondPullbackModL_of_transcendental_j (git blob 6a8b44fb718834f7814af4832312da8add81b9a9, sha256 abdb852d3d9b3e6d995acfe3c48d7a6f85fe621f98790d38009a168ecef58df4).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XH
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_JqCoeff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XHDiamondModL
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_algHom_qExpFunctionFieldC_gammaH_bot_comp_eq_iff_and_comp_diamondPullbackModL_of_transcendental_j

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open ModularCurve WeierstrassCurve WeierstrassCurve.Affine
open scoped MatrixGroups

universe u v in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_algHom_qExpFunctionFieldC_gammaH_bot_comp_eq_iff_and_comp_diamondPullbackModL_of_transcendental_j
    (K : Type u) [Field K] [IsAlgClosed K] (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0)
    (x : qExpFunctionFieldC K (CohCarrier.GammaH M ⊥)) (hx : (x : LaurentSeries K) = jqModC K)
    (k Ω : Type v) [Field k] [Field Ω] [DecidableEq Ω] [Algebra K k] [Algebra K Ω] [Algebra k Ω]
    [IsScalarTower K k Ω] [IsAlgClosure k Ω] (E : WeierstrassCurve k) [E.IsElliptic]
    (hE : Transcendental K E.j) (hgen : IntermediateField.adjoin K ({E.j} : Set k) = ⊤) :
    ∃ (P₀ : (E.baseChange Ω).toAffine.Point)
      (ψ₀ : qExpFunctionFieldC K (CohCarrier.GammaH M ⊥) →ₐ[K] Ω),
      addOrderOf P₀ = M ∧ ψ₀ x = algebraMap k Ω E.j ∧
      (∀ σ : Ω ≃ₐ[k] Ω,
        (WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω) P₀ = P₀ ∨
            WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω) P₀ = -P₀) ↔
          ((σ : Ω →ₐ[k] Ω).restrictScalars K).comp ψ₀ = ψ₀) ∧
      (∀ (ρ : CongruenceSubgroup.Gamma0 M →*
          (qExpFunctionFieldC K (CohCarrier.GammaH M ⊥) ≃ₐ[K]
            qExpFunctionFieldC K (CohCarrier.GammaH M ⊥))),
        IsDiamondPullbackModL K M ⊥ ρ →
        ∀ γ : CongruenceSubgroup.Gamma0 M, ∃ σ : Ω ≃ₐ[k] Ω,
          WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω) P₀ =
              ((((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M).val) • P₀ ∧
            ψ₀.comp (ρ γ : qExpFunctionFieldC K (CohCarrier.GammaH M ⊥) →ₐ[K]
                qExpFunctionFieldC K (CohCarrier.GammaH M ⊥)) =
              ((σ : Ω →ₐ[k] Ω).restrictScalars K).comp ψ₀) := by
  revert K M hM x hx k Ω E hE hgen
  exact @_root_.P2MW.S_ModularCurve_exists_algHom_qExpFunctionFieldC_gammaH_bot_comp_eq_iff_and_comp_diamondPullbackModL_of_transcendental_j.solution
