/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_qExpFunctionFieldC_gammaH_bot_coe_eq_toricPoint_pow_and_diamondPullbackModL_apply_eq (git blob 7dba6de15244159cd5ca593b46541775ca2453da, sha256 608cdf27ddeb1814d4728f42a3a3cb1538464970610e2e0a1a3fdd24b682815b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XH
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XHDiamondModL
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_TateSlots
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_qExpFunctionFieldC_gammaH_bot_coe_eq_toricPoint_pow_and_diamondPullbackModL_apply_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open ModularCurve WeierstrassCurve
open scoped MatrixGroups

universe u in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_qExpFunctionFieldC_gammaH_bot_coe_eq_toricPoint_pow_and_diamondPullbackModL_apply_eq
    (K : Type u) [Field K] (M : ℕ) (hM : 2 ≤ M) (ζ : K) (hζ : IsPrimitiveRoot ζ M) :
    ∃ w₁ w₂ : (ZMod M)ˣ → qExpFunctionFieldC K (CohCarrier.GammaH M ⊥),
      (∀ t : (ZMod M)ˣ, (w₁ t : LaurentSeries K) =
        (tateLaurent K).c₄ * (1 + 12 * (toricPoint K 1 (ζ ^ (t : ZMod M).val)).1) /
          (tateLaurent K).c₆) ∧
      (∀ t : (ZMod M)ˣ, (w₂ t : LaurentSeries K) =
        ((toricPoint K 1 (ζ ^ (t : ZMod M).val)).1 +
            6 * (toricPoint K 1 (ζ ^ (t : ZMod M).val)).1 ^ 2 + 2 * (tateLaurent K).a₄) /
          (tateLaurent K).c₄) ∧
      ∀ (ρ : CongruenceSubgroup.Gamma0 M →*
          (qExpFunctionFieldC K (CohCarrier.GammaH M ⊥) ≃ₐ[K]
            qExpFunctionFieldC K (CohCarrier.GammaH M ⊥))),
        IsDiamondPullbackModL K M ⊥ ρ →
        ∀ (γ : CongruenceSubgroup.Gamma0 M) (t : (ZMod M)ˣ),
          ρ γ (w₁ t) = w₁ (t * (CohCarrier.gamma0Units M γ)⁻¹) ∧
            ρ γ (w₂ t) = w₂ (t * (CohCarrier.gamma0Units M γ)⁻¹) := by
  revert K M hM ζ hζ
  exact @_root_.P2MW.S_ModularCurve_exists_qExpFunctionFieldC_gammaH_bot_coe_eq_toricPoint_pow_and_diamondPullbackModL_apply_eq.solution
