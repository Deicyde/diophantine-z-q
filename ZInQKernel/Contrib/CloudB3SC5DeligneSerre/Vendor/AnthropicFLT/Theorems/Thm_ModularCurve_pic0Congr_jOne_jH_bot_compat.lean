/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_pic0Congr_jOne_jH_bot_compat (git blob b9c5fdb37565219c8d9b2b4f229d3e04a970f3ab, sha256 4e21e80b5aabc80154131ece7ee012555a5bfc508e56f871cd8dfe2c02c83904).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1HeckeModule
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XHOperators
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Pic0Congr
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_pic0Congr_jOne_jH_bot_compat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem ModularCurve.pic0Congr_jOne_jH_bot_compat (M : ℕ) [NeZero M]
    (hin : ModularCurve.HeckeDiamondInputsAll M) (hinH : ModularCurve.HeckeDiamondInputsHAll M ⊥)
    (h : ModularCurve.x1FunctionFieldBar M = ModularCurve.xHFunctionFieldBar M ⊥) :
    let e : ModularCurve.JOne M ≃+ ModularCurve.JH M ⊥ :=
      AlgebraicCurve.Pic0.congr (IntermediateField.equivOfEq h).toRingEquiv
        (IntermediateField.equivOfEq h).commutes
    (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (x : ModularCurve.JOne M),
        e (ModularCurve.heckeOperatorOneBar M ⟨ℓ, hℓ⟩ x) =
          (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
            ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M ⊥ ℓ) (e x)) ∧
    (∀ (d : ℕ) (hd : d.Coprime M) (x : ModularCurve.JOne M),
        e (ModularCurve.diamondOneBar M d x) = ModularCurve.diamondHBar M ⊥ (ZMod.unitOfCoprime d hd) (e x)) ∧
    (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : ModularCurve.JOne M),
        e (σ • x) = σ • e x) := by
  revert M hin hinH h
  exact @_root_.P2MW.S_ModularCurve_pic0Congr_jOne_jH_bot_compat.solution
