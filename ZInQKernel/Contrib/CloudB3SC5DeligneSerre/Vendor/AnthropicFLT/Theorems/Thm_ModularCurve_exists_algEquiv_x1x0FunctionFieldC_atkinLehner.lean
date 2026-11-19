/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_algEquiv_x1x0FunctionFieldC_atkinLehner (git blob b4c9ca0666c17c1e601ce44a6e93258de300af6b, sha256 229c807d5e96ebbb270a6a0a5061873a0eb15d9243aa34c432e36291ff049133).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1HeckeOperator
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1Diamond
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_algEquiv_x1x0FunctionFieldC_atkinLehner

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem ModularCurve.exists_algEquiv_x1x0FunctionFieldC_atkinLehner
    (M : ℕ) [NeZero M] (ℓ : ℕ) [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (hβ : ModularCurve.HeckeBetaOneDefined M ℓ)
    (hσ : ∃ σ : ↥(ModularCurve.x1FunctionField M) ≃ₐ[ℚ] ↥(ModularCurve.x1FunctionField M),
      ModularCurve.IsDiamondAut M ℓ σ)
    (hσ' : ∃ σ' : ↥(ModularCurve.x1FunctionFieldBar M) ≃ₐ[AlgebraicClosure ℚ]
        ↥(ModularCurve.x1FunctionFieldBar M),
      ModularCurve.IsBaseChangeAutOf (AlgebraicClosure ℚ) (ModularCurve.diamondAut M ℓ) σ') :
    ∃ W : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.x1x0FunctionFieldC ℚ M (M * ℓ))) ≃ₐ[AlgebraicClosure ℚ]
        ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.x1x0FunctionFieldC ℚ M (M * ℓ))),
      (∀ x : ↥(ModularCurve.x1FunctionFieldBar M),
        W (ModularCurve.heckeBetaOneBar (AlgebraicClosure ℚ) M ℓ x) =
          ModularCurve.heckeAlphaOneBar (AlgebraicClosure ℚ) M ℓ x) ∧
      ∀ x : ↥(ModularCurve.x1FunctionFieldBar M),
        W (ModularCurve.heckeAlphaOneBar (AlgebraicClosure ℚ) M ℓ x) =
          ModularCurve.heckeBetaOneBar (AlgebraicClosure ℚ) M ℓ
            ((ModularCurve.diamondAutBar M ℓ).symm x) := by
  revert M ℓ hℓM hβ hσ hσ'
  exact @_root_.P2MW.S_ModularCurve_exists_algEquiv_x1x0FunctionFieldC_atkinLehner.solution
