/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ContinuousLinearMap_le_ker_or_finiteDimensional_of_forall_inf_highPart_orthogonal (git blob b91232e445bcf611c09e9d3210aee77b2d5f1f2d, sha256 30d6e4671c2357309c5d5088e2e38e3cf9dfcf2e32db782546a301d557b1de6a).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ContinuousLinearMap_le_ker_or_finiteDimensional_of_forall_inf_highPart_orthogonal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open Module.End

theorem ContinuousLinearMap.le_ker_or_finiteDimensional_of_forall_inf_highPart_orthogonal {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] {T : E →L[𝕜] E}
    (hT : IsCompactOperator T) (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) (X : Submodule 𝕜 E)
    (hX : ∀ r : ℝ, 0 < r → X ⊓ (⨆ (μ : 𝕜) (_ : r ≤ ‖μ‖), Module.End.eigenspace (T : Module.End 𝕜 E) μ)ᗮ = ⊥ ∨ X ≤ (⨆ (μ : 𝕜) (_ : r ≤ ‖μ‖), Module.End.eigenspace (T : Module.End 𝕜 E) μ)ᗮ) :
    X ≤ LinearMap.ker (T : E →ₗ[𝕜] E) ∨ FiniteDimensional 𝕜 ↥X := by
  revert 𝕜 E T hT hT' X hX
  exact @_root_.P2MW.S_ContinuousLinearMap_le_ker_or_finiteDimensional_of_forall_inf_highPart_orthogonal.solution
