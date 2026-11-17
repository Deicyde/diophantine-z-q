/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ContinuousLinearMap_map_highPart_orthogonal_le_of_commute (git blob 6eb45dee9405abca054d18c5f7dbfe7f2f4b82b8, sha256 2ea52dd919bdffec4c2a2256388b42683cb6b41f7d2c864de92dc907d166bf81).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ContinuousLinearMap_map_highPart_orthogonal_le_of_commute

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open Module.End

theorem ContinuousLinearMap.map_highPart_orthogonal_le_of_commute {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] {T S : E →L[𝕜] E}
    (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) (hST : S.comp T = T.comp S) (r : ℝ) :
    Submodule.map (S : E →ₗ[𝕜] E) (⨆ (μ : 𝕜) (_ : r ≤ ‖μ‖), Module.End.eigenspace (T : Module.End 𝕜 E) μ)ᗮ ≤ (⨆ (μ : 𝕜) (_ : r ≤ ‖μ‖), Module.End.eigenspace (T : Module.End 𝕜 E) μ)ᗮ := by
  revert 𝕜 E T S hT' hST r
  exact @_root_.P2MW.S_ContinuousLinearMap_map_highPart_orthogonal_le_of_commute.solution
