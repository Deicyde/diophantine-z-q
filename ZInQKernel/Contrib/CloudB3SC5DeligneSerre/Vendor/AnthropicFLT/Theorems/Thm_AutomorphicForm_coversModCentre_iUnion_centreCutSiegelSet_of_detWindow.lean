/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_coversModCentre_iUnion_centreCutSiegelSet_of_detWindow (git blob fd3848af30572692943213daddacf0ce830347e9, sha256 67d269348cf93f4c14397b23586c6ef58cc01c39e76becd5329e72c67dfbeabf).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_SiegelCovering
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_coversModCentre_iUnion_centreCutSiegelSet_of_detWindow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm AutomorphicForm.WindowedSiegel
  AutomorphicForm.SiegelCovering

theorem AutomorphicForm.coversModCentre_iUnion_centreCutSiegelSet_of_detWindow
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ e₁ e₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (he₂ : 0 < e₂) (he : e₁ ≤ e₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) :
    CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u e₁ e₂) := by
  revert F c u d₁ d₂ e₁ e₂ T he₂ he hcov
  exact @_root_.P2MW.S_AutomorphicForm_coversModCentre_iUnion_centreCutSiegelSet_of_detWindow.solution
