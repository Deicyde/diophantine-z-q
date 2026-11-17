/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_not_coversModCentre_iUnion_centreCutSiegelSet_of_eq_zero (git blob 732342f05de45a2cfef0e0d02dcd7b82737d869f, sha256 32dd13d513ab47e61699e0c4b21574456f7b016a322ef073ea7ff30660294e1b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_SiegelCovering
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_not_coversModCentre_iUnion_centreCutSiegelSet_of_eq_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm AutomorphicForm.WindowedSiegel
  AutomorphicForm.SiegelCovering

theorem AutomorphicForm.not_coversModCentre_iUnion_centreCutSiegelSet_of_eq_zero
    (F : Type) [Field F] [NumberField F] (c d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)) :
    ¬ CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c 0 d₁ d₂) := by
  revert F c d₁ d₂ T
  exact @_root_.P2MW.S_AutomorphicForm_not_coversModCentre_iUnion_centreCutSiegelSet_of_eq_zero.solution
