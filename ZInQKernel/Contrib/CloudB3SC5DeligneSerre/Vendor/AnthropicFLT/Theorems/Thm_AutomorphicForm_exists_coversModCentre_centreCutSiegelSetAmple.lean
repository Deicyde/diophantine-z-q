/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_exists_coversModCentre_centreCutSiegelSetAmple (git blob 505f12b0893f5e70c54b7ac7f1f024812c9fc7d5, sha256 b38421b0bf0ea3daa2d1584e44f1c0ec1a5010912bea998c909ea4ab2b98da18).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CentreCutSiegelSetAmple
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_SiegelCovering
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_exists_coversModCentre_centreCutSiegelSetAmple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open NumberField NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

theorem AutomorphicForm.exists_coversModCentre_centreCutSiegelSetAmple
    (F : Type) [Field F] [NumberField F] :
    ∃ κ R : ℝ, 1 ≤ κ ∧ 0 ≤ R ∧
      ∀ (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)),
        CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) →
        CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple F c (max u R) d₁ d₂ κ) := by
  revert F
  exact @_root_.P2MW.S_AutomorphicForm_exists_coversModCentre_centreCutSiegelSetAmple.solution
