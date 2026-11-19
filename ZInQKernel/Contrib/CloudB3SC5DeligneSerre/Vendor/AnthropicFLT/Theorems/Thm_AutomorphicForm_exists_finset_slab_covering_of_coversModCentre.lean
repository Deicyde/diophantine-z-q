/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_exists_finset_slab_covering_of_coversModCentre (git blob 8c22536e7958d386ef90ed667189c5613b7efc7b, sha256 4c8e4004acdc909ae46e8277f2a86b4d41d9983178f5f3f89f9cc894b1d2e98c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_SiegelCovering
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_TateGlobalZeta
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_exists_finset_slab_covering_of_coversModCentre

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
theorem AutomorphicForm.exists_finset_slab_covering_of_coversModCentre
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (α β : ℝ) (hα : 0 < α) :
    ∃ T' : Finset (AdelicGL2 (𝓞 F) F), ∀ g : AdelicGL2 (𝓞 F) F,
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β →
        ∃ γ : GL (Fin 2) F,
          globalPoints (𝓞 F) F γ * g ∈ ⋃ x ∈ T', (· * x) '' centreCutSiegelSet F c u d₁ d₂ := by
  revert F c u d₁ d₂ T hd hcov α β hα
  exact @_root_.P2MW.S_AutomorphicForm_exists_finset_slab_covering_of_coversModCentre.solution
