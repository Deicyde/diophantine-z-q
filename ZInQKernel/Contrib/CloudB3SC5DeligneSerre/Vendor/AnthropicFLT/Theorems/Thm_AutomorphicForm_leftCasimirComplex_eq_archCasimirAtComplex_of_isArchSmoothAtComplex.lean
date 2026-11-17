/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_leftCasimirComplex_eq_archCasimirAtComplex_of_isArchSmoothAtComplex (git blob 9f0d369cc49546f7aca7c55a1103349ba30154b2, sha256 2aab9c707e31fbd6be3679ea473dddd34afceff7807896032dcc35363070893d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalConstituent
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_FactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RightConvolution
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_leftCasimirComplex_eq_archCasimirAtComplex_of_isArchSmoothAtComplex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.leftCasimirComplex_eq_archCasimirAtComplex_of_isArchSmoothAtComplex
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsComplex)
    (θ : AdelicGL2 (𝓞 K) K → ℂ) (hθ : IsArchSmoothAtComplex hw θ) :
    let L : ArchDirComplex → (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun d γ y => deriv (fun t : ℝ => γ (archFlowAtComplex hw d (-t) * y)) 0
    ∀ y : AdelicGL2 (𝓞 K) K,
      -((1 / 4 : ℂ) * ((1 / 4 : ℂ) * ((1 : ℂ) * L .H (L .H θ) y + ((-Complex.I) : ℂ) * L .H (L .iH θ) y + ((-Complex.I) : ℂ) * L .iH (L .H θ) y + (-1 : ℂ) * L .iH (L .iH θ) y)) - (1 / 2 : ℂ) * ((1 / 2 : ℂ) * ((1 : ℂ) * L .H θ y + ((-Complex.I) : ℂ) * L .iH θ y)) + (1 / 4 : ℂ) * ((1 : ℂ) * L .E (L .Fm θ) y + ((-Complex.I) : ℂ) * L .E (L .iFm θ) y + ((-Complex.I) : ℂ) * L .iE (L .Fm θ) y + (-1 : ℂ) * L .iE (L .iFm θ) y)) = archCasimirAtComplex hw θ y ∧
      -((1 / 4 : ℂ) * ((1 / 4 : ℂ) * ((1 : ℂ) * L .H (L .H θ) y + (Complex.I : ℂ) * L .H (L .iH θ) y + (Complex.I : ℂ) * L .iH (L .H θ) y + (-1 : ℂ) * L .iH (L .iH θ) y)) - (1 / 2 : ℂ) * ((1 / 2 : ℂ) * ((1 : ℂ) * L .H θ y + (Complex.I : ℂ) * L .iH θ y)) + (1 / 4 : ℂ) * ((1 : ℂ) * L .E (L .Fm θ) y + (Complex.I : ℂ) * L .E (L .iFm θ) y + (Complex.I : ℂ) * L .iE (L .Fm θ) y + (-1 : ℂ) * L .iE (L .iFm θ) y)) = archCasimirBarAtComplex hw θ y := by
  revert K w hw θ hθ
  exact @_root_.P2MW.S_AutomorphicForm_leftCasimirComplex_eq_archCasimirAtComplex_of_isArchSmoothAtComplex.solution
