/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_archCasimirAtComplex_add_archCasimirBarAtComplex_eq_of_isArchSmoothAtComplex (git blob 9df165d16d1295d9a059a832aabaf7e44af13816, sha256 824db371d4e177aa236da645d2d4d835d2ac13e731bd740eada31628305b2013).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_archCasimirAtComplex_add_archCasimirBarAtComplex_eq_of_isArchSmoothAtComplex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open NumberField AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.Completion

theorem AutomorphicForm.archCasimirAtComplex_add_archCasimirBarAtComplex_eq_of_isArchSmoothAtComplex
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsComplex)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAtComplex hw φ) :
    archCasimirAtComplex hw φ + archCasimirBarAtComplex hw φ
      = (1 / 8 : ℂ) • archKCasimirAtComplex hw φ
        - (1 / 8 : ℂ) • (archDerivAtComplex hw .H (archDerivAtComplex hw .H φ) +
            (archDerivAtComplex hw .E (archDerivAtComplex hw .E φ + archDerivAtComplex hw .Fm φ) +
              archDerivAtComplex hw .Fm (archDerivAtComplex hw .E φ + archDerivAtComplex hw .Fm φ)) +
            (archDerivAtComplex hw .iFm (archDerivAtComplex hw .iFm φ - archDerivAtComplex hw .iE φ) -
              archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm φ - archDerivAtComplex hw .iE φ))) := by
  revert F w hw φ hφ
  exact @_root_.P2MW.S_AutomorphicForm_archCasimirAtComplex_add_archCasimirBarAtComplex_eq_of_isArchSmoothAtComplex.solution
