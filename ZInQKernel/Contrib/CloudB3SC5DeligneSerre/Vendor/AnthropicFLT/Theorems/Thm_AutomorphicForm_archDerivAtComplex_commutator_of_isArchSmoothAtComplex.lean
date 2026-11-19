/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_archDerivAtComplex_commutator_of_isArchSmoothAtComplex (git blob 13e6d168206c6d1caf3776af775e6cc82bf33def, sha256 19ff23e9245114286849c56c6d83795312f743931d4d1e52c351b45252b0d1a7).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_archDerivAtComplex_commutator_of_isArchSmoothAtComplex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open NumberField AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.Completion

theorem AutomorphicForm.archDerivAtComplex_commutator_of_isArchSmoothAtComplex
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsComplex)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAtComplex hw φ) :
    archDerivAtComplex hw .H (archDerivAtComplex hw .E φ) - archDerivAtComplex hw .E (archDerivAtComplex hw .H φ) =
      (2 : ℂ) • archDerivAtComplex hw .E φ ∧
    archDerivAtComplex hw .H (archDerivAtComplex hw .Fm φ) - archDerivAtComplex hw .Fm (archDerivAtComplex hw .H φ) =
      (-2 : ℂ) • archDerivAtComplex hw .Fm φ ∧
    archDerivAtComplex hw .E (archDerivAtComplex hw .Fm φ) - archDerivAtComplex hw .Fm (archDerivAtComplex hw .E φ) =
      (1 : ℂ) • archDerivAtComplex hw .H φ ∧
    archDerivAtComplex hw .H (archDerivAtComplex hw .iE φ) - archDerivAtComplex hw .iE (archDerivAtComplex hw .H φ) =
      (2 : ℂ) • archDerivAtComplex hw .iE φ ∧
    archDerivAtComplex hw .H (archDerivAtComplex hw .iFm φ) - archDerivAtComplex hw .iFm (archDerivAtComplex hw .H φ) =
      (-2 : ℂ) • archDerivAtComplex hw .iFm φ ∧
    archDerivAtComplex hw .E (archDerivAtComplex hw .iFm φ) - archDerivAtComplex hw .iFm (archDerivAtComplex hw .E φ) =
      (1 : ℂ) • archDerivAtComplex hw .iH φ ∧
    archDerivAtComplex hw .iE (archDerivAtComplex hw .Fm φ) - archDerivAtComplex hw .Fm (archDerivAtComplex hw .iE φ) =
      (1 : ℂ) • archDerivAtComplex hw .iH φ ∧
    archDerivAtComplex hw .iH (archDerivAtComplex hw .E φ) - archDerivAtComplex hw .E (archDerivAtComplex hw .iH φ) =
      (2 : ℂ) • archDerivAtComplex hw .iE φ ∧
    archDerivAtComplex hw .iH (archDerivAtComplex hw .Fm φ) - archDerivAtComplex hw .Fm (archDerivAtComplex hw .iH φ) =
      (-2 : ℂ) • archDerivAtComplex hw .iFm φ ∧
    archDerivAtComplex hw .iH (archDerivAtComplex hw .iE φ) - archDerivAtComplex hw .iE (archDerivAtComplex hw .iH φ) =
      (-2 : ℂ) • archDerivAtComplex hw .E φ ∧
    archDerivAtComplex hw .iH (archDerivAtComplex hw .iFm φ) - archDerivAtComplex hw .iFm (archDerivAtComplex hw .iH φ) =
      (2 : ℂ) • archDerivAtComplex hw .Fm φ ∧
    archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm φ) - archDerivAtComplex hw .iFm (archDerivAtComplex hw .iE φ) =
      (-1 : ℂ) • archDerivAtComplex hw .H φ ∧
    archDerivAtComplex hw .H (archDerivAtComplex hw .iH φ) - archDerivAtComplex hw .iH (archDerivAtComplex hw .H φ) =
      0 ∧
    archDerivAtComplex hw .E (archDerivAtComplex hw .iE φ) - archDerivAtComplex hw .iE (archDerivAtComplex hw .E φ) =
      0 ∧
    archDerivAtComplex hw .Fm (archDerivAtComplex hw .iFm φ) - archDerivAtComplex hw .iFm (archDerivAtComplex hw .Fm φ) =
      0 := by
  revert F w hw φ hφ
  exact @_root_.P2MW.S_AutomorphicForm_archDerivAtComplex_commutator_of_isArchSmoothAtComplex.solution
