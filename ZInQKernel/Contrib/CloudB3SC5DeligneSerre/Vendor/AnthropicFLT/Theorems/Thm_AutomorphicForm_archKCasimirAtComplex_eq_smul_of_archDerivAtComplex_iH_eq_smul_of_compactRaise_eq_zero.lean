/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_archKCasimirAtComplex_eq_smul_of_archDerivAtComplex_iH_eq_smul_of_compactRaise_eq_zero (git blob 58d9e43e824caeb433263d5a12759f774d6b3f97, sha256 e10958e2542524aa3991982eba3157b6af754400b36c3011e9ec035c4e2ff435).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_archKCasimirAtComplex_eq_smul_of_archDerivAtComplex_iH_eq_smul_of_compactRaise_eq_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open NumberField AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.Completion

theorem AutomorphicForm.archKCasimirAtComplex_eq_smul_of_archDerivAtComplex_iH_eq_smul_of_compactRaise_eq_zero
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsComplex)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAtComplex hw φ) (n : ℕ)
    (hwt : archDerivAtComplex hw .iH φ = (Complex.I * (n : ℂ)) • φ)
    (hJ : archDerivAtComplex hw .Fm φ - archDerivAtComplex hw .E φ
      + Complex.I • (archDerivAtComplex hw .iE φ + archDerivAtComplex hw .iFm φ) = 0) :
    archKCasimirAtComplex hw φ = (-(((n : ℂ) ^ 2 + 2 * (n : ℂ)))) • φ := by
  revert F w hw φ hφ n hwt hJ
  exact @_root_.P2MW.S_AutomorphicForm_archKCasimirAtComplex_eq_smul_of_archDerivAtComplex_iH_eq_smul_of_compactRaise_eq_zero.solution
