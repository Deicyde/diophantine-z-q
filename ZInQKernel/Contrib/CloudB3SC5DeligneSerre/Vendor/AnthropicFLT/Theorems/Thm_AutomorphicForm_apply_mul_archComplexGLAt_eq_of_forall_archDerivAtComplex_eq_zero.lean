/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_apply_mul_archComplexGLAt_eq_of_forall_archDerivAtComplex_eq_zero (git blob 39c6c50794df676eb1f7c7382e6c0980897aa9e5, sha256 6699b7bef582e8d3c4135428159ad013ce7ed978c2667a5992714e8c4871ab3d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_apply_mul_archComplexGLAt_eq_of_forall_archDerivAtComplex_eq_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open NumberField AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.Completion

theorem AutomorphicForm.apply_mul_archComplexGLAt_eq_of_forall_archDerivAtComplex_eq_zero
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsComplex)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAtComplex hw φ)
    (hD : ∀ d : ArchDirComplex, archDerivAtComplex hw d φ = 0)
    (g : AdelicGL2 (𝓞 F) F) (h : GL (Fin 2) ℂ) (hh : Matrix.GeneralLinearGroup.det h = 1) :
    φ (g * archComplexGLAt hw h) = φ g := by
  revert F w hw φ hφ hD g h hh
  exact @_root_.P2MW.S_AutomorphicForm_apply_mul_archComplexGLAt_eq_of_forall_archDerivAtComplex_eq_zero.solution
