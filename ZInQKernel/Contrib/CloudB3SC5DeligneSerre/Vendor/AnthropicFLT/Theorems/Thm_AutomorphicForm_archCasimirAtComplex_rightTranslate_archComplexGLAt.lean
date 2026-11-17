/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_archCasimirAtComplex_rightTranslate_archComplexGLAt (git blob e132d5c079d19cda44ca5e6126759358598ca382, sha256 09ef4a945cd4f981a250e9b12238364bf22b728ec54d5b69452a2d098f8e7ff4).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalConstituent
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_FactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RightConvolution
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_archCasimirAtComplex_rightTranslate_archComplexGLAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.archCasimirAtComplex_rightTranslate_archComplexGLAt
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsComplex)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hxc : Continuous x) (hxs : IsArchSmoothAtComplex hw x)
    (hD1 : ∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d x))
    (hD2 : ∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' x))) :
    ∀ m : GL (Fin 2) ℂ,
        IsArchSmoothAtComplex hw (rightTranslate K (archComplexGLAt hw m) x) ∧
        (∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d (rightTranslate K (archComplexGLAt hw m) x))) ∧
        (∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d'
          (rightTranslate K (archComplexGLAt hw m) x)))) ∧
        archCasimirAtComplex hw (rightTranslate K (archComplexGLAt hw m) x) =
          rightTranslate K (archComplexGLAt hw m) (archCasimirAtComplex hw x) ∧
        archCasimirBarAtComplex hw (rightTranslate K (archComplexGLAt hw m) x) =
          rightTranslate K (archComplexGLAt hw m) (archCasimirBarAtComplex hw x) := by
  revert K w hw x hxc hxs hD1 hD2
  exact @_root_.P2MW.S_AutomorphicForm_archCasimirAtComplex_rightTranslate_archComplexGLAt.solution
