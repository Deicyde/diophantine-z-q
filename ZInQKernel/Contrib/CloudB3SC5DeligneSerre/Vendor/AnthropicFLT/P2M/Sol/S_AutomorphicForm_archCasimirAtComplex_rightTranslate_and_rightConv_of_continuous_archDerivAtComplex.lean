/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_archCasimirAtComplex_rightTranslate_and_rightConv_of_continuous_archDerivAtComplex (git blob 156a23091f0b2b38b506d27bd3f9090f7cd66337, sha256 fde17597ec60390d5ccb3b2e22bcf0869b7f7b0a3a276bdf21023928de7b6771).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_archCasimirAtComplex_rightTranslate_rowIsometryInclAt_of_ne
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_archCasimirAtComplex_rightTranslate_archComplexGLAt
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_archCasimirAtComplex_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAtComplex
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchDerivCasimirComplexAPI
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalConstituent
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_FactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RightConvolution

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_archCasimirAtComplex_rightTranslate_and_rightConv_of_continuous_archDerivAtComplex

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

open NumberField.InfinitePlace.Completion

theorem solution
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsComplex)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hxc : Continuous x) (hxs : IsArchSmoothAtComplex hw x)
    (hD1 : ∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d x))
    (hD2 : ∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' x))) :
    (∀ (w' : InfinitePlace K) (k : rowIsometrySubgroup₀ w'.Completion),
        IsArchSmoothAtComplex hw (rightTranslate K (rowIsometryInclAt₀ K w' k) x) ∧
        (∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d (rightTranslate K (rowIsometryInclAt₀ K w' k) x))) ∧
        (∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d'
          (rightTranslate K (rowIsometryInclAt₀ K w' k) x)))) ∧
        archCasimirAtComplex hw (rightTranslate K (rowIsometryInclAt₀ K w' k) x) =
          rightTranslate K (rowIsometryInclAt₀ K w' k) (archCasimirAtComplex hw x) ∧
        archCasimirBarAtComplex hw (rightTranslate K (rowIsometryInclAt₀ K w' k) x) =
          rightTranslate K (rowIsometryInclAt₀ K w' k) (archCasimirBarAtComplex hw x)) ∧
    (∀ (f : AdelicGL2 (𝓞 K) K → ℂ) (tys : AutomorphicForm.ArchTypeFamily K),
        IsFactorizableTestFn K f → IsArchBiFinite K tys f →
        IsArchSmoothAtComplex hw (rightConv K x f) ∧
        (∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d (rightConv K x f))) ∧
        (∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' (rightConv K x f)))) ∧
        archCasimirAtComplex hw (rightConv K x f) = rightConv K (archCasimirAtComplex hw x) f ∧
        archCasimirBarAtComplex hw (rightConv K x f) = rightConv K (archCasimirBarAtComplex hw x) f) := by
  classical
  refine ⟨?_, AutomorphicForm.archCasimirAtComplex_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAtComplex
    K w hw x hxc hxs hD1 hD2⟩
  intro w' k
  by_cases hw' : w' = w
  · subst hw'

    have hkm : rowIsometryInclAt₀ K w' k =
        archComplexGLAt hw (glEquivOfRingEquiv (ringEquivComplexOfIsComplex hw) (k : GL (Fin 2) w'.Completion)) := by
      rw [rowIsometryInclAt₀_apply, archComplexGLAt_glEquivOfRingEquiv]
    rw [hkm]
    exact AutomorphicForm.archCasimirAtComplex_rightTranslate_archComplexGLAt K w' hw x hxc hxs hD1 hD2 _
  · exact AutomorphicForm.archCasimirAtComplex_rightTranslate_rowIsometryInclAt_of_ne K w hw x hxc hxs hD1 hD2 w' hw' k
