/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_archCasimirAtComplex_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAtComplex (git blob e3bc56266d316f2ebdb16536ddffa86ca66e9f5d, sha256 5988c6bd31a3ebdbfe61b91c341459f8331c995e263678661f2631b1491a0c67).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalConstituent
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_FactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RightConvolution
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_archCasimirAtComplex_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAtComplex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.archCasimirAtComplex_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAtComplex
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsComplex)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hxc : Continuous x) (hxs : IsArchSmoothAtComplex hw x)
    (hD1 : ∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d x))
    (hD2 : ∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' x))) :
    ∀ (f : AdelicGL2 (𝓞 K) K → ℂ) (tys : AutomorphicForm.ArchTypeFamily K),
        IsFactorizableTestFn K f → IsArchBiFinite K tys f →
        IsArchSmoothAtComplex hw (rightConv K x f) ∧
        (∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d (rightConv K x f))) ∧
        (∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' (rightConv K x f)))) ∧
        archCasimirAtComplex hw (rightConv K x f) = rightConv K (archCasimirAtComplex hw x) f ∧
        archCasimirBarAtComplex hw (rightConv K x f) = rightConv K (archCasimirBarAtComplex hw x) f := by
  revert K w hw x hxc hxs hD1 hD2
  exact @_root_.P2MW.S_AutomorphicForm_archCasimirAtComplex_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAtComplex.solution
