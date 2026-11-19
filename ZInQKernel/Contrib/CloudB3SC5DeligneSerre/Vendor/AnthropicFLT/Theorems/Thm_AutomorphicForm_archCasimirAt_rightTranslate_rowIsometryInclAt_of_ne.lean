/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_archCasimirAt_rightTranslate_rowIsometryInclAt_of_ne (git blob 8195167714a5be513224123a16b1f962ed7376a4, sha256 8139500f8bf6cc48258e3399fe7f6bbe552945d10f0a5c57596f742def696688).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalConstituent
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchDerivCasimir
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_FactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RightConvolution
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_archCasimirAt_rightTranslate_rowIsometryInclAt_of_ne

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.archCasimirAt_rightTranslate_rowIsometryInclAt_of_ne
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hxc : Continuous x) (hxs : IsArchSmoothAt hw x)
    (hD1 : ∀ d : ArchDir, Continuous (archDerivAt hw d x))
    (hD2 : ∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' x))) :
    ∀ (w' : InfinitePlace K) (hw' : w' ≠ w) (k : rowIsometrySubgroup₀ w'.Completion),
        IsArchSmoothAt hw (rightTranslate K (rowIsometryInclAt₀ K w' k) x) ∧
        (∀ d : ArchDir, Continuous (archDerivAt hw d (rightTranslate K (rowIsometryInclAt₀ K w' k) x))) ∧
        (∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d'
          (rightTranslate K (rowIsometryInclAt₀ K w' k) x)))) ∧
        archCasimirAt hw (rightTranslate K (rowIsometryInclAt₀ K w' k) x) =
          rightTranslate K (rowIsometryInclAt₀ K w' k) (archCasimirAt hw x) := by
  revert K w hw x hxc hxs hD1 hD2
  exact @_root_.P2MW.S_AutomorphicForm_archCasimirAt_rightTranslate_rowIsometryInclAt_of_ne.solution
