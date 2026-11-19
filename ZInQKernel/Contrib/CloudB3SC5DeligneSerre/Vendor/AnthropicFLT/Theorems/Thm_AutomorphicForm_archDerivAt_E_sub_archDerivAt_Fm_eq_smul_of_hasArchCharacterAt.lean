/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAt (git blob 7c848894b407645f6269a71bc14dd49f8dcfa5e0, sha256 9425e2a9e9d03834f1e2fcd64262bf0d0fe824d0e0b6ec53369e33f03a45fa2a).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalConstituent
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchDerivCasimir
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_FactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RightConvolution
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAt
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal) (n : ℤ)
    (y : AdelicGL2 (𝓞 K) K → ℂ) (hys : IsArchSmoothAt hw y)
    (hyn : HasArchCharacterAt₀ K w (archWeightCharAt hw n) y) :
    archDerivAt hw .E y - archDerivAt hw .Fm y = (Complex.I * n) • y := by
  revert K w hw n y hys hyn
  exact @_root_.P2MW.S_AutomorphicForm_archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAt.solution
