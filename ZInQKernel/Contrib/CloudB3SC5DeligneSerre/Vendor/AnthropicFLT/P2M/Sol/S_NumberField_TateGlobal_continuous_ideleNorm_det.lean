/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_NumberField_TateGlobal_continuous_ideleNorm_det (git blob 4ea6d2970777c302639e856a71108d0c64aafd2a, sha256 7a4e735b3af696409ff7bff1fbd2b7e378b23e3083776298939ed7a9be36f521).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_TateGlobalZeta
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_NumberField_TateGlobal_continuous_ideleNorm_det

set_option autoImplicit false

open NumberField AutomorphicForm

open NumberField.TateGlobal in

theorem solution (F : Type) [Field F] [NumberField F] :
    Continuous fun g : AdelicGL2 (𝓞 F) F => ideleNorm F (Matrix.GeneralLinearGroup.det g) :=
  (NumberField.TateGlobal.continuous_ideleNorm F).comp Matrix.GeneralLinearGroup.continuous_det
