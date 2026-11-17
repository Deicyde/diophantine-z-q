/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_EisensteinWeightOne_e1Chi3IsModular (git blob dd98734d29503bbeeea93ed21d7a072c015fa0af, sha256 67aceaafdb6165d02ea28c14d0f800ae518d5c0f565dd944206fa48d7afad4a2).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularForm_EisensteinChiNegThree
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_EisensteinWeightOne_e1Chi3IsModular

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open EisensteinWeightOne
theorem EisensteinWeightOne.e1Chi3IsModular : EisensteinWeightOne.E1Chi3IsModular := @_root_.P2MW.S_EisensteinWeightOne_e1Chi3IsModular.solution
