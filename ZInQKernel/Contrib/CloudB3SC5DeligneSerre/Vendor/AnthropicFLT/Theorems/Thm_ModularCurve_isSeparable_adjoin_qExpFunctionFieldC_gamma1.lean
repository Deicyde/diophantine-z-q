/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_isSeparable_adjoin_qExpFunctionFieldC_gamma1 (git blob 00b28c6828d28bc81a14a3e360c941b3c1055a0d, sha256 315bfb964205fe40bc61640198dee0dd33ee877b802a045974dc60b180c0f0df).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_JqCoeff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_isSeparable_adjoin_qExpFunctionFieldC_gamma1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open ModularCurve

universe u in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.isSeparable_adjoin_qExpFunctionFieldC_gamma1
    (K : Type u) [Field K] [IsAlgClosed K] (M : ℕ) [NeZero M]
    (x : qExpFunctionFieldC K (CongruenceSubgroup.Gamma1 M))
    (hx : (x : LaurentSeries K) = jqModC K) :
    Algebra.IsSeparable
      (IntermediateField.adjoin K ({x} : Set (qExpFunctionFieldC K (CongruenceSubgroup.Gamma1 M))))
      (qExpFunctionFieldC K (CongruenceSubgroup.Gamma1 M)) := by
  revert K M x hx
  exact @_root_.P2MW.S_ModularCurve_isSeparable_adjoin_qExpFunctionFieldC_gamma1.solution
