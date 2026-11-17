/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_closure_elemSet_eq_top (git blob d719b19594f40a3c4f0476b32fdbc9821b95422b, sha256 440a786e54074a8c357de23876db77b76d80d38d864e875094cdd1b4d908585c).
Modified for the Z-in-Q kernel (2026-11-16, cluster C5): import paths relocated (modules already
vendored elsewhere in the kernel are imported from there), the upstream lakefile options set as
`set_option` lines, and: dropped import P2M.Util (wrapper commands replaced by ordinary Lean); replaced 1 proof-wrapper tactic call(s) by `revert` + `exact` of the paired Sol proof.
Any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_SL2Elementary
import Mathlib.Data.ZMod.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_closure_elemSet_eq_top

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem ModularCurve.closure_elemSet_eq_top (N : ℕ) [NeZero N] :
    Subgroup.closure (ModularCurve.elemSet (ZMod N)) = ⊤ := by
  revert N
  exact @_root_.P2MW.S_ModularCurve_closure_elemSet_eq_top.solution
