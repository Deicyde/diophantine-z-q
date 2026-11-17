/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_WeierstrassCurve_finite_stabilizer_variableChange (git blob 84918271e6559857ebd4fbb7577c76c983959eab, sha256 1f3249196f660df45e2b382afcf4de256af21db3d5ae45565b74a55c578ec337).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_WeierstrassCurve_finite_stabilizer_variableChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem WeierstrassCurve.finite_stabilizer_variableChange (F : Type*) [Field F] (E : WeierstrassCurve F) [E.IsElliptic] : Finite (MulAction.stabilizer (WeierstrassCurve.VariableChange F) E) := by
  revert F E
  exact @_root_.P2MW.S_WeierstrassCurve_finite_stabilizer_variableChange.solution
