/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_RationalFunctionField_hasPrincipalDivisors (git blob 7d0f359e7938d1263f36cc4c4fd57c87423de4a9, sha256 2f7edd096c3848818ed3c9519109a42624adbc1e0e7e68087a4e4d33a121b4e1).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.FieldTheory.RatFunc.Basic
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_RationalFunctionField_hasPrincipalDivisors

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicCurve
theorem AlgebraicCurve.RationalFunctionField.hasPrincipalDivisors (K : Type*) [Field K] : HasPrincipalDivisors K (RatFunc K) := by
  revert K
  exact @_root_.P2MW.S_AlgebraicCurve_RationalFunctionField_hasPrincipalDivisors.solution
