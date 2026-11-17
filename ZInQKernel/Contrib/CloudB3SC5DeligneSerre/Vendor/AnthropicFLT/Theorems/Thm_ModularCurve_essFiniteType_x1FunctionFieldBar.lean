/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_essFiniteType_x1FunctionFieldBar (git blob 29f2d64ee0ee4e8384ed9177db166febcaf01da1, sha256 980ab632620dda09960618af116ad3bba0c18c6662055c3f0c8399d6eef22cbf).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_essFiniteType_x1FunctionFieldBar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace AlgebraicCurve
end AlgebraicCurve
namespace ModularCurve
end ModularCurve

set_option autoImplicit false

open _root_.AlgebraicCurve hiding essFiniteType_of_transcendental_of_finiteDimensional
open _root_.ModularCurve

theorem ModularCurve.essFiniteType_x1FunctionFieldBar (M : ℕ) [NeZero M] :
    Algebra.EssFiniteType (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar M) := by
  revert M
  exact @_root_.P2MW.S_ModularCurve_essFiniteType_x1FunctionFieldBar.solution
