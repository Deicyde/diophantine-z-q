/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_TateCurve_defectCoeff_zero (git blob 6d2d68f18779cda9171bb3c95d568c329a544b6d, sha256 dd5f4e7a8fba612f1c2ad4e29e7a9a48714322d04f8319054387cef31198bbec).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_TateCurve_Defect
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_TateCurve_defectCoeff_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open TateCurve
open scoped NNReal
theorem TateCurve.defectCoeff_zero {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u : K} (hu1 : u ≠ 1) : defectCoeff u 0 = 0 := by
  revert K u hu1
  exact @_root_.P2MW.S_TateCurve_defectCoeff_zero.solution
