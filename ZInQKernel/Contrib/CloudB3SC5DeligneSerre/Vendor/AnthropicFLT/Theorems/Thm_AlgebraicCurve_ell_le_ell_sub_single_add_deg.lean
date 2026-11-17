/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_ell_le_ell_sub_single_add_deg (git blob f70f102c2ad4a9bc0fa49b7b8fffd9e4002724d9, sha256 ed4d74978095ac92491ee31a4ef33783c74e5f2d8055aef677fa76aea6bd4819).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_ell_le_ell_sub_single_add_deg

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace AlgebraicCurve
theorem ell_le_ell_sub_single_add_deg {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F] (D : Divisor K F) (P : Place K F) :
    ell D ≤ ell (D - Finsupp.single P 1) + P.deg := by
  revert K F D P
  exact @_root_.P2MW.S_AlgebraicCurve_ell_le_ell_sub_single_add_deg.solution
end AlgebraicCurve
