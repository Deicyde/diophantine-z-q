/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_constantsAreBase_of_isAlgClosed (git blob b1cd21181abd188f91d79572a7f63bd89b5e0fa5, sha256 f49645dbf4d8ef9614c1f0dcbed9566d2b1521008cb50eeea99966a7d043bbc1).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_constantsAreBase_of_isAlgClosed

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem AlgebraicCurve.constantsAreBase_of_isAlgClosed (K F : Type*) [Field K] [Field F] [Algebra K F]
    [DecidableEq (RatFunc K)] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable (RatFunc K) F]
    [IsAlgClosed K] [AlgebraicCurve.IsCurveOver K F] :
    AlgebraicCurve.ConstantsAreBase K F := by
  revert K F
  exact @_root_.P2MW.S_AlgebraicCurve_constantsAreBase_of_isAlgClosed.solution
