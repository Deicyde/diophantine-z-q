/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_RationalFunctionField_nonempty_place_of_ratFunc_tower (git blob 710613c03ba05fa2226240b235249f05ddbcfda6, sha256 361d029f534a98a68773d805689df471bd62b97dd6a7bb69c52ed1dcb24998f0).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorPushPull
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_exists_restrict_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_RationalFunctionField_nonempty_place_of_ratFunc_tower

open AlgebraicCurve

theorem solution (K : Type*) [Field K]
    [DecidableEq (RatFunc K)] (F : Type*) [Field F] [Algebra K F] [Algebra (RatFunc K) F]
    [IsScalarTower K (RatFunc K) F] [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable (RatFunc K) F] :
    Nonempty (AlgebraicCurve.Place K F) :=
  (AlgebraicCurve.Place.exists_restrict_eq (M := F) (AlgebraicCurve.RationalFunctionField.placeInfty K)).nonempty
