/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_constantsAreBase_of_isAlgClosed (git blob 1776ad9e096ebc07dc680d2c3c90cefa1dac84f1, sha256 fff3e328a58ea69f11ab7867f7f8301c84a360e3091aaf0cd4a978b3da668fe6).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlaceEvaluation
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorPushPull
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_RationalFunctionField_nonempty_place_of_ratFunc_tower
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_isRational_of_isAlgClosed
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_constantsAreBase_of_exists_isRational

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_constantsAreBase_of_isAlgClosed

open AlgebraicCurve

theorem solution (K F : Type*) [Field K] [Field F] [Algebra K F]
    [DecidableEq (RatFunc K)] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable (RatFunc K) F]
    [IsAlgClosed K] [AlgebraicCurve.IsCurveOver K F] :
    AlgebraicCurve.ConstantsAreBase K F := by
  obtain ⟨v⟩ := AlgebraicCurve.RationalFunctionField.nonempty_place_of_ratFunc_tower K F
  have hrat : v.IsRational := AlgebraicCurve.Place.isRational_of_isAlgClosed v
  exact AlgebraicCurve.constantsAreBase_of_exists_isRational v hrat
    (((v.isRational_iff_deg_eq_one).mp hrat).symm ▸ one_ne_zero)
