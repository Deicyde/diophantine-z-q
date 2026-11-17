/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_finsum_ramificationIndexAlong_sub_one_eq (git blob f393e25216b804db12db523a4aadf4f60d433abe, sha256 786522bdb2cd9d93c3558e81b30929b3797009591798c7f6080578553ed71638).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CanonicalDivisor
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RegularDifferentials
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Correspondence
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_finsum_ramificationIndexAlong_sub_one_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve IntermediateField

theorem AlgebraicCurve.finsum_ramificationIndexAlong_sub_one_eq
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    {F : Type*} [Field F] [Algebra K F] [IsCurveOver K F] [Algebra.EssFiniteType K F]
    [HasCanonicalDivisor (K := K) (F := F)]
    {f : F} (htr : Transcendental K f)
    [FiniteDimensional (↥(adjoin K ({f} : Set F))) F] :
    (∑ᶠ w : Place K F, ((Place.ramificationIndexAlong (adjoin K ({f} : Set F)).val w : ℤ) - 1)) =
      2 * (Module.finrank K ↥(regularDifferentials K F) : ℤ) - 2 +
      2 * (Module.finrank (↥(adjoin K ({f} : Set F))) F : ℤ) := by
  revert K F f htr
  exact @_root_.P2MW.S_AlgebraicCurve_finsum_ramificationIndexAlong_sub_one_eq.solution
