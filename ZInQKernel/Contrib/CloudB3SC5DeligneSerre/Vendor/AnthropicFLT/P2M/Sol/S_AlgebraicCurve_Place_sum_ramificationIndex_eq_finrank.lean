/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_Place_sum_ramificationIndex_eq_finrank (git blob 510462b89e98e015d8f02d3005b300f895168758, sha256 5bd50a9120aab9fdd81e9bd1ec1e680ab09fb0512694c73c111bd9b32d51995b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlaceEvaluation
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorPushPull
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_inertiaDeg_eq_one_of_isRational

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_Place_sum_ramificationIndex_eq_finrank

open AlgebraicCurve

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [HasPrincipalDivisors K F'] (v : Place K F) (hv : v.IsRational) (hrat : ∀ w ∈ v.fiber F', Place.IsRational w) : ∑ w ∈ v.fiber F', (w.ramificationIndex F : ℤ) = (Module.finrank F F' : ℤ) := by
  rw [← AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg (F' := F') v]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [w.inertiaDeg_eq_one_of_isRational (hrat w hw)
    ((Place.mem_fiber.mp hw).symm ▸ hv), Nat.cast_one, mul_one]
