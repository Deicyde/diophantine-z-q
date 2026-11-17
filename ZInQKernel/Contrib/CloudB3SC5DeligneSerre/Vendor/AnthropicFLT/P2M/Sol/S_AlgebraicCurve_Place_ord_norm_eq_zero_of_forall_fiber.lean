/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_Place_ord_norm_eq_zero_of_forall_fiber (git blob 61fe503305a7a1797f7a69de481bd4cc4309e413, sha256 4125456d02532fe85a69968b96a747889b6c4f69072198c2c1f988d33a1c874d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlacesOverDVR
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_ord_norm_eq_sum_fiberOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_Place_ord_norm_eq_zero_of_forall_fiber

open AlgebraicCurve

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [CharZero F] [HasPrincipalDivisors K F'] {f : F'} (hf : f ≠ 0) (v : Place K F) (h : ∀ w ∈ v.fiber F', w.ord f = 0) : v.ord (Algebra.norm F f) = 0 := by
  rw [AlgebraicCurve.Place.ord_norm_eq_sum_fiberOver v hf, ← Place.fiber_eq_fiberOver]
  exact Finset.sum_eq_zero fun w hw => by rw [h w hw, mul_zero]
