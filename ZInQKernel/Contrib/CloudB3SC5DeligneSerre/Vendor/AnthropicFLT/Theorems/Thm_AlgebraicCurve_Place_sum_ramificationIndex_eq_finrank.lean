/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndex_eq_finrank (git blob 3f26cffad82cb86ffb9b20daf61b5b67fa2f004d, sha256 58aec3814c36a4d883872743488d56c3d62b0d5b956c03d11c34924a98f1cfc1).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlaceEvaluation
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorPushPull
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Place_sum_ramificationIndex_eq_finrank

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve
theorem AlgebraicCurve.Place.sum_ramificationIndex_eq_finrank {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [HasPrincipalDivisors K F'] (v : Place K F) (hv : v.IsRational) (hrat : ∀ w ∈ v.fiber F', Place.IsRational w) : ∑ w ∈ v.fiber F', (w.ramificationIndex F : ℤ) = (Module.finrank F F' : ℤ) := by
  revert K F F' v hv hrat
  exact @_root_.P2MW.S_AlgebraicCurve_Place_sum_ramificationIndex_eq_finrank.solution
