/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Place_exists_integralClosureAt_of_ord_fiber_nonneg (git blob cb371619497bbdfc383e54f2d6f29d3d8c54c652, sha256 f5794e65d46dabb76c5e981e907f029455308947b65f326193a44138af736fea).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlacesOverDVR
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Place_exists_integralClosureAt_of_ord_fiber_nonneg

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve
theorem AlgebraicCurve.Place.exists_integralClosureAt_of_ord_fiber_nonneg {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] {v : Place K F} [HasPrincipalDivisors K F'] {f : F'} (hf : f ≠ 0) (hord : ∀ w ∈ v.fiber F', 0 ≤ w.ord f) : ∃ c : Place.integralClosureAt F' v, algebraMap (Place.integralClosureAt F' v) F' c = f := by
  revert K F F' v f hf hord
  exact @_root_.P2MW.S_AlgebraicCurve_Place_exists_integralClosureAt_of_ord_fiber_nonneg.solution
