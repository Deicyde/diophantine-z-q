/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap_eq_evalAt_restrict (git blob 5c3c6ad57320edad1c39d3fc4fe8ce28d1e9c4b5, sha256 57e39edee25805a9b9a762a385805b1f798efd62acbf804d8690c5c06aef754e).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlaceEvaluation
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorPushPull
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Place_evalAt_algebraMap_eq_evalAt_restrict

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicCurve
theorem AlgebraicCurve.Place.evalAt_algebraMap_eq_evalAt_restrict {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (w : Place K F') (hv : (w.restrict F).IsRational) {g : F} (hg : g ∈ (w.restrict F).toValuationSubring) : w.evalAt (algebraMap F F' g) = (w.restrict F).evalAt g := by
  revert K F F' w hv g hg
  exact @_root_.P2MW.S_AlgebraicCurve_Place_evalAt_algebraMap_eq_evalAt_restrict.solution
