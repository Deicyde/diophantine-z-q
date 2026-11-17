/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Place_count_normalizedFactors_span_singleton (git blob 72dcaba50b90e1fefde401de8b454324d941b101, sha256 77bde649646fd48be56e5826afc8e21f7f2b69eb37bef89654dc2995e669286e).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlacesOverDVR
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Place_count_normalizedFactors_span_singleton

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve
theorem AlgebraicCurve.Place.count_normalizedFactors_span_singleton {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] {v : Place K F} {w : Place K F'} (hw : w.restrict F = v) {c : Place.integralClosureAt F' v} (hc : c ≠ 0) : (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {c})).count (Place.fiberCenter F' v hw).asIdeal = (w.ord (algebraMap (Place.integralClosureAt F' v) F' c)).toNat := by
  revert K F F' v w hw c hc
  exact @_root_.P2MW.S_AlgebraicCurve_Place_count_normalizedFactors_span_singleton.solution
