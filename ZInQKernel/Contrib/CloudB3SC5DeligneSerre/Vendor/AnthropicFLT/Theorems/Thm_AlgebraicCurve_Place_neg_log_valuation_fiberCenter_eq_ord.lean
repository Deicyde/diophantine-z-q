/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Place_neg_log_valuation_fiberCenter_eq_ord (git blob 85f5584538dbed710d0bbc7a789acde908edf072, sha256 b649b81a525b0bb9b84cc2d55c984ea57e7f10fb00c642df3a2560f50ab97001).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlacesOverDVR
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Place_neg_log_valuation_fiberCenter_eq_ord

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve
theorem AlgebraicCurve.Place.neg_log_valuation_fiberCenter_eq_ord {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] {v : Place K F} {w : Place K F'} (hw : w.restrict F = v) {x : F'} (hx : x ≠ 0) : -WithZero.log ((Place.fiberCenter F' v hw).valuation F' x) = w.ord x := by
  revert K F F' v w hw x hx
  exact @_root_.P2MW.S_AlgebraicCurve_Place_neg_log_valuation_fiberCenter_eq_ord.solution
