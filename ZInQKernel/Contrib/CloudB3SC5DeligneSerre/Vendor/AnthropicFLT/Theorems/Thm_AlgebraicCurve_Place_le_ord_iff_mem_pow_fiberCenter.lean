/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Place_le_ord_iff_mem_pow_fiberCenter (git blob 9ba422be2f17d2ba7eb746cb9b08ee255b36ee90, sha256 affb6610e64ef7f2e82f6cc2affbd29bb7bb9e026f88a61e4c6faf671dae8efd).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlacesOverDVR
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Place_le_ord_iff_mem_pow_fiberCenter

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve
theorem AlgebraicCurve.Place.le_ord_iff_mem_pow_fiberCenter {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] {v : Place K F} {w : Place K F'} (hw : w.restrict F = v) {c : Place.integralClosureAt F' v} (hc : c ≠ 0) (n : ℕ) : (n : ℤ) ≤ w.ord (algebraMap (Place.integralClosureAt F' v) F' c) ↔ c ∈ (Place.fiberCenter F' v hw).asIdeal ^ n := by
  revert K F F' v w hw c hc n
  exact @_root_.P2MW.S_AlgebraicCurve_Place_le_ord_iff_mem_pow_fiberCenter.solution
