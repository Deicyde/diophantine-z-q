/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Place_inertiaDeg_eq_inertiaDeg_fiberCenter (git blob b0e06bf5a753e99ff37716c453bed8ec701eef1c, sha256 080bc04eb8ca428213301998f6ead0d9d223702ff0dbbfcebb00ed05d9ca5056).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlacesOverDVR
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Place_inertiaDeg_eq_inertiaDeg_fiberCenter

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve
theorem AlgebraicCurve.Place.inertiaDeg_eq_inertiaDeg_fiberCenter {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] (v : Place K F) {w : Place K F'}
    (hw : w.restrict F = v) :
    w.inertiaDeg F = (IsLocalRing.maximalIdeal v.toValuationSubring).inertiaDeg' (Place.fiberCenter F' v hw).asIdeal := by
  revert K F F' v w hw
  exact @_root_.P2MW.S_AlgebraicCurve_Place_inertiaDeg_eq_inertiaDeg_fiberCenter.solution
