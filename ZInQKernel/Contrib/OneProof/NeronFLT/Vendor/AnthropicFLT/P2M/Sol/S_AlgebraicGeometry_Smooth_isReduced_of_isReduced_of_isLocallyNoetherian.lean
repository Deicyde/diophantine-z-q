/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicGeometry_Smooth_isReduced_of_isReduced_of_isLocallyNoetherian
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_isReduced_of_smooth_of_field
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicGeometry_Smooth_isReduced_of_isReduced_of_isLocallyNoetherian

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace REDsol

theorem geometricallyReduced_of_smooth {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] : GeometricallyReduced f := by
  refine ⟨fun K _ y Z fst snd h => ?_⟩
  haveI : Smooth snd := MorphismProperty.of_isPullback (P := @Smooth) h inferInstance
  exact AlgebraicGeometry.isReduced_of_smooth_of_field snd

end REDsol

theorem solution
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] [IsReduced Y] [IsLocallyNoetherian Y] :
    IsReduced X := by
  haveI := REDsol.geometricallyReduced_of_smooth f
  exact GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian f
