/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicGeometry_Scheme_exists_opens_extension_of_fromSpecStalk
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_opens_extension_of_fromSpecStalk

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

theorem solution
    {S G H : Scheme.{u}} (sG : G ⟶ S) (sH : H ⟶ S) [LocallyOfFiniteType sH]
    (η : G) [G.IsGermInjectiveAt η]
    (w : Spec (G.presheaf.stalk η) ⟶ H) (hw : w ≫ sH = G.fromSpecStalk η ≫ sG) :
    ∃ (U : G.Opens) (hη : η ∈ U) (v : (U : Scheme.{u}) ⟶ H),
      v ≫ sH = U.ι ≫ sG ∧ U.fromSpecStalkOfMem η hη ≫ v = w := by
  obtain ⟨U, hη, v, h1, h2⟩ := spread_out_of_isGermInjective' sG sH w hw
  exact ⟨U, hη, v, h2, h1.symm⟩
