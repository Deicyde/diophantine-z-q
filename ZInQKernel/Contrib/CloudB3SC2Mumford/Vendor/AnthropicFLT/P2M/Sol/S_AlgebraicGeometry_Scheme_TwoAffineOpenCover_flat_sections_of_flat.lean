/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_flat_sections_of_flat
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_flat_sections_of_flat

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of R)) [Flat c]
    (U : X.Opens) (hU : IsAffineOpen U) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    Module.Flat R Γ(X, U) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
  have h1 : (c.appLE ⊤ U le_top).hom.Flat :=
    HasRingHomProperty.appLE @Flat c inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  have hb : ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).Flat :=
    RingHom.Flat.of_bijective (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.bijective
  have h2 : ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ c.appLE ⊤ U le_top).hom.Flat := by
    rw [CommRingCat.hom_comp]
    exact RingHom.Flat.comp hb h1
  exact RingHom.flat_algebraMap_iff.mp h2
