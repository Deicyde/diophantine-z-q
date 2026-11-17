/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_flat_sections_of_flat. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

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
