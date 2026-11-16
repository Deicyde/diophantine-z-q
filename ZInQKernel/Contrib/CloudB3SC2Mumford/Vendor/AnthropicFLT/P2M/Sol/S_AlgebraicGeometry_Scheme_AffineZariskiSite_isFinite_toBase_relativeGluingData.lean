/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicGeometry_Scheme_AffineZariskiSite_isFinite_toBase_relativeGluingData
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicGeometry_Scheme_AffineZariskiSite_isFinite_toBase_relativeGluingData

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace FormalGAGAFiniteRelSpecAux

open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.AffineZariskiSite

variable {X : Scheme.{u}} {F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u}}
    {α : (AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ F} (H : α.Coequifibered)

scoped instance instIsLocallyDirected :
    ((relativeGluingData H).functor ⋙ Scheme.forget).IsLocallyDirected :=
  Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

set_option backward.isDefEq.respectTransparency false in
theorem ι_toBase (U : X.AffineZariskiSite) :
    (relativeGluingData H).cover.f U ≫ (relativeGluingData H).toBase =
      Spec.map (α.app (op U)) ≫ U.2.fromSpec :=
  colimit.ι_desc _ _

theorem toBase_preimage (U : X.AffineZariskiSite) :
    (relativeGluingData H).toBase ⁻¹ᵁ U.1 = ((relativeGluingData H).cover.f U).opensRange := by
  have h__af := (relativeGluingData H).toBase_preimage_eq_opensRange_ι U
  simp at h__af
  exact h__af

end FormalGAGAFiniteRelSpecAux
-- [port] was: p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_AffineZariskiSite_isFinite_toBase_relativeGluingData.FormalGAGAFiniteRelSpecAux"
open scoped _root_.P2MW.S_AlgebraicGeometry_Scheme_AffineZariskiSite_isFinite_toBase_relativeGluingData.FormalGAGAFiniteRelSpecAux

open FormalGAGAFiniteRelSpecAux AlgebraicGeometry.Scheme in
set_option backward.isDefEq.respectTransparency false in
theorem solution
    {X : Scheme.{u}} {F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u}}
    {α : (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ F} (H : α.Coequifibered)
    (hfin : ∀ U : X.AffineZariskiSite, (α.app (op U)).hom.Finite) :
    IsFinite (Scheme.AffineZariskiSite.relativeGluingData H).toBase := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsFinite) _ (iSup_affineOpens_eq_top _)]
  intro U
  let U' : X.AffineZariskiSite := ⟨U.1, U.2⟩
  let e := IsOpenImmersion.isoOfRangeEq ((AffineZariskiSite.relativeGluingData H).toBase ⁻¹ᵁ U).ι
    ((AffineZariskiSite.relativeGluingData H).cover.f U')
      (by simpa using congr($(toBase_preimage H U').1))
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsFinite e.inv,
    ← MorphismProperty.cancel_right_of_respectsIso @IsFinite _ U.2.isoSpec.hom]
  convert! (IsFinite.SpecMap_iff _).mpr (hfin U')
  rw [← cancel_mono U.2.fromSpec]
  have h := ι_toBase H U'
  simp only [Cover.RelativeGluingData.cover_f] at h
  simp [IsAffineOpen.isoSpec_hom, e, h, U']
