/-
Copyright (c) 2026 Cloud Worker 2 contributors.
Released under Apache 2.0 license as described in Vendor/AnthropicFLT/LICENSE.

The affine connectedness input is reused from anthropics/fermats-last-theorem,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2. Its complete proof import closure,
original notices, and per-file attribution are preserved under Vendor/AnthropicFLT.
This file adds only the affine-target transport and Zariski-local bridge to the
fixed project proposition; it does not change any project definition or pin.
-/

import ZInQKernel.Contrib.ZariskiConn.Basic
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_bijective_appTop

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace ZariskiConn

/-- Transport the source's exact affine-noetherian theorem across `Y ≅ Spec Γ(Y)`. -/
private theorem geometricallyConnected_of_isProper_of_bijective_appTop_affine
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y] [IsLocallyNoetherian Y] [IsProper f]
    (hf : Function.Bijective f.appTop) : GeometricallyConnected f := by
  have : IsNoetherianRing Γ(Y, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top Y⟩
  have hΓ : Function.Bijective (f ≫ Y.isoSpec.hom).appTop := by
    rw [Scheme.Hom.comp_appTop]
    change Function.Bijective (f.appTop.hom.comp Y.isoSpec.hom.appTop.hom)
    exact hf.comp (Scheme.Γ.mapIso Y.isoSpec.op).commRingCatIsoToRingEquiv.bijective
  have hG : GeometricallyConnected (f ≫ Y.isoSpec.hom) :=
    P2MW.S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_bijective_appTop.solution
      (f ≫ Y.isoSpec.hom) hΓ
  have : MorphismProperty.RespectsIso @GeometricallyConnected :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact (MorphismProperty.cancel_right_of_respectsIso @GeometricallyConnected
    f Y.isoSpec.hom).mp hG

/-- **Zariski's connectedness theorem**, exactly the fixed H-67 proposition.

The affine theorem is proved in the vendored source from formal-functions image
stabilization, proper-cohomology finiteness, and flat base change. Geometric
connectedness is Zariski-local at the target, so affine restriction proves the
published locally-noetherian statement without adding any hypotheses. -/
theorem ZariskiConnectedness_proof : ZariskiConnectedness.{u} := by
  intro X Y f hproper hnoetherian hf
  letI : IsProper f := hproper
  letI : IsLocallyNoetherian Y := hnoetherian
  letI : IsZariskiLocalAtTarget @GeometricallyConnected := by
    rw [GeometricallyConnected.eq_geometrically]
    infer_instance
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @GeometricallyConnected)
    _ (iSup_affineOpens_eq_top Y)]
  intro U
  have : IsAffine (U : Y.Opens) := U.2
  have hΓ : Function.Bijective (f ∣_ (U : Y.Opens)).appTop := by
    rw [morphismRestrict_appTop]
    let e := X.presheaf.mapIso
      (eqToIso (image_morphismRestrict_preimage f (U : Y.Opens) ⊤)).op
    exact e.commRingCatIsoToRingEquiv.bijective.comp (hf _)
  exact geometricallyConnected_of_isProper_of_bijective_appTop_affine _ hΓ

#print axioms ZariskiConnectedness_proof
#print axioms P2MW.S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_bijective_appTop.solution

end ZariskiConn
