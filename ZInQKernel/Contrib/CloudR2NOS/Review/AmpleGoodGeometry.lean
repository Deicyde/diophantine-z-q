/-
Copyright (c) 2026 H5/NOS Round-2 Lane6 contributors.
Released under the Apache License, Version 2.0.

NOTICE OF MODIFICATION / PURPOSE (2026-11-14): new actual same-good-model geometry
bridge. It reuses ONLY the exact published Tau Ceti smooth/geometrically-connected
⇒ geometrically-integral proof (not a repeated source survey) and Mathlib's integral
fibre/total-space results, then the actual H76 vertical-stalk constructor.

All source notices remain unchanged. The Tau Ceti theorem's ACTUAL telescope is
Scheme.{u}, arbitrary base; the old FrobPieces Type0 wrapper is NOT substituted.
No model existence, generic-line extension, characteristic, perfectness,
henselianity or projective-model premise is added. Original PkgI2 definitions
and the SAME given Grp model, closed fibre and generic point are preserved.
-/
import ZInQKernel.HDecomp.Objects
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyIntegral
import ZInQKernel.Contrib.CloudR2NOS.Review.AmpleVerticalDVR

set_option autoImplicit false
noncomputable section
universe u

open CategoryTheory AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.Review.AmpleExtension

/-- The SAME original proper smooth geometrically connected group model has
actual geometrically integral fibres, in every characteristic/universe. -/
theorem goodModel_geometricallyIntegral {R : Type u} [CommRing R]
    (G : Grp (Over (Spec (CommRingCat.of R)))) [PkgI2.IsAbelianScheme G] :
    GeometricallyIntegral G.X.hom := by
  haveI : Smooth G.X.hom := PkgI2.IsAbelianScheme.smooth
  haveI : GeometricallyConnected G.X.hom := PkgI2.IsAbelianScheme.geomConnected
  exact TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral G.X.hom

/-- All actual scheme-theoretic fibres are integral; no fibre-integrality Fact
is postulated for the later vertical-DVR construction. -/
theorem goodModel_fibre_isIntegral {R : Type u} [CommRing R]
    (G : Grp (Over (Spec (CommRingCat.of R)))) [PkgI2.IsAbelianScheme G]
    (c : Spec (CommRingCat.of R)) : IsIntegral (G.X.hom.fiber c) := by
  haveI : GeometricallyIntegral G.X.hom := goodModel_geometricallyIntegral G
  infer_instance

/-- The total model over a Noetherian domain is integral. Smoothness supplies
flatness/universal openness; no integral total model is assumed. -/
theorem goodModel_isIntegral {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (G : Grp (Over (Spec (CommRingCat.of R)))) [PkgI2.IsAbelianScheme G] :
    IsIntegral G.X.left := by
  haveI : Smooth G.X.hom := PkgI2.IsAbelianScheme.smooth
  haveI : GeometricallyIntegral G.X.hom := goodModel_geometricallyIntegral G
  exact GeometricallyIntegral.isIntegral_of_isLocallyNoetherian G.X.hom

/-- Construct the actual vertical DVR of the GIVEN arbitrary-DVR group model,
with its point defined from the ORIGINAL scheme-theoretic closed fibre.
The previous intermediate special-fibre-integrality input is now DERIVED. -/
theorem goodModel_vertical_stalk_isDVR {K : Type u} [Field K]
    (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (G : Grp (Over (Spec (CommRingCat.of O)))) [PkgI2.IsAbelianScheme G] :
    letI : IsIntegral (G.X.hom.fiber (IsLocalRing.closedPoint O)) := goodModel_fibre_isIntegral G _
    ∃ _ : IsDomain (G.X.left.presheaf.stalk
        (verticalGenericPoint G.X.hom (IsLocalRing.closedPoint O))),
      IsDiscreteValuationRing (G.X.left.presheaf.stalk
        (verticalGenericPoint G.X.hom (IsLocalRing.closedPoint O))) := by
  letI : IsIntegral (G.X.hom.fiber (IsLocalRing.closedPoint O)) := goodModel_fibre_isIntegral G _
  haveI : Smooth G.X.hom := PkgI2.IsAbelianScheme.smooth
  exact verticalGenericPoint_stalk_isDVR G.X.hom

#print axioms goodModel_geometricallyIntegral
#print axioms goodModel_fibre_isIntegral
#print axioms goodModel_isIntegral
#print axioms goodModel_vertical_stalk_isDVR

end ZInQ.Contrib.CloudR2NOS.Review.AmpleExtension
