/-
Copyright (c) 2026 H5/NOS Round-2 Lane6 contributors.
Released under the Apache License, Version 2.0.

NOTICE OF MODIFICATION / PURPOSE (2026-11-14): new thin bridge from the accepted
H76 smooth-DVR regular-stalk proof to W07's scheme regularity and factorial-stalk
API at c4254cce15b3e284a0a3ae1d73936f2ee195d272. Neither source is rewritten.

This supplies a genuine input to Cartier/Weil generic-line closure. It is NOT a
proof that a generic ample line has been extended or remains ample. The W07 UFD
supplier has an IsRegularRing premise at each stalk; it is DERIVED by W07 from
regularity at ALL scheme points, not silently assumed from one regular local ring.
No projective/ample model, CharZero, perfectness, henselianity or NOS is assumed.
-/
import ZInQKernel.HDecomp.Objects
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.P2M.Sol.S_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk_of_isDiscreteValuationRing
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Regular

set_option autoImplicit false
noncomputable section
universe u

open CategoryTheory AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.Review.AmpleExtension

/-- Smoothness over an arbitrary DVR gives the actual W07 regular-scheme class. -/
theorem smoothDVR_isRegular {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [Smooth f] : AlgebraicGeometry.IsRegular X := by
  constructor
  intro x
  exact ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk_of_isDiscreteValuationRing.solution
    R f x

/-- Every stalk of the SAME smooth DVR model is factorial. The regular-ring
hypothesis of the actual UFD supplier is obtained by its scheme localization proof. -/
theorem smoothDVR_uniqueFactorization_stalk {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [Smooth f] (x : X) :
    UniqueFactorizationMonoid (X.presheaf.stalk x) := by
  letI : AlgebraicGeometry.IsRegular X := smoothDVR_isRegular f
  exact AlgebraicGeometry.IsRegular.uniqueFactorizationMonoid_stalk x

/-- The actual original group-model hypotheses supply smoothness; no field-only
regularity theorem or generic replacement object is used. -/
theorem goodModel_uniqueFactorization_stalk {K : Type u} [Field K]
    (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (G : Grp (Over (Spec (CommRingCat.of O)))) [PkgI2.IsAbelianScheme G]
    (x : G.X.left) : UniqueFactorizationMonoid (G.X.left.presheaf.stalk x) := by
  haveI : Smooth G.X.hom := PkgI2.IsAbelianScheme.smooth
  exact smoothDVR_uniqueFactorization_stalk G.X.hom x

#print axioms smoothDVR_isRegular
#print axioms smoothDVR_uniqueFactorization_stalk
#print axioms goodModel_uniqueFactorization_stalk

end ZInQ.Contrib.CloudR2NOS.Review.AmpleExtension
