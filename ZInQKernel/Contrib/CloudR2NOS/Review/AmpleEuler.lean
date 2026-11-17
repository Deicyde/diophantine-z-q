/-
Copyright (c) 2026 H5/NOS Round-2 Lane6 contributors.
Released under the Apache License, Version 2.0.

NOTICE OF MODIFICATION / PURPOSE (2026-11-14): new thin specialization of the
ACTUAL W07 Jacobian-Challenge Euler-characteristic theorem at c4254cce15b3e284a0a3ae1d73936f2ee195d272.
The underlying source and its LICENSE/NOTICE are unchanged.

This is NOT generic line-bundle extension or special ampleness. It proves the
noncircular proper-flat Euler step for an ALREADY GIVEN invertible module on the
SAME given group model. No projective/ample model, hχ, hdescLine, HenselianLocalRing,
PerfectField, CharZero, or NOS criterion is assumed. The conclusion uses the
source's ACTUAL fibre cohomology, not an independently assigned numeric χ.

The stronger domain-base conclusion applies to every DVR and compares ALL points
of Spec R, in particular the actual generic and closed points. The original
Objects import remains LEGACY; the protected module is not modified.
-/
import ZInQKernel.HDecomp.Objects
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.DirectImage.EulerCharacteristic
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.Flat
import ZInQKernel.Contrib.CloudR2NOS.Review.AmpleFinitePresentation

set_option autoImplicit false
noncomputable section
universe u

open CategoryTheory AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.Review.AmpleExtension

/-- Proper relatively flat finitely presented coefficients have the same ACTUAL
Euler characteristic at any two points of a domain spectrum. No projectivity. -/
theorem eulerCharFiber_eq_over_domain {R : Type u} [CommRing R] [IsDomain R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [IsProper f] [LocallyOfFinitePresentation f]
    (M : X.Modules) [M.IsFinitePresentation] (hflat : M.IsFlatOver f)
    (x y : Spec (CommRingCat.of R)) :
    M.eulerCharFiber f x = M.eulerCharFiber f y := by
  have hχ := AlgebraicGeometry.Scheme.Modules.isLocallyConstant_eulerCharFiber f M hflat
  exact hχ.apply_eq_of_preconnectedSpace x y

/-- Exact original group-model interface. Invertibility + the model's actual
smoothness supplies relative flatness; properness is the given model's properness. -/
theorem goodModel_eulerCharFiber_eq {R : Type u} [CommRing R] [IsDomain R]
    (G : Grp (Over (Spec (CommRingCat.of R)))) [PkgI2.IsAbelianScheme G]
    (M : G.X.left.Modules) [M.IsInvertible]
    (x y : Spec (CommRingCat.of R)) :
    M.eulerCharFiber G.X.hom x = M.eulerCharFiber G.X.hom y := by
  haveI : IsProper G.X.hom := PkgI2.IsAbelianScheme.proper
  haveI : Smooth G.X.hom := PkgI2.IsAbelianScheme.smooth
  haveI : M.IsFinitePresentation := isFinitePresentation_of_invertible M
  exact eulerCharFiber_eq_over_domain G.X.hom M
    (AlgebraicGeometry.Scheme.Modules.isFlatOver_of_isInvertible G.X.hom M) x y

/-- The unchanged arbitrary-DVR setting, with no residue characteristic or
henselian restriction, preserves a nonzero ACTUAL generic-fibre Euler value. -/
theorem goodModel_eulerCharFiber_ne_zero {K : Type u} [Field K]
    (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (G : Grp (Over (Spec (CommRingCat.of O)))) [PkgI2.IsAbelianScheme G]
    (M : G.X.left.Modules) [M.IsInvertible]
    (genericPoint closedPoint : Spec (CommRingCat.of O))
    (hχ : M.eulerCharFiber G.X.hom genericPoint ≠ 0) :
    M.eulerCharFiber G.X.hom closedPoint ≠ 0 := by
  rw [← goodModel_eulerCharFiber_eq G M genericPoint closedPoint]
  exact hχ

#print axioms eulerCharFiber_eq_over_domain
#print axioms goodModel_eulerCharFiber_eq
#print axioms goodModel_eulerCharFiber_ne_zero

end ZInQ.Contrib.CloudR2NOS.Review.AmpleExtension
