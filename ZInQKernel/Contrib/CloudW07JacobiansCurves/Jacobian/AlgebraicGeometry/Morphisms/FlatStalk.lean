-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.AlgebraicGeometry.Morphisms.FlatStalk), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.RingTheory.Flat.Localization

/-!
# Flatness of the spectrum of a local ring

The canonical map from the spectrum of a stalk factors through any affine
neighbourhood as a localization followed by an open immersion.
-/

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry

instance IsAffineOpen.flat_fromSpecStalk {scheme : Scheme.{u}} {openSubset : scheme.Opens}
    (affine : IsAffineOpen openSubset) {point : scheme} (membership : point ∈ openSubset) :
    Flat (affine.fromSpecStalk membership) := by
  dsimp [IsAffineOpen.fromSpecStalk]
  have : Flat (Spec.map (scheme.presheaf.germ openSubset point membership)) := by
    rw [Flat.SpecMap_iff]
    let : Algebra Γ(scheme, openSubset) (scheme.presheaf.stalk point) :=
      (scheme.presheaf.germ openSubset point membership).hom.toAlgebra
    have := affine.isLocalization_stalk ⟨point, membership⟩
    exact RingHom.flat_algebraMap_iff.mpr
      (IsLocalization.flat _ (affine.primeIdealOf ⟨point, membership⟩).asIdeal.primeCompl)
  infer_instance

instance Scheme.flat_fromSpecStalk (scheme : Scheme.{u}) (point : scheme) :
    Flat (scheme.fromSpecStalk point) :=
  IsAffineOpen.flat_fromSpecStalk _ _

end AlgebraicGeometry
