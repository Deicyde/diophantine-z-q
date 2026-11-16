-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.AlgebraicGeometry.ProjectiveSpace.AffineTwist), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveSpace.Affine
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveSpace.Twist
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveSpectrum.Twist.Pullback

/-!
# Twisting sheaves on projective space over an affine scheme

The affine comparison between relative projective space and polynomial `Proj`
identifies their twisting sheaves. The comparison is induced by the coefficient
map on homogeneous fractions; its invertibility is checked on the standard
opens of the homogeneous coordinates.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory MvPolynomial
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

variable (coordinates : Type u)

namespace Proj

variable {sourceRing targetRing : Type u} [CommRing sourceRing] [CommRing targetRing]

/-- Changing polynomial coefficients preserves every twisting sheaf. -/
def projectiveSpaceMapPullbackTwistIso (coefficients : sourceRing →+* targetRing)
    (degree : ℤ) :
    (Scheme.Modules.pullback (projectiveSpaceMap coordinates coefficients)).obj
        (twist (homogeneousSubmodule coordinates sourceRing) degree) ≅
      twist (homogeneousSubmodule coordinates targetRing) degree := by
  unfold projectiveSpaceMap
  refine pullbackTwistIso _ _ degree ?_
  intro point
  have cover := iSup_basicOpen_eq_top' (homogeneousSubmodule coordinates targetRing)
    (MvPolynomial.X : coordinates → MvPolynomial coordinates targetRing)
    (fun coordinate ↦ ⟨1, isHomogeneous_X targetRing coordinate⟩)
    (adjoin_range_X_eq_top coordinates targetRing)
  have pointMem : point ∈ ⨆ coordinate,
      basicOpen (homogeneousSubmodule coordinates targetRing) (X coordinate) := by
    rw [cover]
    trivial
  obtain ⟨coordinate, coordinateMem⟩ := TopologicalSpace.Opens.mem_iSup.mp pointMem
  refine ⟨X coordinate, isHomogeneous_X sourceRing coordinate, ?_⟩
  change point ∈ basicOpen _ (MvPolynomial.map coefficients (X coordinate))
  simpa only [MvPolynomial.map_X] using coordinateMem

end Proj

namespace ProjectiveSpace

open Scheme.Modules

variable (baseRing : CommRingCat.{u})

/-- The canonical map from polynomial `Proj` to relative projective space
identifies the pulled-back relative twists with the polynomial twists. -/
def pullbackFromProjTwistIso (degree : ℤ) :
    (pullback (fromProj coordinates baseRing)).obj
        (twist coordinates (Spec baseRing) degree) ≅
      Proj.twist (homogeneousSubmodule coordinates baseRing) degree := by
  change (pullback (fromProj coordinates baseRing)).obj
      ((pullback (toIntegralModel coordinates (Spec baseRing))).obj _) ≅ _
  refine (pullbackComp (fromProj coordinates baseRing)
    (toIntegralModel coordinates (Spec baseRing))).app _ ≪≫ ?_
  rw [fromProj_toIntegralModel]
  exact Proj.projectiveSpaceMapPullbackTwistIso coordinates _ degree

/-- Under the affine comparison isomorphism, polynomial and relative twisting
sheaves agree. -/
def pullbackAffineIsoTwistIso (degree : ℤ) :
    (pullback (affineIso coordinates baseRing).hom).obj
        (Proj.twist (homogeneousSubmodule coordinates baseRing) degree) ≅
      twist coordinates (Spec baseRing) degree := by
  have composite : (affineIso coordinates baseRing).hom ≫ fromProj coordinates baseRing = 𝟙 _ :=
    (asIso (fromProj coordinates baseRing)).inv_hom_id
  exact (pullback (affineIso coordinates baseRing).hom).mapIso
      (pullbackFromProjTwistIso coordinates baseRing degree).symm ≪≫
    (pullbackComp (affineIso coordinates baseRing).hom (fromProj coordinates baseRing)).app _ ≪≫
    (pullbackCongr composite).app _ ≪≫ (pullbackId _).app _

end ProjectiveSpace

end AlgebraicGeometry
