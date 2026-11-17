-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.AlgebraicGeometry.Picard.Counit), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.DirectImage.Basic
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.ZeroLocusFunctorial
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Picard.Basic

/-!
# The evaluation map of a relative Picard class

The pullback-pushforward counit evaluates the direct image of a line bundle.
When that direct image is invertible over a nonempty parameter scheme, the
evaluation map is nonzero. Its zero locus is locally principal.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

/-- An invertible module sheaf on a nonempty scheme is not zero. -/
theorem Scheme.Modules.not_isZero_of_isInvertible {T : Scheme.{u}} [Nonempty T]
    (M : T.Modules) [M.IsInvertible] : ¬ IsZero M := by
  intro zeroObject
  have scalarEquality : (1 : Γ(T, ⊤)) = 0 :=
    Modules.eq_of_smulHom_eq M (by
      rw [Modules.smulHom_one, Modules.smulHom_zero]
      exact (IsZero.iff_id_eq_zero M).mp zeroObject)
  let point : T := Classical.choice ‹Nonempty T›
  have stalkEquality : (1 : T.presheaf.stalk point) = 0 := by
    simpa using congrArg (T.presheaf.germ ⊤ point trivial) scalarEquality
  exact one_ne_zero stalkEquality

/-- Evaluation of the direct image of the chosen representative of a Picard class. -/
def Scheme.Pic.directImageCounit {X S : Scheme.{u}} (f : X ⟶ S) (T : Over S)
    (L : (pullback f T.hom).Pic) :
    (Modules.pullback (pullback.snd f T.hom)).obj
        ((Modules.pushforward (pullback.snd f T.hom)).obj
          ((fromSkeleton _).obj L.val)) ⟶ (fromSkeleton _).obj L.val :=
  (Modules.pullbackPushforwardAdjunction _).counit.app _

/-- Evaluation is nonzero when the direct image is invertible and the base is nonempty. -/
theorem Scheme.Pic.directImageCounit_ne_zero {X S : Scheme.{u}} (f : X ⟶ S) (T : Over S)
    [Nonempty T.left] (L : (pullback f T.hom).Pic)
    [((Modules.pushforward (pullback.snd f T.hom)).obj
      ((fromSkeleton _).obj L.val)).IsInvertible] :
    Pic.directImageCounit f T L ≠ 0 := by
  intro zeroCounit
  have triangle := (Modules.pullbackPushforwardAdjunction
    (pullback.snd f T.hom)).right_triangle_components ((fromSkeleton _).obj L.val)
  change _ ≫ (Modules.pushforward _).map (Pic.directImageCounit f T L) = _ at triangle
  rw [zeroCounit, Functor.map_zero, comp_zero] at triangle
  exact Modules.not_isZero_of_isInvertible _ ((IsZero.iff_id_eq_zero _).mpr triangle.symm)

/-- The zero ideal of evaluation is locally principal. -/
theorem Scheme.Pic.isLocallyPrincipal_zeroLocus_directImageCounit {X S : Scheme.{u}}
    (f : X ⟶ S) (T : Over S) (L : (pullback f T.hom).Pic)
    [((Modules.pushforward (pullback.snd f T.hom)).obj
      ((fromSkeleton _).obj L.val)).IsInvertible] :
    (Pic.directImageCounit f T L).zeroLocus.IsLocallyPrincipal :=
  Modules.Hom.isLocallyPrincipal_zeroLocus _

end AlgebraicGeometry
