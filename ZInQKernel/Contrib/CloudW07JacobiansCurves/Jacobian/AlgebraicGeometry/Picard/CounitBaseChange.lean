-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.AlgebraicGeometry.Picard.CounitBaseChange), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged except that the `AlgebraicGeometry.baseChangeDiagram*`, `baseChangeCone*` and `baseChangeMap*` declarations are renamed into `AlgebraicGeometry.JacobianChallenge` (CloudW07 edit, to avoid a clash with vendored Stacks names).
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.BaseChangeCounit
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Picard.Counit
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Picard.Presheaf

/-!
# Base change of Picard evaluation maps

Invertibility of the canonical direct-image base-change morphism identifies
the evaluation arrow of a Picard class with that of its pullback. Consequently
their scheme-theoretic zero loci agree after base change.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable {X S : Scheme.{u}} (f : X ⟶ S) {T T' : Over S} (i : T' ⟶ T)
  (L : (pullback f T.hom).Pic)

/-- Canonical direct-image base change identifies evaluation arrows, including
the chosen representatives of the pullback Picard classes. -/
def arrowIsoPullbackDirectImageCounit
    [IsIso ((Modules.pushforwardBaseChange (isPullback_baseChangeMap f i).w.symm).app
      ((fromSkeleton _).obj L.val))] :
    Arrow.mk ((Modules.pullback (JacobianChallenge.baseChangeMap f i)).map (Pic.directImageCounit f T L)) ≅
      Arrow.mk (Pic.directImageCounit f T' (Pic.map (JacobianChallenge.baseChangeMap f i) L)) := by
  let representativeIso : (Modules.pullback (JacobianChallenge.baseChangeMap f i)).obj
      ((fromSkeleton _).obj L.val) ≅
      (fromSkeleton _).obj (Pic.map (JacobianChallenge.baseChangeMap f i) L).val :=
    (fromSkeletonToSkeletonIso _).symm
  let adj := Modules.pullbackPushforwardAdjunction (pullback.snd f T'.hom)
  exact Modules.arrowIsoPullbackCounit (isPullback_baseChangeMap f i).w.symm
      ((fromSkeleton _).obj L.val) ≪≫
    Arrow.isoMk ((Modules.pullback (pullback.snd f T'.hom)).mapIso
      ((Modules.pushforward (pullback.snd f T'.hom)).mapIso representativeIso))
      representativeIso (adj.counit.naturality representativeIso.hom)

/-- The zero locus of evaluation commutes with base change whenever the
canonical direct-image base-change map is invertible. -/
theorem comap_zeroLocus_directImageCounit
    [((Modules.pushforward (pullback.snd f T.hom)).obj
      ((fromSkeleton _).obj L.val)).IsInvertible]
    [((Modules.pushforward (pullback.snd f T'.hom)).obj
      ((fromSkeleton _).obj (Pic.map (JacobianChallenge.baseChangeMap f i) L).val)).IsInvertible]
    [IsIso ((Modules.pushforwardBaseChange (isPullback_baseChangeMap f i).w.symm).app
      ((fromSkeleton _).obj L.val))] :
    (Pic.directImageCounit f T L).zeroLocus.comap (JacobianChallenge.baseChangeMap f i) =
      (Pic.directImageCounit f T' (Pic.map (JacobianChallenge.baseChangeMap f i) L)).zeroLocus := by
  rw [Modules.Hom.comap_zeroLocus]
  exact Modules.Hom.zeroLocus_eq_of_arrowIso _ _ (arrowIsoPullbackDirectImageCounit f i L)

end AlgebraicGeometry
