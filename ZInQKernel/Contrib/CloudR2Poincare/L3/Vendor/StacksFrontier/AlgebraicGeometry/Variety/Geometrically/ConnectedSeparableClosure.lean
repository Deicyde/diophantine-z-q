import Mathlib
import ZInQKernel.Contrib.CloudR2Poincare.L3.VendorAlias
import ZInQKernel.Contrib.CloudR2Poincare.L3.Vendor.StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedFiniteSeparable
import ZInQKernel.Contrib.CloudR2Poincare.L3.InstanceScope

#cloudR2LocalInstances

/-!
# Isolated Stacks proof port

Upstream: AxiomMath/Stacks, commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`,
module `StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedSeparableClosure`, Apache-2.0 (see the adjacent L3/LICENSE).
Prominent change notice, 2026-11-14: imports are restricted to the selected proof
closure; source metadata attributes and module-visibility sections are removed;
all new declarations are isolated beneath `ZInQ.Contrib.CloudR2Poincare.L3.StacksPort` to avoid main namespace clashes.
No proof hypothesis or mathematical conclusion is replaced by an assumed fact.
-/

namespace ZInQ.Contrib.CloudR2Poincare.L3.StacksPort
#cloudR2LocalInstances

open _root_.TopologicalSpace _root_.AlgebraicGeometry _root_.CategoryTheory



/-!
# Geometric connectedness over a separable closure

A scheme over a field is geometrically connected if and only if its base change to a
separable algebraic closure of the field is connected.

## Main results

* `AlgebraicGeometry.geometricallyConnected_iff_connectedSpace_baseChange` characterizes
  geometric connectedness by a single base change to a separable closure.

## Implementation notes

A scheme over `k` is represented by its structure morphism `f : X ⟶ Spec k`. Its base change
to `ksep` is the categorical pullback of `f` along the morphism of spectra induced by
`algebraMap k ksep`. The separable algebraic closure is given abstractly by an
`IsSepClosure k ksep` instance, so the statement applies to any choice of such a closure.

## References

* [Stacks Project, Tag 0387](https://stacks.math.columbia.edu/tag/0387)
-/


open _root_.CategoryTheory
open CategoryTheory Limits CommRingCat

namespace AlgebraicGeometry
#cloudR2LocalInstances

universe u
#cloudR2Vendor descend_connectedSpace in

/-- Connectedness of a base change descends along a further field extension. -/

private lemma descend_connectedSpace
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (k' : Type u) [Field k'] [Algebra k k']
    (g : Spec (.of k') ⟶ Spec (.of k))
    (K : Type u) [Field K] [Algebra k' K]
    (y : Spec (.of K) ⟶ Spec (.of k'))
    (h : ConnectedSpace ↥(pullback f (y ≫ g))) :
    ConnectedSpace ↥(pullback f g) := by
  have : ConnectedSpace ↥(pullback y (pullback.fst g f)) :=
    (pullbackRightPullbackFstIso g f y).schemeIsoToHomeo.connectedSpace_iff.mpr
      ((pullbackSymmetry f (y ≫ g)).schemeIsoToHomeo.connectedSpace_iff.mp h)
  exact (pullbackSymmetry g f).schemeIsoToHomeo.connectedSpace_iff.mp
    ((pullback.snd y (pullback.fst g f)).surjective.connectedSpace
      (pullback.snd y (pullback.fst g f)).continuous)
#cloudR2Vendor geometricallyConnected_iff_connectedSpace_baseChange in

/-- A scheme over a field is geometrically connected if and only if its base change to a
separable algebraic closure is connected. -/

theorem geometricallyConnected_iff_connectedSpace_baseChange
    (k : Type u) [Field k] (ksep : Type u) [Field ksep] [Algebra k ksep]
    [IsSepClosure k ksep] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    GeometricallyConnected f ↔
      ConnectedSpace
        (CategoryTheory.Limits.pullback f
          (Spec.map (CommRingCat.ofHom (algebraMap k ksep))) : Scheme.{u}) := by
  refine ⟨fun hf => hf.geometrically_connectedSpace _ _ _ (.of_hasPullback _ _), fun hsep => ?_⟩
  let : IsSepClosed ksep := IsSepClosure.sep_closed (k := k) (K := ksep)
  rw [geometricallyConnected_iff_forall_finite_separable f]
  intro k' _ _ _ _
  let ι : k' →ₐ[k] ksep := IsSepClosed.lift
  let : Algebra k' ksep := ι.toRingHom.toAlgebra
  let y : Spec (.of ksep) ⟶ Spec (.of k') := Spec.map (CommRingCat.ofHom ι.toRingHom)
  have hy : y ≫ Spec.map (CommRingCat.ofHom (algebraMap k k')) =
      Spec.map (CommRingCat.ofHom (algebraMap k ksep)) := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    simp [ι]
  exact descend_connectedSpace f k' _ ksep y (by rwa [hy])

end AlgebraicGeometry

end ZInQ.Contrib.CloudR2Poincare.L3.StacksPort
