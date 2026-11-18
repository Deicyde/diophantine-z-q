import Mathlib
import ZInQKernel.Contrib.CloudR2Poincare.L3.VendorAlias
import ZInQKernel.Contrib.CloudR2Poincare.L3.Vendor.StacksCore.RingTheory.Flat.FaithfullyFlat.Basic
import ZInQKernel.Contrib.CloudR2Poincare.L3.InstanceScope

#cloudR2LocalInstances

/-!
# Isolated Stacks proof port

Upstream: AxiomMath/Stacks, commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`,
module `StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedBaseChange`, Apache-2.0 (see the adjacent L3/LICENSE).
Prominent change notice, 2026-11-14: imports are restricted to the selected proof
closure; source metadata attributes and module-visibility sections are removed;
all new declarations are isolated beneath `ZInQ.Contrib.CloudR2Poincare.L3.StacksPort` to avoid main namespace clashes.
No proof hypothesis or mathematical conclusion is replaced by an assumed fact.
-/

namespace ZInQ.Contrib.CloudR2Poincare.L3.StacksPort
#cloudR2LocalInstances

open _root_.TopologicalSpace _root_.AlgebraicGeometry _root_.CategoryTheory



/-!
# Geometric connectedness after a field extension

Geometric connectedness of a scheme over a field may be checked after extending the
base field.

## Main results

* `AlgebraicGeometry.geometricallyConnected_iff_baseChange_fieldExtension` states that a scheme
  over a field is geometrically connected if and only if its base change along any field
  extension is geometrically connected.

## Implementation notes

A scheme over `k` is represented by its structure morphism `f : X ⟶ Spec k`. Its base change
to `k'` is represented by the pullback projection to `Spec k'`.

## References

* [Stacks Project, Tag 054N](https://stacks.math.columbia.edu/tag/054N)
-/


open _root_.CategoryTheory
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry
#cloudR2LocalInstances

universe u
#cloudR2Vendor geometricallyConnected_iff_baseChange_fieldExtension in

/-- **Stacks Project, Tag 054N.** A scheme over a field is geometrically connected if and only if
its base change along a field extension is geometrically connected. -/

theorem geometricallyConnected_iff_baseChange_fieldExtension
    {X : Scheme.{u}} (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    (f : X ⟶ Spec (.of k)) :
    GeometricallyConnected f ↔
      GeometricallyConnected
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) := by
  let g : Spec (.of k') ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k k'))
  change GeometricallyConnected f ↔ GeometricallyConnected (pullback.snd f g)
  refine ⟨fun _ ↦ inferInstance, fun h ↦ ⟨?_⟩⟩
  rw [geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro K _ _
  obtain ⟨M, _, _, _, _, _, _⟩ := exists_common_extension k k' K
  let y : Spec (.of M) ⟶ Spec (.of k') :=
    Spec.map (CommRingCat.ofHom (algebraMap k' M))
  let z : Spec (.of M) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K M))
  let q : Spec (.of K) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k K))
  have heq : z ≫ q = y ≫ g := by
    dsimp [y, z, g, q]
    simp only [← Spec.map_comp]
    congr 1
    ext x
    exact (IsScalarTower.algebraMap_apply k K M x).symm.trans
      (IsScalarTower.algebraMap_apply k k' M x)
  have hc : ConnectedSpace ↥(pullback f (z ≫ q)) := by
    rw [heq]
    exact (pullbackLeftPullbackSndIso f g y).schemeIsoToHomeo.connectedSpace_iff.mp
      (h.geometrically_connectedSpace _ _ _ (.of_hasPullback _ _))
  have : ConnectedSpace ↥(pullback z (pullback.fst q f)) :=
    (pullbackRightPullbackFstIso q f z).schemeIsoToHomeo.connectedSpace_iff.mpr
      ((pullbackSymmetry f (z ≫ q)).schemeIsoToHomeo.connectedSpace_iff.mp hc)
  exact (pullbackSymmetry q f).schemeIsoToHomeo.connectedSpace_iff.mp
    ((pullback.snd z (pullback.fst q f)).surjective.connectedSpace
      (pullback.snd z (pullback.fst q f)).continuous)

end AlgebraicGeometry

end ZInQ.Contrib.CloudR2Poincare.L3.StacksPort
