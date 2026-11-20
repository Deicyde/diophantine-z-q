import Mathlib
import ZInQKernel.Contrib.CloudR2Poincare.L3.VendorAlias
import ZInQKernel.Contrib.CloudR2Poincare.L3.Vendor.StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedAffine
import ZInQKernel.Contrib.CloudR2Poincare.L3.Vendor.StacksFrontier.RingTheory.GeometricallyConnected
import ZInQKernel.Contrib.CloudR2Poincare.L3.InstanceScope

#cloudR2LocalInstances

/-!
# Isolated Stacks proof port

Upstream: AxiomMath/Stacks, commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`,
module `StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedSeparablyClosed`, Apache-2.0 (see the adjacent L3/LICENSE).
Prominent change notice, 2026-11-14: imports are restricted to the selected proof
closure; source metadata attributes and module-visibility sections are removed;
all new declarations are isolated beneath `ZInQ.Contrib.CloudR2Poincare.L3.StacksPort` to avoid main namespace clashes.
No proof hypothesis or mathematical conclusion is replaced by an assumed fact.
-/

namespace ZInQ.Contrib.CloudR2Poincare.L3.StacksPort
#cloudR2LocalInstances

open _root_.TopologicalSpace _root_.AlgebraicGeometry _root_.CategoryTheory



/-!
# Connected components after extending a separably closed field

Let `X` be a scheme over a separably closed field `k`. After any field extension `k'/k`, the
canonical morphism from the base change of `X` to `X` induces a bijection on connected
components. Consequently, geometric connectedness over `k` is equivalent to connectedness
of `X`.

## Main results

* `AlgebraicGeometry.baseChange_connectedComponents_bijective` gives the canonical bijection on
  connected components after a field extension.
* `AlgebraicGeometry.geometricallyConnected_iff_connectedSpace` characterizes geometric
  connectedness over a separably closed field.

## Implementation notes

The base change along `k → k'` is the pullback against the corresponding morphism
`Spec k' ⟶ Spec k`, and the map to `X` is its first projection. Thus the first result
specifies the induced map on connected components rather than merely asserting that some
bijection exists. The second result states the final assertion of Tag 0363, that geometric
connectedness over a separably closed field is connectedness, as a separate equivalence.

## References

* [Stacks Project, Tag 0363](https://stacks.math.columbia.edu/tag/0363)
-/


open _root_.CategoryTheory
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry
#cloudR2LocalInstances

universe u
#cloudR2Vendor geometricallyConnected_spec in

/-- Over a separably closed field, the spectrum of any field extension is geometrically
connected. -/
private lemma geometricallyConnected_spec (k k' : Type u) [Field k] [IsSepClosed k]
    [Field k'] [Algebra k k'] :
    GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap k k'))) :=
  (geometricallyConnected_spec_iff k k').2
    ((Algebra.isGeometricallyConnected_iff_connectedSpace_primeSpectrum k k').2 inferInstance)
#cloudR2Vendor baseChange_connectedComponents_bijective in

/-- **Stacks Project, Tag 0363.** Base change along any extension of a separably closed
field induces a bijection on the connected components of a scheme. -/

theorem baseChange_connectedComponents_bijective
    (k k' : Type u) [Field k] [IsSepClosed k] [Field k'] [Algebra k k']
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    Function.Bijective
      (pullback.fst f
        (Spec.map (CommRingCat.ofHom (algebraMap k k')))).continuous.connectedComponentsMap := by
  let g : Spec (.of k') ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k k'))
  let : GeometricallyConnected g := geometricallyConnected_spec k k'
  simpa only [Function.Bijective, Function.Injective, Function.Surjective,
    Scheme.Hom.connectedComponentsHomeomorph_apply] using
    ((pullback.fst f g).connectedComponentsHomeomorph (pullback.fst f g).isOpenMap).bijective
#cloudR2Vendor geometricallyConnected_iff_connectedSpace in

/-- **Stacks Project, Tag 0363.** Over a separably closed field, a scheme is geometrically
connected if and only if its underlying topological space is connected. -/

theorem geometricallyConnected_iff_connectedSpace
    (k : Type u) [Field k] [IsSepClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    GeometricallyConnected f ↔ ConnectedSpace X := by
  refine ⟨fun _ ↦ GeometricallyConnected.connectedSpace_of_subsingleton f, fun _ ↦ ?_⟩
  rw [AlgebraicGeometry.geometricallyConnected_iff,
    AlgebraicGeometry.geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro K _ _
  let g : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have : GeometricallyConnected g := geometricallyConnected_spec k K
  exact GeometricallyConnected.connectedSpace (pullback.fst f g) (pullback.fst f g).isOpenMap

end AlgebraicGeometry

end ZInQ.Contrib.CloudR2Poincare.L3.StacksPort
