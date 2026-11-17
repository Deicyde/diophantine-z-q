/-
Cloud batch 3 W16 H99 port (2026-11-16).
Source: AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b, recovered
StacksFrontier/AlgebraicGeometry/Variety/Geometrically/ConnectedSeparablyClosed.lean.
Changes: Import paths moved to CloudB3W16Connected.
Citation attributes/commands and registration imports omitted; mathematical references retained.
Geometric connectedness of a field extension over a separably closed field follows directly from the recovered tensor-product connectedness theorem. Ring finite-separable criteria and their extra topology lemmas are not needed.
The older vendoring notice below is retained as provenance, not a claim that
this additional port is unchanged. See LICENSE and NOTICE.md in this family.
-/
/-
H71 lane04 VENDORED copy (root-default, publication decision 2026-11-14) of `StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedSeparablyClosed`,
from AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b (original notices retained below). Original sha256 efd7019c49973a81e273747ed4c586856fb2cd7dfc5891473305553075826725.
Modification notice (2026-11-14): module path ZInQKernel.Contrib.CloudB3W16Connected.StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedSeparablyClosed; 3 import directive rewrite(s) to the
vendored/published module identities; 0 resolved `_c496` family rename(s) of declarations
colliding with the published fork graph; the original package type-inference/printing
options (autoImplicit, relaxedAutoImplicit, maxSynthPendingDepth, pp.unicode.fun) as
explicit `set_option` lines after the imports (diagnostic weak.linter options are left to
the root library). No other change.
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import ZInQKernel.Contrib.CloudB3W16Connected.StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedAffine
public import ZInQKernel.Contrib.CloudB3W16Connected.StacksFrontier.RingTheory.TensorProduct.Connected

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true


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

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- Over a separably closed field, the spectrum of any field extension is geometrically
connected. -/
private lemma geometricallyConnected_spec (k k' : Type u) [Field k] [IsSepClosed k]
    [Field k'] [Algebra k k'] :
    GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap k k'))) :=
  (geometricallyConnected_spec_iff k k').2
    ⟨fun K _ _ ↦ Stacks.TensorProduct.ConnectedSpectrum.solution k K k'⟩

/-- **Stacks Project, Tag 0363.** Base change along any extension of a separably closed
field induces a bijection on the connected components of a scheme. -/

public theorem baseChange_connectedComponents_bijective
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

/-- **Stacks Project, Tag 0363.** Over a separably closed field, a scheme is geometrically
connected if and only if its underlying topological space is connected. -/

public theorem geometricallyConnected_iff_connectedSpace
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
