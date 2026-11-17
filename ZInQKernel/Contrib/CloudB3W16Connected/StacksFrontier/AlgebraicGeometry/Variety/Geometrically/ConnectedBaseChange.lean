/-
Cloud batch 3 W16 H99 port (2026-11-16).
Source: AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b, recovered
StacksFrontier/AlgebraicGeometry/Variety/Geometrically/ConnectedBaseChange.lean.
Changes: Import paths moved to CloudB3W16Connected.
Citation attributes/commands and registration imports omitted; mathematical references retained.
The older vendoring notice below is retained as provenance, not a claim that
this additional port is unchanged. See LICENSE and NOTICE.md in this family.
-/
/-
H71 lane04 VENDORED copy (root-default, publication decision 2026-11-14) of `StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedBaseChange`,
from AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b (original notices retained below). Original sha256 b979c86a1cb77d544806097aa79eb0429d21637d2d16e3787094a75e94d43409.
Modification notice (2026-11-14): module path ZInQKernel.Contrib.CloudB3W16Connected.StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedBaseChange; 2 import directive rewrite(s) to the
vendored/published module identities; 0 resolved `_c496` family rename(s) of declarations
colliding with the published fork graph; the original package type-inference/printing
options (autoImplicit, relaxedAutoImplicit, maxSynthPendingDepth, pp.unicode.fun) as
explicit `set_option` lines after the imports (diagnostic weak.linter options are left to
the root library). No other change.
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import ZInQKernel.Contrib.CloudB3W16Connected.StacksCore.RingTheory.Flat.FaithfullyFlat.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true


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

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- **Stacks Project, Tag 054N.** A scheme over a field is geometrically connected if and only if
its base change along a field extension is geometrically connected. -/

public theorem geometricallyConnected_iff_baseChange_fieldExtension
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
