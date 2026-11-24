/-
Cloud batch 3 W16 H99 port (2026-11-16).
Source: AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b, recovered
StacksFrontier/AlgebraicGeometry/Variety/Geometrically/ConnectedCriterion.lean.
Changes: Import paths moved to CloudB3W16Connected.
Citation attributes/commands and registration imports omitted; mathematical references retained.
The older vendoring notice below is retained as provenance, not a claim that
this additional port is unchanged. See LICENSE and NOTICE.md in this family.
-/
/-
H71 lane04 VENDORED copy (root-default, publication decision 2026-11-14) of `StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedCriterion`,
from AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b (original notices retained below). Original sha256 3ee67e7ff7cbcc5b073e50de7b88ae8173d75b7c9e3fc17eb909cf883a49cb8a.
Modification notice (2026-11-14): module path ZInQKernel.Contrib.CloudB3W16Connected.StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedCriterion; 2 import directive rewrite(s) to the
vendored/published module identities; 0 resolved `_c496` family rename(s) of declarations
colliding with the published fork graph; the original package type-inference/printing
options (autoImplicit, relaxedAutoImplicit, maxSynthPendingDepth, pp.unicode.fun) as
explicit `set_option` lines after the imports (diagnostic weak.linter options are left to
the root library). No other change.
-/
module

public import ZInQKernel.Contrib.CloudB3W16Connected.StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedGalois
public import ZInQKernel.Contrib.CloudB3W16Connected.StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedSeparableClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true


/-!
# A criterion for geometric connectedness

Let `T ⟶ X` be a morphism of schemes over a field. If `T` is geometrically connected and
`X` is connected, then `X` is geometrically connected.

## Main results

* `AlgebraicGeometry.geometricallyConnected_of_comp_of_connectedSpace` gives geometric
  connectedness of `X` from connectedness of `X` and geometric connectedness of a scheme
  mapping to it over the base field.

## Implementation notes

A scheme over `k` is represented by its structure morphism to `Spec k`. Given
`f : T ⟶ X` and the structure morphism `p : X ⟶ Spec k`, the induced structure morphism on
`T` is the composite `f ≫ p`; this incorporates the condition that `f` is a morphism over `k`.

## References

* [EGA IV, Corollaire 4.5.13.1(i)]
* [Stacks Project, Tag 056R](https://stacks.math.columbia.edu/tag/056R)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- If a connected scheme over a field admits a morphism over that field from a geometrically
connected scheme, then it is geometrically connected. -/

public lemma geometricallyConnected_of_comp_of_connectedSpace
    (k : Type u) [Field k] {T X : Scheme.{u}} (f : T ⟶ X)
    (p : X ⟶ Spec (.of k)) [GeometricallyConnected (f ≫ p)] [ConnectedSpace X] :
    GeometricallyConnected p := by
  let K := SeparableClosure k
  apply (geometricallyConnected_iff_connectedSpace_baseChange k K p).2
  by_contra h
  exact (not_connectedSpace_of_galois_baseChange k K f p
    (AlgebraicGeometry.pullback_of_geometrically
      (inferInstance : GeometricallyConnected (f ≫ p)).geometrically_connectedSpace K
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) h) ‹ConnectedSpace X›

end AlgebraicGeometry
