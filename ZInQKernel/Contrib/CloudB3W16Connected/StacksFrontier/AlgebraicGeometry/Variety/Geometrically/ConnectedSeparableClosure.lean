/-
Cloud batch 3 W16 H99 port (2026-11-16).
Source: AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b, recovered
StacksFrontier/AlgebraicGeometry/Variety/Geometrically/ConnectedSeparableClosure.lean.
Changes: Import paths moved to CloudB3W16Connected.
Citation attributes/commands and registration imports omitted; mathematical references retained.
Separable-closure equivalence proved directly from the recovered arbitrary-field-base-change and separably-closed-base equivalences, removing finite-separable-level/quasi-compact-open scheme descent.
The older vendoring notice below is retained as provenance, not a claim that
this additional port is unchanged. See LICENSE and NOTICE.md in this family.
-/
/-
H71 lane04 VENDORED copy (root-default, publication decision 2026-11-14) of `StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedSeparableClosure`,
from AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b (original notices retained below). Original sha256 6afc7b6718f49027d349c041e0001c5afb160336da6df5e08b9761de2140d37f.
Modification notice (2026-11-14): module path ZInQKernel.Contrib.CloudB3W16Connected.StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedSeparableClosure; 2 import directive rewrite(s) to the
vendored/published module identities; 0 resolved `_c496` family rename(s) of declarations
colliding with the published fork graph; the original package type-inference/printing
options (autoImplicit, relaxedAutoImplicit, maxSynthPendingDepth, pp.unicode.fun) as
explicit `set_option` lines after the imports (diagnostic weak.linter options are left to
the root library). No other change.
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import ZInQKernel.Contrib.CloudB3W16Connected.StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedBaseChange
public import ZInQKernel.Contrib.CloudB3W16Connected.StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedSeparablyClosed

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true


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

@[expose] public section

open CategoryTheory Limits CommRingCat

namespace AlgebraicGeometry

universe u

/-- A scheme over a field is geometrically connected if and only if its base change to a
separable algebraic closure is connected. -/

public theorem geometricallyConnected_iff_connectedSpace_baseChange
    (k : Type u) [Field k] (ksep : Type u) [Field ksep] [Algebra k ksep]
    [IsSepClosure k ksep] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    GeometricallyConnected f ↔
      ConnectedSpace
        (CategoryTheory.Limits.pullback f
          (Spec.map (CommRingCat.ofHom (algebraMap k ksep))) : Scheme.{u}) := by
  let : IsSepClosed ksep := IsSepClosure.sep_closed (k := k) (K := ksep)
  rw [geometricallyConnected_iff_baseChange_fieldExtension k ksep f,
    geometricallyConnected_iff_connectedSpace]

end AlgebraicGeometry
